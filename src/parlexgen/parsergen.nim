import fusion/matching
import std/[macros, genasts, sugar, sequtils, strutils, tables, sets, options, algorithm, base64]
import unibs

import ./private/utils, ./common
import ./private/parsergen/types


type ParsingError*[T: object, K: enum] = ref object of CatchableError
  token*: Option[T]
  expectedTerminals*: set[K]
  expectedEOF*: bool


macro makeParser*(head,body: untyped): untyped =

  const nonterminalVariantPrefix = "t"
  let
    matchedRuleTuple = ident"s"
    nonterminalType = genSym(nskType, "NonTerminal")

  # --- meta infos: ---

  let (procIdent, tokenType) = getProcMeta(head)

  let tokenKindType = genSym(nskType, "TokenKind")
  let getTokenKindType = quote do:
    type `tokenKindType` = typeof(`tokenType`().kind)

  # --- collect nonterminals: ---

  body.expectKindError(nnkStmtList, "expected list of rules")

  # there is already 1 terminal with no type for S' start symbol
  var
    nonterminals:    seq[tuple[name: string, resTypeId: int]] = @[("", 0)]
    nonterminalInfo: Table[string, tuple[id, resTypeId: int]]
    resTypes:        seq[NimNode]
    resTypeNtMap:    seq[seq[int]]  # resType id -> seq[nt ids that have that type]

  for (i, def) in body.pairs:
    def.expectKindError(nnkCall, "expected rhs parts of rule")
    def[0].expectKindError(nnkBracketExpr, "expected nonterminal with type")
    def[0][0].expectKindError(nnkIdent, "expected nonterminal name")
    let name    = def[0][0].strVal.nimIdentNormalize
    let resType = def[0][1]
    let resTypeId =
      if (let id = resTypes.find(resType); id) != -1: id
      else:
        resTypes &= resType
        resTypeNtMap &= @[]
        high(resTypes)
    assertError(name notin nonterminalInfo, "double definition of nonterminal", def[0][0])
    nonterminals &= (name, resTypeId)
    nonterminalInfo[name] = (high(nonterminals), resTypeId)
    resTypeNtMap[resTypeId] &= high(nonterminals)

  # --- parse rules: ---

  var
    rules: seq[MRules]  # lhs (nont. id) -> seq[rhs] (options)
    actionBodys: seq[NimNode]
    patternLineInfo: seq[LineInfo]  # only for compilation errors
    patternLens: seq[int]  # reduceId -> pattern len
    errorHandlers: seq[tuple[code: NimNode, patternIds: seq[int]]]

  # start rule: S' -> S
  rules &= @[MRuleRhs(pattern: @[newNonTerminal(1)], patternId: -1)]

  var nextPatternId = 0
  for (i, def) in body.pairs:
    def[1].expectKind(nnkStmtList)
    
    rules &= @[]
    for rhsDef in def[1]:

      proc parseRhs(node: NimNode): MRuleRhs =
        result = MRuleRhs(patternId: nextPatternId)
        inc nextPatternId

        proc parseSymbol(i: int, sym: NimNode, single = false): MSymbol =
          sym.expectKindError(nnkIdent,
            if single: "expected a nonterminal or terminal (token kind) or list of those in ()"
            else: "expected a nonterminal or terminal (token kind)"
          )
          let symName = sym.strVal.nimIdentNormalize
          if symName in nonterminalInfo:
            newNonTerminal(nonterminalInfo[symName].id)
          else:
            newTerminal(symName)

        node.expectKindError(nnkCall, "expected a rhs pattern followed by code")
        assertError(len(node) == 2, "expected a rhs pattern followed by code", node)

        let pattern = node[0]
        case pattern.kind
        of nnkTupleConstr:
          for (i, sym) in pattern.pairs:
            result.pattern &= parseSymbol(i, sym)
        of nnkPar:
          result.pattern &= parseSymbol(0, pattern[0], single = true)
        else:
          result.pattern &= parseSymbol(0, pattern, single = true)

        patternLens &= len(result.pattern)
        actionBodys &= node[1]

      if rhsDef.kind == nnkTryStmt:
        var patternIds: seq[int]
        if rhsDef[0].kind != nnkStmtList:
          patternIds &= nextPatternId
          rules[^1] &= parseRhs(rhsDef[0])
        else:
          for node in rhsDef[0]: 
            patternIds &= nextPatternId
            rules[^1] &= parseRhs(node)

        if len(rhsDef) > 1:
          assertError(len(rhsDef) == 2, "cant difine multiple error handler. just one `except` per rule allowed", rhsDef)
          assertError(len(rhsDef[1]) == 1, "error handling `except`s don't have any parameters", rhsDef[1])
          errorHandlers.add (rhsDef[1][0], patternIds)

      else:
        rules[^1] &= parseRhs(rhsDef)

      patternLineInfo &= rhsDef[0].lineInfoObj

  # assert all nts just have one ruleset
  assert len(nonterminals) == len(rules)

  # --- build parsing table: ---

  let (actionTable, gotoTable, stateItems) = block:
    let data = (rules, nonterminals.mapIt(it.name), patternLineInfo).serialize.encode
    let res = execCompiled("parsergen/tablegen", data&"\n")
    res.decode.deserialize((seq[Table[MTerminal, Action]], seq[seq[int]], seq[seq[MItem]]))

  # --- build code: ---

  result = block:
    let
      procResType = resTypes[0]
      symbolType = quote do: Symbol[`tokenType`, `nonterminalType`]

      action       = genSym(nskConst, "action")
      goto         = genSym(nskConst, "goto" )
      stack        = genSym(nskVar, "stack")
      curState     = genSym(nskVar, "state")
      curToken     = genSym(nskLet, "token")
      curTokenKind = genSym(nskLet, "tokenKind")
      nextPatternId  = genSym(nskLet, "patternId")
      errorId      = genSym(nskForVar, "id")
      tokenForError = ident"token"
      errorDotPos   = genSym(nskForVar, "pos")
      errorDotPosRanged = ident"pos"
      
      kindField = ident"kind"  # just too workaround a quote bug

    let nonterminalTypeDef = block:
      var variants =
        nnkRecCase.newTree(
          nnkIdentDefs.newTree(
            ident"id",
            infix(newLit(0), "..", newLit(high(nonterminals))),
            newEmptyNode()
          ),
          nnkOfBranch.newTree(newLit(0), newNilLit())
        )
      for (id, nts) in resTypeNtMap.pairs:
        var branch = nnkOfBranch.newTree()
        for nt in nts:
          branch.add newLit(nt)
        branch.add:
          nnkIdentDefs.newTree(
            ident(nonterminalVariantPrefix & $id),
            resTypes[id],
            newEmptyNode()
          )
        variants.add branch

      nnkObjectTy.newTree(newEmptyNode(), newEmptyNode(), nnkRecList.newTree(variants))

    let gotoTableDef = block:
      var table = nnkBracket.newTree()
      for r in gotoTable:
        var row = nnkBracket.newTree()
        for v in r: row.add newLit(v)
        table.add row
      table

    let actionTableDef = block:
      var table = nnkBracket.newTree()
      let terminals = genSym(nskVar, "row")
      for r in actionTable:
        var rowCollect = newStmtList()
        var onEof = Action(kind: actionNone)
        rowCollect.add quote do:
          var `terminals`: array[`tokenKindType`, Action]
        for (t, action) in r.pairs:
          if t == "": onEof = action
          else:
            let tokenKind = ident(t)
            rowCollect.add:
              genAst(terminals, tokenKind, action):
                terminals[tokenKind] = action
        rowCollect.add:
          genAst(terminals, onEof): (terminals, onEof)
        table.add quote do:
          block: `rowCollect`
      table

    let reduceCaseStmt = block:
      var caseStmt = nnkCaseStmt.newTree(nextPatternId)

      for (lhsm1, rules) in rules[1..^1].pairs:
        for (rhsId, rhs) in rules.pairs:
          var branch = nnkOfBranch.newTree(newLit(rhs.patternId))

          let lhs = lhsm1 + 1
          let patternLen = len(rhs.pattern)

          var branchBody = newStmtList: quote do:
            assert len(`stack`) >= `patternLen`

          var matchedRuleTupleDef = nnkTupleConstr.newTree()

          for (i, symbol) in rhs.pattern.pairs:
            let elem = genSym(nskLet, "elem")
            let revIndex = patternLen-i

            branchBody.add quote do:
              let (`elem`, _) = `stack`[^`revIndex`]

            case symbol.kind
            of mSymTerminal:
              let terminal = ident(symbol.name)
              branchBody.add quote do:
                assert `elem`.kind == symTerminal
                assert `elem`.token.kind == `terminal`
              matchedRuleTupleDef.add quote do:
                `elem`.token

            of mSymNonTerminal:
              let ntId = symbol.id
              let field = ident(nonterminalVariantPrefix & $nonterminals[ntId].resTypeId)
              branchBody.add quote do:
                assert `elem`.kind == symNonTerminal
                assert `elem`.nt.id == `ntId`
              matchedRuleTupleDef.add quote do:
                `elem`.nt.`field`

          let field  = ident(nonterminalVariantPrefix & $nonterminals[lhs].resTypeId)
          let action = actionBodys[rhs.patternId]
          action.expectKind(nnkStmtList)
          branchBody.add: quote do:
            let `matchedRuleTuple` = `matchedRuleTupleDef`
            `stack`.setLen(len(`stack`) - `patternLen`)
            let originState =
              if len(`stack`) > 0: `stack`[^1].state
              else: 0
            `curState` = `goto`[originState][`lhs`]
            assert `curState` >= 0
            `stack` &= (
              `symbolType`(
                kind: symNonTerminal,
                nt: `nonterminalType`(
                  id: `lhs`,
                  `field`: block: `action`
                )
              ),
              `curState`
            )

          branch.add branchBody
          caseStmt.add branch

      caseStmt.add nnkElse.newTree(
        quote do: assert false
      )

      caseStmt

    # saves rule setup of what might be reduced in the future for error handling
    let stateErrorDataDef = block:
      var lookup = nnkBracket.newTree()
      for items in stateItems:
        var data: seq[tuple[id,pos: int]]
        for item in items:
          let rhs = rules[item.ruleIdDot.id]
          let id = rhs.patternId
          if id >= 0:
            data &= (id, item.ruleIdDot.dotPos)
        lookup.add:
          genAst(data): data
      lookup

    let errorHandlingCaseStmt = block:
      var caseStmt = nnkCaseStmt.newTree(errorId)
      for (body, patternIds) in errorHandlers:
        if len(patternIds) == 1:
          let l = patternLens[patternIds[0]]
          caseStmt.add nnkOfBranch.newTree(
            newLit(patternIds[0]),
            quote do:
              let `errorDotPosRanged` = range[0 .. `l`](`errorDotPos`)
              `body`
          )
        else:
          var branch = nnkOfBranch.newTree()
          for id in patternIds:
            branch.add newLit(id)
          branch.add body
          caseStmt.add branch

      caseStmt.add nnkElse.newTree(
        quote do: discard
      )

      caseStmt


    let
      resTypeField = ident(nonterminalVariantPrefix & $0)
      stateNum = newLit(len(stateItems))
      ntNum = newLit(len(nonterminals))

    quote do:
      proc `procIdent`(code: string, lexProc: LexerProc[`tokenType`]): `procResType` =

        type `nonterminalType` = `nonterminalTypeDef`

        `getTokenKindType`

        const
          `goto`   : GotoTable[`stateNum`, `ntNum`]  = `gotoTableDef`
          `action` : ActionTable[`stateNum`, `tokenKindType`] = `actionTableDef`

          stateErrorData : array[`stateNum`, seq[tuple[id,pos: int]]] = `stateErrorDataDef`

        let possibleTokens = block:  # cant make that const (no idea why)
            var res: array[`stateNum`, tuple[terminals: set[`tokenKindType`], eof: bool]]
            for state, actions in `action`:
              for terminal, action in actions.terminals:
                if action.kind != actionNone:
                  res[state].terminals.incl terminal
              res[state].eof = actions.eof.kind != actionNone
            res

        var
          `stack`: seq[tuple[s: `symbolType`, state: int]]
          `curState` = 0
          pos = 0

          lexerState = initLexerState()
          token = lexProc(code, lexerState)

        while true:

          let actionRow = `action`[`curState`]
          let action =
            if options.isSome(token): actionRow.terminals[options.unsafeGet(token).kind]
            else: actionRow.eof

          case action.kind
          of actionShift:
            `curState` = action.goto
            `stack` &= (
              `symbolType`(kind: symTerminal, token: token.get),
              `curState`
            )
            token = lexProc(code, lexerState)

          of actionReduce:
            let `nextPatternId` = action.id
            {.hint[XDeclaredButNotUsed]:off.}
            `reduceCaseStmt`
            {.hint[XDeclaredButNotUsed]:on.}

          of actionAccept:
            assert len(`stack`) == 1
            return `stack`[0].s.nt.`resTypeField`

          of actionNone:
            let `tokenForError` = token
            {.warning[UnreachableCode]:off.}
            for (`errorId`, `errorDotPos`) in stateErrorData[`curState`]:
              `errorHandlingCaseStmt`
            raise ParsingError[`tokenType`, `tokenKindType`](
              msg: "parsing failed",
              token: token,
              expectedTerminals: possibleTokens[`curState`].terminals,
              expectedEOF: possibleTokens[`curState`].eof
            )
            {.warning[UnreachableCode]:on.}