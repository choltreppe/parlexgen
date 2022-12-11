import fusion/matching
import std/[macros, genasts, sugar, sequtils, strutils, tables, sets, options, algorithm]
export sets

import ./private/utils, ./common

# runtime
type
  SymbolKind = enum symTerminal, symNonTerminal
  Symbol[T, N] = object
    case kind: SymbolKind
    of symTerminal: token: T
    of symNonTerminal: nt: N

  ActionKind = enum actionNone, actionShift, actionReduce, actionAccept
  Action* = object
    case kind: ActionKind
    of actionShift:  goto: int
    of actionReduce: id:   int
    else: discard
  ActionTable[S: static int, T: enum] = array[S, tuple[terminals: array[T, Action], eof: Action]]

  GotoTable[S, N: static int] = array[S, array[N, int]]

  ParsingError* = ref object of CatchableError

func `$`*(symbol: Symbol): string =
  case symbol.kind
  of symTerminal: $symbol.token.kind
  of symNonTerminal: $symbol.nt

# meta
type
  MSymbolKind = enum mSymTerminal, mSymNonTerminal
  MSymbol[T: enum] = object
    case kind: MSymbolKind
    of mSymTerminal:    tk: T
    of mSymNonTerminal: id: int
  MRuleRhs[T: enum] = object
    pattern: seq[MSymbol[T]]
    blockId: int  # id for reduce action and error handler
  MRules[T: enum] = seq[MRuleRhs[T]]

  MRuleId = tuple[rule,rhs: int]
  MRuleIdDotted = tuple
    id: MRuleId
    dotPos: int
  MTerminalOrEof[T: enum] = object
    case isEOF: bool
    of true: discard
    else: tk: T
  MLookahead[T: enum] = HashSet[MTerminalOrEof[T]]
  MItem[T: enum] = object
    ruleIdDot: MRuleIdDotted
    lookahead: MLookahead[T]

func `==`*[T](a, b: MSymbol[T]): bool =  # not liking that its exported but for some wierd binding reasons it has to
  if a.kind == b.kind:
    case a.kind
    of mSymTerminal:    a.tk == b.tk
    of mSymNonTerminal: a.id == b.id  
  else: false

func newTerminal[T](tk: T):
  MSymbol[T] = MSymbol[T](kind: mSymTerminal, tk: tk)
func newNonTerminal[T](td: typedesc[T], id: int):
  MSymbol[T] = MSymbol[T](kind: mSymNonTerminal, id: id)

func `[]`[T](rules: seq[MRules[T]], id: MRuleId): MRuleRhs[T] =
  rules[id.rule][id.rhs]

func `==`*[T](a, b: MTerminalOrEof[T]): bool =  # not liking that its exported but for some wierd binding reasons it has to
  if (not a.isEOF) and (not b.isEOF):
    a.tk == b.tk 
  else:
    a.isEOF and b.isEOF

func `<`[T](a,b: MItem[T]): bool = a.ruleIdDot < b.ruleIdDot


proc makeParsingTables[T](ruleSets: seq[MRules[T]], ntNum: int): tuple[action, goto: NimNode, stateNum: int] =
  let ruleSets = ruleSets  # fix for wierd compiler bug

  # --- generate parsing table: ---

  proc findFirstSet(symbol: MSymbol): HashSet[T] =
    var visited: HashSet[int]
    proc findRec(symbol: MSymbol): HashSet[T] =
      case symbol.kind
      of mSymTerminal:
        result.incl symbol.tk
      of mSymNonTerminal:
        if symbol.id notin visited:
          visited.incl symbol.id
          for rhs in ruleSets[symbol.id]:
            result.incl findRec(rhs.pattern[0])

    findRec(symbol)

  let firstSets: seq[MLookahead[T]] = collect:
    for ntId in 0 ..< ntNum:
      findFirstSet(newNonTerminal(T, ntId)).map(
        proc(tk: T): MTerminalOrEof[T] = MTerminalOrEof[T](isEOF: false, tk: tk)
      )

  # - build automaton: -

  proc isRuleEnd(ruleIdDot: MRuleIdDotted): bool =
    ruleIdDot.dotPos == len(ruleSets[ruleIdDot.id].pattern)

  var
    adjacencyMat: seq[seq[Option[MSymbol[T]]]]
    stateItems: seq[seq[MItem[T]]]
    stateLookup: Table[seq[MRuleIdDotted], int]

  # returns state id
  # items are just the initial ones with no closure
  proc buildStateMashine(items: seq[MItem[T]]): int =

    proc findTransitions(currentState: int, items: seq[MItem[T]]) =
      var
        lookaheadTable: Table[MRuleIdDotted, MLookahead[T]]
        transitions: Table[MSymbol[T], seq[MRuleIdDotted]]  # the dotted rule is without the shift (because I need to lookup lookahead)

      proc closure(ruleIdDot: MRuleIdDotted, lookahead: MLookahead[T]) =
        if ruleIdDot in lookaheadTable:
          lookaheadTable[ruleIdDot].incl lookahead

        else:
          assert not isRuleEnd(ruleIdDot)
          lookaheadTable[ruleIdDot] = lookahead
          let pattern = ruleSets[ruleIdDot.id].pattern
          let symbol = pattern[ruleIdDot.dotPos]

          if symbol in transitions:
            transitions[symbol] &= ruleIdDot
          else:
            transitions[symbol] = @[ruleIdDot]

          if symbol.kind == mSymNonTerminal:
            let nextLookahead =
              if ruleIdDot.dotPos == high(pattern):
                lookahead
              else:
                let nextSymbol = pattern[ruleIdDot.dotPos + 1]
                case nextSymbol.kind
                of mSymTerminal:    toHashSet([MTerminalOrEof[T](isEOF: false, tk: nextSymbol.tk)])
                of mSymNonTerminal: firstSets[nextSymbol.id]
            for i in 0 .. high(ruleSets[symbol.id]):
              closure(
                (id: (symbol.id, i), dotPos: 0),
                nextLookahead
              )

      for item in items:
        if not isRuleEnd(item.ruleIdDot):
          closure(item.ruleIdDot, item.lookahead)

      for (symbol, rulesIdDot) in transitions.mpairs:
        sort rulesIdDot
        let newItems =
          rulesIdDot.mapIt(MItem[T](
            ruleIdDot: (id: it.id, dotPos: it.dotPos + 1),
            lookahead: lookaheadTable[it]
          ))
        adjacencyMat[currentState][buildStateMashine(newItems)] = some(symbol)

    let rulesIdDot = items.mapIt(it.ruleIdDot)

    # case: similar state exists (at most differs in lookahead)
    if rulesIdDot in stateLookup:
      let oldState = stateLookup[rulesIdDot]
      var oldItems = stateItems[oldState]
      assert len(oldItems) == len(items)

      var newLookahead = false
      for (i, item) in items.pairs:
        if not(item.lookahead <= oldItems[i].lookahead):
          newLookahead = true
          # update lookahead:
          stateItems[oldState][i].lookahead = oldItems[i].lookahead + item.lookahead

      # if lookahead changed cascade update:
      if newLookahead:
        findTransitions(oldState, items)

      oldState

    # case: no similar state exists:
    else:
      # add state to matrix:
      stateItems &= items
      let currentState = high(stateItems)
      stateLookup[rulesIdDot] = currentState
      adjacencyMat &= newSeqWith(len(adjacencyMat), none(MSymbol[T]))
      for row in adjacencyMat.mitems:
        row &= none(MSymbol[T])

      # find transitions:
      findTransitions(currentState, items)

      currentState

  discard buildStateMashine(@[MItem[T](ruleIdDot: ((0, 0), 0), lookahead: toHashSet([MTerminalOrEof[T](isEOF: true)]))])

  # - build parsing table: -

  var
    actionTable = newSeq[tuple[terminals: array[T, Action], eof: Action]](len(stateItems))
    gotoTable = newSeqWith(len(stateItems), newSeqWith(ntNum, -1))  # (from state, nonterminal) -> target state

  for (fromState, row) in adjacencyMat.pairs:

    template addActionIfNone(fromState: int, terminal: MTerminalOrEof[T], action: Action) =
      if terminal.isEOF:
        if actionTable[fromState].eof.kind == actionNone:
          actionTable[fromState].eof = action
        continue
      else:
        if actionTable[fromState].terminals[terminal.tk].kind == actionNone:
          actionTable[fromState].terminals[terminal.tk] = action
        continue

    # reduces:
    for item in stateItems[fromState]:
      if isRuleEnd(item.ruleIdDot):
        let ruleId = item.ruleIdDot.id

        if ruleId == (0, 0):
          actionTable[fromState].eof = Action(kind: actionAccept)

        else:
          let blockId = ruleSets[item.ruleIdDot.id].blockId
          for terminal in item.lookahead:
            addActionIfNone(fromState, terminal, Action(kind: actionReduce, id: blockId))
            # else conflict:
            error "reduce/reduce conflict"

    for (toState, symbol) in row.pairs:
      if Some(@symbol) ?= symbol:
        case symbol.kind

        # shift:
        of mSymTerminal:
          let terminal = MTerminalOrEof[T](isEOF: false, tk: symbol.tk)
          addActionIfNone(fromState, terminal, Action(kind: actionShift, goto: toState))
          # else conflict:
          error "shift/.. conflict" #TODO: proper error 

        # goto:
        of mSymNonTerminal:
          assert gotoTable[fromState][symbol.id] < 0
          gotoTable[fromState][symbol.id] = toState


  result.action = genAst(actionTable): actionTable
  result.action = result.action[1]
  result.goto   = quote do: `gotoTable`
  result.stateNum = len(stateItems)



macro makeParser*(head,body: untyped): untyped =
  
  func ntFieldIdent(id: int): NimNode = ident("t" & $id)

  let (procIdent, tokenType) = getProcMeta(head)

  let tokenKindType = genSym(nskType, "TokenKind")
  let getTokenKindType = quote do:
    type `tokenKindType` = typeof(`tokenType`().kind)

  let
    nonterminalType = genSym(nskType, "NonTerminal")
    symbolType = quote do: Symbol[`tokenType`, `nonterminalType`]

  let
    actionTable  = genSym(nskConst, "actionTable")
    gotoTable    = genSym(nskConst, "gotoTable"  )
    stack        = genSym(nskVar, "stack")
    curState     = genSym(nskVar, "state")
    curToken     = genSym(nskLet, "token")
    curTokenKind = genSym(nskLet, "tokenKind")
    curReduceId  = genSym(nskLet, "reduceId")
    errorId      = genSym(nskForVar, "id")
    tokenForError = ident"token"
    errorDotPos   = genSym(nskForVar, "pos")
    errorDotPosRanged = ident"pos"

  body.expectKindError(nnkStmtList, "expected list of rules")

  # --- collect nonterminals: ---

  # there is already 1 terminal with no type for S' start symbol
  var
    nonterminals:    seq[tuple[name: string, resTypeId: int]] = @[("", 0)]
    nonterminalInfo: Table[string, tuple[id, resTypeId: int]]
    resTypes:        seq[NimNode]
    resTypeNtMap:    seq[seq[int]]  # resType id -> seq[nt ids that have that type]

  for (i, rules) in body.pairs:
    rules.expectKindError(nnkCall, "expected collection of rules for a nonterminal")
    rules[0].expectKindError(nnkBracketExpr, "expected nonterminal with type")
    rules[0][0].expectKindError(nnkIdent, "expected nonterminal name")
    rules[1].expectKind(nnkStmtList)

    let name = rules[0][0].strVal.nimIdentNormalize
    let resType = rules[0][1]

    let resTypeId =
      if (let id = resTypes.find(resType); id) != -1: id
      else:
        resTypes &= resType
        resTypeNtMap &= @[]
        high(resTypes)
    assertError(name notin nonterminalInfo, "double definition of nonterminal", resType)  # not really the correct node but close enough
    nonterminals &= (name, resTypeId)
    nonterminalInfo[name] = (high(nonterminals), resTypeId)
    resTypeNtMap[resTypeId] &= high(nonterminals)

  # --- build nonterminals type: ---

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
          ntFieldIdent(id),
          resTypes[id],
          newEmptyNode()
        )
      variants.add branch

    nnkObjectTy.newTree(newEmptyNode(), newEmptyNode(), nnkRecList.newTree(variants))

  # --- parse rules (generate code that builds rules): ---
  # --- and build reduce case stmt:
  
  # this is where da magic happens :)
  # I need to generate code that will be used to generate a macro.
  # This macro-ception is needed to unroll for loops (and allow any CT expr, that results in token.kind for terminals) 
  # TODO: for loop unrolling

  let blockId = genSym(nskVar, "blockId")

  var
    reduceCaseStmt = genSym(nskVar, "reduceCaseStmt")
    reduceCaseStmtCollect = quote do:
      var `blockId` = 0
      var `reduceCaseStmt` = nnkCaseStmt.newTree()
      `reduceCaseStmt`.add:
        genAst(): `curReduceId`
    
    errorBlocks: seq[NimNode]

  let ruleDefs   = genSym(nskVar, "ruleDefs")
  var ruleDefsCollect = quote do:
    var `blockId` = 0
    var `ruleDefs` = @[@[MRuleRhs[`tokenKindType`](pattern: @[newNonTerminal(`tokenKindType`, 1)], blockId: -1)]]

  for (i, rules) in body.pairs:
    let ntId = i+1

    let rhsDefs = genSym(nskVar, "rhsDefs" )
    ruleDefsCollect.add quote do:
      var `rhsDefs`: seq[MRuleRhs[`tokenKindType`]]
    
    let
      reduceResTypeId = nonterminals[ntId].resTypeId
      reduceResType = resTypes[reduceResTypeId]

    proc genAddRule(rule: NimNode, captures: seq[NimNode] = @[]): tuple[rule,reduce: NimNode] =

      rule.expectKindError(nnkIfStmt, "expected if statement")
      rule[0].expectKind(nnkElifBranch)

      var ruleDefsCollect = newStmtList()

      let patternDef = genSym(nskVar, "patternDef")
      ruleDefsCollect.add quote do:
        var `patternDef`: seq[MSymbol[`tokenKindType`]] = @[]

      errorBlocks.add:
        case len(rule)
        of 1: newEmptyNode()
        of 2:
          rule[1].expectKindError(nnkElse, "unexpected elif")
          rule[1][0]
        else:
          error "unexpected elifs", rule
          newEmptyNode()

      let reduceBody = rule[0][1]
      var reducePatternVar = nnkTupleConstr.newTree()

      proc parseSymbol(l: int, sym: NimNode) =
        let revIndex = l - len(reducePatternVar)
        if sym.kind in {nnkIdent, nnkSym} and
           (let symName = sym.strVal.nimIdentNormalize;
            symName in nonterminalInfo):
          let (ntId, resTypeId) = nonterminalInfo[symName]
          let field = ntFieldIdent(resTypeId)
          reducePatternVar.add quote do: `stack`[^`revIndex`][0].nt.`field`
          ruleDefsCollect.add quote do:
            `patternDef` &= newNonTerminal(`tokenKindType`, `ntId`)

        else:
          reducePatternVar.add quote do: `stack`[^`revIndex`][0].token
          ruleDefsCollect.add quote do:
            `patternDef` &= newTerminal(`sym`)

      let pattern = rule[0][0]
      case pattern.kind
      of nnkTupleConstr:
        for sym in pattern: parseSymbol(len(pattern), sym)
      of nnkPar:
        parseSymbol(1, pattern[0])
      else:
        parseSymbol(1, pattern)

      let field = ntFieldIdent(nonterminals[ntId].resTypeId)
      let patternLen = len(reducePatternVar)
      let s = ident"s"
      var genAstCall = quote do: genAst(`s` = ident"s")
      for c in captures: genAstCall.add c
      genAstCall.add quote do:
        let `s` = `reducePatternVar`
        `stack`.setLen(len(`stack`) - `patternLen`)
        let originState =
          if len(`stack`) > 0: `stack`[^1].state
          else: 0
        `curState` = `gotoTable`[originState][`ntId`]
        assert `curState` >= 0
        `stack` &= (
          `symbolType`(
            kind: symNonTerminal,
            nt: `nonterminalType`(
              id: `ntId`,
              `field`: block: `reduceBody`
            )
          ),
          `curState`
        )
      result.reduce = quote do:
        `reduceCaseStmt`.add nnkOfBranch.newTree(
          newLit(`blockId`),
          `genAstCall`
        )
        inc `blockId`

      ruleDefsCollect.add quote do:
        `rhsDefs` &= MRuleRhs[`tokenKindType`](pattern: `patternDef`, blockId: `blockId`)
        inc `blockId`
      result.rule = ruleDefsCollect

    for rule in rules[1]:
      if rule.kind == nnkForStmt:
        let parts = forLoopParts(rule)
        parts.body.expectKind(nnkStmtList)
        var loopBodyRule   = newStmtList()
        var loopBodyReduce = newStmtList()
        for rule in parts.body:
          let addNode = genAddRule(rule, parts.idents)
          loopBodyRule.add   addNode.rule
          loopBodyReduce.add addNode.reduce
        var forLoopRule   = nnkForStmt.newTree()
        var forLoopReduce = nnkForStmt.newTree()
        for elem in parts.elems:
          forLoopRule.add   elem
          forLoopReduce.add elem
        forLoopRule.add   parts.vals, loopBodyRule
        forLoopReduce.add parts.vals, loopBodyReduce
        ruleDefsCollect.add       forLoopRule
        reduceCaseStmtCollect.add forLoopReduce

      else:
        let addNode = genAddRule(rule)
        ruleDefsCollect.add       addNode.rule
        reduceCaseStmtCollect.add addNode.reduce

    ruleDefsCollect.add quote do:
      `ruleDefs` &= `rhsDefs`

  reduceCaseStmtCollect.add quote do:
    `reduceCaseStmt`.add nnkElse.newTree(newStmtList(
      quote do: assert false
    ))

  debugEcho reduceCaseStmtCollect.repr

  # --- build parser: ---

  let
    procResType = resTypes[nonterminals[1].resTypeId]
    resTypeField = ntFieldIdent(nonterminals[1].resTypeId)

  let ntNum = len(nonterminals)
  result = quote do:

    `getTokenKindType`
    type `nonterminalType` = `nonterminalTypeDef`
    
    macro getParsingTables(actionTable, gotoTable: untyped): untyped =
      `ruleDefsCollect`
      let (action, goto, stateNum) = makeParsingTables(`ruleDefs`, `ntNum`)
      genAst(action, goto, stateNum, actionTable, gotoTable):
        const
          actionTable: ActionTable[stateNum, `tokenKindType`] = action
          gotoTable:   GotoTable[stateNum, `ntNum`]           = goto

    getParsingTables(`actionTable`, `gotoTable`)

    #const stateErrorData : array[`stateNum`, seq[tuple[id,pos: int]]] = `stateErrorDataDef`

    proc `procIdent`(code: string, lexProc: LexerProc[`tokenType`]): `procResType` =

      var
        `stack`: seq[tuple[s: `symbolType`, state: int]]
        `curState` = 0
        pos = 0

        lexerState = initLexerState()
        token = lexProc(code, lexerState)

      while true:

        let actionRow = `actionTable`[`curState`]
        let action =
          if token.isSome: actionRow.terminals[token.unsafeGet.kind]
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
          let `curReduceId` = action.id
          macro getReduceCaseStmt: untyped =
            `reduceCaseStmtCollect`
            `reduceCaseStmt`
          getReduceCaseStmt()

        of actionAccept:
          assert len(`stack`) == 1
          return `stack`[0].s.nt.`resTypeField`

        of actionNone:
          raise ParsingError(msg: "parsing failed")

          #[let `tokenForError` = token
          {.warning[UnreachableCode]:off.}
          for (`errorId`, `errorDotPos`) in stateErrorData[`curState`]:
            `errorHandlingCaseStmt`
          raise ParsingError(msg: "parsing failed")
          {.warning[UnreachableCode]:on.}]#

  #debugEcho result.repr
