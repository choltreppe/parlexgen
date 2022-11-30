import fusion/matching
import std/[macros, genasts, sugar, sequtils, strutils, tables, sets, options, algorithm]

import ./utils

# runtime
type
  SymbolKind = enum symTerminal, symNonTerminal
  Symbol[T, N] = object
    case kind: SymbolKind
    of symTerminal: token: T
    of symNonTerminal: nt: N

  ActionKind = enum actionNone, actionShift, actionReduce, actionAccept
  Action = object
    case kind: ActionKind
    of actionShift:  goto: int
    of actionReduce: id:   int
    else: discard
  ActionTable[L: static int, T: enum] = array[L, tuple[terminals: array[T, Action], eof: Action]]

  GotoTable[L, N: static int] = array[L, array[N, int]]

func `$`*(symbol: Symbol): string =
  case symbol.kind
  of symTerminal: $symbol.token.kind
  of symNonTerminal: $symbol.nt

# meta
type
  MTerminal = string  # token kind  (empty string means $)
  MNonTerminal = int  # id
  MSymbolKind = enum mSymTerminal, mSymNonTerminal
  MSymbol = object
    case kind: MSymbolKind
    of mSymTerminal:    name: MTerminal
    of mSymNonTerminal: id:   MNonTerminal
  MRuleRhs = object
    pattern: seq[MSymbol]
    reduceId: int
  MRules = seq[MRuleRhs]

  MRuleId = tuple[rule,rhs: int]
  MRuleIdDotted = tuple
    id: MRuleId
    dotPos: int
  MLookahead = HashSet[MTerminal]
  MItem = object
    ruleIdDot: MRuleIdDotted
    lookahead: MLookahead

func `==`(a, b: MSymbol): bool =
  if a.kind == b.kind:
    case a.kind
    of mSymTerminal:    a.name == b.name
    of mSymNonTerminal: a.id   == b.id  
  else: false

func newTerminal(name: string): MSymbol = MSymbol(kind: mSymTerminal,    name: name)
func newNonTerminal(id: int):   MSymbol = MSymbol(kind: mSymNonTerminal, id:   id  )

func `[]`(rules: seq[MRules], id: MRuleId): MRuleRhs =
  rules[id.rule][id.rhs]

func `<`(a,b: MItem): bool = a.ruleIdDot < b.ruleIdDot

func `$`[T](o: Option[T]): string =
  if o.isNone: ""
  else: $get(o)

func `$`(ruleId: MRuleId): string =
  $ruleId.rule & "," & $ruleId.rhs


proc addNewOrAppend[K,V](table: var Table[K, seq[V]], key: K, val: V) =
  if key in table:
    table[key] &= val
  else:
    table[key] = @[val]


macro makeParser*(head,body: untyped): untyped =

  const
    actionParamPrefix = "s"
    nonterminalVariantPrefix = "t"
  let
    nonterminalType = genSym(nskType, "NonTerminal")

  # --- meta infos: ---

  let (procIdent, tokenType) = getProcMeta(head)

  let tokenKindType = genSym(nskType, "TokenKind")
  let getTokenKindType = quote do:
    type `tokenKindType` = typeof(`tokenType`().kind)

  # --- collect nonterminals: ---

  body.expectKind(nnkStmtList)

  # there is already 1 terminal with no type for S' start symbol
  var
    nonterminals:    seq[tuple[name: string, resTypeId: int]] = @[("", 0)]
    nonterminalInfo: Table[string, tuple[id, resTypeId: int]]
    resTypes:        seq[NimNode]
    resTypeNtMap:    seq[seq[int]]  # resType id -> seq[nt ids that have that type]

  for rules in body:
    rules.expectKind(nnkCall)
    rules[0].expectKind(nnkBracketExpr)
    rules[0][0].expectKind(nnkIdent)
    let name    = rules[0][0].strVal.nimIdentNormalize
    let resType = rules[0][1]
    let resTypeId =
      if (let id = resTypes.find(resType); id) != -1: id
      else:
        resTypes &= resType
        resTypeNtMap &= @[]
        high(resTypes)
    assert name notin nonterminalInfo
    nonterminals &= (name, resTypeId)
    nonterminalInfo[name] = (high(nonterminals), resTypeId)
    resTypeNtMap[resTypeId] &= high(nonterminals)

  # --- parse rules: ---

  var
    ruleSets: seq[MRules]  # lhs (nont. id) -> seq[rhs] (options)
    reduceNimNode: seq[NimNode]  # only for errors

  # start rule: S' -> S
  ruleSets &= @[MRuleRhs(pattern: @[newNonTerminal(1)], reduceId: -1)]

  var curReduceId = 0
  for (id, rules) in body.pairs:
    rules[1].expectKind(nnkStmtList)
    
    ruleSets &= @[]
    for rule in rules[1]:
      rule.expectKind(nnkCall)
      reduceNimNode &= rule

      ruleSets[^1] &= MRuleRhs(reduceId: curReduceId)
      inc curReduceId

      proc parseSymbol(i: int, sym: NimNode) =
        sym.expectKind(nnkIdent)

        let symName = sym.strVal.nimIdentNormalize
        ruleSets[^1][^1].pattern.add:
          if symName in nonterminalInfo:
            newNonTerminal(nonterminalInfo[symName].id)
          else:
            newTerminal(symName)

      case rule[0].kind
      of nnkTupleConstr:
        for (i, sym) in rule[0].pairs: parseSymbol(i, sym)
      of nnkPar:
        parseSymbol(0, rule[0][0])
      else:
        parseSymbol(0, rule[0])

  # assert all nts just have one ruleset
  assert len(nonterminals) == len(ruleSets)

  func `$`(s: MSymbol): string =
    case s.kind
    of mSymTerminal: s.name
    of mSymNonTerminal: nonterminals[s.id].name

  func `$`(ruleIdDot: MRuleIdDotted): string =
    nonterminals[ruleIdDot.id.rule].name &
    " -> " &
    collect(
      for (i, sym) in ruleSets[ruleIdDot.id].pattern.pairs:
        if i == ruleIdDot.dotPos: "." & $sym
        else: $sym
    ).join(" ") & (
      if ruleIdDot.dotPos == len(ruleSets[ruleIdDot.id].pattern):
        "."
      else: ""
    )

  func `$`(x: MItem): string =
    ($x.ruleIdDot).alignLeft(20) & $x.lookahead

  func `$`(x: seq[MItem]): string =
    x.mapIt($it).join("\n")

  # --- generate parsing table: ---

  #[func findFirstSet(symbols: seq[Symbol]): HashSet[Terminal] =
    var visited: HashSet[int]
    proc findRec(symbols: seq[Symbol]): tuple[first: HashSet[Terminal], epsilon: bool] =
      result.epsilon = false
      for sym in symbols:
        case sym.kind
        of mSymTerminal:
          result.first.incl sym.name
          result.epsilon = false
          break
        of mSymNonTerminal:
          if sym.id in visited: break
          else:
            visited.incl sym.id
            for rhs in ruleSets[sym.id]:
              let (first, epsilon) = findRec(rhs.pattern)
              result.first.incl first
              result.epsilon =  result.epsilon or epsilon
            if not result.epsilon:
              break
      result.epsilon = true

    let (first, _) = findRec(symbols)
    first]#

  func findFirstSet(symbol: MSymbol): HashSet[MTerminal] =
    var visited: HashSet[int]
    proc findRec(symbol: MSymbol): HashSet[MTerminal] =
      case symbol.kind
      of mSymTerminal:
        result.incl symbol.name.nimIdentNormalize
      of mSymNonTerminal:
        if symbol.id notin visited:
          visited.incl symbol.id
          for rhs in ruleSets[symbol.id]:
            result.incl findRec(rhs.pattern[0])

    findRec(symbol)

  let firstSets: seq[HashSet[MTerminal]] = collect:
    for (i, info) in nonterminals.pairs:
      findFirstSet(newNonTerminal(i))

  for s in firstSets:
    debugEcho s

  # - build automaton: -

  proc isRuleEnd(ruleIdDot: MRuleIdDotted): bool =
    ruleIdDot.dotPos == len(ruleSets[ruleIdDot.id].pattern)

  var
    adjacencyMat: seq[seq[Option[MSymbol]]]
    stateItems: seq[seq[MItem]]
    stateLookup: Table[seq[MRuleIdDotted], int]

  # returns state id
  # items are just the initial ones with no closure
  proc buildStateMashine(items: seq[MItem]): int =

    proc findTransitions(currentState: int, items: seq[MItem]) =
      var
        lookaheadTable: Table[MRuleIdDotted, MLookahead]
        transitions: Table[MSymbol, seq[MRuleIdDotted]]  # the dotted rule is without the shift (because I need to lookup lookahead)

      proc closure(ruleIdDot: MRuleIdDotted, lookahead: MLookahead) =
        if ruleIdDot in lookaheadTable:
          debugEcho "yo"
          lookaheadTable[ruleIdDot].incl lookahead

        else:
          assert not isRuleEnd(ruleIdDot)
          lookaheadTable[ruleIdDot] = lookahead
          let pattern = ruleSets[ruleIdDot.id].pattern
          let symbol = pattern[ruleIdDot.dotPos]
          transitions.addNewOrAppend(symbol, ruleIdDot)
          if symbol.kind == mSymNonTerminal:
            let nextLookahead =
              if ruleIdDot.dotPos == high(pattern):
                lookahead
              else:
                let nextSymbol = pattern[ruleIdDot.dotPos + 1]
                case nextSymbol.kind
                of mSymTerminal:    toHashSet([nextSymbol.name])
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
          rulesIdDot.mapIt(MItem(
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
      adjacencyMat &= newSeqWith(len(adjacencyMat), none(MSymbol))
      for row in adjacencyMat.mitems:
        row &= none(MSymbol)

      # find transitions:
      findTransitions(currentState, items)

      currentState

  discard buildStateMashine(@[MItem(ruleIdDot: ((0, 0), 0), lookahead: toHashSet([""]))])

  # debug:
  
  func `$`(os: Option[MSymbol]): string =
    if os.isNone: ""
    else: $os.get

  debugEcho "    " & toSeq(0..high(stateItems)).mapIt("|" & ($it).alignLeft(8)).join
  for (i, row) in adjacencyMat.pairs:
    debugEcho ($i).alignLeft(4) & row.mapIt("|" & ($it).alignLeft(8)).join

  debugEcho ""
  for (i, s) in stateItems.pairs: debugEcho $i, " ", s

  # - build parsing table: -

  var
    actionTable = newSeq[Table[MTerminal, Action]](len(stateItems))
    gotoTable = newSeqWith(len(stateItems), newSeqWith(len(nonterminals), -1))  # (from state, nonterminal) -> target state

  for (fromState, row) in adjacencyMat.pairs:
    
    proc ruleNimNode(ruleId: MRuleId): NimNode =
      reduceNimNode[ruleSets[ruleId].reduceId]

    func lineInfoShort(node: NimNode): string =
      let lineInfo = lineInfoObj(node)
      "(" & $lineInfo.line & "," & $lineInfo.column & ")"

    # reduces:
    for item in stateItems[fromState]:
      if isRuleEnd(item.ruleIdDot):
        let ruleId = item.ruleIdDot.id

        if ruleId == (0, 0):
          actionTable[fromState][""] = Action(kind: actionAccept)

        else:
          let reduceId = ruleSets[item.ruleIdDot.id].reduceId
          let action = Action(kind: actionReduce, id: reduceId)
          for terminal in item.lookahead:
            if terminal notin actionTable[fromState]:
              actionTable[fromState][terminal] = action

            # conflict:
            else:
              let curAction = actionTable[fromState][terminal]
              assert curAction.kind == actionAccept
              error(
                "reduce/reduce conflict with " & lineInfoShort(reduceNimNode[curAction.id]),
                reduceNimNode[reduceId]
              )

    for (toState, symbol) in row.pairs:
      if Some(@symbol) ?= symbol:
        case symbol.kind

        # shift:
        of mSymTerminal:
          if symbol.name notin actionTable[fromState]:
            actionTable[fromState][symbol.name] = Action(kind: actionShift, goto: toState)

          # conflict:
          else:
            let curAction = actionTable[fromState][symbol.name]
            var shiftRuleNodes: seq[NimNode]
            proc findShiftRules(state: int) =
              for item in stateItems[state]:
                if not isRuleEnd(item.ruleIdDot):
                  shiftRuleNodes &= ruleNimNode(item.ruleIdDot.id)
            findShiftRules(toState)
            case curAction.kind
            of actionReduce:
              error(
                "shift/reduce conflict with:" &
                "  shifts: " & shiftRuleNodes[1..^1].map(lineInfoShort).join(", ") &
                "  reduce: " & lineInfoShort(reduceNimNode[curAction.id]),
                shiftRuleNodes[0]
              )
            of actionShift:
              findShiftRules(curAction.goto)
              error(
                "shift/shift conflict with: " &
                shiftRuleNodes[1..^1].map(lineInfoShort).join(", "),
                shiftRuleNodes[0]
              )
            else:
              assert false

        # goto:
        of mSymNonTerminal:
          assert gotoTable[fromState][symbol.id] < 0
          gotoTable[fromState][symbol.id] = toState

  debugEcho actionTable

  # --- build parser: ---

  result = block:
    let
      procResType = resTypes[0]
      symbolType = quote do: Symbol[`tokenType`, `nonterminalType`]

      action       = genSym(nskLet, "action")
      goto         = genSym(nskLet, "goto" )
      stack        = genSym(nskVar, "stack")
      curState     = genSym(nskVar, "state")
      curToken     = genSym(nskLet, "token")
      curTokenKind = genSym(nskLet, "tokenKind")
      curReduceId  = genSym(nskLet, "reduceId")
      
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
      var caseStmt = nnkCaseStmt.newTree(curReduceId)

      for (lhsm1, rules) in ruleSets[1..^1].pairs:
        for (rhsId, rhs) in rules.pairs:
          var branch = nnkOfBranch.newTree(newLit(rhs.reduceId))

          let lhs = lhsm1 + 1
          let patternLen = len(rhs.pattern)

          var branchBody = newStmtList: quote do:
            assert len(`stack`) >= `patternLen`

          for (i, symbol) in rhs.pattern.reversed.pairs:
            let elem = genSym(nskLet, "elem")
            let param = ident(actionParamPrefix & $(patternLen-i))

            branchBody.add quote do:
              let (`elem`, _) = pop(`stack`)

            branchBody.add:
              case symbol.kind
              of mSymTerminal:
                let terminal = ident(symbol.name)
                quote do:
                  assert `elem`.kind == symTerminal
                  assert `elem`.token.kind == `terminal`
                  let `param` = `elem`.token

              of mSymNonTerminal:
                let ntId = symbol.id
                let field = ident(nonterminalVariantPrefix & $nonterminals[ntId].resTypeId)
                quote do:
                  assert `elem`.kind == symNonTerminal
                  assert `elem`.nt.id == `ntId`
                  let `param` = `elem`.nt.`field`

          let field  = ident(nonterminalVariantPrefix & $nonterminals[lhs].resTypeId)
          let action = body[lhsm1][1][rhsId][1]
          action.expectKind(nnkStmtList)
          branchBody.add: quote do:
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

    let
      resTypeField = ident(nonterminalVariantPrefix & $0)
      stateNum = newLit(len(stateItems))
      ntNum = newLit(len(nonterminals))

    quote do:
      proc `procIdent`(tokens: seq[`tokenType`]): `procResType` =

        type `nonterminalType` = `nonterminalTypeDef`

        `getTokenKindType`

        let
          `goto`  : GotoTable[`stateNum`, `ntNum`]  = `gotoTableDef`
          `action`: ActionTable[`stateNum`, `tokenKindType`] = `actionTableDef`

        debugEcho `goto`
        for row in `action`: debugEcho row

        var
          `stack`: seq[tuple[s: `symbolType`, state: int]]
          `curState` = 0
          pos = 0

        while true:
          debugEcho `stack`

          let actionRow = `action`[`curState`]
          let (token, action) =
            if pos < len(tokens):
              (some(tokens[pos]), actionRow.terminals[tokens[pos].kind])
            else:
              (none(`tokenType`), actionRow.eof)

          case action.kind
          of actionShift:
            `curState` = action.goto
            `stack` &= (
              `symbolType`(kind: symTerminal, token: token.get),
              `curState`
            )
            inc pos

          of actionReduce:
            let `curReduceId` = action.id
            `reduceCaseStmt`

          of actionAccept:
            assert len(`stack`) == 1
            return `stack`[0].s.nt.`resTypeField`

          of actionNone:
            assert false

  debugEcho result.repr