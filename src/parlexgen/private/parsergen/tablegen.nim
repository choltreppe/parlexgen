import std/[strformat ,strutils, sequtils, sets, tables, options, sugar, algorithm, macros, base64]
import fusion/matching
import unibs

import ./types


proc buildParsingTable*(rules: seq[MRules], nonterminals: seq[string], patternLineInfo: seq[LineInfo]):
  tuple[action: seq[Table[MTerminal, Action]], goto: seq[seq[int]], items: seq[seq[MItem]]] =
  
  func findFirstSet(symbol: MSymbol): HashSet[MTerminal] =
    let rules = rules
    var visited: HashSet[int]
    proc findRec(symbol: MSymbol): HashSet[MTerminal] =
      case symbol.kind
      of mSymTerminal:
        result.incl symbol.name.nimIdentNormalize
      of mSymNonTerminal:
        if symbol.id notin visited:
          visited.incl symbol.id
          for rhs in rules[symbol.id]:
            result.incl findRec(rhs.pattern[0])

    findRec(symbol)

  let firstSets: seq[HashSet[MTerminal]] = collect:
    for (i, info) in nonterminals.pairs:
      findFirstSet(newNonTerminal(i))

  # - build automaton: -

  proc isRuleEnd(ruleIdDot: MRuleIdDotted): bool =
    ruleIdDot.dotPos == len(rules[ruleIdDot.id].pattern)

  var
    #adjacencyMat: seq[seq[Option[MSymbol]]]
    stateItems: seq[seq[MItem]]
    stateLookup: Table[seq[MRuleIdDotted], int]

  # returns state id
  # items are just the initial ones with no closure
  proc buildStateMashine(items: seq[MItem], adjacencyMat = newSeq[seq[Option[MSymbol]]]()): (int, seq[seq[Option[MSymbol]]]) =
    var adjacencyMat = adjacencyMat

    proc findTransitions(currentState: int, items: seq[MItem]) =
      var
        lookaheadTable: Table[MRuleIdDotted, MLookahead]
        transitions: Table[MSymbol, seq[MRuleIdDotted]]  # the dotted rule is without the shift (because I need to lookup lookahead)

      proc closure(ruleIdDot: MRuleIdDotted, lookahead: MLookahead) =
        if ruleIdDot in lookaheadTable:
          if lookahead <= lookaheadTable[ruleIdDot]: return
          lookaheadTable[ruleIdDot].incl lookahead
        else:
          lookaheadTable[ruleIdDot] = lookahead

        assert not isRuleEnd(ruleIdDot)
        let pattern = rules[ruleIdDot.id].pattern
        let symbol = pattern[ruleIdDot.dotPos]
        if symbol in transitions:
          if ruleIdDot notin transitions[symbol]:
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
              of mSymTerminal:    toHashSet([nextSymbol.name])
              of mSymNonTerminal: firstSets[nextSymbol.id]
          for i in 0 .. high(rules[symbol.id]):
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
        let (toState, newAdjacencyMat) = buildStateMashine(newItems, adjacencyMat)
        adjacencyMat = newAdjacencyMat
        adjacencyMat[currentState][toState] = some(symbol)

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

      (oldState, adjacencyMat)

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

      (currentState, adjacencyMat)

  let (_, adjacencyMat) = buildStateMashine(@[MItem(ruleIdDot: ((0, 0), 0), lookahead: toHashSet([""]))])

  # - build parsing table: -

  var
    actionTable = newSeq[Table[MTerminal, Action]](len(stateItems))
    gotoTable = newSeqWith(len(stateItems), newSeqWith(len(nonterminals), -1))  # (from state, nonterminal) -> target state

  var gotError = false

  for (fromState, row) in adjacencyMat.pairs:
    
    proc ruleLineInfo(ruleId: MRuleId): LineInfo =
      patternLineInfo[rules[ruleId].patternId]

    func lineInfoShort(lineInfo: LineInfo): string =
      fmt"({lineInfo.line} ,{lineInfo.column})"

    proc echoError(msg: string, lineInfo: LineInfo) =
      echo fmt"{lineInfo} {msg}"
      gotError = true

    for (toState, symbol) in row.pairs:
      if Some(@symbol) ?= symbol:
        case symbol.kind

        # shift:
        of mSymTerminal:
          let action = Action(kind: actionShift, goto: toState)
          if symbol.name notin actionTable[fromState]:
            actionTable[fromState][symbol.name] = action

          # possible conflict:
          else:
            let curAction = actionTable[fromState][symbol.name]
            assert curAction.kind == actionShift and curAction.goto == action.goto

        # goto:
        of mSymNonTerminal:
          assert gotoTable[fromState][symbol.id] < 0
          gotoTable[fromState][symbol.id] = toState

    # reduces:
    for item in stateItems[fromState]:
      if isRuleEnd(item.ruleIdDot):
        let ruleId = item.ruleIdDot.id

        if ruleId == (0, 0):
          actionTable[fromState][""] = Action(kind: actionAccept)

        else:
          let patternId = rules[item.ruleIdDot.id].patternId
          let action = Action(kind: actionReduce, id: patternId)
          for terminal in item.lookahead:
            if terminal notin actionTable[fromState]:
              actionTable[fromState][terminal] = action

            # possible conflict:
            else:
              let curAction = actionTable[fromState][terminal]
              # conflict:
              if curAction.kind != actionReduce or curAction.id != action.id:
                echoError((
                    case curAction.kind
                    of actionShift: "shift/reduce conflict"
                    of actionReduce: "reduce/reduce conflict with " & lineInfoShort(patternLineInfo[curAction.id])
                    else:
                      assert false
                      return
                  ),
                  patternLineInfo[patternId]
                )

  if gotError: quit 1

  (actionTable, gotoTable, stateItems)


when isMainModule:

  let (rules, nonterminals, patternLineInfo) =
    readLine(stdin).decode.deserialize((seq[MRules], seq[string], seq[LineInfo]))

  echo buildParsingTable(rules, nonterminals, patternLineInfo).serialize.encode