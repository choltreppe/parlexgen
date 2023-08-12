#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import regexprs, nfa, macros, base64
import unibs

import ".."/utils

proc findMacro(name: string): PRegExpr {.used.} = nil

proc newRange(a, b: NimNode): NimNode {.compileTime.} =
  newCall(bindSym"..", a, b)

proc charSetLit(cc: set[char]): NimNode {.compileTime.} =
  const
    MaxChar = '\xFF'
  result = newNimNode(nnkCurly)
  var c1 = '\0'
  while true:
    if c1 in cc:
      var c2 = c1
      while c2 < MaxChar and succ(c2) in cc: c2 = succ(c2)
      if c1 == c2:
        result.add newLit(c1)
      elif c2 == succ(c1):
        result.add newLit(c1)
        result.add newLit(c2)
      else:
        result.add newRange(newLit(c1), newLit(c2))
      c1 = c2
    if c1 >= MaxChar: break
    inc c1

proc charAt(s: string; i: int): char {.inline.} =
  result = if i < s.len: s[i] else: '\0'

proc currChar(s, i: NimNode): NimNode {.compileTime.} =
  result = newCall(bindSym"charAt", s, i)

proc getCmp(s, i: NimNode; x: set[char]): NimNode {.compileTime.} =
  result = newCall(bindSym"contains",  charSetLit(x), currChar(s, i))

proc getSpecial(s, i: NimNode; x: Alphabet): NimNode {.compileTime.} =
  result = newCall(bindSym"==", currChar(s, i), newLit(x.val))

proc newVarStmt(name, typ, value: NimNode): NimNode {.compiletime.} =
  return newTree(nnkVarSection, newTree(nnkIdentDefs, name, typ, value))

proc nextState(i, state: NimNode; dest: int): NimNode {.compileTime.} =
  newStmtList(newCall(bindSym"inc", i), newAssignment(state, newLit(dest)))

proc genMatcher(a: DFA; s, i: NimNode; sections: seq[tuple[pattern: string, body: NimNode]]; doStepEnd: NimNode): NimNode {.compileTime.} =
  let state = genSym(nskVar, "state")
  result = newStmtList()
  result.add newVarStmt(#[newTree(nnkPragmaExpr, state,
                          newTree(nnkPragma, ident"goto"))]#state,
                        newTree(nnkBracketExpr, bindSym"range",
                          newRange(newLit(1), newLit(a.stateCount))),
                        newLit(a.startState))
  var caseStmt = newNimNode(nnkCaseStmt)
  caseStmt.add state
  result.add newTree(nnkWhileStmt, bindSym"true", newStmtList(caseStmt, doStepEnd))
  for src in countup(1, a.stateCount):
    let rule = getRule(a, src)
    var ifStmt = newNimNode(nnkIfStmt)
    for dest in allDests(a, src):
      let (others, cs) = allTransitions(a, src, dest)
      if cs != {}:
        ifStmt.add newTree(nnkElifBranch,
                           getCmp(s, i, cs),
                           nextState(i, state, dest))
      for ot in others:
        if ot.kind == reChar:
          ifStmt.add newTree(nnkElifBranch,
                             getSpecial(s, i, ot),
                             nextState(i, state, dest))
        else:
          doAssert false, "not supported " & $ot.kind
    let actions = if rule >= 1:
           sections[rule-1].body
         else:

           newTree(nnkBreakStmt, newNimNode(nnkEmpty))
    if ifStmt.len == 0:
      caseStmt.add newTree(nnkOfBranch, newLit(src), actions)
    else:
      ifStmt.add newTree(nnkElse, actions)
      caseStmt.add newTree(nnkOfBranch, newLit(src), ifStmt)

proc leximMatch*(s, pos: NimNode; sections: seq[tuple[pattern: string, body: NimNode]]; doStepEnd: NimNode): NimNode =
  when false:
    var bigRe: PRegExpr = nil
    var rule = 1
    for (pattern, body) in sections:
      let rex = parseRegExpr(pattern, findMacro,
                            {reNoCaptures, reNoBackrefs})
      rex.rule = rule
      if bigRe.isNil: bigRe = rex
      else: bigRe = altExpr(bigRe, rex)
      inc rule

    var n: NFA
    var d, o: DFA
    regExprToNFA(bigRe, n)
    let alph = fullAlphabet(n)
    NFA_to_DFA(n, d, alph)
    optimizeDFA(d, o, alph)
    result = genMatcher(o, s, pos, sections, doStepEnd)
  else:
    # use 'lexe.exe' helper program in order to speedup lexer generation

    var res: seq[string] = @[]
    for (pattern, body) in sections:
      res.add pattern

    let data = res.serialize.encode

    let o = execCompiled("lexe", data&"\n").decode.deserialize(DFA)

    result = genMatcher(o, s, pos, sections, doStepEnd)
  #echo repr result
