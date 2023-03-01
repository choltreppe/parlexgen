import std/[macros, genasts, sequtils, strutils, options]
import fusion/matching
export options

import ./private/utils, ./common
import ./private/lexim/lexim


type
  LexingError* = ref object of CatchableError
    pos*, line*, col*: int

macro makeLexer*(head,body: untyped): untyped =
  body.expectKindError(nnkStmtList, "expected list of rules")
  
  let (procIdent, tokenType) = getProcMeta(head)

  let
    code   = genSym(nskParam, "code")
    state  = genSym(nskParam, "state")
    oldPos = ident"pos"
    line   = ident"line"
    col    = ident"col"
    match  = ident"match"
    rules  = genSym(nskVar, "rules")
    matchingBlock = genSym(nskLabel, "matching")

  proc genAddRule(rule: NimNode, captures: seq[NimNode] = @[]): NimNode =
    rule.expectKindError({nnkCall, nnkCommand}, "expected pattern with token generation code")
    # TODO: verify rule[0] is string (not neccesary literal)
    let pattern = rule[0]
    let action  = rule[1]
    action.expectKind(nnkStmtList)

    let matchBody =
      if len(action) == 1 and action[0].kind in {nnkContinueStmt, nnkDiscardStmt}:
        newStmtList(nnkBreakStmt.newTree(matchingBlock))
      else:
        genAst(action, code, state, match, oldPos):
          let match = code[oldPos ..< state.pos]
          return some(action)

    let genAstCall = quote do:
      genAst(`oldPos`=ident"pos", `line`=ident"line", `col`=ident"col")
    for capture in captures:
      genAstCall.add capture
    genAstCall.add matchBody

    newCall(ident"add", rules,
      nnkTupleConstr.newTree(pattern, genAstCall)
    )

  var rulesSeqDef = newStmtList(quote do:
    var `rules`: seq[(string, NimNode)]
  )

  for rule in body:

    # -- loops of rules: --

    if rule.kind == nnkForStmt:
      let parts = forLoopParts(rule)

      parts.body.expectKind(nnkStmtList)

      var loopBody = newStmtList()
      for rule in parts.body:
        loopBody.add genAddRule(rule, parts.idents)

      var forLoop = nnkForStmt.newTree()
      for elem in parts.elems: forLoop.add elem
      forLoop.add parts.vals, loopBody

      rulesSeqDef.add forLoop

      continue

    # -- plain rules: --
    rulesSeqDef.add genAddRule(rule)

  quote do:
    proc `procIdent`(`code`: string, `state`: var LexerState): Option[`tokenType`] =
      while `state`.pos < len(`code`):
        let `oldPos` = `state`.pos
        let `line`   = `state`.line
        let `col`    = `state`.col
        block `matchingBlock`:
          macro impl(c, pos, doEnd: untyped) =
            `rulesSeqDef`
            result = leximMatch(c, pos, `rules`, doEnd)

          impl(`code`, `state`.pos):
            if `state`.pos < len(`code`):
              case `code`[`state`.pos]:
              of '\n':
                inc `state`.line
                `state`.col = 0
              of '\r':
                `state`.col = 0
              else:
                inc `state`.col

          raise LexingError(pos: `oldPos`, line: `line`, col: `col`, msg: "lexing failed")
      return none(`tokenType`)


iterator tokens*[T](code: string, lexer: LexerProc[T]): T =
  var state = initLexerState()
  while Some(@token) ?= lexer(code, state):
    yield token