import std/[macros, re]

import ./utils


type LexingError* = ref object of CatchableError

macro makeLexer*(head,body: untyped): untyped =
  body.expectKind(nnkStmtList)
  
  let (procIdent, tokenType) = getProcMeta(head)

  let
    code   = genSym(nskParam, "code")
    pos    = genSym(nskVar  , "pos" )
    line   = ident"line"
    col    = ident"col"
    match  = ident"match"
    tokens = ident"result"
    posForError = ident"pos"

  var
    matchingAttempts = newStmtList()
    skipPatternDefined = false
    errorHandler = newEmptyNode()

  proc addMatchingAttempt(pattern, body: NimNode) =
    matchingAttempts.add quote do:
      let l = `code`.matchLen(re(`pattern`), `pos`)
      if l >= 0:
        let `match` = `code`[`pos` ..< `pos` + l]
        `body`
        `pos` += l
        `col` += l - `match`.count({'\n', '\r'})
        continue

  for rule in body:

    if rule.kind == nnkPrefix:
      rule[0].expectKind(nnkIdent)
      rule[1].expectKind(nnkIdent)
      rule[2].expectKind(nnkStmtList)
      assertError(rule[0].strVal == "!", "unexpected '" & rule[0].strVal & "'", rule[0])

      if rule[1].strVal.eqIdent("skip"):
        assertError(not skipPatternDefined, "double definition of skip pattern", rule)
        assertError(len(rule[2]) == 1, "expected just a string literal", rule[2])
        # TODO: verify rule[0] is string (not neccesary literal)
        addMatchingAttempt rule[2][0], newEmptyNode()

      elif rule[1].strVal.eqIdent("error"):
        rule[2].expectKind(nnkStmtList)
        assertError(errorHandler.kind == nnkEmpty, "double definition of error handler", rule)
        errorHandler = rule[2]

      else:
        error "unexpected '" & rule[1].strVal & "'", rule[1]

      skipPatternDefined = true
      continue

    rule.expectKind(nnkCall)
    # TODO: verify rule[0] is string (not neccesary literal)
    let pattern = rule[0]
    let action  = rule[1]
    addMatchingAttempt pattern, quote do:
      `tokens` &= `action`

  result = quote do:
    proc `procIdent`(`code`: string): seq[`tokenType`] =
      var `pos` = 0
      var `line`, `col` = 1
      while `pos` < len(`code`):
        if `code`[`pos`] == '\n':
          inc `line`
          `col` = 0
        `matchingAttempts`
        `errorHandler`
        raise LexingError(msg: "lexing error at (" & $`line` & ", " & $`col` & ")")

  debugEcho result.repr