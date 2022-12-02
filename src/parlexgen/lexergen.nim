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
    regexs      = genSym(nskLet, "regexs")
    loopRegexs  = genSym(nskLet, "loopRegexs")
    localRegexs = genSym(nskVar, "localRegexs")
    loopRegexCount = genSym(nskVar, "i")
    loopGotMatch   = genSym(nskVar, "gotMatch")

  var
    matchingAttempts = newStmtList()
    regexsDef = nnkBracket.newTree()
    loopRegexsDef = nnkBracket.newTree()
    skipPatternDefined = false
    errorHandler = newEmptyNode()

  proc addMatchingAttempt(pattern, body: NimNode) =
    let regexId = len(regexsDef)
    regexsDef.add quote do: re(`pattern`)
    matchingAttempts.add quote do:
      let l = `code`.matchLen(`regexs`[`regexId`], `pos`)
      if l >= 0:
        let `match` = `code`[`pos` ..< `pos` + l]
        `body`
        `pos` += l
        `col` += l - `match`.count({'\n', '\r'})
        continue

  for rule in body:

    # -- special handlers: ---

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

    # -- loops of rules: --

    if rule.kind == nnkForStmt:
      let
        elem = rule[0]
        vals = rule[1]
        body = rule[2]

      body.expectKind(nnkStmtList)

      let regexId = len(loopRegexsDef)
      var collectRegexs = newStmtList()
      var matchingLoopBody = newStmtList()
      for rule in body:
        rule.expectKindError({nnkCall, nnkCommand}, "expected pattern with token generation code")
        let pattern = rule[0]
        let action  = rule[1]

        collectRegexs.add quote do:
          `localRegexs` &= re(`pattern`)

        matchingLoopBody.add quote do:
          let l = `code`.matchLen(`loopRegexs`[`regexId`][`loopRegexCount`], `pos`)
          if l >= 0:
            let `match` = `code`[`pos` ..< `pos` + l]
            `tokens` &= `action`
            `pos` += l
            `col` += l - `match`.count({'\n', '\r'})
            `loopGotMatch` = true
            break
          inc `loopRegexCount`

      loopRegexsDef.add quote do:
        block:
          var `localRegexs`: seq[Regex]
          for `elem` in `vals`:
            `collectRegexs`
          `localRegexs`

      matchingAttempts.add quote do:
        var `loopRegexCount` = 0
        var `loopGotMatch` = false
        for `elem` in `vals`:
          `matchingLoopBody`
        if `loopGotMatch`: continue

      continue

    # -- normal rules: --

    rule.expectKindError({nnkCall, nnkCommand}, "expected pattern with token generation code")
    # TODO: verify rule[0] is string (not neccesary literal)
    let pattern = rule[0]
    let action  = rule[1]
    addMatchingAttempt pattern, quote do:
      `tokens` &= `action`

  result = quote do:
    proc `procIdent`(`code`: string): seq[`tokenType`] =
      let `regexs`     {.global.} = `regexsDef`
      let `loopRegexs` {.global.} = `loopRegexsDef`
      var `pos` = 0
      var `line`, `col` = 1
      while `pos` < len(`code`):
        if `code`[`pos`] == '\n':
          inc `line`
          `col` = 0
        `matchingAttempts`
        {.warning[UnreachableCode]:off.}
        `errorHandler`
        raise LexingError(msg: "lexing error at (" & $`line` & ", " & $`col` & ")")
        {.warning[UnreachableCode]:on.}