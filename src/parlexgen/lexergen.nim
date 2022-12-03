import std/[macros, re]

import ./private/utils


type LexingError* = ref object of CatchableError
  pos*: int

macro makeLexer*(head,body: untyped): untyped =
  body.expectKindError(nnkStmtList, "expected list of rules")
  
  let (procIdent, tokenType) = getProcMeta(head)

  let
    code   = genSym(nskParam, "code")
    pos    = ident"pos"
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
    hasNormalDefs = false
    hasLoopDefs = false

  for rule in body:

    # -- loops of rules: --

    if rule.kind == nnkForStmt:
      hasLoopDefs = true

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
            `tokens`.add: `action`
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
    hasNormalDefs = true

    rule.expectKindError({nnkCall, nnkCommand}, "expected pattern with token generation code")
    # TODO: verify rule[0] is string (not neccesary literal)
    let pattern = rule[0]
    let action  = rule[1]
    let regexId = len(regexsDef)
    regexsDef.add quote do: re(`pattern`)
    let body =
      if len(action) == 1 and action[0].kind == nnkDiscardStmt: newEmptyNode()
      else: quote do: `tokens`.add: `action`
    matchingAttempts.add quote do:
      let l = `code`.matchLen(`regexs`[`regexId`], `pos`)
      if l >= 0:
        let `match` = `code`[`pos` ..< `pos` + l]
        `body`
        `pos` += l
        `col` += l - `match`.count({'\n', '\r'})
        continue

  let assignRegexs =
    if hasNormalDefs:
      quote do:
        let `regexs` {.global.} = `regexsDef`
    else:
      newEmptyNode()

  let assignLoopRegexs =
    if hasLoopDefs:
      quote do:
        let `loopRegexs` {.global.} = `loopRegexsDef`
    else:
      newEmptyNode()

  result = quote do:
    proc `procIdent`(`code`: string): seq[`tokenType`] =
      `assignRegexs`
      `assignLoopRegexs`
      var `pos` = 0
      var `line`, `col` = 1
      while `pos` < len(`code`):
        if `code`[`pos`] == '\n':
          inc `line`
          `col` = 0
        `matchingAttempts`
        raise LexingError(pos: `pos`, msg: "lexing error at (" & $`line` & ", " & $`col` & ")")