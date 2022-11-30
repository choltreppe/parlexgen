import std/[macros]
import regex

import ./utils


type LexToken = object
  match: string
  id: int
  row,col: int

macro makeLexer*(head,body: untyped): untyped =
  body.expectKind(nnkStmtList)
  
  let (procIdent, tokenType) = getProcMeta(head)

  let
    code   = genSym(nskParam, "code" )
    pos    = genSym(nskVar  , "pos"  )
    match  = genSym(nskVar  , "match")
    tokens = ident"result"
    it     = ident"it"

  var matchingTrys = newStmtList()
  for rule in body:
    matchingTrys.add:

      if rule.kind == nnkCommand and rule[0].kind == nnkIdent and rule[0].strVal == "skip":
        let pattern = rule[1]
        quote do:
          if `code`[`pos`..^1].find(re("$(" & `pattern` & ")"), `match`):
            assert `match`.boundaries.a == 0
            `pos` += `match`.boundaries.b + 1
            continue

      else:
        rule.expectKind(nnkCall)
        let pattern = rule[0]
        let action  = rule[1]
        quote do:
          if `code`[`pos`..^1].find(re("^(" & `pattern` & ")"), `match`):
            assert `match`.boundaries.a == 0
            `pos` += `match`.boundaries.b + 1
            let `it` = LexToken(
              match: `code`[`match`.boundaries]
              # TODO: id,row,col
            )
            `tokens` &=  `action`
            continue

  result = quote do:
    proc `procIdent`(`code`: string): seq[`tokenType`] =
      var `pos` = 0
      var `match`: RegexMatch
      while `pos` < len(`code`):
        `matchingTrys`
        echo "lexError at ", $`pos`
        return