This module provides a macro for generating (LALR(1)) parsers.<br>
It also provides one for generating lexers but the generated lexers arent realy optimal, so if you realy need best performance better use something else for the lexer.
The syntax for the grammar definition is inspired by https://github.com/loloicci/nimly

## makeParser
here is a small example of the `makeParser` macro (details will be explained beneeth)
```nim
makeParser parse[Token]:
  stmnts[seq[Stmnt]]:
    (stmnts, SEMI, stmnt): s1 & s3
    stmnt: @[s1]

    !error: echo "stmnts"

  stmnt[Stmnt]:
    (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s1.name, exp: s3)
    (OUT, IDENT): Stmnt(kind: stmntOutput, outVar: s2.name)

    !error: echo "stmnt"

  mul[Exp]:
    (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s1, right: s3)
    add: s1

    !error: echo "expected mul expression"

  add[Exp]:
    (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s1, right: s3)
    val: s1

    !error: echo "expected add expression"

  val[Exp]:
    (LPAR, mul, RPAR): s2
    NUM: Exp(kind: ekNum, val: s1.val)
    IDENT: Exp(kind: ekVar, name: s1.name)

  !error: echo "parse error: ", token
```

### signature
The signature defines the name of the generated proc, its input token type and if its exported.

The following
```nim
makeParser name[T]:
```
generates
```nim
proc name(tokens: seq[T]): A =
```

and
```nim
makeParser name*[T]:
```
generates
```nim
proc name*(tokens: seq[T]): A =
```

(where A is the parsing result type deduced by the production rules)

### body
The body is a list of production rules, grouped by lhs <br>
Take a look at the example

### error handling
You can add error handling code with `!error:` for a nonterminal (lhs) specificcaly and for the whole parser.<br>
If parsing fails, the specific handlers for all nonterminals that could be reduced next will be called first,<br>
then the handler for the whole parser,
<br>
an `ParsingError` is raised.

You can use `token` inside the error handler to access the token currently read.

**Those are all executed, not just if the others dont exists** so you are completly free in your controlflow. You can return from each handler or just fall through to the next in the herachy or raise your own exception or whatever.

## makeLexer
Example:
```nim
makeLexer lex[Token]:

  "out": Token(kind: OUT, line: line, col: col)

  r"[0-9]+": Token(kind: NUM, val: parseInt(match), line: line, col: col)

  r"[a-zA-Z][a-zA-Z0-9]*":
    Token(kind: IDENT, name: match, line: line, col: col)

  for t in PLUS .. ASSIGN:
    (r"\" & $t): Token(kind: t, line: line, col: col)

  !skip: r"[ \n\r]+"
  !error:
    echo line, " ", col, ": lex error"
```

inside the token building blocks you can use `match`, `line`, `col` to access the matched string an pos in ininput string.<br>
inside `!error` you can also access `line` and `col`<br>
use `!skip` to define pattern that should be ignored


## Contribution
PRs and issues are very welcome

## TODO
- write better documentation
- write more tests maybe
- improve lexer
