This module provides a macro for generating lexers and parsers (LALR(1))<br>
With focus on easy to use custom error handling.<br>

The lexer is build on top of [lexim](https://github.com/Araq/lexim)

**This is still in developement and not ready for production**

Here is an example with detailed explanation:<br>
(the type definition are omitted. take a look at tests/test1.nim for the whole code)
```nim
# Generates a ParserProc[Token]  (take a look at src/parlexgen/common.nim for details)
makeLexer lex[Token]:

  # If the pattern ("out") is matched the following block is executed to build a token.
  # Note: After the pattern is a block definition not a function,
  #       so don't use 'return' or 'result'.
  # Inside the block you have following vars:
  #  match: the matched string
  #  pos: the index of the start of the match inside the input string
  #  line, col
  "out": Token(kind: OUT, line: line, col: col)

  r"[0-9]+":
    echo "found number " & match & " at (" & $line & ", " & $col & ")"
    Token(kind: NUM, val: parseInt(match), line: line, col: col)

  r"[a-zA-Z][a-zA-Z0-9]*": Token(kind: IDENT, name: match, line: line, col: col)

  # You can also define rules with a loop.
  # The loop must be compile-time computable
  # You can define multiple rules in one loop.
  for t in PLUS .. ASSIGN:
    (r"\" & $t): Token(kind: t, line: line, col: col)

  # The patterns don't have to be string literals, they can be any compile-time expression

  # Use discard to skip.
  r"[ \n\r]+": discard


# Generates a 'proc parse*(code: string, lexer: LexerProc[Token]): seq[Stmnt]'
makeParser parse*[Token]:

  # define all rules with the same lefthand side in one block,
  # with the resulting type anotated.
  stmnts[seq[Stmnt]]:

    # List of different rules for this nt
    # You have access to 's', a tuple of the matched symbols.
    #  In this first case of type: (seq[Stmnt], Token, Stmnt)
    # Note: Like in the lexer, producing code if not a seperate function so returning would return from the whole parsing function
    if (stmnts, SEMI, stmnt): s[0] & s[2]

    if stmnt: @[s[0]]

  stmnt[Stmnt]:
    if (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s[0].name, exp: s[2])
    
    if (OUT, IDENT):
      debugEcho "found out statement"
      Stmnt(kind: stmntOutput, outVar: s[1].name)

  mul[Exp]:
    if (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s[0], right: s[2])

    # Optionaly you can add a else case to your rule
    # This gets executed when parsing fails,
    # and this rule is one of the possible next rules that would be reduced
    # Inside this block you have the following vars:
    #  pos: the position inside your rule (so 0: mul, 1: ASTERIX, 2: add, 3: just behind)
    #       this var is alway of type range[0..len(rule)]
    #  token: this is either some(token), the token currently read
    #         or none if its at EOF
    # After this block is executed, the function doesnt return automatically.
    # This is because it could happen that multiple rules could be reduced next,
    # so all of those error handlers get called, if they exist.
    # And afterwards a ParsingError is raised.
    # But you can return yourself from inside the else block if you want
    else:
      echo:
        case pos
        of 0, 2: "expected number or math expression"
        of 1:    "invalid math expression"
        of 3:    "unexpected " & $token & " after math expression"
    
    if add: s[0]

  add[Exp]:
    if (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s[0], right: s[2])
    if val: s[0]

  val[Exp]:
    if (LPAR, mul, RPAR): s[1]
    if NUM: Exp(kind: ekNum, val: s[0].val)
    if IDENT: Exp(kind: ekVar, name: s[0].name)
    

echo parse(
  dedent"""
    foo = (1+3) * 3;
    out foo;
    b = foo * 2;
    out b
  """,
  lex
)
```


## Contribution
PRs and issues are very welcome

## TODO
- improve lexer ?