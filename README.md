This module provides a macro for generating (LALR(1)) parsers.<br>
With focus on easy to use custom error handling.<br>
It also provides one for generating lexers but the generated lexers arent realy optimal yet, so if you realy need best performance better use something else for the lexer.
**This is still in developement and not ready for production**

Here is an example with detailed explanation:<br>
(the type definition are omitted. take a look at tests/test1.nim for the whole code)
```nim
# Generates a 'proc lex(code: string): seq[Token]'
makeLexer lex[Token]:

  # If [0-9]+ is matched the following block is executed to build a token.
  # Note: After the pattern is a block definition not a function,
  #       so don't use 'return' or 'result'.
  # Inside the block you have following vars:
  #  match: the matched string
  #  pos: the index of the start of the match inside the input string
  #  line, col
  r"[0-9]+": Token(kind: NUM, val: parseInt(match), line: line, col: col)

  # Matches get tryed top to bottom, so this should be above the ident one.
  "out": Token(kind: OUT, line: line, col: col)

  r"[a-zA-Z][a-zA-Z0-9]*": Token(kind: IDENT, name: match, line: line, col: col)

  # You can also define rules with a loop.
  # You can define multiple rules in one loop.
  for t in PLUS .. ASSIGN:
    (r"\" & $t): Token(kind: t, line: line, col: col)

  # Use discard to skip.
  r"[ \n\r]+": discard


# Generates a 'proc parse*(tokens: seq[Token]): seq[Stmnt]'
makeParser parse*[Token]:

  # define all rules with the same lefthand side in one block,
  # with the resulting type anotated.
  stmnts[seq[Stmnt]]:
    # List of cases with if folowed by the rhs of the production rule
    # Note: Like in the lexer, producing code if not a seperate function so returning would return from the whole parsing function
    if (stmnts, SEMI, stmnt): s1 & s3
    if stmnt: @[s1]

  stmnt[Stmnt]:
    if (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s1.name, exp: s3)
    
    if (OUT, IDENT):
      debugEcho "found out statement"
      Stmnt(kind: stmntOutput, outVar: s2.name)

  mul[Exp]:
    if (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s1, right: s3)
    # Optionaly you can add a else case to your rule
    # This gets executed when parsing fails,
    # and this rule is one of the possible next rules that would be reduced
    # Inside this block you have the following vars:
    #  pos: the position inside your rule (so 0: mul, 1: ASTERIX, 2: add)
    #       and 3 is just behind the rule
    #       this var is range[0..len(rule)]
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
    
    if add: s1

  add[Exp]:
    if (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s1, right: s3)
    if val: s1

  val[Exp]:
    if (LPAR, mul, RPAR): s2
    if NUM: Exp(kind: ekNum, val: s1.val)
    if IDENT: Exp(kind: ekVar, name: s1.name)
    

echo parse(lex(dedent"""
  a = (1+3) * 3;
  out a;
  b = a * 2;
  out b
"""))
```


## Contribution
PRs and issues are very welcome

## TODO
- improve lexer ?