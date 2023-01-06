import unittest
import parlexgen

import std/[strutils, strformat, sequtils, options, macros]
import fusion/matching

import parlexgen/common

test "test":
  type
    Op = enum opMul="*", opAdd="+"
    ExpKind = enum ekNum, ekVar, ekOp
    Exp = ref object
      case kind: ExpKind
      of ekNum: val: int
      of ekVar: name: string
      of ekOp:
        op: Op
        left, right: Exp

    StmntKind = enum stmntAssign, stmntOutput
    Stmnt = object
      case kind: StmntKind
      of stmntAssign:
        res: string
        exp: Exp
      of stmntOutput:
        outVar: string

    TokenKind = enum NUM, IDENT, OUT="out", PLUS="+", ASTERIX="*", LPAR="(", RPAR=")", SEMI=";", ASSIGN="="
    Token = object
      case kind: TokenKind
      of NUM: val: int
      of IDENT: name: string
      else: discard
      line, col: int

  func `$`(exp: Exp): string =
    case exp.kind
    of ekNum: $exp.val
    of ekVar: exp.name
    of ekOp: "(" & $exp.left & " " & $exp.op & " " & $exp.right & ")"

  func `$`(stmnt: Stmnt): string =
    case stmnt.kind
    of stmntAssign:
      stmnt.res & " = " & $stmnt.exp
    of stmntOutput:
      "out " & stmnt.outVar

  func `$`(stmnts: seq[Stmnt]): string =
    stmnts.mapIt($it).join("; ")


  # Generates a ParserProc[Token]  (take a look at src/parlexgen/common.nim for details)
  # If you want the generated proc to be exported use:
  # makeLexer lex*[Token]:
  # this also applies to the parser
  makeLexer lex[Token]:

    # If the pattern ("out") is matched the following block is executed to build a token.
    # Note: After the pattern is a block definition not a function,
    #       so don't use 'return' or 'result'.
    # Inside the block you have following vars:
    #  match: the matched string
    #  pos: the index of the start of the match inside the input string
    #  line, col
    ($OUT): Token(kind: OUT, line: line, col: col)
    # as you can see, you may can use any const expr for the pattern

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

    # Use continue to skip (or discard).
    r"\s+": continue


  # Generates a 'proc parse(code: string, lexer: LexerProc[Token]): seq[Stmnt]'
  makeParser parse[Token]:

    # define all rules with the same lefthand side in one block,
    # with the resulting type anotated.
    stmnts[seq[Stmnt]]:

      # List of different rules for this nt
      # You have access to 's', a tuple of the matched symbols.
      #  In this first case of type: (seq[Stmnt], Token, Stmnt)
      # Note: Like in the lexer, the produced code is not a seperate function so returning would return from the whole parsing function
      (stmnts, SEMI, stmnt): s[0] & s[2]

      stmnt: @[s[0]]

    stmnt[Stmnt]:
      (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s[0].name, exp: s[2])
      
      (OUT, IDENT):
        debugEcho "found out statement"
        Stmnt(kind: stmntOutput, outVar: s[1].name)

    mul[Exp]:
      # You can use try/except for error handling.
      # So the except block gets executed when parsing fails,
      # and this rule is one of the possible next rules that would be reduced.
      # Inside this block you have the following vars:
      #  pos: the position inside your rule (so 0: mul, 1: ASTERIX, 2: add, 3: just behind)
      #       this var is alway of type range[0..len(rule)]
      #  token: this is either some(token), the token currently read
      #         or none if its at EOF
      # After this block is executed, the function doesnt return automatically.
      # This is because it could happen that multiple rules could be reduced next,
      # so all of those error handlers get called, if they exist.
      # And afterwards a ParsingError is raised.
      # But you can return yourself from inside the except block if you want
      try:
        (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s[0], right: s[2])
      except:
        echo:
          case pos
          of 0, 2: "expected number or math expression"
          of 1:    "invalid math expression"
          of 3:    "unexpected " & $token & " after math expression"
      
      add: s[0]

    add[Exp]:
      # You may also put multiple rules in one try block,
      # but if you do so you cant use the `pos` var in the except block.
      try:
        (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s[0], right: s[2])
        val: s[0]
      except:
        echo "parsing additin expression failed"

    val[Exp]:
      (LPAR, mul, RPAR): s[1]
      NUM: Exp(kind: ekNum, val: s[0].val)
      IDENT: Exp(kind: ekVar, name: s[0].name)
      

  check:
    $parse(
      dedent"""
        a = (1+3) * 3;
        out a;
        b = a * 2;
        out b
      """,
      lex
    ) ==
    "a = ((1 + 3) * 3); out a; b = (a * 2); out b"