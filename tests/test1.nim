import unittest
import parlexgen

import std/[strutils, strformat, sequtils, options, macros]

when true:
  test "test1":
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


    makeLexer lex[Token]:

      "out": Token(kind: OUT, line: line, col: col)

      r"[0-9]+": Token(kind: NUM, val: parseInt(match), line: line, col: col)

      r"[a-zA-Z][a-zA-Z0-9]*": Token(kind: IDENT, name: match, line: line, col: col)

      for t in PLUS .. ASSIGN:
        (r"\" & $t): Token(kind: t, line: line, col: col)

      !skip: r"[ \n\r]+"
      !error:
        echo line, " ", col, ": lex error"


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

    echo parse(lex(dedent"""
      a = (1+2) * 3;
      out a;
      b = a * a;
      out b
    """))

    check true

when false:
  test "test2":

    type
      TestTerminalsKind = enum a, b
      TestTerminals = object
        kind: TestTerminalsKind

    let ta = TestTerminals(kind: a)
    let tb = TestTerminals(kind: b)

    makeParser testParser[TestTerminals]:
      S[string]:
        (A, A): "(" & s1 & " " & s2 & ")"

      A[string]:
        (a, A): "(a " & s2 & ")"
        b: "b"

    echo testParser(@[ta, tb, ta, ta, tb])

    check true