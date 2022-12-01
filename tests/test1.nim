import unittest
import parlexgen

import std/[strutils, strformat, sequtils, options, macros]

when true:
  test "test1":
    type
      Op = enum opMul="*", opAdd="+"
      ExpKind = enum ekNum, ekOp
      Exp = ref object
        case kind: ExpKind
        of ekNum: val: int
        of ekOp:
          op: Op
          left, right: Exp

      StmntKind = enum stmntAssign
      Stmnt = object
        case kind: StmntKind
        of stmntAssign:
          res: int
          exp: Exp

      TokenKind = enum NUM, ADD, MUL, LPAR, RPAR, SEMI, ASSIGN
      Token = object
        case kind: TokenKind
        of NUM: val: int
        else: discard

    func `$`(exp: Exp): string =
      case exp.kind
      of ekNum: $exp.val
      of ekOp: "(" & $exp.left & " " & $exp.op & " " & $exp.right & ")"

    func `$`(stmnt: Stmnt): string =
      case stmnt.kind
      of stmntAssign:
        $stmnt.res & " = " & $stmnt.exp

    func `$`(stmnts: seq[Stmnt]): string =
      stmnts.mapIt($it).join(";")

    makeLexer lex[Token]:
      r"[0-9]+": Token(kind: NUM, val: parseInt(match))
      r"\+":     Token(kind: ADD)
      r"\*":     Token(kind: MUL)
      r"\(":     Token(kind: LPAR)
      r"\)":     Token(kind: RPAR)
      r";":      Token(kind: SEMI)
      r"=":      Token(kind: ASSIGN)
      !skip: r" +"
      !error:
        echo line, " ", col

    makeParser parse[Token]:
      stmnts[seq[Stmnt]]:
        (stmnts, SEMI, stmnt): s1 & s3
        stmnt: @[s1]

      stmnt[Stmnt]:
        (NUM, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s1.val, exp: s3)

      mul[Exp]:
        (add, MUL, mul): Exp(kind: ekOp, op: opMul, left: s1, right: s3)
        add: s1

        !error: echo "expected mul expression"

      add[Exp]:
        (val, ADD, add): Exp(kind: ekOp, op: opAdd, left: s1, right: s3)
        val: s1

        !error:
          echo "expected add expression"
          echo token

      val[Exp]:
        (LPAR, mul, RPAR): s2
        NUM: Exp(kind: ekNum, val: s1.val)

      !error: return

    echo parse(lex("0=(1+2) * 3"))

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