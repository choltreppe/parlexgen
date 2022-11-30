import unittest
import parlexgen

import std/[strutils, strformat, sequtils]

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
      r"[0-9]+": Token(kind: NUM, val: parseInt(it.match))
      r"\+":     Token(kind: ADD)
      r"\*":     Token(kind: MUL)
      r"\(":     Token(kind: LPAR)
      r"\)":     Token(kind: RPAR)
      r";":      Token(kind: SEMI)
      r"=":      Token(kind: ASSIGN)
      skip r" +"

    makeParser parse[Token]:
      stmnts[seq[Stmnt]]:
        (stmnts, SEMI, stmnt): s1 & s3
        stmnt: @[s1]

      stmnt[Stmnt]:
        (NUM, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s1.val, exp: s3)

      mul[Exp]:
        (add, MUL, mul): Exp(kind: ekOp, op: opMul, left: s1, right: s3)
        add: s1

      add[Exp]:
        (val, ADD, add): Exp(kind: ekOp, op: opAdd, left: s1, right: s3)
        val: s1

      val[Exp]:
        (LPAR, mul, RPAR): s2
        NUM: Exp(kind: ekNum, val: s1.val)

    let tokens = lex("0=(1+1)")
    echo tokens
    #echo parse(tokens)
    echo parse(@[
      Token(kind: NUM, val: 0),
      Token(kind: ASSIGN),
      Token(kind: LPAR),
      Token(kind: NUM, val: 1),
      Token(kind: MUL),
      Token(kind: NUM, val: 2),
      Token(kind: ADD),
      Token(kind: NUM, val: 3),
      Token(kind: RPAR)
    ])

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

when false:
  test "test3":
    
    type
      TestTerminalKind = enum a, b
      TestTerminal = object
        kind: TestTerminalKind

    makeParser testParser[TestTerminal]:
      S[int]:
        A: 0
        B: 0

      A[int]:
        (a, b): 0

      B[int]:
        a: 0

when false:
  test "test4":

    type
      TestTerminalKind = enum LPAR, RPAR, ADD, NUM
      TestTerminal = object
        kind: TestTerminalKind

    func t(kind: TestTerminalKind): TestTerminal =
      TestTerminal(kind: kind)

    makeParser testParser[TestTerminal]:
      add[int]:
        (val, ADD, add): 0
        val: 0

      val[int]:
        (LPAR, add, RPAR): 0
        NUM: 0

    echo testParser(@[t NUM, t ADD, t NUM])

    check true