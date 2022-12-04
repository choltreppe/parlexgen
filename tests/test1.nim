import unittest
import parlexgen

import std/[strutils, strformat, sequtils, options, macros, genasts]
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


  makeLexer lex[Token]:

    r"[0-9]+": Token(kind: NUM, val: parseInt(match), line: 0, col: 0)

    "out": Token(kind: OUT, line: 0, col: 0)

    r"[a-zA-Z][a-zA-Z0-9]*": Token(kind: IDENT, name: match, line: 0, col: 0)

    for t in PLUS .. ASSIGN:
      (r"\" & $t): Token(kind: t, line: 0, col: 0)

    r"\s+": continue


  makeParser parse[Token]:
    stmnts[seq[Stmnt]]:
      if (stmnts, SEMI, stmnt): s1 & s3
      if stmnt: @[s1]

    stmnt[Stmnt]:
      if (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s1.name, exp: s3)
      
      if (OUT, IDENT): Stmnt(kind: stmntOutput, outVar: s2.name)

    mul[Exp]:
      if (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s1, right: s3)
      else:
        echo:
          case pos
          of 0, 2: "expected number or math expression"
          of 1:    "invalid math expression"  # should nerver happen
          of 3:    "unexpected " & $token & " after math expression"  # should also never happen i think
      
      if add: s1

    add[Exp]:
      if (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s1, right: s3)
      else: echo 7

      if val: s1
      else: echo 8

    val[Exp]:
      if (LPAR, mul, RPAR): s2
      else: echo 9

      if NUM: Exp(kind: ekNum, val: s1.val)
      else: echo 10
      
      if IDENT: Exp(kind: ekVar, name: s1.name)
      else: echo 11
      

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