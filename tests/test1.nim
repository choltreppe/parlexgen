import unittest
import parlexgen

import std/[strutils, strformat, sequtils, options, macros, genasts]
import fusion/matching

import parlexgen/common

test "test":
  type
    Op = enum opMul="*", opAdd="+", opSub="-"
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

    TokenKind = enum NUM, IDENT, OUT="out", PLUS="+", MINUS="-", ASTERIX="*", LPAR="(", RPAR=")", SEMI=";", ASSIGN="="
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


  const outPattern = "out"

  makeLexer lex[Token]:

    outPattern: Token(kind: OUT, line: line, col: col)

    r"[0-9]+":
      echo "found number " & match & " at (" & $line & ", " & $col & ")"
      Token(kind: NUM, val: parseInt(match), line: line, col: col)

    r"[a-zA-Z][a-zA-Z0-9]*": Token(kind: IDENT, name: match, line: line, col: col)

    for t in PLUS .. ASSIGN:
      (r"\" & $t): Token(kind: t, line: line, col: col)

    r"\s+": continue


  makeParser parse[Token]:
    stmnts[seq[Stmnt]]:
      if (stmnts, SEMI, stmnt): s[0] & s[2]
      if stmnt: @[s[0]]

    stmnt[Stmnt]:
      if (IDENT, ASSIGN, mul): Stmnt(kind: stmntAssign, res: s[0].name, exp: s[2])
      
      if (OUT, IDENT): Stmnt(kind: stmntOutput, outVar: s[1].name)

    mul[Exp]:
      if (mul, ASTERIX, add): Exp(kind: ekOp, op: opMul, left: s[0], right: s[2])
      else:
        echo:
          case pos
          of 0, 2: "expected number or math expression"
          of 1:    "invalid math expression"  # should nerver happen
          of 3:    "unexpected " & $token & " after math expression"  # should also never happen i think
      
      if add: s[0]

    add[Exp]:
      for (t, o) in [(PLUS, opAdd), (MINUS, opSub)]:
        if (add, t, val): Exp(kind: ekOp, op: o, left: s[0], right: s[2])
        else: echo 7
      #if (add, PLUS, val): Exp(kind: ekOp, op: opAdd, left: s[0], right: s[2])
      #else: echo 7

      if val: s[0]
      else: echo 8

    val[Exp]:
      if (LPAR, mul, RPAR): s[1]
      else: echo 9

      if NUM: Exp(kind: ekNum, val: s[0].val)
      else: echo 10
      
      if IDENT: Exp(kind: ekVar, name: s[0].name)
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