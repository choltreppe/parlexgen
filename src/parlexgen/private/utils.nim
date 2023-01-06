import std/[macros, tables] 

proc assertError*(cond: bool, msg: string, node: NimNode) =
  if not cond:
    error msg, node

proc expectKindError*(node: NimNode, kind: NimNodeKind, msg: string) =
  if node.kind != kind:
    error msg, node

proc expectKindError*(node: NimNode, kinds: set[NimNodeKind], msg: string) =
  if node.kind notin kinds:
    error msg, node

func getProcMeta*(head: NimNode): tuple[ident, typ: NimNode] =
  case head.kind
  of nnkInfix:
    assertError(head[0].strVal == "*", "unexpected '" & head[0].strVal & "' did you mean '*' ?", head[0])
    head[1].expectKindError(nnkIdent, "expected name of proc")
    head[2].expectKindError(nnkBracket, "expected type of tokens")
    result.ident = nnkPostfix.newTree(ident"*", head[1])
    result.typ   = head[2][0]

  of nnkBracketExpr:
    head[0].expectKindError(nnkIdent, "expected name of proc")
    result.ident = head[0]
    result.typ   = head[1]

  else:
    error "expected name of proc and type of tokens", head


proc forLoopParts*(node: NimNode): tuple[elems,idents: seq[NimNode], vals,body: NimNode] =
  node.expectKind(nnkForStmt)
  result.elems = node[0..^3]
  result.vals  = node[^2]
  result.body  = node[^1]
  for elem in result.elems:
    if elem.kind == nnkVarTuple:
      for i in elem:
        if i.kind != nnkEmpty:
          i.expectKind(nnkIdent)
          result.idents &= i
    else:
      elem.expectKind(nnkIdent)
      result.idents &= elem