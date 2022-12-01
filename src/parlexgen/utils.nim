import std/[macros, tables] 

proc assertError*(cond: bool, msg: string, node: NimNode) =
  if not cond:
    error msg, node

proc expectKindError*(node: NimNode, kind: NimNodeKind, msg: string) =
  if node.kind != kind:
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

proc addNewOrAppend*[K,V](table: var Table[K, seq[V]], key: K, val: V) =
  if key in table:
    table[key] &= val
  else:
    table[key] = @[val]