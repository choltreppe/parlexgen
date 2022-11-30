import std/macros 

func getProcMeta*(head: NimNode): tuple[ident, typ: NimNode] =
  case head.kind
  of nnkInfix:
    assert head[0].strVal == "*"
    head[1].expectKind(nnkIdent)
    head[2].expectKind(nnkBracket)
    result.ident = nnkPostfix.newTree(ident"*", head[1])
    result.typ   = head[2][0]

  of nnkBracketExpr:
    head[0].expectKind(nnkIdent)
    result.ident = head[0]
    result.typ   = head[1]
    
  else:
    assert false
    return