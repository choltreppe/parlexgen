import std/sets


# --- runtime ---

type
  SymbolKind* = enum symTerminal, symNonTerminal
  Symbol*[T, N] = object
    case kind*: SymbolKind
    of symTerminal: token*: T
    of symNonTerminal: nt*: N

  ActionKind* = enum actionNone, actionShift, actionReduce, actionAccept
  Action* = object
    case kind*: ActionKind
    of actionShift:  goto*: int
    of actionReduce: id*:   int
    else: discard
  ActionTable*[L: static int, T: enum] = array[L, tuple[terminals: array[T, Action], eof: Action]]

  GotoTable*[L, N: static int] = array[L, array[N, int]]

func `$`*(symbol: Symbol): string =
  case symbol.kind
  of symTerminal: $symbol.token.kind
  of symNonTerminal: $symbol.nt


# --- meta ---

type
  MTerminal* = string  # token kind  (empty string means $)
  MNonTerminal* = int  # id
  MSymbolKind* = enum mSymTerminal, mSymNonTerminal
  MSymbol* = object
    case kind*: MSymbolKind
    of mSymTerminal:    name*: MTerminal
    of mSymNonTerminal: id*:   MNonTerminal
  MRuleRhs* = object
    pattern*: seq[MSymbol]
    patternId*: int
  MRules* = seq[MRuleRhs]

  MRuleId* = tuple[rule,rhs: int]
  MRuleIdDotted* = tuple
    id: MRuleId
    dotPos: int
  MLookahead* = HashSet[MTerminal]
  MItem* = object
    ruleIdDot*: MRuleIdDotted
    lookahead*: MLookahead

func `==`*(a, b: MSymbol): bool =
  if a.kind == b.kind:
    case a.kind
    of mSymTerminal:    a.name == b.name
    of mSymNonTerminal: a.id   == b.id
  else: false

func newTerminal*(name: string): MSymbol = MSymbol(kind: mSymTerminal,    name: name)
func newNonTerminal*(id: int):   MSymbol = MSymbol(kind: mSymNonTerminal, id:   id  )

func `[]`*(rules: seq[MRules], id: MRuleId): MRuleRhs =
  rules[id.rule][id.rhs]

func `<`*(a,b: MItem): bool = a.ruleIdDot < b.ruleIdDot
