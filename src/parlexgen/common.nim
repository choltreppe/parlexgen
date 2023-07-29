import std/options

type
  LexerState* = object
    pos*,line*,col*: int
    runeCol*: int  # unicode position of col
    runeOffset*: int
    
  LexerProc*[T] = proc(code: string, state: var LexerState): Option[T]

func initLexerState*: LexerState = LexerState(pos: 0, line: 1, col: 1)