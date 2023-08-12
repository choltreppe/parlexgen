# Package

version       = "0.2.3"
author        = "Joel Lienhard"
description   = "parser/lexer generator (LALR)"
license       = "MIT"
srcDir        = "src"
installExt = @["nim"]
bin = @["parlexgen/private/lexim/lexe",
        "parlexgen/private/parsergen/tablegen"]


# Dependencies

requires "nim >= 1.6.6"
requires "fusion >= 1.1"
requires "unibs >= 0.2.0"
