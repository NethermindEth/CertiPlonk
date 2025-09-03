import Lake

open System Lake DSL

package poly where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.22.0-rc2"

require Parser from git
  "https://github.com/fgdorais/lean4-parser"@"fd87222e41892ca1f5f7722c585cfe401871d653"

@[default_target]
lean_lib CMvPolynomial

@[default_target]
lean_lib FF

lean_exe Parse {
  root := `CocoaParser
  srcDir := "FF"
  exeName := "parse"
}
