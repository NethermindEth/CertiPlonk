import Lake

open System Lake DSL

package poly where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.22.0-rc2"

lean_lib CMvPolynomial

@[default_target] lean_exe poly where root := `Main
