import Lake
open Lake DSL

package matrixTransport where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "71a80585ee495fc24472fd0eaffc89d94e4fd8d6"

@[default_target]
lean_lib MatrixTransport
