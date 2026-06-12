import Lake
open Lake DSL

package FECG_LEAN where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.7.0"

lean_lib FECG_LEAN
lean_lib MultiModal
lean_lib Composite
lean_lib verifier
