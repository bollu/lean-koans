import Lake
open Lake DSL

package «Playground»

lean_lib Playground

@[default_target]
lean_exe «playground» {
  root := `Playground
  supportInterpreter := true
}

-- require «egg-tactic» from git  "https://github.com/opencompl/egg-tactic-code" @ "499ef2d"
require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop"
