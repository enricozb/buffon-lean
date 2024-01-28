import Lake
open Lake DSL

package «buffon» where
  -- add package configuration options here

lean_lib «Buffon» where
  -- add library configuration options here

@[default_target]
lean_exe «buffon» where
  root := `Main

-- a mathlib version that uses lean-toolchain 4.4.0
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "cf8e23a62939ed7cc530fbb68e83539730f32f86"
