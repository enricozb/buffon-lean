import Lake
open Lake DSL

package «buffon» where
  -- add package configuration options here

lean_lib «Buffon» where
  -- add library configuration options here

@[default_target]
lean_exe «buffon» where
  root := `Main
