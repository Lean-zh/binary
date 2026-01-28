import Lake
open Lake DSL

package "binary" where
  version := v!"0.1.0"

@[default_target]
lean_lib Binary where

lean_exe Test where
  root := `Test
