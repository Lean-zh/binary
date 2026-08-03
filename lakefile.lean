import Lake
open Lake DSL

package "binary" where
  version := v!"0.1.0"
  releaseRepo := "https://github.com/Lean-zh/binary"
  preferReleaseBuild := true

@[default_target]
lean_lib Binary where

lean_exe Test where
  root := `Test
