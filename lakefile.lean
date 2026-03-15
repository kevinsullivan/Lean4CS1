import Lake
open Lake DSL

package «fp-course» where
  name := "fp-course"

@[default_target]
lean_lib «FPCourse» where
  globs := #[.andSubmodules `FPCourse]
