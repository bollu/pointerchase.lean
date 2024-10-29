import Lake
open Lake DSL

package "bdd-lean" where
  -- add package configuration options here

lean_lib Bdd.Basic where
  -- add library configuration options here

@[default_target]
lean_exe "bdd-lean" where
  root := `Main
