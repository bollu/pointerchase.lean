import Lake
open Lake DSL

package "pointerchase" where
  -- add package configuration options here

lean_lib PointerChase where
  -- add library configuration options here

lean_lib Examples where
  -- add library configuration options here

@[default_target]
lean_exe "chase.examples" where
  root := `Examples
