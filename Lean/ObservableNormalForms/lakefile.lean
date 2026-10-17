import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.35.0"

package «ObservableNormalForms» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «ObservableNormalForms» where

