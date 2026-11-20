import Lake
open Lake DSL

package «software-certification-is-monotone» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib Cert where
  roots := #[`Cert, `Control, `Axioms]
