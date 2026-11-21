import Lake
open Lake DSL

package libp2p_fv where
  leanOptions := #[⟨`weak.veil.smt.trust, false⟩]

require veil from git "https://github.com/verse-lab/veil.git" @
  "578ec0b77a0936cb502e15bdb468047211abd6b9"

@[default_target]
lean_lib Libp2p where
  globs := #[.submodules `Libp2p]
