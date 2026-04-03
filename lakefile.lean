import Lake
open Lake DSL

package «spectral-reduction» {
  -- Configuration du paquet
}

lean_lib «Spectral» {
  -- Dossier où se trouvera votre code
}

@[default_target]
lean_exe «spectral-reduction» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
