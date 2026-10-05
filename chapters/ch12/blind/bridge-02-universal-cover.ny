export "02-universal-cover"
export "../../../src/1206-universal-cover-universal"

{` Bridges for abelian.tex, sec:univ-cover-simple (blocks 252, 301, 331). The blind universal cover, its
   point, its projection (pointed by refl) and BlindIsSimplyConnected are ours by refl. `}

{` Definition (abelian.tex:252). `}
def bridge_def_univ_cover (A : Type) (a : A) : Id Type (BlindUnivCover A a) (UnivCover A a) ≔ refl (UnivCover A a)

def bridge_def_univ_cover_pointed (A : Type) (a : A) : Id Pointed (blind_univ_cover_pointed A a) (univ_cover_pointed A a)
  ≔ refl (univ_cover_pointed A a)

def bridge_def_univ_cover_proj (A : Type) (a : A)
  : Id (BookPointedMap (univ_cover_pointed A a) (A, a)) (blind_univ_cover_proj_pointed A a) (univ_cover_projection A a)
  ≔ refl (univ_cover_projection A a)

def bridge_def_simply_connected (X : Pointed) : Id Type (BlindIsSimplyConnected X) (SimplyConnected X)
  ≔ refl (SimplyConnected X)

{` lemma:universal-cover-simply-connected (abelian.tex:301). `}
def bridge_universal_cover_simply_connected : blind_universal_cover_simply_connected
  ≔ A a ↦ univ_cover_simply_connected A a

def bridge_universal_cover_simply_connected_converse (b : blind_universal_cover_simply_connected) (A : Type) (a : A)
  : SimplyConnected (univ_cover_pointed A a)
  ≔ b A a

{` lemma:universal-cover-is-universal (abelian.tex:331). `}
def bridge_universal_cover_is_universal : blind_universal_cover_is_universal
  ≔ A a ↦ (univ_cover_projection_covering A a, univ_cover_universal A a)

def bridge_universal_cover_is_universal_converse (b : blind_universal_cover_is_universal) (A : Type) (a : A)
  : IsUniversalPointedCover (univ_cover_pointed A a) (A, a) (univ_cover_projection A a)
  ≔ b A a .snd
