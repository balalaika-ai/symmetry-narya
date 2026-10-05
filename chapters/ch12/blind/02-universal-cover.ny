{` Blind statements for chapter 12 (abelian.tex), sec:univ-cover-simple. `}
export "01-center"
export "../../../src/98-pointed-universal-coverings"

{` A pointed type (A, a) is simply connected when both A and a = a are connected (abelian.tex:249). `}
def BlindIsSimplyConnected (X : Pointed) : Type ≔ Product (Connected (X .carrier)) (Connected (Loop X))

{` Universal covering (abelian.tex:252). A_(a)<1> ≔ Σ_{x:A} ‖a = x‖₀, with the first projection; pointed at
   (a, |refl a|₀) as stated right after the definition. `}
def BlindUnivCover (A : Type) (a : A) : Type ≔ Σ A (x ↦ SetTrunc (Id A a x))

def blind_univ_cover_point (A : Type) (a : A) : BlindUnivCover A a ≔ (a, set_trunc (Id A a a) (refl a))

def blind_univ_cover_pointed (A : Type) (a : A) : Pointed ≔ (BlindUnivCover A a, blind_univ_cover_point A a)

def blind_univ_cover_proj (A : Type) (a : A) : BlindUnivCover A a → A ≔ u ↦ u .fst

{` fst as a pointed map A_(a)<1> →* (A, a); fst(a, |refl|) ≡ a, pointed by refl. `}
def blind_univ_cover_proj_pointed (A : Type) (a : A) : BookPointedMap (blind_univ_cover_pointed A a) (A, a)
  ≔ (blind_univ_cover_proj A a, refl a)

{` lemma:universal-cover-simply-connected (abelian.tex:301). `}
def blind_universal_cover_simply_connected : Type
  ≔ (A : Type) (a : A) → BlindIsSimplyConnected (blind_univ_cover_pointed A a)

{` lemma:universal-cover-is-universal (abelian.tex:331). fst : A_(a)<1> →* A is a universal covering in the sense of
   def:univ-cover: a pointed covering (fibers are sets) that is universal. `}
def blind_universal_cover_is_universal : Type
  ≔ (A : Type) (a : A)
    → Product (IsCovering (BlindUnivCover A a) A (blind_univ_cover_proj A a))
        (IsUniversalPointedCover (blind_univ_cover_pointed A a) (A, a) (blind_univ_cover_proj_pointed A a))
