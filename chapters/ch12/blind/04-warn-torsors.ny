{` Blind statements for chapter 12 (abelian.tex), subsection "Higher deloopings" (Wärn's torsors). `}
export "03-abelian-sc2types"

{` Definition (Wärn) (abelian.tex:678). TX ≔ Σ_{Y:U} ‖Y‖ × Π_{y:Y} (Y, y) ≃* X, and TX_* ≔ Σ_{t:TX} fst t. `}
def BlindTorsors (X : Pointed) : Type
  ≔ Σ Type (Y ↦ Product (Mere Y) ((y : Y) → BookPointedEquiv (Y, y) X))

def BlindPointedTorsors (X : Pointed) : Type ≔ Σ (BlindTorsors X) (t ↦ t .fst)

{` "Y is a delooping of X" (not defined formally in the book): Y is connected and ΩY ≃* X. `}
def BlindIsDelooping (X Y : Pointed) : Type ≔ Product (Connected (Y .carrier)) (BookPointedEquiv (Omega Y) X)

{` Lemma (Wärn) (abelian.tex:688). If TX_* is contractible, then for every pointed X-torsor (t, y), (TX, t) is a
   delooping of X. `}
def blind_warn_delooping : Type
  ≔ (X : Pointed) → BookIsContr (BlindPointedTorsors X)
    → (ty : BlindPointedTorsors X) → BlindIsDelooping X (BlindTorsors X, ty .fst)

{` Sections of f : A → B: s : B → A with f ∘ s = id_B (def:surjection, footnote). `}
def BlindSections (A B : Type) (f : A → B) : Type
  ≔ Σ (B → A) (s ↦ Id (B → B) (x ↦ f (s x)) (identity B))

{` xca:sections-as-dependent-functions (abelian.tex:707). sec(f) ≃ Π_{b:B} Σ_{a:A} b = f(a). `}
def blind_sections_as_dependent_functions : Type
  ≔ (A B : Type) (f : A → B) → BookEquiv (BlindSections A B f) ((b : B) → Σ A (a ↦ Id B b (f a)))

{` lem:warn-abelian-group (abelian.tex:730). For abelian G, T(BG) ≃ B²G (as types). `}
def blind_warn_abelian_group : Type
  ≔ (G : AbelianGroup) → BookEquiv (BlindTorsors (BG (G .fst))) (BlindBB (G .fst) .carrier)
