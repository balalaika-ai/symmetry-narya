export "95-type-theoretic-yoneda"

def type_family_paths_equiv (X : Type) (R S : X → Type)
  : Equiv (Id (X → Type) R S) ((y : X) → Equiv (R y) (S y))
  ≔ compose_equiv (Id (X → Type) R S) ((y : X) → Id Type (R y) (S y))
      ((y : X) → Equiv (R y) (S y)) (function_extensionality X (_ ↦ Type) R S)
      (pi_equiv X (y ↦ Id Type (R y) (S y)) (y ↦ Equiv (R y) (S y))
        (y ↦ transport_univalence_equiv (R y) (S y)))

def representable_path_decode (X : Type) (x z : X)
  (p : Id (X → Type) (Representable X x) (Representable X z)) : Id X z x
  ≔ p (refl x) .trr (refl x)

{` Evaluation of a family path is an equivalence, by pointwise univalence
   and Yoneda.  Its map is literally transport of reflexivity. `}
def representable_path_decode_equiv (X : Type) (x z : X)
  : Equiv (Id (X → Type) (Representable X x) (Representable X z)) (Id X z x)
  ≔ compose_equiv (Id (X → Type) (Representable X x) (Representable X z))
      (YonedaSections X (Representable X z) x) (Id X z x)
      (compose_equiv (Id (X → Type) (Representable X x) (Representable X z))
        (RepresentableEquivalences X x z) (YonedaSections X (Representable X z) x)
        (type_family_paths_equiv X (Representable X x) (Representable X z))
        (representable_equivalences_sections X x z))
      (yoneda_evaluation_equiv X (Representable X z) x)

def representable_path_decode_refl (X : Type) (x : X)
  : Id (Id X x x) (representable_path_decode X x x (refl (Representable X x))) (inverse X x x (refl x))
  ≔ concat (Id X x x) (representable_path_decode X x x (refl (Representable X x)))
      (refl x) (inverse X x x (refl x))
      (transport_refl Type (Y ↦ Y) (Id X x x) (refl x))
      (inverse (Id X x x) (inverse X x x (refl x)) (refl x) (inverse_refl X x))

def representable_path_decode_ap (X : Type) (x z : X) (p : Id X x z)
  : Id (Id X z x) (representable_path_decode X x z (map_path X (X → Type) (Representable X) x z p))
      (inverse X x z p)
  ≔ J X x (z p ↦ Id (Id X z x)
      (representable_path_decode X x z (map_path X (X → Type) (Representable X) x z p)) (inverse X x z p))
      (representable_path_decode_refl X x) z p

{` Keep normalization of the two concrete equivalences outside the proof. `}
def equivalence_from_coordinates (A B Y : Type) (u : Equiv A Y) (v : Equiv B Y) (f : A → B)
  (agreement : (a : A) → Id Y (v .map (f a)) (u .map a)) : Equiv A B
  ≔ let e ≔ compose_equiv A Y B u (canonical_inverse_equiv B Y v) in
    equiv_change_map A B e f (a ↦ equivalence_injective B Y v (e .map a) (f a)
      (concat Y (v .map (e .map a)) (u .map a) (v .map (f a))
        (equiv_counit B Y v (u .map a))
        (inverse Y (v .map (f a)) (u .map a) (agreement a))))

def representable_ap_equiv (X : Type) (x z : X)
  : BookEquiv (Id X x z) (Id (X → Type) (Representable X x) (Representable X z))
  ≔ book_equivalence (Id X x z) (Id (X → Type) (Representable X x) (Representable X z))
      (equivalence_from_coordinates (Id X x z)
        (Id (X → Type) (Representable X x) (Representable X z)) (Id X z x)
        (inverse_path_equiv X x z) (representable_path_decode_equiv X x z)
        (map_path X (X → Type) (Representable X) x z) (representable_path_decode_ap X x z))

{` xca:TTYoneda, second clause.  The book's injection has propositional
   fibers, for arbitrary X, not merely an injective map between sets. `}
def representable_embedding (X : Type) : IsEmbedding X (X → Type) (Representable X)
  ≔ path_equivalences_embedding X (X → Type) (Representable X)
      (x z ↦ representable_ap_equiv X x z .equiv)

def representable_fiber_proposition (X : Type) (F : X → Type)
  : isProp (BookFiber X (X → Type) (Representable X) F)
  ≔ representable_embedding X F
