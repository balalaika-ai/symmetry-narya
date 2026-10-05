export "148-order-gcd-lcm"

{` Conventions for higher truncations: the index k : Nat stands for the book
   level n = k - 1, so k = 0 is the propositional truncation and k = 1 the
   set truncation.  An n-type has HLevel index n + 2 = k + 1. `}

def prop_hlevel (n : Nat) (A : Type) (h : isProp A) : HLevel (suc. n) A
  ≔ match n [
  | zero. ↦ prop_to_hlevel_one A h
  | suc. n ↦ hlevel_raise (suc. n) A (prop_hlevel n A h) ]

{` The type of book (k-1)-types. `}
def NTypes (k : Nat) : Type ≔ Σ Type (HLevel (suc. k))

def ntypes_path_equiv (k : Nat) (X Y : NTypes k) : Equiv (Id (NTypes k) X Y) (Equiv (X .fst) (Y .fst))
  ≔ compose_equiv (Id (NTypes k) X Y) (Id Type (X .fst) (Y .fst)) (Equiv (X .fst) (Y .fst))
      (subtype_path_equiv Type (HLevel (suc. k)) (Z ↦ hlevel_isprop (suc. k) Z) X Y)
      (univalence_equiv (X .fst) (Y .fst))

def equiv_hlevel (k : Nat) (X Y : Type) (hY : HLevel (suc. k) Y) : HLevel (suc. k) (Equiv X Y)
  ≔ hlevel_equiv (suc. k) (Σ (X → Y) (isEquiv X Y)) (Equiv X Y)
      (canonical_inverse_equiv (Equiv X Y) (Σ (X → Y) (isEquiv X Y)) (equiv_sigma_equiv X Y))
      (hlevel_sigma (suc. k) (X → Y) (isEquiv X Y) (hlevel_function (suc. k) X Y hY)
        (f ↦ prop_hlevel k (isEquiv X Y f) (isequiv_isprop X Y f)))

{` The type of n-types is an (n+1)-type. `}
def ntypes_level (k : Nat) : HLevel (suc. (suc. k)) (NTypes k)
  ≔ X Y ↦ hlevel_equiv (suc. k) (Equiv (X .fst) (Y .fst)) (Id (NTypes k) X Y)
      (canonical_inverse_equiv (Id (NTypes k) X Y) (Equiv (X .fst) (Y .fst)) (ntypes_path_equiv k X Y))
      (equiv_hlevel k (X .fst) (Y .fst) (Y .snd))

{` A (k-1)-truncation of A: an n-type with a unit map through which every map
   into an n-type factors uniquely (precomposition is an equivalence). `}
def TruncStructure (k : Nat) (A : Type) : Type ≔ sig (
  carrier : Type,
  unit_map : A → carrier,
  level : HLevel (suc. k) carrier,
  universal : (B : Type) → HLevel (suc. k) B
    → BookIsEquiv (carrier → B) (A → B) (h ↦ compose A carrier B h unit_map) )

def trunc_precompose_equiv (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  : Equiv (R .carrier → B) (A → B)
  ≔ native_equivalence (R .carrier → B) (A → B)
      (h ↦ compose A (R .carrier) B h (R .unit_map), R .universal B hB)

def trunc_extend (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  (g : A → B) : R .carrier → B
  ≔ R .universal B hB g .center .fst

def trunc_extend_beta (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  (g : A → B) (a : A) : Id B (g a) (trunc_extend k A R B hB g (R .unit_map a))
  ≔ R .universal B hB g .center .snd (refl a)

def trunc_maps_equal (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  (h h' : R .carrier → B) (p : (a : A) → Id B (h (R .unit_map a)) (h' (R .unit_map a)))
  : Id (R .carrier → B) h h'
  ≔ equivalence_injective (R .carrier → B) (A → B) (trunc_precompose_equiv k A R B hB) h h'
      (funext A (_ ↦ B) (compose A (R .carrier) B h (R .unit_map)) (compose A (R .carrier) B h' (R .unit_map)) p)

{` Dependent elimination into families of n-types, derived from the
   universal property. `}
def trunc_induction (k : Nat) (A : Type) (R : TruncStructure k A) (P : R .carrier → Type)
  (hP : (c : R .carrier) → HLevel (suc. k) (P c)) (f : (a : A) → P (R .unit_map a)) (c : R .carrier) : P c
  ≔ let C ≔ R .carrier in
    let S ≔ Σ C P in
    let hS ≔ hlevel_sigma (suc. k) C P (R .level) hP in
    let s ≔ trunc_extend k A R S hS (a ↦ (R .unit_map a, f a)) in
    let fs ≔ trunc_maps_equal k A R C (R .level) (x ↦ s x .fst) (identity C)
      (a ↦ inverse C (R .unit_map a) (s (R .unit_map a) .fst)
        (refl ((w ↦ w .fst) : S → C) (trunc_extend_beta k A R S hS (a ↦ (R .unit_map a, f a)) a))) in
    transport C P (s c .fst) c (happly C (_ ↦ C) (x ↦ s x .fst) (identity C) fs c) (s c .snd)

def pi_injective (X : Type) (B D : X → Type) (k : (x : X) → B x → D x)
  (hk : (x : X) → PathReflecting (B x) (D x) (k x))
  : PathReflecting ((x : X) → B x) ((x : X) → D x) (s x ↦ k x (s x))
  ≔ s t p ↦ funext X B s t (x ↦ hk x (s x) (t x) (p (refl x)))

def type_path_transport_injective (X Y : Type)
  : PathReflecting (Id Type X Y) (X → Y) (q ↦ transport Type (Z ↦ Z) X Y q)
  ≔ q r h ↦ equivalence_injective (Id Type X Y) (Equiv X Y) (univalence_equiv X Y) q r
      (equiv_path X Y (id_to_equiv X Y q) (id_to_equiv X Y r)
        (funext X (_ ↦ Y) (id_to_equiv X Y q .map) (id_to_equiv X Y r .map)
          (a ↦ concat Y (id_to_equiv X Y q .map a) (transport Type (Z ↦ Z) X Y q a) (id_to_equiv X Y r .map a)
            (id_to_equiv_transport X Y q a)
            (concat Y (transport Type (Z ↦ Z) X Y q a) (transport Type (Z ↦ Z) X Y r a) (id_to_equiv X Y r .map a)
              (h (refl a))
              (inverse Y (id_to_equiv X Y r .map a) (transport Type (Z ↦ Z) X Y r a) (id_to_equiv_transport X Y r a))))))

def inverse_injective (A : Type) (x y : A) : PathReflecting (Id A x y) (Id A y x) (inverse A x y)
  ≔ p q h ↦ calc
      p = inverse A y x (inverse A x y p) by inverse (Id A x y) (inverse A y x (inverse A x y p)) p (inverse_inverse A x y p)
      = inverse A y x (inverse A x y q) by refl (inverse A y x) h
      = q by inverse_inverse A x y q ∎

def precompose_equiv (X Y Z : Type) (e : Equiv X Y) : Equiv (Y → Z) (X → Z)
  ≔ quasi_inverse_equiv (Y → Z) (X → Z) (h x ↦ h (e .map x)) (k y ↦ k (equiv_inverse_map X Y e y))
      (h ↦ funext Y (_ ↦ Z) (y ↦ h (e .map (equiv_inverse_map X Y e y))) h (y ↦ refl h (equiv_counit X Y e y)))
      (k ↦ funext X (_ ↦ Z) (x ↦ k (equiv_inverse_map X Y e (e .map x))) k (x ↦ refl k (equiv_retraction X Y e x)))
