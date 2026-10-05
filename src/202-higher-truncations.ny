export "201-truncation-step"

{` Extensions of g over the fiber of the unit at z. `}
def TruncExtensions (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type) (g : A → B)
  (z : TruncStep k R A) : Type
  ≔ Σ B (y ↦ (w : BookFiber A (TruncStep k R A) (trunc_step_unit k R A) z) → Id B y (g (w .fst)))

def trunc_step_extension_chain (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type)
  (hB : HLevel (suc. (suc. k)) B) (g : A → B) (x : A) (y : B)
  : Equiv ((w : BookFiber A (TruncStep k R A) (trunc_step_unit k R A) (trunc_step_unit k R A x)) → Id B y (g (w .fst)))
      (Id B y (g x))
  ≔ let C ≔ TruncStep k R A in let u ≔ trunc_step_unit k R A in
    let P1 ≔ (w : BookFiber A C u (u x)) → Id B y (g (w .fst)) in
    let P2 ≔ (x' : A) (p : Id C (u x) (u x')) → Id B y (g x') in
    let P3 ≔ (x' : A) → R (Id A x x') .carrier → Id B y (g x') in
    let P4 ≔ (x' : A) → Id A x x' → Id B y (g x') in
    let e12 ≔ curry_equiv A (x' ↦ Id C (u x) (u x')) (x' p ↦ Id B y (g x')) in
    let e23 ≔ pi_family_equiv A (x' ↦ Id C (u x) (u x') → Id B y (g x')) (x' ↦ R (Id A x x') .carrier → Id B y (g x'))
      (x' ↦ precompose_equiv (R (Id A x x') .carrier) (Id C (u x) (u x')) (Id B y (g x')) (trunc_step_path_equiv k R A x x')) in
    let e34 ≔ pi_family_equiv A (x' ↦ R (Id A x x') .carrier → Id B y (g x')) (x' ↦ Id A x x' → Id B y (g x'))
      (x' ↦ trunc_precompose_equiv k (Id A x x') (R (Id A x x')) (Id B y (g x')) (hB y (g x'))) in
    let e45 ≔ yoneda_evaluation_equiv A (x' ↦ Id B y (g x')) x in
    compose_equiv P1 P4 (Id B y (g x)) (compose_equiv P1 P3 P4 (compose_equiv P1 P2 P3 e12 e23) e34) e45

def trunc_step_extensions_unit (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type)
  (hB : HLevel (suc. (suc. k)) B) (g : A → B) (x : A)
  : BookIsContr (TruncExtensions k R A B g (trunc_step_unit k R A x))
  ≔ book_contractibility_equiv (Σ B (y ↦ Id B y (g x))) (TruncExtensions k R A B g (trunc_step_unit k R A x))
      (family_equiv B (y ↦ Id B y (g x))
        (y ↦ (w : BookFiber A (TruncStep k R A) (trunc_step_unit k R A) (trunc_step_unit k R A x)) → Id B y (g (w .fst)))
        (y ↦ canonical_inverse_equiv
          ((w : BookFiber A (TruncStep k R A) (trunc_step_unit k R A) (trunc_step_unit k R A x)) → Id B y (g (w .fst)))
          (Id B y (g x)) (trunc_step_extension_chain k R A B hB g x y)))
      .map (book_contraction (Σ B (y ↦ Id B y (g x))) (path_to_contractible B (g x)))

{` The book's contractible type of extensions over each fiber; it is a
   proposition, so surjectivity of the unit reduces it to the units. `}
def trunc_step_extensions (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type)
  (hB : HLevel (suc. (suc. k)) B) (g : A → B) (z : TruncStep k R A)
  : BookIsContr (TruncExtensions k R A B g z)
  ≔ mere_rec (BookFiber A (TruncStep k R A) (trunc_step_unit k R A) z) (BookIsContr (TruncExtensions k R A B g z))
      (book_iscontr_isprop (TruncExtensions k R A B g z))
      (s ↦ transport (TruncStep k R A) (w ↦ BookIsContr (TruncExtensions k R A B g w)) (trunc_step_unit k R A (s .fst)) z
        (inverse (TruncStep k R A) z (trunc_step_unit k R A (s .fst)) (s .snd))
        (trunc_step_extensions_unit k R A B hB g (s .fst)))
      (image_factor_surjective A (A → NTypes k) (trunc_path_family k R A) z)

def trunc_step_extend (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type)
  (hB : HLevel (suc. (suc. k)) B) (g : A → B) (z : TruncStep k R A) : B
  ≔ trunc_step_extensions k R A B hB g z .center .fst

def trunc_step_universal (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (B : Type)
  (hB : HLevel (suc. (suc. k)) B)
  : BookIsEquiv (TruncStep k R A → B) (A → B) (h ↦ compose A (TruncStep k R A) B h (trunc_step_unit k R A))
  ≔ book_quasi_inverse_equiv (TruncStep k R A → B) (A → B)
      (h ↦ compose A (TruncStep k R A) B h (trunc_step_unit k R A)) (trunc_step_extend k R A B hB)
      (h ↦ funext (TruncStep k R A) (_ ↦ B)
        (trunc_step_extend k R A B hB (compose A (TruncStep k R A) B h (trunc_step_unit k R A))) h
        (z ↦ refl ((t ↦ t .fst) : TruncExtensions k R A B (compose A (TruncStep k R A) B h (trunc_step_unit k R A)) z → B)
          (trunc_step_extensions k R A B hB (compose A (TruncStep k R A) B h (trunc_step_unit k R A)) z .contract
            (h z, w ↦ refl h (w .snd)))))
      (g ↦ funext A (_ ↦ B) (compose A (TruncStep k R A) B (trunc_step_extend k R A B hB g) (trunc_step_unit k R A)) g
        (a ↦ trunc_step_extensions k R A B hB g (trunc_step_unit k R A a) .center .snd (a, refl (trunc_step_unit k R A a))))
      .equiv

def trunc_step (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) : TruncStructure (suc. k) A
  ≔ (TruncStep k R A, trunc_step_unit k R A, trunc_step_level k R A, trunc_step_universal k R A)

def trunc_base (A : Type) : TruncStructure zero. A
  ≔ (Mere A, mere A, prop_to_hlevel_one (Mere A) (mere_isprop A),
     B hB ↦ mere_universal_property A B (hlevel_one_to_prop B hB) .equiv)

{` def:join-construction-of-truncation: all n-truncations, n = k - 1 ≥ -1,
   by induction; level 0 is the propositional truncation. `}
def truncation (k : Nat) (A : Type) : TruncStructure k A
  ≔ match k [ zero. ↦ trunc_base A | suc. k ↦ trunc_step k (truncation k) A ]

def Trunc (k : Nat) (A : Type) : Type ≔ truncation k A .carrier
def trunc_unit (k : Nat) (A : Type) : A → Trunc k A ≔ truncation k A .unit_map
def trunc_level (k : Nat) (A : Type) : HLevel (suc. k) (Trunc k A) ≔ truncation k A .level

{` The universal property: precomposition with the unit is an equivalence
   (‖A‖ₙ → B) ≃ (A → B) for every n-type B. `}
def trunc_universal_property (k : Nat) (A B : Type) (hB : HLevel (suc. k) B)
  : BookEquiv (Trunc k A → B) (A → B)
  ≔ (h ↦ compose A (Trunc k A) B h (trunc_unit k A), truncation k A .universal B hB)

{` eq:trunc-path-eq: ‖x = y‖ₙ ≃ (|x|ₙ₊₁ = |y|ₙ₊₁). `}
def trunc_path_equiv (k : Nat) (A : Type) (x y : A)
  : Equiv (Trunc k (Id A x y)) (Id (Trunc (suc. k) A) (trunc_unit (suc. k) A x) (trunc_unit (suc. k) A y))
  ≔ trunc_step_path_equiv k (truncation k) A x y

def trunc_path_equiv_unit (k : Nat) (A : Type) (x y : A) (r : Id A x y)
  : Id (Id (Trunc (suc. k) A) (trunc_unit (suc. k) A x) (trunc_unit (suc. k) A y))
      (trunc_step_path_gen k (truncation k) A x y r) (trunc_path_equiv k A x y .map (trunc_unit k (Id A x y) r))
  ≔ trunc_extend_beta k (Id A x y) (truncation k (Id A x y))
      (Id (Trunc (suc. k) A) (trunc_unit (suc. k) A x) (trunc_unit (suc. k) A y))
      (trunc_step_level k (truncation k) A (trunc_unit (suc. k) A x) (trunc_unit (suc. k) A y))
      (trunc_step_path_gen k (truncation k) A x y) r

{` Transparent descriptions of the levels. `}
def trunc_zero_mere (A : Type) : Id Type (Trunc zero. A) (Mere A) ≔ refl (Mere A)

def trunc_succ_image (k : Nat) (A : Type)
  : Id Type (Trunc (suc. k) A) (Image A (A → NTypes k) (trunc_path_family k (truncation k) A))
  ≔ refl (Image A (A → NTypes k) (trunc_path_family k (truncation k) A))

def trunc_induction_book (k : Nat) (A : Type) (P : Trunc k A → Type)
  (hP : (c : Trunc k A) → HLevel (suc. k) (P c)) (f : (a : A) → P (trunc_unit k A a)) (c : Trunc k A) : P c
  ≔ trunc_induction k A (truncation k A) P hP f c

{` At level 1 the construction agrees with the set truncation of 43. `}
def trunc_one_to_set_trunc (A : Type) : Trunc (suc. zero.) A → SetTrunc A
  ≔ trunc_extend (suc. zero.) A (truncation (suc. zero.) A) (SetTrunc A)
      (set_to_hlevel_two (SetTrunc A) (set_trunc_set A)) (set_trunc A)

def set_trunc_to_trunc_one (A : Type) : SetTrunc A → Trunc (suc. zero.) A
  ≔ set_trunc_rec A (Trunc (suc. zero.) A) (hlevel_two_to_set (Trunc (suc. zero.) A) (trunc_level (suc. zero.) A))
      (trunc_unit (suc. zero.) A)

def trunc_one_unit_compare (A : Type) (a : A)
  : Id (SetTrunc A) (trunc_one_to_set_trunc A (trunc_unit (suc. zero.) A a)) (set_trunc A a)
  ≔ inverse (SetTrunc A) (set_trunc A a) (trunc_one_to_set_trunc A (trunc_unit (suc. zero.) A a))
      (trunc_extend_beta (suc. zero.) A (truncation (suc. zero.) A) (SetTrunc A)
        (set_to_hlevel_two (SetTrunc A) (set_trunc_set A)) (set_trunc A) a)

def trunc_one_set_trunc_equiv (A : Type) : Equiv (Trunc (suc. zero.) A) (SetTrunc A)
  ≔ let T1 ≔ Trunc (suc. zero.) A in
    let f ≔ trunc_one_to_set_trunc A in let g ≔ set_trunc_to_trunc_one A in
    quasi_inverse_equiv T1 (SetTrunc A) f g
      (happly T1 (_ ↦ T1) (v ↦ g (f v)) (identity T1)
        (trunc_maps_equal (suc. zero.) A (truncation (suc. zero.) A) T1 (trunc_level (suc. zero.) A)
          (v ↦ g (f v)) (identity T1) (a ↦ refl g (trunc_one_unit_compare A a))))
      (set_trunc_induction A (z ↦ Id (SetTrunc A) (f (g z)) z)
        (z ↦ prop_is_set (Id (SetTrunc A) (f (g z)) z) (set_trunc_set A (f (g z)) z))
        (a ↦ trunc_one_unit_compare A a))
