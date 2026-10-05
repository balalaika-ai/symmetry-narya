export "475-standard-bicycle-normality"

{` rem:inf-dihedral-frieze (group.tex 2262–2296) and the exercise at
   group.tex 2298. The pictures (frieze, translations and 180° rotations)
   are informal; their mathematical content is stated for every normal
   bicycle with base point x₀: T ≔ cbid(a x₀, x₀) = cbid(x₀, a⁻¹x₀),
   R ≔ cbid(b x₀, x₀) = cbid(x₀, b⁻¹x₀), T(⟦ℓ⟧x₀) = ⟦ℓ inl(−1)⟧x₀,
   R(⟦ℓ⟧x₀) = ⟦ℓ inr(−1)⟧x₀ and a(T⁻²R x₀) = T⁻²RT⁻¹x₀; then for the
   infinite dihedral bicycle R(aⁿx₀) = aⁿbx₀ and (X,a,b) = (X,T,R). `}

def bicycle_frieze_T (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) : Id Bicycles B B
  ≔ bicycle_cbid B h (bicycle_a B .map x0) x0

def bicycle_frieze_R (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) : Id Bicycles B B
  ≔ bicycle_cbid B h (bicycle_b B .map x0) x0

{` ⟦inl(−1)⟧ = a⁻¹ and ⟦inr(−1)⟧ = b⁻¹ (−1 = neg. 0). `}
def bicycle_letter_minus_one_left : List (Sum Int Int) ≔ cons. (inl. (neg. zero.)) nil.
def bicycle_letter_minus_one_right : List (Sum Int Int) ≔ cons. (inr. (neg. zero.)) nil.

{` T = cbid(a x₀, x₀) = cbid(x₀, a⁻¹ x₀). `}
def bicycle_frieze_T_alt (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (Id Bicycles B B) (bicycle_frieze_T B h x0)
      (bicycle_cbid B h x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0))
  ≔ let X ≔ bicycle_carrier B in
    let ainv ≔ equiv_inverse_map X X (bicycle_a B) in
    concat (Id Bicycles B B) (bicycle_frieze_T B h x0)
      (bicycle_cbid B h (ainv (bicycle_a B .map x0)) (ainv x0))
      (bicycle_cbid B h x0 (ainv x0))
      (bicycle_cbid_meaning B h bicycle_letter_minus_one_left (bicycle_a B .map x0) x0)
      (refl ((w ↦ bicycle_cbid B h w (ainv x0)) : X → Id Bicycles B B) (equiv_retraction X X (bicycle_a B) x0))

def bicycle_frieze_R_alt (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (Id Bicycles B B) (bicycle_frieze_R B h x0)
      (bicycle_cbid B h x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0))
  ≔ let X ≔ bicycle_carrier B in
    let binv ≔ equiv_inverse_map X X (bicycle_b B) in
    concat (Id Bicycles B B) (bicycle_frieze_R B h x0)
      (bicycle_cbid B h (binv (bicycle_b B .map x0)) (binv x0))
      (bicycle_cbid B h x0 (binv x0))
      (bicycle_cbid_meaning B h bicycle_letter_minus_one_right (bicycle_b B .map x0) x0)
      (refl ((w ↦ bicycle_cbid B h w (binv x0)) : X → Id Bicycles B B) (equiv_retraction X X (bicycle_b B) x0))

{` A symmetry s with s(x₀) = y sends ⟦ℓ⟧x₀ to ⟦ℓ⟧y. `}
def bicycle_symmetry_word_value (B : Bicycles) (s : Id Bicycles B B) (x0 y : bicycle_carrier B)
  (q : Id (bicycle_carrier B) y (bicycle_path_evaluate B B s x0)) (l : List (Sum Int Int))
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B s (bicycle_word_map B l x0)) (bicycle_word_map B l y)
  ≔ concat (bicycle_carrier B) (bicycle_path_evaluate B B s (bicycle_word_map B l x0))
      (bicycle_word_map B l (bicycle_path_evaluate B B s x0)) (bicycle_word_map B l y)
      (bicycle_path_evaluate_meaning B B s l x0)
      (refl (bicycle_word_map B l) (inverse (bicycle_carrier B) y (bicycle_path_evaluate B B s x0) q))

def bicycle_frieze_T_base (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (bicycle_carrier B)
      (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0)
      (bicycle_path_evaluate B B (bicycle_frieze_T B h x0) x0)
  ≔ let X ≔ bicycle_carrier B in
    let ainv ≔ equiv_inverse_map X X (bicycle_a B) in
    concat X (ainv x0) (bicycle_path_evaluate B B (bicycle_cbid B h x0 (ainv x0)) x0)
      (bicycle_path_evaluate B B (bicycle_frieze_T B h x0) x0)
      (bicycle_cbid_sends B h x0 (ainv x0))
      (refl ((s ↦ bicycle_path_evaluate B B s x0) : Id Bicycles B B → X)
        (inverse (Id Bicycles B B) (bicycle_frieze_T B h x0) (bicycle_cbid B h x0 (ainv x0)) (bicycle_frieze_T_alt B h x0)))

def bicycle_frieze_R_base (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (bicycle_carrier B)
      (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0)
      (bicycle_path_evaluate B B (bicycle_frieze_R B h x0) x0)
  ≔ let X ≔ bicycle_carrier B in
    let binv ≔ equiv_inverse_map X X (bicycle_b B) in
    concat X (binv x0) (bicycle_path_evaluate B B (bicycle_cbid B h x0 (binv x0)) x0)
      (bicycle_path_evaluate B B (bicycle_frieze_R B h x0) x0)
      (bicycle_cbid_sends B h x0 (binv x0))
      (refl ((s ↦ bicycle_path_evaluate B B s x0) : Id Bicycles B B → X)
        (inverse (Id Bicycles B B) (bicycle_frieze_R B h x0) (bicycle_cbid B h x0 (binv x0)) (bicycle_frieze_R_alt B h x0)))

{` T(⟦ℓ⟧x₀) = ⟦ℓ inl(−1)⟧(x₀) and R(⟦ℓ⟧x₀) = ⟦ℓ inr(−1)⟧(x₀): T and R append
   inl(−1), inr(−1) at the end of the word naming a point. `}
def bicycle_frieze_T_word (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) (l : List (Sum Int Int))
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B (bicycle_frieze_T B h x0) (bicycle_word_map B l x0))
      (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_left) x0)
  ≔ concat (bicycle_carrier B) (bicycle_path_evaluate B B (bicycle_frieze_T B h x0) (bicycle_word_map B l x0))
      (bicycle_word_map B l (bicycle_word_map B bicycle_letter_minus_one_left x0))
      (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_left) x0)
      (bicycle_symmetry_word_value B (bicycle_frieze_T B h x0) x0
        (bicycle_word_map B bicycle_letter_minus_one_left x0) (bicycle_frieze_T_base B h x0) l)
      (inverse (bicycle_carrier B) (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_left) x0)
        (bicycle_word_map B l (bicycle_word_map B bicycle_letter_minus_one_left x0))
        (bicycle_meaning_append (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l bicycle_letter_minus_one_left x0))

def bicycle_frieze_R_word (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) (l : List (Sum Int Int))
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B (bicycle_frieze_R B h x0) (bicycle_word_map B l x0))
      (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_right) x0)
  ≔ concat (bicycle_carrier B) (bicycle_path_evaluate B B (bicycle_frieze_R B h x0) (bicycle_word_map B l x0))
      (bicycle_word_map B l (bicycle_word_map B bicycle_letter_minus_one_right x0))
      (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_right) x0)
      (bicycle_symmetry_word_value B (bicycle_frieze_R B h x0) x0
        (bicycle_word_map B bicycle_letter_minus_one_right x0) (bicycle_frieze_R_base B h x0) l)
      (inverse (bicycle_carrier B) (bicycle_word_map B (append (Sum Int Int) l bicycle_letter_minus_one_right) x0)
        (bicycle_word_map B l (bicycle_word_map B bicycle_letter_minus_one_right x0))
        (bicycle_meaning_append (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l bicycle_letter_minus_one_right x0))

{` The middle expressions of the display: T = cbid(⟦ℓ⟧x₀, ⟦ℓ⟧(a⁻¹x₀)) and
   R = cbid(⟦ℓ⟧x₀, ⟦ℓ⟧(b⁻¹x₀)). `}
def bicycle_frieze_T_cbid_word (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) (l : List (Sum Int Int))
  : Id (Id Bicycles B B) (bicycle_frieze_T B h x0)
      (bicycle_cbid B h (bicycle_word_map B l x0)
        (bicycle_word_map B l (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0)))
  ≔ concat (Id Bicycles B B) (bicycle_frieze_T B h x0)
      (bicycle_cbid B h x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0))
      (bicycle_cbid B h (bicycle_word_map B l x0)
        (bicycle_word_map B l (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0)))
      (bicycle_frieze_T_alt B h x0)
      (bicycle_cbid_meaning B h l x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_a B) x0))

def bicycle_frieze_R_cbid_word (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B) (l : List (Sum Int Int))
  : Id (Id Bicycles B B) (bicycle_frieze_R B h x0)
      (bicycle_cbid B h (bicycle_word_map B l x0)
        (bicycle_word_map B l (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0)))
  ≔ concat (Id Bicycles B B) (bicycle_frieze_R B h x0)
      (bicycle_cbid B h x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0))
      (bicycle_cbid B h (bicycle_word_map B l x0)
        (bicycle_word_map B l (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0)))
      (bicycle_frieze_R_alt B h x0)
      (bicycle_cbid_meaning B h l x0 (equiv_inverse_map (bicycle_carrier B) (bicycle_carrier B) (bicycle_b B) x0))

{` Symmetries commute with a: s(a w) = a(s w). `}
def bicycle_symmetry_commutes_a (B : Bicycles) (s : Id Bicycles B B) (w : bicycle_carrier B)
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B s (bicycle_a B .map w)) (bicycle_a B .map (bicycle_path_evaluate B B s w))
  ≔ bicycle_path_evaluate_meaning B B s (cons. (inl. (pos. (suc. zero.))) nil.) w

{` T⁻¹(x₀) = a x₀, since T(a x₀) = x₀. `}
def bicycle_frieze_T_inverse_base (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0)) x0) (bicycle_a B .map x0)
  ≔ let T ≔ bicycle_frieze_T B h x0 in
    concat (bicycle_carrier B) (bicycle_path_evaluate B B (inverse Bicycles B B T) x0)
      (bicycle_path_evaluate B B (inverse Bicycles B B T) (bicycle_path_evaluate B B T (bicycle_a B .map x0)))
      (bicycle_a B .map x0)
      (refl (bicycle_path_evaluate B B (inverse Bicycles B B T)) (bicycle_cbid_sends B h (bicycle_a B .map x0) x0))
      (bicycle_path_evaluate_inverse B B T (bicycle_a B .map x0))

{` "a(T⁻²R(x₀)) = T⁻²RT⁻¹(x₀)": with T⁻¹ the inverse symmetry, as composite
   functions applied to x₀. `}
def bicycle_frieze_example (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  : Id (bicycle_carrier B)
      (bicycle_a B .map
        (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0))
          (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0))
            (bicycle_path_evaluate B B (bicycle_frieze_R B h x0) x0))))
      (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0))
        (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0))
          (bicycle_path_evaluate B B (bicycle_frieze_R B h x0)
            (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_frieze_T B h x0)) x0))))
  ≔ let X ≔ bicycle_carrier B in
    let Ti ≔ inverse Bicycles B B (bicycle_frieze_T B h x0) in
    let R ≔ bicycle_frieze_R B h x0 in
    let ti ≔ bicycle_path_evaluate B B Ti in
    let r ≔ bicycle_path_evaluate B B R in
    let a ≔ bicycle_a B .map in
    calc
      a (ti (ti (r x0)))
      = ti (a (ti (r x0))) by inverse X (ti (a (ti (r x0)))) (a (ti (ti (r x0)))) (bicycle_symmetry_commutes_a B Ti (ti (r x0)))
      = ti (ti (a (r x0))) by refl ti (inverse X (ti (a (r x0))) (a (ti (r x0))) (bicycle_symmetry_commutes_a B Ti (r x0)))
      = ti (ti (r (a x0)))
        by refl ((w ↦ ti (ti w)) : X → X) (inverse X (r (a x0)) (a (r x0)) (bicycle_symmetry_commutes_a B R x0))
      = ti (ti (r (ti x0)))
        by refl ((w ↦ ti (ti (r w))) : X → X) (inverse X (ti x0) (a x0) (bicycle_frieze_T_inverse_base B h x0)) ∎

{` The infinite dihedral bicycle: R(aⁿx₀) = aⁿ b x₀ (here b⁻¹ = b), for every x₀. `}
def dihedral_frieze_R_power (x0 : Sum Int Int) (n : Int)
  : Id (Sum Int Int)
      (bicycle_path_evaluate infinite_dihedral_bicycle infinite_dihedral_bicycle
        (bicycle_frieze_R infinite_dihedral_bicycle infinite_dihedral_bicycle_normal x0)
        (permutation_power (Sum Int Int) dihedral_a_equiv n x0))
      (permutation_power (Sum Int Int) dihedral_a_equiv n (dihedral_b_map x0))
  ≔ bicycle_symmetry_word_value infinite_dihedral_bicycle
      (bicycle_frieze_R infinite_dihedral_bicycle infinite_dihedral_bicycle_normal x0) x0 (dihedral_b_map x0)
      (bicycle_frieze_R_base infinite_dihedral_bicycle infinite_dihedral_bicycle_normal x0)
      (cons. (inl. n) nil.)

{` Exercise at group.tex 2298, with x₀ = inl 0 as in fig:first-frieze-bicycle.
   T and R are identified with the translation σ⁺₋₁ and the reflection σ⁻₀
   (uniqueness of symmetries with a given value), e(inl n) = inl(−n),
   e(inr n) = inr n intertwines (a, b) with (T, R), and the bicycle
   (X, T, R) is identified with (X, a, b). `}
def dihedral_origin : Sum Int Int ≔ inl. int_zero

def dihedral_bicycle_normal : IsNormalBicycle infinite_dihedral_bicycle ≔ infinite_dihedral_bicycle_normal

def dihedral_frieze_T_shift
  : Id (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle)
      (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_shift_iso (neg. zero.)))
      (bicycle_frieze_T infinite_dihedral_bicycle dihedral_bicycle_normal dihedral_origin)
  ≔ bicycle_cbid_unique infinite_dihedral_bicycle dihedral_bicycle_normal (dihedral_a_map dihedral_origin) dihedral_origin
      (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_shift_iso (neg. zero.)))
      (refl (inl. int_zero : Sum Int Int))

def dihedral_frieze_R_reflection
  : Id (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle)
      (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_reflection_iso int_zero))
      (bicycle_frieze_R infinite_dihedral_bicycle dihedral_bicycle_normal dihedral_origin)
  ≔ bicycle_cbid_unique infinite_dihedral_bicycle dihedral_bicycle_normal (dihedral_b_map dihedral_origin) dihedral_origin
      (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_reflection_iso int_zero))
      (refl (inl. int_zero : Sum Int Int))

{` T and R as permutations of Z ⊔ Z (the underlying equivalences of the
   symmetries), with their values: T = σ⁺₋₁ (downward translation),
   R = σ⁻₀ (rotation about the midpoint of x₀ and b x₀). `}
def dihedral_frieze_T_equiv : Equiv (Sum Int Int) (Sum Int Int)
  ≔ bicycle_paths_equiv infinite_dihedral_bicycle infinite_dihedral_bicycle
      .map (bicycle_frieze_T infinite_dihedral_bicycle dihedral_bicycle_normal dihedral_origin) .fst

def dihedral_frieze_R_equiv : Equiv (Sum Int Int) (Sum Int Int)
  ≔ bicycle_paths_equiv infinite_dihedral_bicycle infinite_dihedral_bicycle
      .map (bicycle_frieze_R infinite_dihedral_bicycle dihedral_bicycle_normal dihedral_origin) .fst

def dihedral_frieze_T_values (w : Sum Int Int)
  : Id (Sum Int Int) (dihedral_shift_map (neg. zero.) w) (dihedral_frieze_T_equiv .map w)
  ≔ refl ((s ↦ bicycle_path_evaluate infinite_dihedral_bicycle infinite_dihedral_bicycle s w)
        : Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle → Sum Int Int)
      dihedral_frieze_T_shift

def dihedral_frieze_R_values (w : Sum Int Int)
  : Id (Sum Int Int) (dihedral_reflection_map int_zero w) (dihedral_frieze_R_equiv .map w)
  ≔ refl ((s ↦ bicycle_path_evaluate infinite_dihedral_bicycle infinite_dihedral_bicycle s w)
        : Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle → Sum Int Int)
      dihedral_frieze_R_reflection

{` e(inl n) = inl(−n), e(inr n) = inr n. `}
def dihedral_flip_map : Sum Int Int → Sum Int Int ≔ [ inl. n ↦ inl. (int_neg n) | inr. n ↦ inr. n ]

def dihedral_flip_involutive (x : Sum Int Int) : Id (Sum Int Int) (dihedral_flip_map (dihedral_flip_map x)) x
  ≔ match x [ inl. n ↦ inl. (int_neg_neg n) | inr. n ↦ refl (inr. n : Sum Int Int) ]

def dihedral_flip_equiv : Equiv (Sum Int Int) (Sum Int Int)
  ≔ quasi_inverse_equiv (Sum Int Int) (Sum Int Int) dihedral_flip_map dihedral_flip_map
      dihedral_flip_involutive dihedral_flip_involutive

def dihedral_flip_commutes_T : Commutes (Sum Int Int) (Sum Int Int) dihedral_a_equiv dihedral_frieze_T_equiv dihedral_flip_map
  ≔ [ inl. n ↦ concat (Sum Int Int) (inl. (int_neg (int_succ n))) (inl. (int_add (neg. zero.) (int_neg n)))
        (dihedral_frieze_T_equiv .map (inl. (int_neg n)))
        (inl. (concat Int (int_neg (int_succ n)) (int_pred (int_neg n)) (int_add (neg. zero.) (int_neg n))
          (dihedral_neg_succ n) (int_add_comm (int_neg n) (neg. zero.))))
        (dihedral_frieze_T_values (inl. (int_neg n)))
    | inr. n ↦ concat (Sum Int Int) (inr. (int_pred n)) (inr. (int_add (neg. zero.) n))
        (dihedral_frieze_T_equiv .map (inr. n))
        (inr. (int_add_comm n (neg. zero.)))
        (dihedral_frieze_T_values (inr. n)) ]

def dihedral_flip_commutes_R : Commutes (Sum Int Int) (Sum Int Int) dihedral_b_equiv dihedral_frieze_R_equiv dihedral_flip_map
  ≔ [ inl. n ↦ concat (Sum Int Int) (inr. n) (inr. (int_add int_zero (int_neg (int_neg n))))
        (dihedral_frieze_R_equiv .map (inl. (int_neg n)))
        (inr. (concat Int n (int_neg (int_neg n)) (int_add int_zero (int_neg (int_neg n)))
          (inverse Int (int_neg (int_neg n)) n (int_neg_neg n))
          (inverse Int (int_add int_zero (int_neg (int_neg n))) (int_neg (int_neg n)) (int_add_zero_left (int_neg (int_neg n))))))
        (dihedral_frieze_R_values (inl. (int_neg n)))
    | inr. n ↦ concat (Sum Int Int) (inl. (int_neg n)) (inl. (int_add int_zero (int_neg n)))
        (dihedral_frieze_R_equiv .map (inr. n))
        (inl. (inverse Int (int_add int_zero (int_neg n)) (int_neg n) (int_add_zero_left (int_neg n))))
        (dihedral_frieze_R_values (inr. n)) ]

{` The geometric cousin (Z ⊔ Z, T, R) is a bicycle, and it is identified
   with the infinite dihedral bicycle. `}
def dihedral_frieze_bicycle : Bicycles
  ≔ mkbicycle (Sum Int Int, dihedral_set) dihedral_frieze_T_equiv dihedral_frieze_R_equiv
      (bicycle_connected_transfer (Sum Int Int) (Sum Int Int) dihedral_a_equiv dihedral_b_equiv
        dihedral_frieze_T_equiv dihedral_frieze_R_equiv dihedral_flip_equiv
        dihedral_flip_commutes_T dihedral_flip_commutes_R dihedral_bicycle_connected)

def dihedral_frieze_identification : Id Bicycles infinite_dihedral_bicycle dihedral_frieze_bicycle
  ≔ bicycle_path_from_iso infinite_dihedral_bicycle dihedral_frieze_bicycle
      (dihedral_flip_equiv, (dihedral_flip_commutes_T, dihedral_flip_commutes_R))
