export "562-gset-transitivity-finiteness"
export "563-gset-fixed-points"
export "153-heavy-transport"
export "174-cyclic-permutations"

{` Chapter 5 (actions.tex): the example after xca:AutC3 (the standard
   Σ_n-set as a composite, transitive for n > 0; the action of Σ_n on
   decidable subsets of Fin n) and xca:Gset-A->B (the Σ_2 × Σ_2-set
   (A, B) ↦ (A → B) and the easier cases: the action, the invariant maps
   and the orbit relation on the underlying set). `}

{` The standard Σ_n-set (core standard_symmetric_gset) is the composite of
   the standard action id : BΣ_n → BΣ_n with the projection BΣ_n → Set. `}
def standard_symmetric_gset_composite (n : Nat)
  : Id (GSet (symmetric_group n)) (standard_symmetric_gset n)
      (z ↦ standard_action (symmetric_group n) z .fst)
  ≔ refl (standard_symmetric_gset n)

{` Footnote: the standard Σ_n-set is transitive for n > 0: for y : Fin (n+1),
   the transposition (0 y) sends y to 0. `}
def standard_symmetric_transposition (n : Nat) (y : Fin (suc. n)) : USym (symmetric_group (suc. n))
  ≔ permutation_symmetry (standard_set (suc. n))
      (transposition_equiv (Fin (suc. n)) (fin_decidable_equality (suc. n)) (inr. star.) y)

def standard_symmetric_gset_transitive (n : Nat)
  : IsTransitive (symmetric_group (suc. n)) (standard_symmetric_gset (suc. n))
  ≔ let G ≔ symmetric_group (suc. n) in
    let F ≔ Fin (suc. n) in
    let R : F → Type ≔ y ↦ Σ (USym G) (g ↦ Id F (inr. star.) (gset_usym_act G (standard_symmetric_gset (suc. n)) g y)) in
    mere (Σ F (x ↦ (y : F) → Mere (Σ (USym G) (g ↦ Id F x (gset_usym_act G (standard_symmetric_gset (suc. n)) g y)))))
      (inr. star., y ↦ mere (R y)
        (standard_symmetric_transposition n y,
         inverse F (transposition F (fin_decidable_equality (suc. n)) (inr. star.) y y) (inr. star.)
           (transposition_right F (fin_decidable_equality (suc. n)) (inr. star.) y)))

{` For n = 0 it is not transitive (its underlying set is empty). `}
def standard_symmetric_gset_zero_not_transitive
  (t : IsTransitive (symmetric_group zero.) (standard_symmetric_gset zero.)) : Empty
  ≔ mere_rec (Fin zero.) Empty empty_prop (e ↦ e)
      (gset_transitive_nonempty (symmetric_group zero.) (standard_symmetric_gset zero.) t)

{` Composing further with S ↦ (S → Bool) : Set → Set gives the action of
   Σ_n on the set Fin n → Bool of decidable subsets of Fin n. `}
def bool_power_set (S : SetTypes) : SetTypes ≔ (S .fst → Bool, pi_set (S .fst) (_ ↦ Bool) (_ ↦ bool_set))

def decidable_subsets_gset (n : Nat) : GSet (symmetric_group n)
  ≔ z ↦ bool_power_set (standard_symmetric_gset n z)

def decidable_subsets_gset_underlying (n : Nat)
  : Id Type (gset_underlying (symmetric_group n) (decidable_subsets_gset n)) (Fin n → Bool)
  ≔ refl (Fin n → Bool)

{` The action is by precomposition with the inverse: (g · s)(g · x) = s(x). `}
def decidable_subsets_act (n : Nat) (g : USym (symmetric_group n)) (s : Fin n → Bool) (x : Fin n)
  : Id Bool
      (gset_usym_act (symmetric_group n) (decidable_subsets_gset n) g s
        (gset_usym_act (symmetric_group n) (standard_symmetric_gset n) g x))
      (s x)
  ≔ let G ≔ symmetric_group n in
    let B ≔ BG G .carrier in
    let sh ≔ shape G in
    let Y : B → Type ≔ z ↦ z .fst .fst in
    calc
      gset_usym_act G (decidable_subsets_gset n) g s (transport B Y sh sh g x)
      = transport B (_ ↦ Bool) sh sh g (s (transport B Y sh sh (inverse B sh sh g) (transport B Y sh sh g x)))
        by transport_function_family B Y (_ ↦ Bool) sh sh g s (transport B Y sh sh g x)
      = s (transport B Y sh sh (inverse B sh sh g) (transport B Y sh sh g x))
        by transport_constant B Bool sh sh g (s (transport B Y sh sh (inverse B sh sh g) (transport B Y sh sh g x)))
      = s x by refl s (transport_inverse_roundtrip B Y sh sh g x) ∎

{` Litmus (Σ_3): τ = (0 1) moves the decidable subset {0} to a subset
   containing 1. `}
def fin3_singleton_zero : Fin three → Bool ≔ [ inr. _ ↦ true. | inl. _ ↦ false. ]

def sigma3_decidable_subset_moved
  : Id Bool (gset_usym_act (symmetric_group three) (decidable_subsets_gset three) sigma3_tau fin3_singleton_zero fin3_one)
      true.
  ≔ decidable_subsets_act three sigma3_tau fin3_singleton_zero fin3_zero

{` xca:Gset-A->B. G ≔ Σ_2 × Σ_2 (B(Σ_2 × Σ_2) ≡ BΣ_2 × BΣ_2) and
   X(A, B) ≔ (A → B). `}
def sigma_two : Group ≔ symmetric_group two

def sigma_two_squared : Group ≔ product_group sigma_two sigma_two

def function_gset : GSet sigma_two_squared
  ≔ ab ↦ (ab .fst .fst .fst → ab .snd .fst .fst,
      pi_set (ab .fst .fst .fst) (_ ↦ ab .snd .fst .fst) (_ ↦ ab .snd .fst .snd))

def function_gset_underlying : Id Type (gset_underlying sigma_two_squared function_gset) (Fin two → Fin two)
  ≔ refl (Fin two → Fin two)

{` The action on X(sh_G) = (Fin 2 → Fin 2): for g = (σ, τ),
   (g · f)(σ · x) = τ · f(x), i.e. g · f = τ ∘ f ∘ σ⁻¹. `}
def function_gset_act (g : USym sigma_two_squared) (f : Fin two → Fin two) (x : Fin two)
  : Id (Fin two)
      (gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two (standard_symmetric_gset two) (g .fst) x))
      (gset_usym_act sigma_two (standard_symmetric_gset two) (g .snd) (f x))
  ≔ let B ≔ BG sigma_two_squared .carrier in
    let sh ≔ shape sigma_two_squared in
    let Y : B → Type ≔ ab ↦ ab .fst .fst .fst in
    let Z : B → Type ≔ ab ↦ ab .snd .fst .fst in
    calc
      gset_usym_act sigma_two_squared function_gset g f (transport B Y sh sh g x)
      = transport B Z sh sh g (f (transport B Y sh sh (inverse B sh sh g) (transport B Y sh sh g x)))
        by transport_function_family B Y Z sh sh g f (transport B Y sh sh g x)
      = transport B Z sh sh g (f x)
        by refl ((u ↦ transport B Z sh sh g (f u)) : Fin two → Fin two) (transport_inverse_roundtrip B Y sh sh g x) ∎

{` The easier cases: the constant Σ_2 × Σ_2-set 2 × 2, and the Σ_2-sets
   X(-, 2) and X(2, -) (restrictions along the two inclusions). `}
def gset_fin2_squared_set : SetTypes
  ≔ (Product (Fin two) (Fin two), sigma_set (Fin two) (_ ↦ Fin two) (fin_set two) (_ ↦ fin_set two))

def constant_square_gset : GSet sigma_two_squared ≔ gset_trivial sigma_two_squared gset_fin2_squared_set

def function_gset_left : GSet sigma_two
  ≔ gset_restrict sigma_two sigma_two_squared (product_group_incl1 sigma_two sigma_two) function_gset

def function_gset_right : GSet sigma_two
  ≔ gset_restrict sigma_two sigma_two_squared (product_group_incl2 sigma_two sigma_two) function_gset

def function_gset_left_value (A : BG sigma_two .carrier)
  : Id Type (function_gset_left A .fst) (A .fst .fst → Fin two)
  ≔ refl (A .fst .fst → Fin two)

def function_gset_right_value (B0 : BG sigma_two .carrier)
  : Id Type (function_gset_right B0 .fst) (Fin two → B0 .fst .fst)
  ≔ refl (Fin two → B0 .fst .fst)

{` The swap τ of Fin 2 (the transposition (0 1)) and its symmetry in Σ_2;
   it has no fixed point. `}
def gset_fin2_zero : Fin two ≔ inr. star.

def gset_fin2_one : Fin two ≔ inl. (inr. star.)

def gset_fin2_transposition : Equiv (Fin two) (Fin two)
  ≔ transposition_equiv (Fin two) (fin_decidable_equality two) gset_fin2_zero gset_fin2_one

def sigma_two_swap : USym sigma_two ≔ permutation_symmetry (standard_set two) gset_fin2_transposition

def gset_fin2_zero_code : Fin two → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def gset_fin2_zero_not_one (p : Id (Fin two) gset_fin2_zero gset_fin2_one) : Empty
  ≔ transport (Fin two) gset_fin2_zero_code gset_fin2_zero gset_fin2_one p star.

def gset_fin2_transposition_no_fixed (y : Fin two)
  (h : Id (Fin two) (gset_fin2_transposition .map y) y) : Empty
  ≔ let d ≔ fin_decidable_equality two in
    match y [
    | inr. star. ↦ gset_fin2_zero_not_one
        (inverse (Fin two) gset_fin2_one gset_fin2_zero
          (concat (Fin two) gset_fin2_one (gset_fin2_transposition .map gset_fin2_zero) gset_fin2_zero
            (inverse (Fin two) (gset_fin2_transposition .map gset_fin2_zero) gset_fin2_one
              (transposition_left (Fin two) d gset_fin2_zero gset_fin2_one))
            h))
    | inl. (inr. star.) ↦ gset_fin2_zero_not_one
        (concat (Fin two) gset_fin2_zero (gset_fin2_transposition .map gset_fin2_one) gset_fin2_one
          (inverse (Fin two) (gset_fin2_transposition .map gset_fin2_one) gset_fin2_zero
            (transposition_right (Fin two) d gset_fin2_zero gset_fin2_one))
          h)
    | inl. (inl. e) ↦ match e [] ]

{` The main case: X^hG is empty. An invariant map gives f : Fin 2 → Fin 2
   fixed by g = (refl, τ); then f(x) = τ(f(x)), impossible. `}
def function_gset_no_fixed_points (u : GSetFixedPoints sigma_two_squared function_gset) : Empty
  ≔ let f ≔ u .fst in
    let g : USym sigma_two_squared ≔ (refl (shape sigma_two), sigma_two_swap) in
    let x ≔ gset_fin2_zero in
    let std ≔ standard_symmetric_gset two in
    gset_fin2_transposition_no_fixed (f x)
      (calc
        gset_fin2_transposition .map (f x)
        = gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two std (refl (shape sigma_two)) x)
          by inverse (Fin two)
            (gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two std (refl (shape sigma_two)) x))
            (gset_fin2_transposition .map (f x)) (function_gset_act g f x)
        = gset_usym_act sigma_two_squared function_gset g f x
          by refl (gset_usym_act sigma_two_squared function_gset g f) (gset_act_unit sigma_two std x)
        = f x by refl ((k ↦ k x) : (Fin two → Fin two) → Fin two) (u .snd g) ∎)

def function_gset_no_invariant_maps (s : InvariantMaps sigma_two_squared function_gset) : Empty
  ≔ function_gset_no_fixed_points (invariant_map_fixed sigma_two_squared function_gset s)

{` Constant 2 × 2: every element is fixed, X^hG ≃ 2 × 2. `}
def constant_square_invariant_equiv
  : Equiv (InvariantMaps sigma_two_squared constant_square_gset) (Product (Fin two) (Fin two))
  ≔ compose_equiv (InvariantMaps sigma_two_squared constant_square_gset)
      (GSetFixedPoints sigma_two_squared constant_square_gset) (Product (Fin two) (Fin two))
      (invariant_maps_fixed_equiv sigma_two_squared constant_square_gset)
      (quasi_inverse_equiv (GSetFixedPoints sigma_two_squared constant_square_gset) (Product (Fin two) (Fin two))
        (u ↦ u .fst) (x ↦ trivial_gset_fixed_point sigma_two_squared gset_fin2_squared_set x)
        (u ↦ subtype_equal (Product (Fin two) (Fin two))
          (x ↦ (g : USym sigma_two_squared) →
            Id (Product (Fin two) (Fin two)) (gset_usym_act sigma_two_squared constant_square_gset g x) x)
          (gset_fixed_points_prop sigma_two_squared constant_square_gset)
          (trivial_gset_fixed_point sigma_two_squared gset_fin2_squared_set (u .fst)) u (refl (u .fst)))
        (x ↦ refl x))

{` X(2, -): a fixed f would satisfy τ ∘ f = f; X^hΣ_2 is empty. `}
def function_gset_right_no_invariant_maps (s : InvariantMaps sigma_two function_gset_right) : Empty
  ≔ let u ≔ invariant_map_fixed sigma_two function_gset_right s in
    let f ≔ u .fst in
    let x ≔ gset_fin2_zero in
    let std ≔ standard_symmetric_gset two in
    let g : USym sigma_two_squared ≔ (refl (shape sigma_two), sigma_two_swap) in
    gset_fin2_transposition_no_fixed (f x)
      (calc
        gset_fin2_transposition .map (f x)
        = gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two std (refl (shape sigma_two)) x)
          by inverse (Fin two)
            (gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two std (refl (shape sigma_two)) x))
            (gset_fin2_transposition .map (f x)) (function_gset_act g f x)
        = gset_usym_act sigma_two_squared function_gset g f x
          by refl (gset_usym_act sigma_two_squared function_gset g f) (gset_act_unit sigma_two std x)
        = f x by refl ((k ↦ k x) : (Fin two → Fin two) → Fin two) (u .snd sigma_two_swap) ∎)

{` X(-, 2): the fixed points are the constant maps, so X^hΣ_2 ≃ 2 (the
   value at 0; a fixed f satisfies f ∘ τ = f). `}
def function_gset_left_fixed_constant (u : GSetFixedPoints sigma_two function_gset_left) (x : Fin two)
  : Id (Fin two) (u .fst (gset_fin2_transposition .map x)) (u .fst x)
  ≔ let f ≔ u .fst in
    let std ≔ standard_symmetric_gset two in
    let g : USym sigma_two_squared ≔ (sigma_two_swap, refl (shape sigma_two)) in
    calc
      f (gset_fin2_transposition .map x)
      = gset_usym_act sigma_two_squared function_gset g f (gset_usym_act sigma_two std sigma_two_swap x)
        by refl ((k ↦ k (gset_fin2_transposition .map x)) : (Fin two → Fin two) → Fin two)
          (inverse (Fin two → Fin two) (gset_usym_act sigma_two function_gset_left sigma_two_swap f) f (u .snd sigma_two_swap))
      = gset_usym_act sigma_two std (refl (shape sigma_two)) (f x) by function_gset_act g f x
      = f x by gset_act_unit sigma_two std (f x) ∎

{` Constant maps are fixed in X(-, 2): (g · c)(y) = c(g⁻¹ · y) = b. `}
def function_gset_left_constant_fixed (b : Fin two) : GSetFixedPoints sigma_two function_gset_left
  ≔ let B ≔ BG sigma_two .carrier in
    let sh ≔ shape sigma_two in
    let Y : B → Type ≔ z ↦ z .fst .fst in
    (_ ↦ b, g ↦ funext (Fin two) (_ ↦ Fin two) (gset_usym_act sigma_two function_gset_left g (_ ↦ b)) (_ ↦ b)
      (y ↦ concat (Fin two) (gset_usym_act sigma_two function_gset_left g (_ ↦ b) y)
        (transport B (_ ↦ Fin two) sh sh g b) b
        (transport_function_family B Y (_ ↦ Fin two) sh sh g (_ ↦ b) y)
        (transport_constant B (Fin two) sh sh g b)))

def gset_fin2_maps_equal (f f' : Fin two → Fin two)
  (h0 : Id (Fin two) (f gset_fin2_zero) (f' gset_fin2_zero)) (h1 : Id (Fin two) (f gset_fin2_one) (f' gset_fin2_one))
  : Id (Fin two → Fin two) f f'
  ≔ funext (Fin two) (_ ↦ Fin two) f f'
      [ inr. star. ↦ h0 | inl. (inr. star.) ↦ h1 | inl. (inl. e) ↦ match e [] ]

{` X(-, 2): X^hΣ_2 ≃ 2, by the value at 0 (the fixed points are the
   constant maps). `}
def function_gset_left_fixed_equiv : Equiv (GSetFixedPoints sigma_two function_gset_left) (Fin two)
  ≔ quasi_inverse_equiv (GSetFixedPoints sigma_two function_gset_left) (Fin two)
      (u ↦ u .fst gset_fin2_zero) function_gset_left_constant_fixed
      (u ↦ subtype_equal (Fin two → Fin two)
        (f ↦ (g : USym sigma_two) → Id (Fin two → Fin two) (gset_usym_act sigma_two function_gset_left g f) f)
        (gset_fixed_points_prop sigma_two function_gset_left)
        (function_gset_left_constant_fixed (u .fst gset_fin2_zero)) u
        (gset_fin2_maps_equal (_ ↦ u .fst gset_fin2_zero) (u .fst) (refl (u .fst gset_fin2_zero))
          (concat (Fin two) (u .fst gset_fin2_zero) (u .fst (gset_fin2_transposition .map gset_fin2_zero)) (u .fst gset_fin2_one)
            (inverse (Fin two) (u .fst (gset_fin2_transposition .map gset_fin2_zero)) (u .fst gset_fin2_zero)
              (function_gset_left_fixed_constant u gset_fin2_zero))
            (refl (u .fst) (transposition_left (Fin two) (fin_decidable_equality two) gset_fin2_zero gset_fin2_one)))))
      (b ↦ refl b)

def function_gset_left_invariant_equiv : Equiv (InvariantMaps sigma_two function_gset_left) (Fin two)
  ≔ compose_equiv (InvariantMaps sigma_two function_gset_left) (GSetFixedPoints sigma_two function_gset_left) (Fin two)
      (invariant_maps_fixed_equiv sigma_two function_gset_left) function_gset_left_fixed_equiv
