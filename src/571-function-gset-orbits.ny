import "565-standard-symmetric-gsets"
import "570-orbit-classifiers"
import "583-fixed-point-subgroups"
import "178-binomial-subsets"
import "120-two-boolean-circle-coverings"

{` Chapter 5, xca:Gset-A->B, the sets of orbits. G = Σ_2 × Σ_2 acts on
   X(A, B) = (A → B) by g · f = τ ∘ f ∘ σ⁻¹ (module 565, function_gset_act).
   - X/G ≃ Bool: the orbits are the constant maps and the bijections
     (classifier: "f is constant", decided uniformly over all (A, B) since
     2-element sets are finite with decidable equality);
   - the constant G-set 2 × 2: X/G ≃ 2 × 2 (trivial action);
   - X(2, -) (τ ∘ f): X/Σ_2 ≃ Bool (constant maps / bijections);
   - X(-, 2) (f ∘ σ⁻¹): X/Σ_2 ≃ Fin 3 (constant 0, constant 1, bijections).
   The invariant maps are in module 565. `}

def FunctionIsConstant (A B : Type) (f : A → B) : Type ≔ (a a' : A) → Id B (f a) (f a')

def function_is_constant_decidable (A B : Type) (hA : IsFinite A) (hB : DecidableEquality B) (sB : isSet B) (f : A → B)
  : Decidable (FunctionIsConstant A B f)
  ≔ finite_quantifiers A hA (a ↦ (a' : A) → Id B (f a) (f a'))
      (a ↦ pi_prop A (a' ↦ Id B (f a) (f a')) (a' ↦ sB (f a) (f a')))
      (a ↦ finite_quantifiers A hA (a' ↦ Id B (f a) (f a')) (a' ↦ sB (f a) (f a')) (a' ↦ hB (f a) (f a')) .fst)
      .fst

def fn_orbits_bool_false (X : Type) (d : Decidable X) (n : Not X) : Id Bool (decision_bool X d) false.
  ≔ match d [ inl. x ↦ absurd (Id Bool true. false.) (n x) | inr. _ ↦ refl (false. : Bool) ]

{` Orbit relations from paths and from a given group element. `}
def fn_orbits_rel_path (G : Group) (X : GSet G) (x y : gset_underlying G X) (p : Id (gset_underlying G X) x y)
  : OrbitRelation G X x y
  ≔ mere (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) y))
      (usym_unit G, concat (gset_underlying G X) (gset_usym_act G X (usym_unit G) x) x y (gset_act_unit G X x) p)

def fn_orbits_rel_act (G : Group) (X : GSet G) (g : USym G) (x y : gset_underlying G X)
  (p : Id (gset_underlying G X) (gset_usym_act G X g x) y) : OrbitRelation G X x y
  ≔ mere (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) y)) (g, p)

{` The maps Fin 2 → Fin 2 used as representatives. `}
def fn_const_zero : Fin two → Fin two ≔ _ ↦ gset_fin2_zero

def fn_const_one : Fin two → Fin two ≔ _ ↦ gset_fin2_one

def fn_identity : Fin two → Fin two ≔ x ↦ x

def fn_const_zero_constant : FunctionIsConstant (Fin two) (Fin two) fn_const_zero ≔ _ _ ↦ refl gset_fin2_zero

def fn_const_one_constant : FunctionIsConstant (Fin two) (Fin two) fn_const_one ≔ _ _ ↦ refl gset_fin2_one

def fn_identity_not_constant (h : FunctionIsConstant (Fin two) (Fin two) fn_identity) : Empty
  ≔ gset_fin2_zero_not_one (h gset_fin2_zero gset_fin2_one)

def fn_swap_not_constant (f : Fin two → Fin two) (h0 : Id (Fin two) (f gset_fin2_zero) gset_fin2_one)
  (h1 : Id (Fin two) (f gset_fin2_one) gset_fin2_zero) (h : FunctionIsConstant (Fin two) (Fin two) f) : Empty
  ≔ gset_fin2_zero_not_one
      (concat (Fin two) gset_fin2_zero (f gset_fin2_one) gset_fin2_one (inverse (Fin two) (f gset_fin2_one) gset_fin2_zero h1)
        (concat (Fin two) (f gset_fin2_one) (f gset_fin2_zero) gset_fin2_one (h gset_fin2_one gset_fin2_zero) h0))

def fn_const_from_values (f : Fin two → Fin two) (b : Fin two) (h0 : Id (Fin two) (f gset_fin2_zero) b)
  (h1 : Id (Fin two) (f gset_fin2_one) b) : FunctionIsConstant (Fin two) (Fin two) f
  ≔ let v : (a : Fin two) → Id (Fin two) (f a) b ≔ [ inr. star. ↦ h0 | inl. (inr. star.) ↦ h1 | inl. (inl. e) ↦ match e [] ] in
    a a' ↦ concat (Fin two) (f a) b (f a') (v a) (inverse (Fin two) (f a') b (v a'))

def fn_values_path (f f' : Fin two → Fin two) (a b : Fin two)
  (h0 : Id (Fin two) (f gset_fin2_zero) a) (h1 : Id (Fin two) (f gset_fin2_one) b)
  (k0 : Id (Fin two) (f' gset_fin2_zero) a) (k1 : Id (Fin two) (f' gset_fin2_one) b) : Id (Fin two → Fin two) f f'
  ≔ gset_fin2_maps_equal f f'
      (concat (Fin two) (f gset_fin2_zero) a (f' gset_fin2_zero) h0 (inverse (Fin two) (f' gset_fin2_zero) a k0))
      (concat (Fin two) (f gset_fin2_one) b (f' gset_fin2_one) h1 (inverse (Fin two) (f' gset_fin2_one) b k1))

def fn_tau_zero : Id (Fin two) (gset_fin2_transposition .map gset_fin2_zero) gset_fin2_one
  ≔ transposition_left (Fin two) (fin_decidable_equality two) gset_fin2_zero gset_fin2_one

def fn_tau_one : Id (Fin two) (gset_fin2_transposition .map gset_fin2_one) gset_fin2_zero
  ≔ transposition_right (Fin two) (fin_decidable_equality two) gset_fin2_zero gset_fin2_one

{` The action of g = (e, τ): (g · f)(x) = τ(f(x)). `}
def fn_swap_right : USym sigma_two_squared ≔ (refl (shape sigma_two), sigma_two_swap)

def fn_swap_right_act (f : Fin two → Fin two) (x : Fin two)
  : Id (Fin two) (gset_usym_act sigma_two_squared function_gset fn_swap_right f x) (gset_fin2_transposition .map (f x))
  ≔ let std ≔ standard_symmetric_gset two in
    let gf ≔ gset_usym_act sigma_two_squared function_gset fn_swap_right f in
    concat (Fin two) (gf x) (gf (gset_usym_act sigma_two std (refl (shape sigma_two)) x)) (gset_fin2_transposition .map (f x))
      (inverse (Fin two) (gf (gset_usym_act sigma_two std (refl (shape sigma_two)) x)) (gf x)
        (refl gf (gset_act_unit sigma_two std x)))
      (function_gset_act fn_swap_right f x)

{` The action of g = (τ, e): (g · f)(τ x) = f(x). `}
def fn_swap_left : USym sigma_two_squared ≔ (sigma_two_swap, refl (shape sigma_two))

def fn_swap_left_act (f : Fin two → Fin two) (x : Fin two)
  : Id (Fin two) (gset_usym_act sigma_two_squared function_gset fn_swap_left f (gset_fin2_transposition .map x)) (f x)
  ≔ let std ≔ standard_symmetric_gset two in
    concat (Fin two) (gset_usym_act sigma_two_squared function_gset fn_swap_left f (gset_fin2_transposition .map x))
      (gset_usym_act sigma_two std (refl (shape sigma_two)) (f x)) (f x)
      (function_gset_act fn_swap_left f x) (gset_act_unit sigma_two std (f x))

{` ---- X(A, B) = (A → B) under Σ_2 × Σ_2. ---- `}

def function_gset_classifier : GSetHom sigma_two_squared function_gset (gset_trivial sigma_two_squared boolean_set)
  ≔ ab f ↦
      decision_bool (FunctionIsConstant (ab .fst .fst .fst) (ab .snd .fst .fst) f)
        (function_is_constant_decidable (ab .fst .fst .fst) (ab .snd .fst .fst)
          (finite_sets_at_finite two (ab .fst))
          (finite_decidable_equality (ab .snd .fst .fst) (finite_sets_at_finite two (ab .snd)))
          (ab .snd .fst .snd) f)

def function_gset_rep : Bool → Fin two → Fin two ≔ [ true. ↦ fn_const_zero | false. ↦ fn_identity ]

def function_gset_classifier_at (f : Fin two → Fin two)
  : Id Bool (function_gset_classifier (shape sigma_two_squared) f)
      (decision_bool (FunctionIsConstant (Fin two) (Fin two) f)
        (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
          (finite_decidable_equality (Fin two) (finite_sets_at_finite two (shape sigma_two))) (fin_set two) f))
  ≔ refl (function_gset_classifier (shape sigma_two_squared) f)

def function_gset_classifier_constant (f : Fin two → Fin two) (h : FunctionIsConstant (Fin two) (Fin two) f)
  : Id Bool (function_gset_classifier (shape sigma_two_squared) f) true.
  ≔ decision_bool_true (FunctionIsConstant (Fin two) (Fin two) f)
      (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
        (finite_decidable_equality (Fin two) (finite_sets_at_finite two (shape sigma_two))) (fin_set two) f) h

def function_gset_classifier_nonconstant (f : Fin two → Fin two) (n : Not (FunctionIsConstant (Fin two) (Fin two) f))
  : Id Bool (function_gset_classifier (shape sigma_two_squared) f) false.
  ≔ fn_orbits_bool_false (FunctionIsConstant (Fin two) (Fin two) f)
      (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
        (finite_decidable_equality (Fin two) (finite_sets_at_finite two (shape sigma_two))) (fin_set two) f) n

def function_gset_rep_class (b : Bool)
  : Id Bool (function_gset_classifier (shape sigma_two_squared) (function_gset_rep b)) b
  ≔ match b [
  | true. ↦ function_gset_classifier_constant fn_const_zero fn_const_zero_constant
  | false. ↦ function_gset_classifier_nonconstant fn_identity fn_identity_not_constant ]

{` Every f is related to the representative of its class. `}
def function_gset_rel_rep_at (f : Fin two → Fin two) (b : Bool)
  (hb : Id Bool (function_gset_classifier (shape sigma_two_squared) f) b)
  (r : OrbitRelation sigma_two_squared function_gset f (function_gset_rep b))
  : OrbitRelation sigma_two_squared function_gset f (function_gset_rep (function_gset_classifier (shape sigma_two_squared) f))
  ≔ transport Bool (b' ↦ OrbitRelation sigma_two_squared function_gset f (function_gset_rep b'))
      b (function_gset_classifier (shape sigma_two_squared) f)
      (inverse Bool (function_gset_classifier (shape sigma_two_squared) f) b hb) r

def function_gset_rel_rep_cases (f : Fin two → Fin two) (a b : Fin two)
  (h0 : Id (Fin two) (f gset_fin2_zero) a) (h1 : Id (Fin two) (f gset_fin2_one) b)
  : OrbitRelation sigma_two_squared function_gset f (function_gset_rep (function_gset_classifier (shape sigma_two_squared) f))
  ≔ let G ≔ sigma_two_squared in
    let X ≔ function_gset in
    let F2 ≔ Fin two → Fin two in
    let z ≔ gset_fin2_zero in
    let o ≔ gset_fin2_one in
    let gf ≔ gset_usym_act G X fn_swap_right f in
    match a [
    | inr. star. ↦ match b [
      | inr. star. ↦ function_gset_rel_rep_at f true. (function_gset_classifier_constant f (fn_const_from_values f z h0 h1))
          (fn_orbits_rel_path G X f fn_const_zero (fn_values_path f fn_const_zero z z h0 h1 (refl z) (refl z)))
      | inl. (inr. star.) ↦ function_gset_rel_rep_at f false.
          (function_gset_classifier_nonconstant f (h ↦ gset_fin2_zero_not_one
            (concat (Fin two) z (f z) o (inverse (Fin two) (f z) z h0) (concat (Fin two) (f z) (f o) o (h z o) h1))))
          (fn_orbits_rel_path G X f fn_identity (fn_values_path f fn_identity z o h0 h1 (refl z) (refl o)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inr. star.) ↦ match b [
      | inr. star. ↦ function_gset_rel_rep_at f false. (function_gset_classifier_nonconstant f (fn_swap_not_constant f h0 h1))
          (fn_orbits_rel_act G X fn_swap_right f fn_identity
            (fn_values_path gf fn_identity z o
              (concat (Fin two) (gf z) (gset_fin2_transposition .map (f z)) z (fn_swap_right_act f z)
                (concat (Fin two) (gset_fin2_transposition .map (f z)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h0) fn_tau_one))
              (concat (Fin two) (gf o) (gset_fin2_transposition .map (f o)) o (fn_swap_right_act f o)
                (concat (Fin two) (gset_fin2_transposition .map (f o)) (gset_fin2_transposition .map z) o
                  (refl (gset_fin2_transposition .map) h1) fn_tau_zero))
              (refl z) (refl o)))
      | inl. (inr. star.) ↦ function_gset_rel_rep_at f true. (function_gset_classifier_constant f (fn_const_from_values f o h0 h1))
          (fn_orbits_rel_act G X fn_swap_right f fn_const_zero
            (fn_values_path gf fn_const_zero z z
              (concat (Fin two) (gf z) (gset_fin2_transposition .map (f z)) z (fn_swap_right_act f z)
                (concat (Fin two) (gset_fin2_transposition .map (f z)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h0) fn_tau_one))
              (concat (Fin two) (gf o) (gset_fin2_transposition .map (f o)) z (fn_swap_right_act f o)
                (concat (Fin two) (gset_fin2_transposition .map (f o)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h1) fn_tau_one))
              (refl z) (refl z)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inl. e) ↦ match e [] ]

{` xca:Gset-A->B: X/G ≃ Bool, [f] ↦ "f is constant"; the two orbits are
   the constant maps and the bijections. `}
def function_gset_orbits_equiv : Equiv (Orbits sigma_two_squared function_gset) Bool
  ≔ orbits_classifier_equiv sigma_two_squared function_gset boolean_set function_gset_classifier function_gset_rep
      function_gset_rep_class (f ↦ function_gset_rel_rep_cases f (f gset_fin2_zero) (f gset_fin2_one)
        (refl (f gset_fin2_zero)) (refl (f gset_fin2_one)))

{` ---- The constant G-set 2 × 2: X/G ≃ 2 × 2. ---- `}

def constant_square_orbits_equiv
  : Equiv (Orbits sigma_two_squared constant_square_gset) (Product (Fin two) (Fin two))
  ≔ orbits_classifier_equiv sigma_two_squared constant_square_gset gset_fin2_squared_set (_ x ↦ x) (x ↦ x)
      (x ↦ refl x) (x ↦ fn_orbits_rel_path sigma_two_squared constant_square_gset x x (refl x))

{` ---- X(2, -): B ↦ (2 → B) under Σ_2, g · f = τ ∘ f. X/Σ_2 ≃ Bool. ---- `}

def function_gset_right_classifier : GSetHom sigma_two function_gset_right (gset_trivial sigma_two boolean_set)
  ≔ z f ↦
      decision_bool (FunctionIsConstant (Fin two) (z .fst .fst) f)
        (function_is_constant_decidable (Fin two) (z .fst .fst) (finite_sets_at_finite two (shape sigma_two))
          (finite_decidable_equality (z .fst .fst) (finite_sets_at_finite two z)) (z .fst .snd) f)

def function_gset_right_classifier_base (f : Fin two → Fin two)
  : Id Bool (function_gset_right_classifier (shape sigma_two) f) (function_gset_classifier (shape sigma_two_squared) f)
  ≔ refl (function_gset_classifier (shape sigma_two_squared) f)

def function_gset_right_rel_rep_cases (f : Fin two → Fin two) (a b : Fin two)
  (h0 : Id (Fin two) (f gset_fin2_zero) a) (h1 : Id (Fin two) (f gset_fin2_one) b)
  : OrbitRelation sigma_two function_gset_right f
      (function_gset_rep (function_gset_right_classifier (shape sigma_two) f))
  ≔ let G ≔ sigma_two in
    let X ≔ function_gset_right in
    let z ≔ gset_fin2_zero in
    let o ≔ gset_fin2_one in
    let gf ≔ gset_usym_act sigma_two_squared function_gset fn_swap_right f in
    match a [
    | inr. star. ↦ match b [
      | inr. star. ↦ transport Bool (b' ↦ OrbitRelation G X f (function_gset_rep b')) true.
          (function_gset_right_classifier (shape sigma_two) f)
          (inverse Bool (function_gset_classifier (shape sigma_two_squared) f) true.
            (function_gset_classifier_constant f (fn_const_from_values f z h0 h1)))
          (fn_orbits_rel_path G X f fn_const_zero (fn_values_path f fn_const_zero z z h0 h1 (refl z) (refl z)))
      | inl. (inr. star.) ↦ transport Bool (b' ↦ OrbitRelation G X f (function_gset_rep b')) false.
          (function_gset_right_classifier (shape sigma_two) f)
          (inverse Bool (function_gset_classifier (shape sigma_two_squared) f) false.
            (function_gset_classifier_nonconstant f (h ↦ gset_fin2_zero_not_one
              (concat (Fin two) z (f z) o (inverse (Fin two) (f z) z h0) (concat (Fin two) (f z) (f o) o (h z o) h1)))))
          (fn_orbits_rel_path G X f fn_identity (fn_values_path f fn_identity z o h0 h1 (refl z) (refl o)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inr. star.) ↦ match b [
      | inr. star. ↦ transport Bool (b' ↦ OrbitRelation G X f (function_gset_rep b')) false.
          (function_gset_right_classifier (shape sigma_two) f)
          (inverse Bool (function_gset_classifier (shape sigma_two_squared) f) false.
            (function_gset_classifier_nonconstant f (fn_swap_not_constant f h0 h1)))
          (fn_orbits_rel_act G X sigma_two_swap f fn_identity
            (fn_values_path gf fn_identity z o
              (concat (Fin two) (gf z) (gset_fin2_transposition .map (f z)) z (fn_swap_right_act f z)
                (concat (Fin two) (gset_fin2_transposition .map (f z)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h0) fn_tau_one))
              (concat (Fin two) (gf o) (gset_fin2_transposition .map (f o)) o (fn_swap_right_act f o)
                (concat (Fin two) (gset_fin2_transposition .map (f o)) (gset_fin2_transposition .map z) o
                  (refl (gset_fin2_transposition .map) h1) fn_tau_zero))
              (refl z) (refl o)))
      | inl. (inr. star.) ↦ transport Bool (b' ↦ OrbitRelation G X f (function_gset_rep b')) true.
          (function_gset_right_classifier (shape sigma_two) f)
          (inverse Bool (function_gset_classifier (shape sigma_two_squared) f) true.
            (function_gset_classifier_constant f (fn_const_from_values f o h0 h1)))
          (fn_orbits_rel_act G X sigma_two_swap f fn_const_zero
            (fn_values_path gf fn_const_zero z z
              (concat (Fin two) (gf z) (gset_fin2_transposition .map (f z)) z (fn_swap_right_act f z)
                (concat (Fin two) (gset_fin2_transposition .map (f z)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h0) fn_tau_one))
              (concat (Fin two) (gf o) (gset_fin2_transposition .map (f o)) z (fn_swap_right_act f o)
                (concat (Fin two) (gset_fin2_transposition .map (f o)) (gset_fin2_transposition .map o) z
                  (refl (gset_fin2_transposition .map) h1) fn_tau_one))
              (refl z) (refl z)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inl. e) ↦ match e [] ]

def function_gset_right_orbits_equiv : Equiv (Orbits sigma_two function_gset_right) Bool
  ≔ orbits_classifier_equiv sigma_two function_gset_right boolean_set function_gset_right_classifier function_gset_rep
      function_gset_rep_class (f ↦ function_gset_right_rel_rep_cases f (f gset_fin2_zero) (f gset_fin2_one)
        (refl (f gset_fin2_zero)) (refl (f gset_fin2_one)))

{` ---- X(-, 2): A ↦ (A → 2) under Σ_2, g · f = f ∘ σ⁻¹. X/Σ_2 ≃ Fin 3:
   constant 0, constant 1, bijections. ---- `}

def fn_three_class (P Q : Type) (dp : Decidable P) (dq : Decidable Q) : Fin three
  ≔ match dp [ inl. _ ↦ match dq [ inl. _ ↦ fin3_zero | inr. _ ↦ fin3_one ] | inr. _ ↦ fin3_two ]

def fn_three_class_zero (P Q : Type) (dp : Decidable P) (dq : Decidable Q) (p : P) (q : Q)
  : Id (Fin three) (fn_three_class P Q dp dq) fin3_zero
  ≔ match dp [
  | inl. _ ↦ match dq [ inl. _ ↦ refl fin3_zero | inr. n ↦ absurd (Id (Fin three) fin3_one fin3_zero) (n q) ]
  | inr. n ↦ absurd (Id (Fin three) fin3_two fin3_zero) (n p) ]

def fn_three_class_one (P Q : Type) (dp : Decidable P) (dq : Decidable Q) (p : P) (nq : Not Q)
  : Id (Fin three) (fn_three_class P Q dp dq) fin3_one
  ≔ match dp [
  | inl. _ ↦ match dq [ inl. q ↦ absurd (Id (Fin three) fin3_zero fin3_one) (nq q) | inr. _ ↦ refl fin3_one ]
  | inr. n ↦ absurd (Id (Fin three) fin3_two fin3_one) (n p) ]

def fn_three_class_two (P Q : Type) (dp : Decidable P) (dq : Decidable Q) (np : Not P)
  : Id (Fin three) (fn_three_class P Q dp dq) fin3_two
  ≔ match dp [ inl. p ↦ absurd (Id (Fin three) (fn_three_class P Q (inl. p) dq) fin3_two) (np p) | inr. _ ↦ refl fin3_two ]

def FunctionHitsZero (A : Type) (f : A → Fin two) : Type ≔ Mere (Σ A (a ↦ Id (Fin two) (f a) gset_fin2_zero))

def function_hits_zero_decidable (A : Type) (hA : IsFinite A) (f : A → Fin two) : Decidable (FunctionHitsZero A f)
  ≔ finite_quantifiers A hA (a ↦ Id (Fin two) (f a) gset_fin2_zero) (a ↦ fin_set two (f a) gset_fin2_zero)
      (a ↦ fin_decidable_equality two (f a) gset_fin2_zero) .snd

def function_gset_left_classifier : GSetHom sigma_two function_gset_left (gset_trivial sigma_two (standard_set three))
  ≔ z f ↦
      fn_three_class (FunctionIsConstant (z .fst .fst) (Fin two) f) (FunctionHitsZero (z .fst .fst) f)
        (function_is_constant_decidable (z .fst .fst) (Fin two) (finite_sets_at_finite two z) (fin_decidable_equality two)
          (fin_set two) f)
        (function_hits_zero_decidable (z .fst .fst) (finite_sets_at_finite two z) f)

def function_gset_left_rep : Fin three → Fin two → Fin two
  ≔ [ inr. _ ↦ fn_const_zero | inl. (inr. _) ↦ fn_const_one | inl. (inl. (inr. _)) ↦ fn_identity
    | inl. (inl. (inl. e)) ↦ match e [] ]

def fn_left_class_zero (f : Fin two → Fin two) (h : FunctionIsConstant (Fin two) (Fin two) f) (q : FunctionHitsZero (Fin two) f)
  : Id (Fin three) (function_gset_left_classifier (shape sigma_two) f) fin3_zero
  ≔ fn_three_class_zero (FunctionIsConstant (Fin two) (Fin two) f) (FunctionHitsZero (Fin two) f)
      (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
        (fin_decidable_equality two) (fin_set two) f)
      (function_hits_zero_decidable (Fin two) (finite_sets_at_finite two (shape sigma_two)) f) h q

def fn_left_class_one (f : Fin two → Fin two) (h : FunctionIsConstant (Fin two) (Fin two) f) (nq : Not (FunctionHitsZero (Fin two) f))
  : Id (Fin three) (function_gset_left_classifier (shape sigma_two) f) fin3_one
  ≔ fn_three_class_one (FunctionIsConstant (Fin two) (Fin two) f) (FunctionHitsZero (Fin two) f)
      (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
        (fin_decidable_equality two) (fin_set two) f)
      (function_hits_zero_decidable (Fin two) (finite_sets_at_finite two (shape sigma_two)) f) h nq

def fn_left_class_two (f : Fin two → Fin two) (n : Not (FunctionIsConstant (Fin two) (Fin two) f))
  : Id (Fin three) (function_gset_left_classifier (shape sigma_two) f) fin3_two
  ≔ fn_three_class_two (FunctionIsConstant (Fin two) (Fin two) f) (FunctionHitsZero (Fin two) f)
      (function_is_constant_decidable (Fin two) (Fin two) (finite_sets_at_finite two (shape sigma_two))
        (fin_decidable_equality two) (fin_set two) f)
      (function_hits_zero_decidable (Fin two) (finite_sets_at_finite two (shape sigma_two)) f) n

{` A map with f(0) = f(1) = 1 does not hit 0. `}
def fn_misses_zero (f : Fin two → Fin two) (h0 : Id (Fin two) (f gset_fin2_zero) gset_fin2_one)
  (h1 : Id (Fin two) (f gset_fin2_one) gset_fin2_one) (q : FunctionHitsZero (Fin two) f) : Empty
  ≔ mere_rec (Σ (Fin two) (a ↦ Id (Fin two) (f a) gset_fin2_zero)) Empty (x y ↦ match x [])
      (t ↦ gset_fin2_zero_not_one
        (concat (Fin two) gset_fin2_zero (f (t .fst)) gset_fin2_one (inverse (Fin two) (f (t .fst)) gset_fin2_zero (t .snd))
          (concat (Fin two) (f (t .fst)) (f gset_fin2_zero) gset_fin2_one
            (fn_const_from_values f gset_fin2_one h0 h1 (t .fst) gset_fin2_zero) h0)))
      q

def function_gset_left_rep_class (k : Fin three)
  : Id (Fin three) (function_gset_left_classifier (shape sigma_two) (function_gset_left_rep k)) k
  ≔ match k [
  | inr. star. ↦ fn_left_class_zero fn_const_zero fn_const_zero_constant
      (mere (Σ (Fin two) (a ↦ Id (Fin two) (fn_const_zero a) gset_fin2_zero)) (gset_fin2_zero, refl gset_fin2_zero))
  | inl. (inr. star.) ↦ fn_left_class_one fn_const_one fn_const_one_constant
      (fn_misses_zero fn_const_one (refl gset_fin2_one) (refl gset_fin2_one))
  | inl. (inl. (inr. star.)) ↦ fn_left_class_two fn_identity fn_identity_not_constant
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fn_left_rel_rep_at (f : Fin two → Fin two) (k : Fin three)
  (hk : Id (Fin three) (function_gset_left_classifier (shape sigma_two) f) k)
  (r : OrbitRelation sigma_two function_gset_left f (function_gset_left_rep k))
  : OrbitRelation sigma_two function_gset_left f (function_gset_left_rep (function_gset_left_classifier (shape sigma_two) f))
  ≔ transport (Fin three) (k' ↦ OrbitRelation sigma_two function_gset_left f (function_gset_left_rep k'))
      k (function_gset_left_classifier (shape sigma_two) f)
      (inverse (Fin three) (function_gset_left_classifier (shape sigma_two) f) k hk) r

def function_gset_left_rel_rep_cases (f : Fin two → Fin two) (a b : Fin two)
  (h0 : Id (Fin two) (f gset_fin2_zero) a) (h1 : Id (Fin two) (f gset_fin2_one) b)
  : OrbitRelation sigma_two function_gset_left f
      (function_gset_left_rep (function_gset_left_classifier (shape sigma_two) f))
  ≔ let G ≔ sigma_two in
    let X ≔ function_gset_left in
    let z ≔ gset_fin2_zero in
    let o ≔ gset_fin2_one in
    let gf ≔ gset_usym_act sigma_two_squared function_gset fn_swap_left f in
    let τ ≔ gset_fin2_transposition .map in
    match a [
    | inr. star. ↦ match b [
      | inr. star. ↦ fn_left_rel_rep_at f fin3_zero
          (fn_left_class_zero f (fn_const_from_values f z h0 h1)
            (mere (Σ (Fin two) (a' ↦ Id (Fin two) (f a') z)) (z, h0)))
          (fn_orbits_rel_path G X f fn_const_zero (fn_values_path f fn_const_zero z z h0 h1 (refl z) (refl z)))
      | inl. (inr. star.) ↦ fn_left_rel_rep_at f fin3_two
          (fn_left_class_two f (h ↦ gset_fin2_zero_not_one
            (concat (Fin two) z (f z) o (inverse (Fin two) (f z) z h0) (concat (Fin two) (f z) (f o) o (h z o) h1))))
          (fn_orbits_rel_path G X f fn_identity (fn_values_path f fn_identity z o h0 h1 (refl z) (refl o)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inr. star.) ↦ match b [
      | inr. star. ↦ fn_left_rel_rep_at f fin3_two (fn_left_class_two f (fn_swap_not_constant f h0 h1))
          (fn_orbits_rel_act G X sigma_two_swap f fn_identity
            (fn_values_path gf fn_identity z o
              (concat (Fin two) (gf z) (gf (τ o)) z (refl gf (inverse (Fin two) (τ o) z fn_tau_one))
                (concat (Fin two) (gf (τ o)) (f o) z (fn_swap_left_act f o) h1))
              (concat (Fin two) (gf o) (gf (τ z)) o (refl gf (inverse (Fin two) (τ z) o fn_tau_zero))
                (concat (Fin two) (gf (τ z)) (f z) o (fn_swap_left_act f z) h0))
              (refl z) (refl o)))
      | inl. (inr. star.) ↦ fn_left_rel_rep_at f fin3_one
          (fn_left_class_one f (fn_const_from_values f o h0 h1) (fn_misses_zero f h0 h1))
          (fn_orbits_rel_path G X f fn_const_one (fn_values_path f fn_const_one o o h0 h1 (refl o) (refl o)))
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inl. e) ↦ match e [] ]

def function_gset_left_orbits_equiv : Equiv (Orbits sigma_two function_gset_left) (Fin three)
  ≔ orbits_classifier_equiv sigma_two function_gset_left (standard_set three) function_gset_left_classifier
      function_gset_left_rep function_gset_left_rep_class
      (f ↦ function_gset_left_rel_rep_cases f (f gset_fin2_zero) (f gset_fin2_one)
        (refl (f gset_fin2_zero)) (refl (f gset_fin2_one)))
