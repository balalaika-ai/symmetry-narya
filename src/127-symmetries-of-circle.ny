export "126-circle-equivalence-components"

def inverse_concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z)
  : Id (Id A z x) (inverse A x z (concat A x y z p q))
      (concat A z y x (inverse A y z q) (inverse A x y p))
  ≔ J A x
      (y p ↦ (z : A) → (q : Id A y z) →
        Id (Id A z x) (inverse A x z (concat A x y z p q))
          (concat A z y x (inverse A y z q) (inverse A x y p)))
      (z q ↦ calc
        inverse A x z (concat A x x z (refl x) q) = inverse A x z q
          by refl (inverse A x z) (concat_1p A x z q)
        = concat A z x x (inverse A x z q) (refl x)
          by concat_p1 A z x (inverse A x z q)
        = concat A z x x (inverse A x z q) (inverse A x x (refl x))
          by refl (concat A z x x (inverse A x z q)) (inverse_refl A x) ∎) y p z q

def circle_loops_commute (C : CircleSignature) (p q : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base))
      (concat (C .carrier) (C .base) (C .base) (C .base) p q)
      (concat (C .carrier) (C .base) (C .base) (C .base) q p)
  ≔ equivalence_injective (Id (C .carrier) (C .base) (C .base)) Int
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
      (concat (C .carrier) (C .base) (C .base) (C .base) p q)
      (concat (C .carrier) (C .base) (C .base) (C .base) q p) (calc
        circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q)
        = int_add (circle_winding C p) (circle_winding C q) by circle_winding_composition C p q
        = int_add (circle_winding C q) (circle_winding C p) by int_add_comm (circle_winding C p) (circle_winding C q)
        = circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) q p)
          by circle_winding_composition C q p ∎)

def loop_inversion_equiv (A : Type) (a : A) : Equiv (Id A a a) (Id A a a)
  ≔ quasi_inverse_equiv (Id A a a) (Id A a a) (inverse A a a) (inverse A a a)
      (inverse_inverse A a a) (inverse_inverse A a a)

def circle_reflection_equiv (C : CircleSignature) : BookEquiv (C .carrier) (C .carrier)
  ≔ circle_delooping_equiv C (C .carrier) (native_circle_connected C) (C .base)
      (loop_inversion_equiv (C .carrier) (C .base)) (inverse_refl (C .carrier) (C .base))
      (p q ↦ calc
        inverse (C .carrier) (C .base) (C .base) (concat (C .carrier) (C .base) (C .base) (C .base) p q)
        = concat (C .carrier) (C .base) (C .base) (C .base)
            (inverse (C .carrier) (C .base) (C .base) q) (inverse (C .carrier) (C .base) (C .base) p)
          by inverse_concat (C .carrier) (C .base) (C .base) (C .base) p q
        = concat (C .carrier) (C .base) (C .base) (C .base)
            (inverse (C .carrier) (C .base) (C .base) p) (inverse (C .carrier) (C .base) (C .base) q)
          by circle_loops_commute C (inverse (C .carrier) (C .base) (C .base) q)
            (inverse (C .carrier) (C .base) (C .base) p) ∎)

def CircleEquivalenceComponent (C : CircleSignature) (f : C .carrier → C .carrier) : Type
  ≔ Sum (Mere (Id (C .carrier → C .carrier) (identity (C .carrier)) f))
      (Mere (Id (C .carrier → C .carrier) (circle_reflection C) f))

def circle_equivalence_component_prop (C : CircleSignature) (f : C .carrier → C .carrier)
  : isProp (CircleEquivalenceComponent C f)
  ≔ disjoint_sum_prop (Mere (Id (C .carrier → C .carrier) (identity (C .carrier)) f))
      (Mere (Id (C .carrier → C .carrier) (circle_reflection C) f))
      (mere_isprop (Id (C .carrier → C .carrier) (identity (C .carrier)) f))
      (mere_isprop (Id (C .carrier → C .carrier) (circle_reflection C) f))
      (p q ↦ int_encode (pos. (suc. zero.)) (neg. zero.) (calc
        (pos. (suc. zero.) : Int) = circle_map_degree C (identity (C .carrier)) by circle_degree_identity C
        = circle_map_degree C f by circle_component_degree C (identity (C .carrier)) f p
        = circle_map_degree C (circle_reflection C) by circle_component_degree C (circle_reflection C) f q
        = (neg. zero. : Int) by circle_degree_reflection C ∎))

def circle_component_is_equivalence (C : CircleSignature) (f : C .carrier → C .carrier)
  (p : CircleEquivalenceComponent C f) : isEquiv (C .carrier) (C .carrier) f
  ≔ match p [
  | inl. p ↦ mere_rec (Id (C .carrier → C .carrier) (identity (C .carrier)) f)
      (isEquiv (C .carrier) (C .carrier) f) (isequiv_isprop (C .carrier) (C .carrier) f)
      (q ↦ transport (C .carrier → C .carrier) (isEquiv (C .carrier) (C .carrier))
        (identity (C .carrier)) f q (identity_equiv (C .carrier) .equiv)) p
  | inr. p ↦ mere_rec (Id (C .carrier → C .carrier) (circle_reflection C) f)
      (isEquiv (C .carrier) (C .carrier) f) (isequiv_isprop (C .carrier) (C .carrier) f)
      (q ↦ transport (C .carrier → C .carrier) (isEquiv (C .carrier) (C .carrier))
        (circle_reflection C) f q
        (native_equivalence (C .carrier) (C .carrier) (circle_reflection_equiv C) .equiv)) p ]

def sigma_sum_to (A : Type) (P Q : A → Type) (u : Σ A (a ↦ Sum (P a) (Q a)))
  : Sum (Σ A P) (Σ A Q)
  ≔ match u .snd [ inl. p ↦ inl. (u .fst, p) | inr. q ↦ inr. (u .fst, q) ]

def sigma_sum_from (A : Type) (P Q : A → Type) : Sum (Σ A P) (Σ A Q) → Σ A (a ↦ Sum (P a) (Q a))
  ≔ [ inl. u ↦ (u .fst, inl. (u .snd)) | inr. u ↦ (u .fst, inr. (u .snd)) ]

def sigma_sum_eta (A : Type) (P Q : A → Type) (a : A) (s : Sum (P a) (Q a))
  : Id (Σ A (x ↦ Sum (P x) (Q x)))
      (sigma_sum_from A P Q (sigma_sum_to A P Q (a, s))) (a, s)
  ≔ match s [ inl. p ↦ refl (a, inl. p) | inr. q ↦ refl (a, inr. q) ]

def sigma_sum_equiv (A : Type) (P Q : A → Type)
  : Equiv (Σ A (a ↦ Sum (P a) (Q a))) (Sum (Σ A P) (Σ A Q))
  ≔ quasi_inverse_equiv (Σ A (a ↦ Sum (P a) (Q a))) (Sum (Σ A P) (Σ A Q))
      (sigma_sum_to A P Q) (sigma_sum_from A P Q)
      (u ↦ sigma_sum_eta A P Q (u .fst) (u .snd))
      [ inl. u ↦ refl (inl. u : Sum (Σ A P) (Σ A Q)) | inr. u ↦ refl (inr. u : Sum (Σ A P) (Σ A Q)) ]

{` The unnumbered conclusion immediately after the two exercises: the
   full type of self-equivalences is equivalent to two copies of the circle. `}
def circle_symmetries_two_circles (C : CircleSignature)
  : Equiv (Equiv (C .carrier) (C .carrier)) (Sum (C .carrier) (C .carrier))
  ≔ let F ≔ C .carrier → C .carrier in
    let P : F → Type ≔ f ↦ Mere (Id F (identity (C .carrier)) f) in
    let Q : F → Type ≔ f ↦ Mere (Id F (circle_reflection C) f) in
    compose_equiv (Equiv (C .carrier) (C .carrier)) (Σ F (CircleEquivalenceComponent C)) (Sum (C .carrier) (C .carrier))
      (compose_equiv (Equiv (C .carrier) (C .carrier)) (Σ F (isEquiv (C .carrier) (C .carrier)))
        (Σ F (CircleEquivalenceComponent C)) (equiv_sigma_equiv (C .carrier) (C .carrier))
        (family_equiv F (isEquiv (C .carrier) (C .carrier)) (CircleEquivalenceComponent C)
          (f ↦ iff_equiv (isEquiv (C .carrier) (C .carrier) f) (CircleEquivalenceComponent C f)
            (isequiv_isprop (C .carrier) (C .carrier) f) (circle_equivalence_component_prop C f)
            (h ↦ circle_equivalence_two_components C (f, h)) (circle_component_is_equivalence C f))))
      (compose_equiv (Σ F (CircleEquivalenceComponent C)) (Sum (Σ F P) (Σ F Q)) (Sum (C .carrier) (C .carrier))
        (sigma_sum_equiv F P Q)
        (sum_equiv (Σ F P) (Σ F Q) (C .carrier) (C .carrier)
          (canonical_inverse_equiv (C .carrier) (Σ F P) (circle_map_component_equiv C (identity (C .carrier))))
          (canonical_inverse_equiv (C .carrier) (Σ F Q) (circle_map_component_equiv C (circle_reflection C)))))

def circle_type_symmetries_two_circles (C : CircleSignature)
  : Equiv (Id Type (C .carrier) (C .carrier)) (Sum (C .carrier) (C .carrier))
  ≔ compose_equiv (Id Type (C .carrier) (C .carrier)) (Equiv (C .carrier) (C .carrier))
      (Sum (C .carrier) (C .carrier)) (univalence_equiv (C .carrier) (C .carrier)) (circle_symmetries_two_circles C)
