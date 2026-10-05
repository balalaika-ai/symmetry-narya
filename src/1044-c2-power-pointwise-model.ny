export "1042-c2-power-abstract-models"
export "430-pointwise-abstract-groups"

{` Chapter 10, the remark at fingp.tex 105 (|C_2^n| = 2^n is
   dwarfed by the number of subgroups), supporting material:
   - c2pow_vec_iso: abstr(C_2^n) ≅ (Fin n → Bool) with pointwise xor
     (pointwise_abstract_group of module 430), for every n;
   - finite_injection_card_le: an injection between finite types does not
     decrease cardinality. `}

def c2vec_abstract (n : Nat) : AbstractGroup ≔ pointwise_abstract_group c2abs_bool (Fin n)

def c2vec_postcompose_equiv (X A B : Type) (e : Equiv A B) : Equiv (X → A) (X → B)
  ≔ quasi_inverse_equiv (X → A) (X → B) (f x ↦ e .map (f x)) (g x ↦ equiv_inverse_map A B e (g x))
      (f ↦ funext X (_ ↦ A) (x ↦ equiv_inverse_map A B e (e .map (f x))) f (x ↦ equiv_retraction A B e (f x)))
      (g ↦ funext X (_ ↦ B) (x ↦ e .map (equiv_inverse_map A B e (g x))) g (x ↦ equiv_counit A B e (g x)))

def c2pow_vec_equiv (n : Nat) : Equiv (USym (c2pow_group n)) (Fin n → Bool)
  ≔ let C ≔ cyclic_group two in
    compose_equiv (USym (c2pow_group n)) (Fin n → USym C) (Fin n → Bool)
      (power_group_usym_equiv (Fin n) (fin_is_finite n) C)
      (c2vec_postcompose_equiv (Fin n) (USym C) Bool (c2_iso .fst))

def c2pow_component (n : Nat) (s : USym (c2pow_group n)) (i : Fin n) : USym (cyclic_group two)
  ≔ happly (Fin n) (_ ↦ BG (cyclic_group two) .carrier) (_ ↦ shape (cyclic_group two)) (_ ↦ shape (cyclic_group two)) s i

def c2pow_component_mul (n : Nat) (s t : USym (c2pow_group n)) (i : Fin n)
  : Id Bool (c2_iso .fst .map (c2pow_component n (usym_mul (c2pow_group n) s t) i))
      (bool_xor (c2_iso .fst .map (c2pow_component n s i)) (c2_iso .fst .map (c2pow_component n t i)))
  ≔ let C ≔ cyclic_group two in
    let o : Fin n → BG C .carrier ≔ _ ↦ shape C in
    concat Bool (c2_iso .fst .map (c2pow_component n (usym_mul (c2pow_group n) s t) i))
      (c2_iso .fst .map (usym_mul C (c2pow_component n s i) (c2pow_component n t i)))
      (bool_xor (c2_iso .fst .map (c2pow_component n s i)) (c2_iso .fst .map (c2pow_component n t i)))
      (map_path (USym C) Bool (c2_iso .fst .map)
        (c2pow_component n (usym_mul (c2pow_group n) s t) i)
        (usym_mul C (c2pow_component n s i) (c2pow_component n t i))
        (c2pow_happly_concat (Fin n) (BG C .carrier) o o o t s i))
      (c2_iso .snd (c2pow_component n s i) (c2pow_component n t i))

{` abstr(C_2^n) ≅ (Fin n → Bool, pointwise xor). `}
def c2pow_vec_iso (n : Nat) : AbstractIso (abstr (c2pow_group n)) (c2vec_abstract n)
  ≔ (c2pow_vec_equiv n,
     s t ↦ funext (Fin n) (_ ↦ Bool) (c2pow_vec_equiv n .map (usym_mul (c2pow_group n) s t))
       (pointwise_mul c2abs_bool (Fin n) (c2pow_vec_equiv n .map s) (c2pow_vec_equiv n .map t))
       (i ↦ c2pow_component_mul n s t i))

{` Injections between finite types. `}
def finite_injection_fiber_prop (A B : Type) (hB : IsFinite B) (f : A → B)
  (inj : (a a' : A) → Id B (f a) (f a') → Id A a a') (b : B) : isProp (BookFiber A B f b)
  ≔ u v ↦ subtype_equal A (a ↦ Id B b (f a)) (a ↦ finite_sethood B hB b (f a)) u v
      (inj (u .fst) (v .fst) (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)))

def finite_injection_fiber_decidable (A B : Type) (hA : IsFinite A) (hB : IsFinite B) (f : A → B)
  (inj : (a a' : A) → Id B (f a) (f a') → Id A a a') (b : B) : Decidable (BookFiber A B f b)
  ≔ let F ≔ BookFiber A B f b in
    match finite_quantifiers A hA (a ↦ Id B b (f a)) (a ↦ finite_sethood B hB b (f a))
      (a ↦ finite_decidable_equality B hB b (f a)) .snd [
    | inl. m ↦ inl. (mere_rec F F (finite_injection_fiber_prop A B hB f inj b) (w ↦ w) m)
    | inr. no ↦ inr. (w ↦ no (mere F w)) ]

def finite_injection_image_equiv (A B : Type) (hB : IsFinite B) (f : A → B)
  (inj : (a a' : A) → Id B (f a) (f a') → Id A a a') : Equiv A (Σ B (BookFiber A B f))
  ≔ quasi_inverse_equiv A (Σ B (BookFiber A B f)) (a ↦ (f a, (a, refl (f a)))) (u ↦ u .snd .fst)
      (a ↦ refl a)
      (u ↦ subtype_equal B (BookFiber A B f) (finite_injection_fiber_prop A B hB f inj)
        (f (u .snd .fst), (u .snd .fst, refl (f (u .snd .fst)))) u
        (inverse B (u .fst) (f (u .snd .fst)) (u .snd .snd)))

def finite_injection_card_le (A B : Type) (hA : IsFinite A) (hB : IsFinite B) (f : A → B)
  (inj : (a a' : A) → Id B (f a) (f a') → Id A a a') : Le (cardinality A hA) (cardinality B hB)
  ≔ let P ≔ BookFiber A B f in
    let hP ≔ finite_injection_fiber_prop A B hB f inj in
    let dP ≔ finite_injection_fiber_decidable A B hA hB f inj in
    let S ≔ Σ B P in
    let N ≔ Σ B (b ↦ Not (P b)) in
    let hS : IsFinite S ≔ finite_decidable_subset B hB P hP dP in
    let hN : IsFinite N
      ≔ finite_decidable_subset B hB (b ↦ Not (P b)) (b ↦ negation_prop (P b))
          (b ↦ match dP b [ inl. p ↦ inr. (n ↦ n p) | inr. n ↦ inl. n ]) in
    let hSum : IsFinite (Sum S N) ≔ finite_sum S N hS hN in
    let a ≔ cardinality S hS in
    let eA : Id Nat (cardinality A hA) a ≔ cardinality_equiv A S (finite_injection_image_equiv A B hB f inj) hA hS in
    let eB : Id Nat (cardinality B hB) (add a (cardinality N hN))
      ≔ concat Nat (cardinality B hB) (cardinality (Sum S N) hSum) (add a (cardinality N hN))
          (cardinality_equiv B (Sum S N) (fingp_decidable_split_equiv B P hP dP) hB hSum)
          (cardinality_sum S N hS hN hSum) in
    transport Nat (x ↦ Le (cardinality A hA) x) (add a (cardinality N hN)) (cardinality B hB)
      (inverse Nat (cardinality B hB) (add a (cardinality N hN)) eB)
      (transport Nat (x ↦ Le x (add a (cardinality N hN))) a (cardinality A hA)
        (inverse Nat (cardinality A hA) a eA) (le_add_base a (cardinality N hN)))
