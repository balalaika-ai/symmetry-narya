export "272-quotient-fiber-equivalence"
export "261-circle-flip-conjugation"

{` Claims made in the running text of chapter 3 (circle.tex), outside the
   numbered blocks, that were not yet formalized (inventory
   text-claims-ch3.json).  Each group starts with the book line and a short
   quote.  Among them: the book's inverse h of thm:fiber-cdg with g∘h = id and
   the "left to the reader" h∘g = id; the first proof of thm:S1bysymmetries
   (the triangles of eq:setbundle-Sc-univ-comp); identifications in
   Σ_{X:U}(X → X) for arbitrary types; uniqueness of the diagonal e from
   cancel_injection alone; the LPO footnote of thm:fiber-cdg; the (−1)-image
   of –/m as FinSet_m; and a number of smaller remarks. `}

{` Part 1. Iterations of a trivial loop (circle.tex:49), lifts into coverings
   (circle.tex:795) and φ(k,r) as iterated addition (circle.tex:2813). `}

{` circle.tex:49-50: "if there is an identification of type p = refl_a, then
   all the iterations of p can be identified with each other". `}
def loop_power_nat_trivial (A : Type) (a : A) (p : Id A a a) (h : Id (Id A a a) p (refl a)) (n : Nat)
  : Id (Id A a a) (loop_power_nat A a p n) (refl a)
  ≔ match n [
  | zero. ↦ refl (refl a)
  | suc. n ↦
      concat (Id A a a) (concat A a a a (loop_power_nat A a p n) p)
        (concat A a a a (loop_power_nat A a p n) (refl a)) (refl a)
        (refl (concat A a a a (loop_power_nat A a p n)) h)
        (concat (Id A a a) (concat A a a a (loop_power_nat A a p n) (refl a)) (loop_power_nat A a p n) (refl a)
          (transport_refl A ((y ↦ Id A a y) : A → Type) a (loop_power_nat A a p n))
          (loop_power_nat_trivial A a p h n)) ]

def loop_power_trivial (A : Type) (a : A) (p : Id A a a) (h : Id (Id A a a) p (refl a)) (z : Int)
  : Id (Id A a a) (loop_power A a p z) (refl a)
  ≔ match z [
  | pos. n ↦ loop_power_nat_trivial A a p h n
  | neg. n ↦ loop_power_nat_trivial A a (inverse A a a p)
      (concat (Id A a a) (inverse A a a p) (inverse A a a (refl a)) (refl a)
        (refl (inverse A a a) h) (inverse_refl A a)) (suc. n) ]

def trivial_loop_powers_equal (A : Type) (a : A) (p : Id A a a) (h : Id (Id A a a) p (refl a)) (z w : Int)
  : Id (Id A a a) (loop_power A a p z) (loop_power A a p w)
  ≔ concat (Id A a a) (loop_power A a p z) (refl a) (loop_power A a p w)
      (loop_power_trivial A a p h z)
      (inverse (Id A a a) (loop_power A a p w) (refl a) (loop_power_trivial A a p h w))

{` circle.tex:795-797 (after def:univ-cover): "In the above definition we get
   that h : A →* C is a covering as well by xca:covering-utils(left-cancel)". `}
def pointed_cover_lift_covering (A B C : Pointed) (f : BookPointedMap A B) (g : BookPointedMap C B)
  (hf : IsCovering (A .carrier) (B .carrier) (f .fst)) (hg : IsCovering (C .carrier) (B .carrier) (g .fst))
  (l : PointedCoverLifts A B C f g) : IsCovering (A .carrier) (C .carrier) (l .fst .fst)
  ≔ coverings_left_cancel (A .carrier) (C .carrier) (B .carrier) (l .fst .fst) (g .fst) hg
      (transport (A .carrier → B .carrier) (k ↦ IsCovering (A .carrier) (B .carrier) k) (f .fst)
        (compose (A .carrier) (C .carrier) (B .carrier) (g .fst) (l .fst .fst)) (l .snd .fst) hf)

{` circle.tex:2812-2813, margin note in lem:deg-m-on-Cyc: "In terms of
   iterated addition, we have φ(k,r) = (z ↦ z+m)^r(k)".  Translation by m
   (int_translation_equiv, z ↦ m + z = z + m) commutes with translation by k,
   and int_mul m r is its r-th power at 0. `}
def int_translations_commute (k y z : Int)
  : Id Int (int_add k (int_add y z)) (int_add y (int_add k z))
  ≔ concat Int (int_add k (int_add y z)) (int_add (int_add k y) z) (int_add y (int_add k z))
      (inverse Int (int_add (int_add k y) z) (int_add k (int_add y z)) (int_add_assoc k y z))
      (concat Int (int_add (int_add k y) z) (int_add (int_add y k) z) (int_add y (int_add k z))
        (refl ((v ↦ int_add v z) : Int → Int) (int_add_comm k y))
        (int_add_assoc y k z))

def integer_radix_iterated_addition (m : Nat) (k : Fin m) (r : Int)
  : Id Int (integer_radix_value m (k, r))
      (permutation_power Int (int_translation_equiv (pos. m)) r (pos. (fin_book_below_equiv m .map k .fst)))
  ≔ let T ≔ int_translation_equiv (pos. m) in
    let K : Int ≔ pos. (fin_book_below_equiv m .map k .fst) in
    permutation_power_intertwine Int Int T T (int_add K) (z ↦ int_translations_commute K (pos. m) z) r int_zero

{` Part 2. Small claims: circle.tex:325, 351, 566, 980/994, 1814, 2503, 2561, 2575, 3124. `}

{` circle.tex:325, after lem:circleisconnected: "having an element of type
   ∏_{z:S¹}(base = z) contradicts the univalence axiom".  Such an element
   contracts S¹ onto base, so S¹ would be a set, which circle_not_set
   refutes (via the universal covering, i.e. via univalence). `}
def circle_based_paths_section_absurd (C : CircleSignature)
  (h : (z : C .carrier) → Id (C .carrier) (C .base) z) : Empty
  ≔ circle_not_set C
      (prop_is_set (C .carrier)
        (contractible_prop (C .carrier) (C .base, z ↦ inverse (C .carrier) (C .base) z (h z))))

{` circle.tex:351, footnote ft:many-integers, the first three alternatives.
   (i) "the copy of ℕ where 2n means n and 2n+1 means -n-1". `}
def parity_double (n : Nat) : Nat ≔ match n [ zero. ↦ zero. | suc. k ↦ suc. (suc. (parity_double k)) ]

def parity_int_shift : Int → Int ≔ [ pos. n ↦ pos. (suc. n) | neg. n ↦ neg. (suc. n) ]

def parity_nat_to_int (m : Nat) : Int
  ≔ match m [
  | zero. ↦ pos. zero.
  | suc. zero. ↦ neg. zero.
  | suc. (suc. k) ↦ parity_int_shift (parity_nat_to_int k) ]

def parity_int_to_nat : Int → Nat ≔ [ pos. n ↦ parity_double n | neg. n ↦ suc. (parity_double n) ]

{` 2n means n. `}
def parity_nat_to_int_even (n : Nat) : Id Int (parity_nat_to_int (parity_double n)) (pos. n)
  ≔ match n [
  | zero. ↦ refl (pos. zero. : Int)
  | suc. k ↦ refl parity_int_shift (parity_nat_to_int_even k) ]

{` 2n+1 means -n-1 (neg. n is -(n+1)). `}
def parity_nat_to_int_odd (n : Nat) : Id Int (parity_nat_to_int (suc. (parity_double n))) (neg. n)
  ≔ match n [
  | zero. ↦ refl (neg. zero. : Int)
  | suc. k ↦ refl parity_int_shift (parity_nat_to_int_odd k) ]

def parity_int_to_nat_shift (z : Int)
  : Id Nat (parity_int_to_nat (parity_int_shift z)) (suc. (suc. (parity_int_to_nat z)))
  ≔ match z [
  | pos. n ↦ refl (parity_double (suc. n))
  | neg. n ↦ refl (suc. (parity_double (suc. n))) ]

def parity_int_nat_roundtrip (m : Nat) : Id Nat (parity_int_to_nat (parity_nat_to_int m)) m
  ≔ match m [
  | zero. ↦ refl (zero. : Nat)
  | suc. zero. ↦ refl (suc. zero. : Nat)
  | suc. (suc. k) ↦ concat Nat (parity_int_to_nat (parity_int_shift (parity_nat_to_int k)))
      (suc. (suc. (parity_int_to_nat (parity_nat_to_int k)))) (suc. (suc. k))
      (parity_int_to_nat_shift (parity_nat_to_int k))
      (refl ((j ↦ suc. (suc. j)) : Nat → Nat) (parity_int_nat_roundtrip k)) ]

def parity_nat_int_roundtrip (z : Int) : Id Int (parity_nat_to_int (parity_int_to_nat z)) z
  ≔ match z [ pos. n ↦ parity_nat_to_int_even n | neg. n ↦ parity_nat_to_int_odd n ]

{` The decoding ℕ → ℤ of the parity encoding is an equivalence. `}
def parity_nat_int_equiv : Equiv Nat Int
  ≔ quasi_inverse_equiv Nat Int parity_nat_to_int parity_int_to_nat parity_int_nat_roundtrip parity_nat_int_roundtrip

def parity_nat_int_book_map : BookIsEquiv Nat Int parity_nat_to_int
  ≔ book_equivalence Nat Int parity_nat_int_equiv .equiv

{` (ii) "the sum ℕ ⊔ ℕ, where inl n means -n-1 and inr n means n" (module
   283 has the opposite labelling). `}
def book_nat_sum_to_int : Sum Nat Nat → Int ≔ [ inl. n ↦ neg. n | inr. n ↦ pos. n ]
def book_int_to_nat_sum : Int → Sum Nat Nat ≔ [ pos. n ↦ inr. n | neg. n ↦ inl. n ]

def book_nat_sum_int_equiv : Equiv (Sum Nat Nat) Int
  ≔ quasi_inverse_equiv (Sum Nat Nat) Int book_nat_sum_to_int book_int_to_nat_sum
      [ inl. n ↦ refl (inl. n : Sum Nat Nat) | inr. n ↦ refl (inr. n : Sum Nat Nat) ]
      [ pos. n ↦ refl (pos. n : Int) | neg. n ↦ refl (neg. n : Int) ]

def book_nat_sum_int_book_map : BookIsEquiv (Sum Nat Nat) Int book_nat_sum_to_int
  ≔ book_equivalence (Sum Nat Nat) Int book_nat_sum_int_equiv .equiv

{` (iii) "the sum ℕ ⊔ 1 ⊔ ℕ, where from the left copy of ℕ we get -n-1, from
   the center 0 : 1 we get 0, and from the right copy of ℕ we get n+1". `}
def nat_unit_nat_to_int : Sum Nat (Sum Unit Nat) → Int
  ≔ [ inl. n ↦ neg. n | inr. w ↦ match w [ inl. _ ↦ pos. zero. | inr. n ↦ pos. (suc. n) ] ]

def int_to_nat_unit_nat : Int → Sum Nat (Sum Unit Nat)
  ≔ [ pos. zero. ↦ inr. (inl. star.) | pos. (suc. n) ↦ inr. (inr. n) | neg. n ↦ inl. n ]

def nat_unit_nat_roundtrip (w : Sum Nat (Sum Unit Nat))
  : Id (Sum Nat (Sum Unit Nat)) (int_to_nat_unit_nat (nat_unit_nat_to_int w)) w
  ≔ match w [
  | inl. n ↦ refl (inl. n : Sum Nat (Sum Unit Nat))
  | inr. v ↦ match v [
    | inl. u ↦ match u [ star. ↦ refl (inr. (inl. star.) : Sum Nat (Sum Unit Nat)) ]
    | inr. n ↦ refl (inr. (inr. n) : Sum Nat (Sum Unit Nat)) ] ]

def int_nat_unit_nat_roundtrip (z : Int) : Id Int (nat_unit_nat_to_int (int_to_nat_unit_nat z)) z
  ≔ match z [
  | pos. zero. ↦ refl (pos. zero. : Int)
  | pos. (suc. n) ↦ refl (pos. (suc. n) : Int)
  | neg. n ↦ refl (neg. n : Int) ]

def nat_unit_nat_int_equiv : Equiv (Sum Nat (Sum Unit Nat)) Int
  ≔ quasi_inverse_equiv (Sum Nat (Sum Unit Nat)) Int nat_unit_nat_to_int int_to_nat_unit_nat
      nat_unit_nat_roundtrip int_nat_unit_nat_roundtrip

def nat_unit_nat_int_book_map : BookIsEquiv (Sum Nat (Sum Unit Nat)) Int nat_unit_nat_to_int
  ≔ book_equivalence (Sum Nat (Sum Unit Nat)) Int nat_unit_nat_int_equiv .equiv

{` circle.tex:566: "A′ :≡ Σ_{z:S¹} Bool = (S¹ × Bool) = (S¹ + S¹), and the
   latter type is not connected".  The first identification is by
   definition; the second holds for any type in place of S¹. `}
def product_bool_sum_at (A : Type) (a : A) (b : Bool) : Sum A A
  ≔ match b [ false. ↦ inl. a | true. ↦ inr. a ]

def sum_product_bool (A : Type) : Sum A A → Product A Bool
  ≔ [ inl. a ↦ (a, false.) | inr. a ↦ (a, true.) ]

def product_bool_sum_roundtrip_at (A : Type) (a : A) (b : Bool)
  : Id (Product A Bool) (sum_product_bool A (product_bool_sum_at A a b)) (a, b)
  ≔ match b [ false. ↦ refl ((a, false.) : Product A Bool) | true. ↦ refl ((a, true.) : Product A Bool) ]

def product_bool_sum_equiv (A : Type) : Equiv (Product A Bool) (Sum A A)
  ≔ quasi_inverse_equiv (Product A Bool) (Sum A A) (w ↦ product_bool_sum_at A (w .fst) (w .snd)) (sum_product_bool A)
      (w ↦ product_bool_sum_roundtrip_at A (w .fst) (w .snd))
      [ inl. a ↦ refl (inl. a : Sum A A) | inr. a ↦ refl (inr. a : Sum A A) ]

def sum_self_not_connected (A : Type) (h : Connected (Sum A A)) : Empty
  ≔ mere_rec (Sum A A) Empty empty_prop
      (x ↦ match x [
        | inl. a ↦ mere_rec (Id (Sum A A) (inl. a) (inr. a)) Empty empty_prop
            (p ↦ sum_encode A A (inl. a) (inr. a) p) (h .snd (inl. a) (inr. a))
        | inr. a ↦ mere_rec (Id (Sum A A) (inr. a) (inl. a)) Empty empty_prop
            (p ↦ sum_encode A A (inr. a) (inl. a) p) (h .snd (inr. a) (inl. a)) ])
      (h .fst)

def circle_constant_boolean_product_path (C : CircleSignature)
  : Id Type (Σ (C .carrier) (_ ↦ Bool)) (Product (C .carrier) Bool)
  ≔ refl (Product (C .carrier) Bool)

def circle_constant_boolean_sum_equiv (C : CircleSignature)
  : Equiv (Σ (C .carrier) (_ ↦ Bool)) (Sum (C .carrier) (C .carrier))
  ≔ product_bool_sum_equiv (C .carrier)

def circle_constant_boolean_sum_path (C : CircleSignature)
  : Id Type (Σ (C .carrier) (_ ↦ Bool)) (Sum (C .carrier) (C .carrier))
  ≔ concat Type (Σ (C .carrier) (_ ↦ Bool)) (Product (C .carrier) Bool) (Sum (C .carrier) (C .carrier))
      (circle_constant_boolean_product_path C)
      (ua (Product (C .carrier) Bool) (Sum (C .carrier) (C .carrier)) (product_bool_sum_equiv (C .carrier)))

def circle_sum_not_connected (C : CircleSignature) (h : Connected (Sum (C .carrier) (C .carrier))) : Empty
  ≔ sum_self_not_connected (C .carrier) h

{` circle.tex:980-994: "giving an h(z) : P(z) → Q(z) for all z : S¹ is the
   same as specifying an element h(base) : P(base) → Q(base) and ... an
   identification h(loop) : Q(loop) h(base) P(loop)⁻¹ = h(base)".  Here
   P(loop) and Q(loop) are transport along loop, P(loop)⁻¹ transport along
   loop⁻¹. `}
def circle_family_map_conjugate (C : CircleSignature) (P Q : C .carrier → Type)
  (h : P (C .base) → Q (C .base)) : P (C .base) → Q (C .base)
  ≔ y ↦ transport (C .carrier) Q (C .base) (C .base) (C .loop)
      (h (transport (C .carrier) P (C .base) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop)) y))

def CircleFamilyMapLoop (C : CircleSignature) (P Q : C .carrier → Type) (h : P (C .base) → Q (C .base)) : Type
  ≔ Id (P (C .base) → Q (C .base)) (circle_family_map_conjugate C P Q h) h

{` A path over loop in the family z ↦ (P z → Q z) is such an identification. `}
def circle_family_map_loop_equiv (C : CircleSignature) (P Q : C .carrier → Type) (h : P (C .base) → Q (C .base))
  : Equiv (Id (FunctionFamily (C .carrier) P Q) (C .loop) h h) (CircleFamilyMapLoop C P Q h)
  ≔ let X ≔ C .carrier in let b ≔ C .base in let l ≔ C .loop in
    let F ≔ FunctionFamily X P Q in
    compose_equiv (Id F l h h) (Id (P b → Q b) (transport X F b b l h) h) (CircleFamilyMapLoop C P Q h)
      (pathover_transport_equiv X F b b l h h)
      (concat_left_equiv (P b → Q b) (circle_family_map_conjugate C P Q h) (transport X F b b l h) h
        (inverse (P b → Q b) (transport X F b b l h) (circle_family_map_conjugate C P Q h)
          (funext (P b) (_ ↦ Q b) (transport X F b b l h) (circle_family_map_conjugate C P Q h)
            (y ↦ transport_function_family X P Q b b l h y))))

def circle_family_maps_equiv (C : CircleSignature) (P Q : C .carrier → Type)
  : Equiv ((z : C .carrier) → P z → Q z) (Σ (P (C .base) → Q (C .base)) (CircleFamilyMapLoop C P Q))
  ≔ let F ≔ FunctionFamily (C .carrier) P Q in
    compose_equiv ((z : C .carrier) → P z → Q z) (CircleBoundary (C .carrier) (C .base) (C .loop) F)
      (Σ (P (C .base) → Q (C .base)) (CircleFamilyMapLoop C P Q))
      (circle_dependent_universal_property C F)
      (family_equiv (P (C .base) → Q (C .base)) (h ↦ Id F (C .loop) h h) (CircleFamilyMapLoop C P Q)
        (circle_family_map_loop_equiv C P Q))

{` The map is h ↦ (h(base), h(loop)), with h(loop) the image of apd_h(loop). `}
def circle_family_maps_book_map (C : CircleSignature) (P Q : C .carrier → Type)
  : BookIsEquiv ((z : C .carrier) → P z → Q z) (Σ (P (C .base) → Q (C .base)) (CircleFamilyMapLoop C P Q))
      (h ↦ (h (C .base), circle_family_map_loop_equiv C P Q (h (C .base)) .map (refl h (C .loop))))
  ≔ book_equivalence ((z : C .carrier) → P z → Q z) (Σ (P (C .base) → Q (C .base)) (CircleFamilyMapLoop C P Q))
      (circle_family_maps_equiv C P Q) .equiv

{` circle.tex:994: "If P, Q are families of sets, then h(loop) is a proof
   that this diagram commutes": Q(loop) ∘ h(base) = h(base) ∘ P(loop). `}
def circle_family_map_loop_square_equiv (C : CircleSignature) (P Q : C .carrier → Type)
  (hQ : isSet (Q (C .base))) (h : P (C .base) → Q (C .base))
  : Equiv (CircleFamilyMapLoop C P Q h)
      ((y : P (C .base)) → Id (Q (C .base))
        (transport (C .carrier) Q (C .base) (C .base) (C .loop) (h y))
        (h (transport (C .carrier) P (C .base) (C .base) (C .loop) y)))
  ≔ let X ≔ C .carrier in let b ≔ C .base in let l ≔ C .loop in
    let tP ≔ transport X P b b l in
    let tPi ≔ transport X P b b (inverse X b b l) in
    let tQ ≔ transport X Q b b l in
    let k ≔ circle_family_map_conjugate C P Q h in
    iff_equiv (CircleFamilyMapLoop C P Q h)
      ((y : P b) → Id (Q b) (tQ (h y)) (h (tP y)))
      (pi_set (P b) (_ ↦ Q b) (_ ↦ hQ) k h)
      (pi_prop (P b) (y ↦ Id (Q b) (tQ (h y)) (h (tP y))) (y ↦ hQ (tQ (h y)) (h (tP y))))
      (c y ↦ concat (Q b) (tQ (h y)) (k (tP y)) (h (tP y))
        (refl ((w ↦ tQ (h w)) : P b → Q b)
          (inverse (P b) (tPi (tP y)) y (transport_inverse_roundtrip X P b b l y)))
        (happly (P b) (_ ↦ Q b) k h c (tP y)))
      (s ↦ funext (P b) (_ ↦ Q b) k h (y ↦ concat (Q b) (k y) (h (tP (tPi y))) (h y)
        (s (tPi y))
        (refl h (concat (P b) (tP (tPi y)) (transport X P b b (inverse X b b (inverse X b b l)) (tPi y)) y
          (refl ((r ↦ transport X P b b r (tPi y)) : Id X b b → P b)
            (inverse (Id X b b) (inverse X b b (inverse X b b l)) l (inverse_inverse X b b l)))
          (transport_inverse_roundtrip X P b b (inverse X b b l) y)))))

{` circle.tex:1814, margin note: "(–)^0 : (base = base) → (base = base) is
   constant and hence not injective". `}
def loop_power_zero_constant (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base)) (loop_power_nat (C .carrier) (C .base) p zero.) (refl (C .base))
  ≔ refl (refl (C .base))

def loop_power_zero_not_injective (C : CircleSignature)
  (h : PathReflecting (Id (C .carrier) (C .base) (C .base)) (Id (C .carrier) (C .base) (C .base))
    (p ↦ loop_power_nat (C .carrier) (C .base) p zero.)) : Empty
  ≔ let L ≔ Id (C .carrier) (C .base) (C .base) in
    let e ≔ native_equivalence Int L (circle_integer_loop_equiv C) in
    int_encode int_zero (pos. (suc. zero.))
      (equivalence_injective Int L e int_zero (pos. (suc. zero.))
        (h (loop_power (C .carrier) (C .base) (C .loop) int_zero)
          (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))
          (refl (refl (C .base)))))

{` circle.tex:3124, margin note after def:n-image: "If A and B are sets, then
   the fibers of f : A → B are sets as well.  Hence im_0(f) amounts to the
   set of pairs (b,a) such that b = f(a)". `}
def set_map_fiber_set (A B : Type) (hA : isSet A) (hB : isSet B) (f : A → B) (b : B)
  : isSet (BookFiber A B f b)
  ≔ sigma_set A (a ↦ Id B b (f a)) hA (a ↦ prop_is_set (Id B b (f a)) (hB b (f a)))

def zero_image_of_sets_pairs (A B : Type) (hA : isSet A) (hB : isSet B) (f : A → B)
  : Equiv (NImage (suc. zero.) A B f) (Σ B (b ↦ Σ A (a ↦ Id B b (f a))))
  ≔ compose_equiv (NImage (suc. zero.) A B f) (ZeroImage A B f) (Σ B (b ↦ Σ A (a ↦ Id B b (f a))))
      (n_image_zero_equiv A B f)
      (family_equiv B (b ↦ SetTrunc (BookFiber A B f b)) (b ↦ BookFiber A B f b)
        (b ↦ set_trunc_of_set_equiv (BookFiber A B f b) (set_map_fiber_set A B hA hB f b)))

def zero_image_of_sets_set (A B : Type) (hA : isSet A) (hB : isSet B) (f : A → B)
  : isSet (Σ B (b ↦ Σ A (a ↦ Id B b (f a))))
  ≔ sigma_set B (b ↦ BookFiber A B f b) hB (set_map_fiber_set A B hA hB f)

{` circle.tex:2503: "Since the starting point in a cycle doesn't matter, we
   could also have written, e.g., (3 1 2)(5 4)".  General rotation invariance
   (a_1 a_2 ... a_k) = (a_2 ... a_k a_1), and the book's example on
   {1,...,5}. `}
def rotation_decide_branch_congr (A P : Type) (d : Decidable P) (y1 y2 n1 n2 : A)
  (hy : P → Id A y1 y2) (hn : Not P → Id A n1 n2)
  : Id A (decide_branch A P d y1 n1) (decide_branch A P d y2 n2)
  ≔ match d [ inl. p ↦ hy p | inr. q ↦ hn q ]

{` Moving a1 from the front (as the value "first") to the end of the list. `}
def cycle_lookup_move_first (A : Type) (d : DecidableEquality A) (a1 f : A) (l : List A) (x : A)
  (nx : Not (Id A x a1))
  : Id A (cycle_lookup A d a1 l x) (cycle_lookup A d f (append A l (cons. a1 nil.)) x)
  ≔ match l [
  | nil. ↦ inverse A (cycle_lookup A d f (cons. a1 nil.) x) x
      (decide_branch_no A (Id A x a1) (d x a1) f x nx)
  | cons. b rest ↦ rotation_decide_branch_congr A (Id A x b) (d x b)
      (cycle_next_head A a1 rest) (cycle_next_head A f (append A rest (cons. a1 nil.)))
      (cycle_lookup A d a1 rest x) (cycle_lookup A d f (append A rest (cons. a1 nil.)) x)
      (_ ↦ match rest [
        | nil. ↦ refl a1
        | cons. c _ ↦ refl c ])
      (_ ↦ cycle_lookup_move_first A d a1 f rest x nx) ]

def cycle_notation_rotate_at (A : Type) (d : DecidableEquality A) (a1 a2 : A) (rest : List A)
  (h : PairwiseDistinct A (cons. a1 (cons. a2 rest))) (x : A)
  : Id A (cycle_notation A d a1 (cons. a2 rest) x) (cycle_notation A d a2 (append A rest (cons. a1 nil.)) x)
  ≔ match d x a1 [
  | inl. p ↦ calc
      cycle_notation A d a1 (cons. a2 rest) x = a2
        by decide_branch_yes A (Id A x a1) (d x a1) a2 (cycle_lookup A d a1 (cons. a2 rest) x) p
      = cycle_notation A d a2 (append A rest (cons. a1 nil.)) a1
        by inverse A (cycle_notation A d a2 (append A rest (cons. a1 nil.)) a1) a2
          (cycle_notation_successor A d a2 rest a1 nil. (h .fst))
      = cycle_notation A d a2 (append A rest (cons. a1 nil.)) x
        by refl (cycle_notation A d a2 (append A rest (cons. a1 nil.))) (inverse A x a1 p) ∎
  | inr. n ↦ concat A (cycle_notation A d a1 (cons. a2 rest) x) (cycle_lookup A d a1 (cons. a2 rest) x)
      (cycle_notation A d a2 (append A rest (cons. a1 nil.)) x)
      (decide_branch_no A (Id A x a1) (d x a1) a2 (cycle_lookup A d a1 (cons. a2 rest) x) n)
      (cycle_lookup_move_first A d a1 a2 (cons. a2 rest) x n) ]

def cycle_notation_rotate (A : Type) (d : DecidableEquality A) (a1 a2 : A) (rest : List A)
  (h : PairwiseDistinct A (cons. a1 (cons. a2 rest)))
  : Id (A → A) (cycle_notation A d a1 (cons. a2 rest)) (cycle_notation A d a2 (append A rest (cons. a1 nil.)))
  ≔ funext A (_ ↦ A) (cycle_notation A d a1 (cons. a2 rest)) (cycle_notation A d a2 (append A rest (cons. a1 nil.)))
      (cycle_notation_rotate_at A d a1 a2 rest h)

{` The book's example: (1 2 3)(4 5) = (3 1 2)(5 4) as maps of {1,...,5},
   with 1,...,5 the elements of Fin 5 in the order of fin_book_below_equiv. `}
def fin5_1 : Fin (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ inr. star.
def fin5_2 : Fin (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ inl. (inr. star.)
def fin5_3 : Fin (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ inl. (inl. (inr. star.))
def fin5_4 : Fin (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ inl. (inl. (inl. (inr. star.)))
def fin5_5 : Fin (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ inl. (inl. (inl. (inl. (inr. star.))))

def cycle_notation_example_left (x : Fin (suc. (suc. (suc. (suc. (suc. zero.))))))
  : Fin (suc. (suc. (suc. (suc. (suc. zero.)))))
  ≔ let F ≔ Fin (suc. (suc. (suc. (suc. (suc. zero.))))) in
    let d ≔ fin_decidable_equality (suc. (suc. (suc. (suc. (suc. zero.))))) in
    cycle_notation F d fin5_1 (cons. fin5_2 (cons. fin5_3 nil.)) (cycle_notation F d fin5_4 (cons. fin5_5 nil.) x)

def cycle_notation_example_right (x : Fin (suc. (suc. (suc. (suc. (suc. zero.))))))
  : Fin (suc. (suc. (suc. (suc. (suc. zero.)))))
  ≔ let F ≔ Fin (suc. (suc. (suc. (suc. (suc. zero.))))) in
    let d ≔ fin_decidable_equality (suc. (suc. (suc. (suc. (suc. zero.))))) in
    cycle_notation F d fin5_3 (cons. fin5_1 (cons. fin5_2 nil.)) (cycle_notation F d fin5_5 (cons. fin5_4 nil.) x)

def cycle_notation_example_rotation
  : Id (Fin (suc. (suc. (suc. (suc. (suc. zero.))))) → Fin (suc. (suc. (suc. (suc. (suc. zero.))))))
      cycle_notation_example_left cycle_notation_example_right
  ≔ let F ≔ Fin (suc. (suc. (suc. (suc. (suc. zero.))))) in
    funext F (_ ↦ F) cycle_notation_example_left cycle_notation_example_right (x ↦ match x [
    | inr. u ↦ match u [ star. ↦ refl fin5_2 ]
    | inl. x ↦ match x [
      | inr. u ↦ match u [ star. ↦ refl fin5_3 ]
      | inl. x ↦ match x [
        | inr. u ↦ match u [ star. ↦ refl fin5_1 ]
        | inl. x ↦ match x [
          | inr. u ↦ match u [ star. ↦ refl fin5_5 ]
          | inl. x ↦ match x [
            | inr. u ↦ match u [ star. ↦ refl fin5_4 ]
            | inl. e ↦ match e [] ] ] ] ] ])

{` circle.tex:2561, footnote: "(1 2) = (2 3)(1 3)(2 3) as permutations of
   {1,2,3}" (rightmost factor applied first). `}
def fin3_1 : Fin (suc. (suc. (suc. zero.))) ≔ inr. star.
def fin3_2 : Fin (suc. (suc. (suc. zero.))) ≔ inl. (inr. star.)
def fin3_3 : Fin (suc. (suc. (suc. zero.))) ≔ inl. (inl. (inr. star.))

def fin3_transposition (a b : Fin (suc. (suc. (suc. zero.)))) : Equiv (Fin (suc. (suc. (suc. zero.)))) (Fin (suc. (suc. (suc. zero.))))
  ≔ transposition_equiv (Fin (suc. (suc. (suc. zero.)))) (fin_decidable_equality (suc. (suc. (suc. zero.)))) a b

def transposition_product_example
  : Id (Equiv (Fin (suc. (suc. (suc. zero.)))) (Fin (suc. (suc. (suc. zero.)))))
      (fin3_transposition fin3_1 fin3_2)
      (compose_equiv (Fin (suc. (suc. (suc. zero.)))) (Fin (suc. (suc. (suc. zero.))))
        (Fin (suc. (suc. (suc. zero.))))
        (compose_equiv (Fin (suc. (suc. (suc. zero.)))) (Fin (suc. (suc. (suc. zero.))))
          (Fin (suc. (suc. (suc. zero.))))
          (fin3_transposition fin3_2 fin3_3) (fin3_transposition fin3_1 fin3_3))
        (fin3_transposition fin3_2 fin3_3))
  ≔ let F ≔ Fin (suc. (suc. (suc. zero.))) in
    equiv_homotopy F F (fin3_transposition fin3_1 fin3_2)
      (compose_equiv F F F (compose_equiv F F F (fin3_transposition fin3_2 fin3_3) (fin3_transposition fin3_1 fin3_3))
        (fin3_transposition fin3_2 fin3_3))
      (x ↦ match x [
      | inr. u ↦ match u [ star. ↦ refl fin3_2 ]
      | inl. x ↦ match x [
        | inr. u ↦ match u [ star. ↦ refl fin3_1 ]
        | inl. x ↦ match x [
          | inr. u ↦ match u [ star. ↦ refl fin3_3 ]
          | inl. e ↦ match e [] ] ] ])

{` circle.tex:2575, footnote to eq:type-factorial (Escardó): for any type X,
   Aut(X ⊔ 1) ≃ (X ⊔ 1)′ × Aut(X), where Y′ ≔ Σ_{y:Y} ∏_{z:Y}((y = z) ⊔ ¬(y = z)),
   and "by a local version of Hedberg's thm:hedberg, Y′ is a subtype of Y". `}
def IsolatedPoint (Y : Type) (y : Y) : Type ≔ (z : Y) → Decidable (Id Y y z)
def IsolatedPoints (Y : Type) : Type ≔ Σ Y (IsolatedPoint Y)

def isolated_collapse_decomposition (A : Type) (y : A) (c : (z : A) → Id A y z → Id A y z)
  (z : A) (p : Id A y z)
  : Id (Id A y z) p (concat A y y z (inverse A y y (c y (refl y))) (c z p))
  ≔ J A y (z p ↦ Id (Id A y z) p (concat A y y z (inverse A y y (c y (refl y))) (c z p)))
      (inverse (Id A y y) (concat A y y y (inverse A y y (c y (refl y))) (c y (refl y))) (refl y)
        (concat_inverse_left A y y (c y (refl y)))) z p

{` Local Hedberg: the paths out of an isolated point form propositions. `}
def isolated_paths_prop (A : Type) (y : A) (d : IsolatedPoint A y) (z : A) : isProp (Id A y z)
  ≔ p q ↦
    let c ≔ ((w r ↦ decision_collapse A y w (d w) r) : (w : A) → Id A y w → Id A y w) in
    let r ≔ inverse A y y (c y (refl y)) in
    concat (Id A y z) p (concat A y y z r (c z p)) q (isolated_collapse_decomposition A y c z p)
      (concat (Id A y z) (concat A y y z r (c z p)) (concat A y y z r (c z q)) q
        (refl (concat A y y z r) (decision_collapse_constant A y z (d z) p q))
        (inverse (Id A y z) q (concat A y y z r (c z q)) (isolated_collapse_decomposition A y c z q)))

{` Y′ is a subtype of Y. `}
def isolated_point_prop (A : Type) (y : A) : isProp (IsolatedPoint A y)
  ≔ d1 d2 ↦ funext A (z ↦ Decidable (Id A y z)) d1 d2
      (z ↦ decidability_prop (Id A y z) (isolated_paths_prop A y d1 z) (d1 z) (d2 z))

{` The added point of X ⊔ 1 is isolated, and equivalences preserve isolated points. `}
def option_point_isolated (X : Type) : IsolatedPoint (Sum X Unit) (inr. star.)
  ≔ z ↦ match z [
  | inl. x ↦ inr. (p ↦ sum_encode X Unit (inr. star.) (inl. x) p)
  | inr. u ↦ inl. (inr. (unit_prop star. u)) ]

def equiv_isolated_point (Y : Type) (s : Equiv Y Y) (y : Y) (d : IsolatedPoint Y y)
  : IsolatedPoint Y (s .map y)
  ≔ z ↦ match d (equiv_inverse_map Y Y s z) [
  | inl. p ↦ inl. (concat Y (s .map y) (s .map (equiv_inverse_map Y Y s z)) z (refl (s .map) p) (equiv_counit Y Y s z))
  | inr. n ↦ inr. (q ↦ n (concat Y y (equiv_inverse_map Y Y s (s .map y)) (equiv_inverse_map Y Y s z)
      (inverse Y (equiv_inverse_map Y Y s (s .map y)) y (equiv_retraction Y Y s y))
      (refl (equiv_inverse_map Y Y s) q))) ]

{` The transposition of two isolated points of an arbitrary type. `}
def isolated_swap (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b) (x : Y) : Y
  ≔ decide_branch Y (Id Y a x) (da x) b (decide_branch Y (Id Y b x) (db x) a x)

def isolated_swap_left (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b)
  : Id Y (isolated_swap Y a da b db a) b
  ≔ decide_branch_yes Y (Id Y a a) (da a) b (decide_branch Y (Id Y b a) (db a) a a) (refl a)

def isolated_swap_right (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b)
  : Id Y (isolated_swap Y a da b db b) a
  ≔ decide_branch_elim Y (Id Y a b) (da b) b (decide_branch Y (Id Y b b) (db b) a b) a
      (p ↦ inverse Y a b p) (_ ↦ decide_branch_yes Y (Id Y b b) (db b) a b (refl b))

def isolated_swap_fixed (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b) (x : Y)
  (na : Not (Id Y a x)) (nb : Not (Id Y b x)) : Id Y (isolated_swap Y a da b db x) x
  ≔ concat Y (isolated_swap Y a da b db x) (decide_branch Y (Id Y b x) (db x) a x) x
      (decide_branch_no Y (Id Y a x) (da x) b (decide_branch Y (Id Y b x) (db x) a x) na)
      (decide_branch_no Y (Id Y b x) (db x) a x nb)

def isolated_swap_at_b (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b) (x : Y)
  (na : Not (Id Y a x)) (q : Id Y b x) : Id Y (isolated_swap Y a da b db x) a
  ≔ concat Y (isolated_swap Y a da b db x) (decide_branch Y (Id Y b x) (db x) a x) a
      (decide_branch_no Y (Id Y a x) (da x) b (decide_branch Y (Id Y b x) (db x) a x) na)
      (decide_branch_yes Y (Id Y b x) (db x) a x q)

def isolated_swap_involutive (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b) (x : Y)
  : Id Y (isolated_swap Y a da b db (isolated_swap Y a da b db x)) x
  ≔ let t ≔ isolated_swap Y a da b db in
    match da x [
    | inl. p ↦ calc
        t (t x) = t b by refl t (concat Y (t x) (t a) b (refl t (inverse Y a x p)) (isolated_swap_left Y a da b db))
        = a by isolated_swap_right Y a da b db
        = x by p ∎
    | inr. na ↦ match db x [
      | inl. q ↦ calc
          t (t x) = t a by refl t (isolated_swap_at_b Y a da b db x na q)
          = b by isolated_swap_left Y a da b db
          = x by q ∎
      | inr. nb ↦ calc
          t (t x) = t x by refl t (isolated_swap_fixed Y a da b db x na nb)
          = x by isolated_swap_fixed Y a da b db x na nb ∎ ] ]

def isolated_swap_equiv (Y : Type) (a : Y) (da : IsolatedPoint Y a) (b : Y) (db : IsolatedPoint Y b) : Equiv Y Y
  ≔ quasi_inverse_equiv Y Y (isolated_swap Y a da b db) (isolated_swap Y a da b db)
      (isolated_swap_involutive Y a da b db) (isolated_swap_involutive Y a da b db)

{` s ↦ (s(pt), restriction of (pt s(pt)) ∘ s), as in module 175. `}
def escardo_normalize (X : Type) (s : Equiv (Sum X Unit) (Sum X Unit)) : Equiv (Sum X Unit) (Sum X Unit)
  ≔ compose_equiv (Sum X Unit) (Sum X Unit) (Sum X Unit) s
      (isolated_swap_equiv (Sum X Unit) (inr. star.) (option_point_isolated X) (s .map (inr. star.))
        (equiv_isolated_point (Sum X Unit) s (inr. star.) (option_point_isolated X)))

def escardo_normalize_fix (X : Type) (s : Equiv (Sum X Unit) (Sum X Unit))
  : Id (Sum X Unit) (escardo_normalize X s .map (inr. star.)) (inr. star.)
  ≔ isolated_swap_right (Sum X Unit) (inr. star.) (option_point_isolated X) (s .map (inr. star.))
      (equiv_isolated_point (Sum X Unit) s (inr. star.) (option_point_isolated X))

def escardo_option_to (X : Type) (s : Equiv (Sum X Unit) (Sum X Unit))
  : Product (IsolatedPoints (Sum X Unit)) (Equiv X X)
  ≔ ((s .map (inr. star.), equiv_isolated_point (Sum X Unit) s (inr. star.) (option_point_isolated X)),
      fixed_restriction X (escardo_normalize X s) (escardo_normalize_fix X s))

def escardo_option_from (X : Type) (u : Product (IsolatedPoints (Sum X Unit)) (Equiv X X))
  : Equiv (Sum X Unit) (Sum X Unit)
  ≔ compose_equiv (Sum X Unit) (Sum X Unit) (Sum X Unit) (option_extension X (u .snd))
      (isolated_swap_equiv (Sum X Unit) (inr. star.) (option_point_isolated X) (u .fst .fst) (u .fst .snd))

def escardo_option_eta (X : Type) (s : Equiv (Sum X Unit) (Sum X Unit))
  : Id (Equiv (Sum X Unit) (Sum X Unit)) (escardo_option_from X (escardo_option_to X s)) s
  ≔ let Y ≔ Sum X Unit in
    let ds ≔ equiv_isolated_point Y s (inr. star.) (option_point_isolated X) in
    let sw ≔ isolated_swap Y (inr. star.) (option_point_isolated X) (s .map (inr. star.)) ds in
    let t ≔ escardo_normalize X s in
    equiv_homotopy Y Y (escardo_option_from X (escardo_option_to X s)) s
      (x ↦ calc
        sw (option_extension X (fixed_restriction X t (escardo_normalize_fix X s)) .map x)
        = sw (t .map x) by refl sw (fixed_restriction_extension X t (escardo_normalize_fix X s) x)
        = s .map x by isolated_swap_involutive Y (inr. star.) (option_point_isolated X) (s .map (inr. star.)) ds (s .map x) ∎)

def escardo_option_epsilon (X : Type) (u : Product (IsolatedPoints (Sum X Unit)) (Equiv X X))
  : Id (Product (IsolatedPoints (Sum X Unit)) (Equiv X X)) (escardo_option_to X (escardo_option_from X u)) u
  ≔ let Y ≔ Sum X Unit in
    let o ≔ option_point_isolated X in
    let s ≔ escardo_option_from X u in
    let first : Id Y (s .map (inr. star.)) (u .fst .fst)
      ≔ isolated_swap_left Y (inr. star.) o (u .fst .fst) (u .fst .snd) in
    let firstiso : Id (IsolatedPoints Y) (escardo_option_to X s .fst) (u .fst)
      ≔ subtype_equal Y (IsolatedPoint Y) (isolated_point_prop Y) (escardo_option_to X s .fst) (u .fst) first in
    let t ≔ escardo_normalize X s in
    let tfix ≔ escardo_normalize_fix X s in
    (firstiso, equiv_homotopy X X (fixed_restriction X t tfix) (u .snd)
      (a ↦ inl_injective X (fixed_restriction_map X t tfix a) (u .snd .map a) (calc
        (inl. (fixed_restriction_map X t tfix a) : Y) = t .map (inl. a) by fixed_restriction_beta X t tfix a
        = isolated_swap Y (inr. star.) o (u .fst .fst) (u .fst .snd) (s .map (inl. a))
          by refl ((w ↦ isolated_swap Y (inr. star.) o (w .fst) (w .snd) (s .map (inl. a))) : IsolatedPoints Y → Y) firstiso
        = inl. (u .snd .map a)
          by isolated_swap_involutive Y (inr. star.) o (u .fst .fst) (u .fst .snd) (inl. (u .snd .map a)) ∎)))

def escardo_option_equiv (X : Type)
  : Equiv (Equiv (Sum X Unit) (Sum X Unit)) (Product (IsolatedPoints (Sum X Unit)) (Equiv X X))
  ≔ quasi_inverse_equiv (Equiv (Sum X Unit) (Sum X Unit)) (Product (IsolatedPoints (Sum X Unit)) (Equiv X X))
      (escardo_option_to X) (escardo_option_from X) (escardo_option_eta X) (escardo_option_epsilon X)

{` The circle statements above, instantiated at the circle constructed in
   modules 220–223. `}
def S1_circle_based_paths_section_absurd
  (h : (z : constructed_circle .carrier) → Id (constructed_circle .carrier) (constructed_circle .base) z) : Empty
  ≔ circle_based_paths_section_absurd constructed_circle h

def S1_circle_constant_boolean_sum_equiv
  : Equiv (Σ (constructed_circle .carrier) (_ ↦ Bool)) (Sum (constructed_circle .carrier) (constructed_circle .carrier))
  ≔ circle_constant_boolean_sum_equiv constructed_circle

def S1_circle_sum_not_connected (h : Connected (Sum (constructed_circle .carrier) (constructed_circle .carrier))) : Empty
  ≔ circle_sum_not_connected constructed_circle h

def S1_circle_family_maps_equiv (P Q : constructed_circle .carrier → Type)
  : Equiv ((z : constructed_circle .carrier) → P z → Q z)
      (Σ (P (constructed_circle .base) → Q (constructed_circle .base)) (CircleFamilyMapLoop constructed_circle P Q))
  ≔ circle_family_maps_equiv constructed_circle P Q

def S1_loop_power_zero_not_injective
  (h : PathReflecting (Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
    (Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
    (p ↦ loop_power_nat (constructed_circle .carrier) (constructed_circle .base) p zero.)) : Empty
  ≔ loop_power_zero_not_injective constructed_circle h

{` Part 3. Endomorphisms, components and the first proof of thm:S1bysymmetries: circle.tex:1265-1531, 2661. `}

{` Running-text claims of circle.tex (chapter 3) on endomorphisms, components
   of Σ_{X:U}(X → X), and the first proof of thm:S1bysymmetries
   (eq:setbundle-Sc-univ-comp). `}

{` circle.tex:1291-1310: "lem:isEq-pair= and def:pathover-trp give an
   equivalence between the identity type (X,t) = (Y,u) and type of pairs
   consisting of a p : X = Y and an identification trp_D(p)(t) = u ...
   In total, we have an equivalence between the identity type (X,t) = (Y,u)
   and the sum type Σ_{e : X ≃ Y} et = ue", for ARBITRARY types X, Y.
   First the fiberwise step, for a path p of types, by path induction:
   trp_D(p)(t) = u is equivalent to p̃∘t = u∘p̃, where p̃ is transport. `}
def endomorphism_pathover_equiv (X Y : Type) (p : Id Type X Y) (t : X → X) (u : Y → Y)
  : Equiv (Id (T ↦ T → T) p t u) (Id (X → Y) (x ↦ p .trr (t x)) (x ↦ u (p .trr x)))
  ≔ J Type X
      (Y p ↦ (u : Y → Y) → Equiv (Id (T ↦ T → T) p t u) (Id (X → Y) (x ↦ p .trr (t x)) (x ↦ u (p .trr x))))
      (u ↦ id_to_equiv (Id (X → X) t u)
        (Id (X → X) (x ↦ transport Type (T ↦ T) X X (refl X) (t x)) (x ↦ u (transport Type (T ↦ T) X X (refl X) x)))
        (refl ((a b ↦ Id (X → X) a b) : (X → X) → (X → X) → Type)
          (funext X (_ ↦ X) t (x ↦ transport Type (T ↦ T) X X (refl X) (t x))
            (x ↦ inverse X (transport Type (T ↦ T) X X (refl X) (t x)) (t x) (transport_refl Type (T ↦ T) X (t x))))
          (funext X (_ ↦ X) u (x ↦ u (transport Type (T ↦ T) X X (refl X) x))
            (x ↦ refl u (inverse X (transport Type (T ↦ T) X X (refl X) x) x (transport_refl Type (T ↦ T) X x))))))
      Y p u

{` The type Σ_{e : X ≃ Y} (e∘t = u∘e) of isomorphisms of endomorphisms. `}
def EndomorphismIsomorphisms (s t : Endomorphisms) : Type
  ≔ Σ (Equiv (s .fst) (t .fst)) (e ↦ Id (s .fst → t .fst) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x)))

{` A map of sums over an equivalence of bases with fiberwise equivalences is
   an equivalence; the map is the explicit (a, x) ↦ (e(a), d_a(x)). `}
def sigma_over_equivalence_isequiv (A B : Type) (F : A → Type) (e : Equiv A B) (G : B → Type)
  (d : (a : A) → Equiv (F a) (G (e .map a)))
  : isEquiv (Σ A F) (Σ B G) (w ↦ (e .map (w .fst), d (w .fst) .map (w .snd)))
  ≔ equivalence_induction A
      (B e ↦ (G : B → Type) (d : (a : A) → Equiv (F a) (G (e .map a)))
        → isEquiv (Σ A F) (Σ B G) (w ↦ (e .map (w .fst), d (w .fst) .map (w .snd))))
      (G d ↦ family_equiv A F G d .equiv) B e G d

{` circle.tex:1300, the displayed equivalence (X,t) = (Y,u) ≃ Σ_{e : X ≃ Y} et = ue
   in Σ_{X:U}(X → X), for arbitrary types.  The map is the book's: a path
   (p, q) goes to the transport equivalence of p together with the image of
   q (endomorphism_paths_equiv_first). `}
def endomorphism_paths_equiv (s t : Endomorphisms)
  : Equiv (Id Endomorphisms s t) (EndomorphismIsomorphisms s t)
  ≔ compose_equiv (Id Endomorphisms s t) (SigmaPath Type (T ↦ T → T) s t) (EndomorphismIsomorphisms s t)
      (canonical_inverse_equiv (SigmaPath Type (T ↦ T → T) s t) (Id Endomorphisms s t)
        (sigma_path_equiv Type (T ↦ T → T) s t))
      ((w ↦ (transport_univalence_equiv (s .fst) (t .fst) .map (w .fst),
          endomorphism_pathover_equiv (s .fst) (t .fst) (w .fst) (s .snd) (t .snd) .map (w .snd))),
       sigma_over_equivalence_isequiv (Id Type (s .fst) (t .fst)) (Equiv (s .fst) (t .fst))
        (p ↦ Id (T ↦ T → T) p (s .snd) (t .snd))
        (transport_univalence_equiv (s .fst) (t .fst))
        (e ↦ Id (s .fst → t .fst) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x)))
        (p ↦ endomorphism_pathover_equiv (s .fst) (t .fst) p (s .snd) (t .snd)))

def endomorphism_paths_equiv_first (s t : Endomorphisms) (r : Id Endomorphisms s t)
  : Id (Equiv (s .fst) (t .fst)) (endomorphism_paths_equiv s t .map r .fst) (transport_equiv (s .fst) (t .fst) (r .fst))
  ≔ refl (transport_equiv (s .fst) (t .fst) (r .fst))

{` circle.tex:1311: "These types are sets whenever X and Y are, and then we may
   write et = ue": for a set Y the condition et = ue is a proposition, so the
   isomorphisms form a subtype of X ≃ Y, and both types are sets. `}
def endomorphism_commutation_prop (s t : Endomorphisms) (ht : isSet (t .fst)) (e : Equiv (s .fst) (t .fst))
  : isProp (Id (s .fst → t .fst) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x)))
  ≔ pi_set (s .fst) (_ ↦ t .fst) (_ ↦ ht) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x))

def endomorphism_isomorphisms_set (s t : Endomorphisms) (ht : isSet (t .fst))
  : isSet (EndomorphismIsomorphisms s t)
  ≔ sigma_set (Equiv (s .fst) (t .fst))
      (e ↦ Id (s .fst → t .fst) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x)))
      (equivalences_set (s .fst) (t .fst) ht)
      (e ↦ prop_is_set (Id (s .fst → t .fst) (x ↦ e .map (s .snd x)) (x ↦ t .snd (e .map x)))
        (endomorphism_commutation_prop s t ht e))

def endomorphism_paths_set (s t : Endomorphisms) (ht : isSet (t .fst)) : isSet (Id Endomorphisms s t)
  ≔ hlevel_two_to_set (Id Endomorphisms s t)
      (hlevel_equiv (suc. (suc. zero.)) (EndomorphismIsomorphisms s t) (Id Endomorphisms s t)
        (canonical_inverse_equiv (Id Endomorphisms s t) (EndomorphismIsomorphisms s t) (endomorphism_paths_equiv s t))
        (set_to_hlevel_two (EndomorphismIsomorphisms s t) (endomorphism_isomorphisms_set s t ht)))

{` circle.tex:1265-1275: "components of Σ_{X:Set}(X ≃ X) ... correspond to
   components of Σ_{X:U}(X → X) at pairs (X,t), where X is a set with a
   permutation t", with the footnote: "for any (Y,u) in the same connected
   component of Σ_{X:U}(X → X) as (X,t), we have that Y also is a set and u
   also a permutation of Y". `}
def PermutationStructure (t : Endomorphisms) : Type
  ≔ Σ (isSet (t .fst)) (_ ↦ isEquiv (t .fst) (t .fst) (t .snd))

def permutation_structure_prop (t : Endomorphisms) : isProp (PermutationStructure t)
  ≔ sigma_prop (isSet (t .fst)) (_ ↦ isEquiv (t .fst) (t .fst) (t .snd)) (isset_isprop (t .fst))
      (_ ↦ isequiv_isprop (t .fst) (t .fst) (t .snd))

def permutation_endomorphism (p : Permutations) : Endomorphisms ≔ (p .fst .fst, p .snd .map)

def permutation_endomorphism_structure (p : Permutations) : PermutationStructure (permutation_endomorphism p)
  ≔ (p .fst .snd, p .snd .equiv)

def permutations_endomorphism_subtype : Equiv Permutations (Σ Endomorphisms PermutationStructure)
  ≔ quasi_inverse_equiv Permutations (Σ Endomorphisms PermutationStructure)
      (p ↦ (permutation_endomorphism p, permutation_endomorphism_structure p))
      (t ↦ ((t .fst .fst, t .snd .fst), (t .fst .snd, t .snd .snd)))
      (p ↦ refl p) (t ↦ refl t)

{` The footnote of circle.tex:1271. `}
def permutation_component_structure (p : Permutations) (s : NativeComponent Endomorphisms (permutation_endomorphism p))
  : PermutationStructure (s .fst)
  ≔ mere_transport native_truncation Endomorphisms PermutationStructure permutation_structure_prop
      (permutation_endomorphism p) (s .fst) (s .snd) (permutation_endomorphism_structure p)

{` circle.tex:1265: the component of ((X,_),t) in Σ_{X:Set}(X ≃ X) is equivalent,
   by forgetting, to the component of (X,t) in Σ_{X:U}(X → X). `}
def permutation_component_forget_equiv (p : Permutations)
  : Equiv (NativeComponent Permutations p) (NativeComponent Endomorphisms (permutation_endomorphism p))
  ≔ compose_equiv (NativeComponent Permutations p)
      (NativeComponent (Σ Endomorphisms PermutationStructure) (permutations_endomorphism_subtype .map p))
      (NativeComponent Endomorphisms (permutation_endomorphism p))
      (component_equiv Permutations (Σ Endomorphisms PermutationStructure) permutations_endomorphism_subtype p)
      (component_subtype_equiv Endomorphisms PermutationStructure permutation_structure_prop
        (permutations_endomorphism_subtype .map p))

def permutation_component_forget_map (p : Permutations) (c : NativeComponent Permutations p)
  : Id Endomorphisms (permutation_component_forget_equiv p .map c .fst) (permutation_endomorphism (c .fst))
  ≔ refl (permutation_endomorphism (c .fst))

{` circle.tex:1258-1264: restricting gf : SetBundle(S¹) ≃ Σ_{X:Set}(X ≃ X) to
   components, followed by the forgetful equivalence above: the component of
   a covering is the component of its monodromy (X,t) in Σ_{X:U}(X → X). `}
def covering_component_endomorphism_equiv (C : CircleSignature) (c : Coverings (C .carrier))
  : Equiv (NativeComponent (Coverings (C .carrier)) c)
      (NativeComponent Endomorphisms (permutation_endomorphism (circle_coverings_permutations C .map c)))
  ≔ compose_equiv (NativeComponent (Coverings (C .carrier)) c)
      (NativeComponent Permutations (circle_coverings_permutations C .map c))
      (NativeComponent Endomorphisms (permutation_endomorphism (circle_coverings_permutations C .map c)))
      (component_equiv (Coverings (C .carrier)) Permutations (circle_coverings_permutations C) c)
      (permutation_component_forget_equiv (circle_coverings_permutations C .map c))

{` circle.tex:2657-2662: "the universal covering over Cyc₀ is represented by
   the constant function cst_{pt₀} : 1 → Cyc₀ ... In light of lem:IdCisZet
   the fiber of this universal covering over (X,t) : Cyc₀ is (equivalent to)
   X itself". `}
def infinite_cycle_constant_fiber_equiv (y : CycleComponent zero.)
  : Equiv (BookFiber Unit (CycleComponent zero.) (constant Unit (CycleComponent zero.) infinite_cycle_point) y)
      (y .fst .fst .fst .fst)
  ≔ let pt ≔ infinite_cycle_point in let Z ≔ CycleComponent zero. in
    compose_equiv (BookFiber Unit Z (constant Unit Z pt) y) (Id Z y pt) (y .fst .fst .fst .fst)
      (constant_unit_fiber_equiv Z pt y)
      (compose_equiv (Id Z y pt) (Id Z pt y) (y .fst .fst .fst .fst)
        (inverse_path_equiv Z y pt)
        (compose_equiv (Id Z pt y) (Id Cycles infinite_cycle (y .fst)) (y .fst .fst .fst .fst)
          (subtype_path_equiv Cycles (d ↦ Mere (Id Cycles infinite_cycle d))
            (d ↦ mere_isprop (Id Cycles infinite_cycle d)) pt y)
          (native_equivalence (Id Cycles infinite_cycle (y .fst)) (y .fst .fst .fst .fst)
            (cycle_evaluation_from_component infinite_cycle (y .fst) (y .snd) int_zero))))

{` The equivalence sends (★, q) to the transport of 0 along q⁻¹, as in lem:IdCisZet. `}
def infinite_cycle_constant_fiber_map (y : CycleComponent zero.)
  (w : BookFiber Unit (CycleComponent zero.) (constant Unit (CycleComponent zero.) infinite_cycle_point) y)
  : Id (y .fst .fst .fst .fst) (infinite_cycle_constant_fiber_equiv y .map w)
      (cycle_path_evaluate infinite_cycle (y .fst)
        (inverse (CycleComponent zero.) y infinite_cycle_point (w .snd) .fst) int_zero)
  ≔ refl (infinite_cycle_constant_fiber_equiv y .map w)

{` Moving the base point of a component along a path. `}
def component_rebase_equiv (A : Type) (a b : A) (q : Id A a b)
  : Equiv (NativeComponent A b) (NativeComponent A a)
  ≔ quasi_inverse_equiv (NativeComponent A b) (NativeComponent A a)
      (w ↦ (w .fst, trunc_map native_truncation (Id A b (w .fst)) (Id A a (w .fst)) (concat A a b (w .fst) q) (w .snd)))
      (w ↦ (w .fst, trunc_map native_truncation (Id A a (w .fst)) (Id A b (w .fst))
        (concat A b a (w .fst) (inverse A a b q)) (w .snd)))
      (w ↦ subtype_equal A (x ↦ Mere (Id A b x)) (x ↦ mere_isprop (Id A b x))
        (w .fst, trunc_map native_truncation (Id A a (w .fst)) (Id A b (w .fst)) (concat A b a (w .fst) (inverse A a b q))
          (trunc_map native_truncation (Id A b (w .fst)) (Id A a (w .fst)) (concat A a b (w .fst) q) (w .snd)))
        w (refl (w .fst)))
      (w ↦ subtype_equal A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x))
        (w .fst, trunc_map native_truncation (Id A b (w .fst)) (Id A a (w .fst)) (concat A a b (w .fst) q)
          (trunc_map native_truncation (Id A a (w .fst)) (Id A b (w .fst)) (concat A b a (w .fst) (inverse A a b q)) (w .snd)))
        w (refl (w .fst)))

{` circle.tex:1476-1484 (first proof of thm:S1bysymmetries): "ev_U : (S¹ → U) ≃
   Σ_{X:U}(X ≃ X) maps the type family uc_base to the pair (base = base, loop·–),
   which can be identified with (ℤ,s) through cor:S1groupoid.  Hence, ev_U
   restricts to an equivalence between the connected component of uc_base in
   S¹ → U and the connected component of (ℤ,s)".  The book's uc_z is
   (x ↦ z = x), i.e. Representable S¹ z. `}
def circle_family_endomorphism (C : CircleSignature) (F : C .carrier → Type) : Endomorphisms
  ≔ (F (C .base), x ↦ refl F (C .loop) .trr x)

{` It is the underlying endomorphism of ev_U(F) (circle_families_automorphisms). `}
def circle_family_endomorphism_ev (C : CircleSignature) (F : C .carrier → Type)
  : Id Endomorphisms (circle_family_endomorphism C F)
      (circle_families_automorphisms C .map F .fst, circle_families_automorphisms C .map F .snd .map)
  ≔ refl (circle_family_endomorphism C F)

{` ev_U(uc_base) = (base = base, p ↦ p·loop), literally. `}
def circle_universal_family_endomorphism (C : CircleSignature)
  : Id Endomorphisms (circle_family_endomorphism C (Representable (C .carrier) (C .base)))
      (Id (C .carrier) (C .base) (C .base), p ↦ concat (C .carrier) (C .base) (C .base) (C .base) p (C .loop))
  ≔ refl (circle_family_endomorphism C (Representable (C .carrier) (C .base)))

{` The identification of (ℤ,s) with ev_U(uc_base) through cor:S1groupoid:
   n ↦ loopⁿ is an equivalence with loop^{n+1} = loopⁿ·loop. `}
def circle_universal_family_integer_path (C : CircleSignature)
  : Id Endomorphisms integer_endomorphism (circle_family_endomorphism C (Representable (C .carrier) (C .base)))
  ≔ let L ≔ Id (C .carrier) (C .base) (C .base) in
    let e ≔ native_equivalence Int L (circle_integer_loop_equiv C) in
    let s ≔ ((p ↦ concat (C .carrier) (C .base) (C .base) (C .base) p (C .loop)) : L → L) in
    (ua Int L e,
     equiv_inverse_map (Id (T ↦ T → T) (ua Int L e) int_succ s)
       (Id (Int → L) (x ↦ loop_power (C .carrier) (C .base) (C .loop) (int_succ x))
         (x ↦ s (loop_power (C .carrier) (C .base) (C .loop) x)))
       (endomorphism_pathover_equiv Int L (ua Int L e) int_succ s)
       (funext Int (_ ↦ L) (x ↦ loop_power (C .carrier) (C .base) (C .loop) (int_succ x))
         (x ↦ s (loop_power (C .carrier) (C .base) (C .loop) x))
         (x ↦ inverse L (s (loop_power (C .carrier) (C .base) (C .loop) x))
           (loop_power (C .carrier) (C .base) (C .loop) (int_succ x))
           (loop_power_succ (C .carrier) (C .base) (C .loop) x))))

{` Its type component transports n to loopⁿ (cor:S1groupoid). `}
def circle_universal_family_integer_path_evaluate (C : CircleSignature) (n : Int)
  : Id (Id (C .carrier) (C .base) (C .base))
      (circle_universal_family_integer_path C .fst .trr n) (loop_power (C .carrier) (C .base) (C .loop) n)
  ≔ refl (loop_power (C .carrier) (C .base) (C .loop) n)

{` The restriction of ev_U to components, with values in InfCyc (the
   component of (ℤ,s) in Σ_{X:U}(X → X)). `}
def circle_family_infinite_map (C : CircleSignature)
  (F : NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))) : InfiniteCycles
  ≔ let U ≔ Representable (C .carrier) (C .base) in
    (circle_family_endomorphism C (F .fst),
     trunc_map native_truncation (Id (C .carrier → Type) U (F .fst))
       (Id Endomorphisms integer_endomorphism (circle_family_endomorphism C (F .fst)))
       (q ↦ concat Endomorphisms integer_endomorphism (circle_family_endomorphism C U) (circle_family_endomorphism C (F .fst))
         (circle_universal_family_integer_path C) (refl (circle_family_endomorphism C) q))
       (F .snd))

def automorphisms_endomorphism_subtype
  : Equiv TypeAutomorphisms (Σ Endomorphisms (t ↦ isEquiv (t .fst) (t .fst) (t .snd)))
  ≔ quasi_inverse_equiv TypeAutomorphisms (Σ Endomorphisms (t ↦ isEquiv (t .fst) (t .fst) (t .snd)))
      (a ↦ ((a .fst, a .snd .map), a .snd .equiv)) (w ↦ (w .fst .fst, (w .fst .snd, w .snd)))
      (a ↦ refl a) (w ↦ refl w)

def circle_family_component_composite (C : CircleSignature)
  : Equiv (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))) InfiniteCycles
  ≔ let U ≔ Representable (C .carrier) (C .base) in
    let F ≔ C .carrier → Type in
    let S ≔ Σ Endomorphisms (t ↦ isEquiv (t .fst) (t .fst) (t .snd)) in
    let ev ≔ circle_families_automorphisms C in
    compose_equiv (NativeComponent F U) (NativeComponent TypeAutomorphisms (ev .map U)) InfiniteCycles
      (component_equiv F TypeAutomorphisms ev U)
      (compose_equiv (NativeComponent TypeAutomorphisms (ev .map U))
        (NativeComponent S (automorphisms_endomorphism_subtype .map (ev .map U))) InfiniteCycles
        (component_equiv TypeAutomorphisms S automorphisms_endomorphism_subtype (ev .map U))
        (compose_equiv (NativeComponent S (automorphisms_endomorphism_subtype .map (ev .map U)))
          (NativeComponent Endomorphisms (circle_family_endomorphism C U)) InfiniteCycles
          (component_subtype_equiv Endomorphisms (t ↦ isEquiv (t .fst) (t .fst) (t .snd))
            (t ↦ isequiv_isprop (t .fst) (t .fst) (t .snd)) (automorphisms_endomorphism_subtype .map (ev .map U)))
          (component_rebase_equiv Endomorphisms integer_endomorphism (circle_family_endomorphism C U)
            (circle_universal_family_integer_path C))))

{` circle.tex:1483: ev_U restricts to an equivalence between the component of
   uc_base in S¹ → U and InfCyc; the map is F ↦ (F(base), trp_F(loop)). `}
def circle_family_component_equiv (C : CircleSignature)
  : Equiv (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))) InfiniteCycles
  ≔ let U ≔ Representable (C .carrier) (C .base) in
    equiv_change_map (NativeComponent (C .carrier → Type) U) InfiniteCycles (circle_family_component_composite C)
      (circle_family_infinite_map C)
      (F ↦ subtype_equal Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
        (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
        (circle_family_component_composite C .map F) (circle_family_infinite_map C F)
        (refl (circle_family_endomorphism C (F .fst))))

{` circle.tex:1485-1491 and the left triangle of eq:setbundle-Sc-univ-comp:
   "The equivalence preim maps cst_base to (x:S¹) ↦ Σ_{_:1}(x = base) which
   can be identified with uc_base", and in general "the fiber Σ_{_:1}(x = z)
   of cst_z at x can be identified with uc_z(x) ≡ (z = x), for any z". `}
def covering_fiber_family (B : Type) (c : Coverings B) : B → Type
  ≔ b ↦ BookFiber (c .fst) B (c .snd .fst) b

def unit_fibers_representable (B : Type) (z : B)
  : Id (B → Type) (x ↦ BookFiber Unit B (constant Unit B z) x) (Representable B z)
  ≔ funext B (_ ↦ Type) (x ↦ BookFiber Unit B (constant Unit B z) x) (Representable B z)
      (x ↦ ua (BookFiber Unit B (constant Unit B z) x) (Id B z x)
        (compose_equiv (BookFiber Unit B (constant Unit B z) x) (Id B x z) (Id B z x)
          (constant_unit_fiber_equiv B z x) (inverse_path_equiv B x z)))

def circle_unit_cover (C : CircleSignature) (z : C .carrier) : Coverings (C .carrier)
  ≔ (Unit, (constant Unit (C .carrier) z,
      constant_unit_covering_from_loops (C .carrier) z (circle_groupoid C z z)))

{` preim(1, cst_z), computed by coverings_setfamilies_equiv, is uc_z. `}
def circle_unit_cover_preimage (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier → Type) (x ↦ coverings_setfamilies_equiv (C .carrier) .map (circle_unit_cover C z) x .fst)
      (Representable (C .carrier) z)
  ≔ unit_fibers_representable (C .carrier) z

{` The left map (1, cst_–) : S¹ → SetBundle(S¹)_(1, cst_base). `}
def circle_unit_cover_component (C : CircleSignature) (z : C .carrier)
  : NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base))
  ≔ (circle_unit_cover C z,
     trunc_map native_truncation (Id (C .carrier) (C .base) z)
       (Id (Coverings (C .carrier)) (circle_unit_cover C (C .base)) (circle_unit_cover C z))
       (map_path (C .carrier) (Coverings (C .carrier)) (circle_unit_cover C) (C .base) z)
       (native_circle_connected C .snd (C .base) z))

{` The middle map uc_– : S¹ → (S¹ → U)_(uc_base). `}
def circle_universal_family_map (C : CircleSignature) (z : C .carrier)
  : NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))
  ≔ representable_component_map (C .carrier) (native_circle_connected C) (C .base) z

{` preim restricted to components: a covering goes to its family of fibers. `}
def circle_unit_preimage_map (C : CircleSignature)
  (w : NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
  : NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))
  ≔ let B ≔ C .carrier in let U ≔ Representable B (C .base) in
    let fib ≔ covering_fiber_family B in
    (fib (w .fst),
     trunc_map native_truncation (Id (Coverings B) (circle_unit_cover C (C .base)) (w .fst))
       (Id (B → Type) U (fib (w .fst)))
       (q ↦ concat (B → Type) U (fib (circle_unit_cover C (C .base))) (fib (w .fst))
         (inverse (B → Type) (fib (circle_unit_cover C (C .base))) U (unit_fibers_representable B (C .base)))
         (map_path (Coverings B) (B → Type) fib (circle_unit_cover C (C .base)) (w .fst) q))
       (w .snd))

def setfamilies_split_equiv (B : Type)
  : Equiv (B → SetTypes) (Σ (B → Type) (F ↦ (b : B) → isSet (F b)))
  ≔ quasi_inverse_equiv (B → SetTypes) (Σ (B → Type) (F ↦ (b : B) → isSet (F b)))
      (S ↦ (b ↦ S b .fst, b ↦ S b .snd)) (w ↦ b ↦ (w .fst b, w .snd b)) (S ↦ refl S) (w ↦ refl w)

def circle_unit_preimage_composite (C : CircleSignature)
  : Equiv (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
      (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
  ≔ let B ≔ C .carrier in let c0 ≔ circle_unit_cover C (C .base) in
    let f ≔ coverings_setfamilies_equiv B in let sp ≔ setfamilies_split_equiv B in
    let S ≔ Σ (B → Type) (F ↦ (b : B) → isSet (F b)) in
    compose_equiv (NativeComponent (Coverings B) c0) (NativeComponent (B → SetTypes) (f .map c0))
      (NativeComponent (B → Type) (Representable B (C .base)))
      (component_equiv (Coverings B) (B → SetTypes) f c0)
      (compose_equiv (NativeComponent (B → SetTypes) (f .map c0)) (NativeComponent S (sp .map (f .map c0)))
        (NativeComponent (B → Type) (Representable B (C .base)))
        (component_equiv (B → SetTypes) S sp (f .map c0))
        (compose_equiv (NativeComponent S (sp .map (f .map c0))) (NativeComponent (B → Type) (covering_fiber_family B c0))
          (NativeComponent (B → Type) (Representable B (C .base)))
          (component_subtype_equiv (B → Type) (F ↦ (b : B) → isSet (F b))
            (F ↦ pi_prop B (b ↦ isSet (F b)) (b ↦ isset_isprop (F b))) (sp .map (f .map c0)))
          (component_rebase_equiv (B → Type) (Representable B (C .base)) (covering_fiber_family B c0)
            (inverse (B → Type) (covering_fiber_family B c0) (Representable B (C .base)) (unit_fibers_representable B (C .base))))))

{` The bottom-left map preim of eq:setbundle-Sc-univ-comp is an equivalence. `}
def circle_unit_preimage_equiv (C : CircleSignature)
  : Equiv (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
      (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
  ≔ let B ≔ C .carrier in
    equiv_change_map (NativeComponent (Coverings B) (circle_unit_cover C (C .base)))
      (NativeComponent (B → Type) (Representable B (C .base))) (circle_unit_preimage_composite C)
      (circle_unit_preimage_map C)
      (w ↦ subtype_equal (B → Type) (F ↦ Mere (Id (B → Type) (Representable B (C .base)) F))
        (F ↦ mere_isprop (Id (B → Type) (Representable B (C .base)) F))
        (circle_unit_preimage_composite C .map w) (circle_unit_preimage_map C w)
        (refl (covering_fiber_family B (w .fst))))

{` circle.tex:1503-1507: "Both the left and the right triangle represent
   identity types.  We have an identification for the left triangle because
   the fiber Σ_{_:1}(x = z) of cst_z at x can be identified with uc_z(x)". `}
def circle_first_proof_left_triangle (C : CircleSignature)
  : Id (C .carrier → NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
      (compose (C .carrier) (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
        (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
        (circle_unit_preimage_map C) (circle_unit_cover_component C))
      (circle_universal_family_map C)
  ≔ let B ≔ C .carrier in
    funext B (_ ↦ NativeComponent (B → Type) (Representable B (C .base)))
      (z ↦ circle_unit_preimage_map C (circle_unit_cover_component C z)) (circle_universal_family_map C)
      (z ↦ subtype_equal (B → Type) (F ↦ Mere (Id (B → Type) (Representable B (C .base)) F))
        (F ↦ mere_isprop (Id (B → Type) (Representable B (C .base)) F))
        (circle_unit_preimage_map C (circle_unit_cover_component C z)) (circle_universal_family_map C z)
        (unit_fibers_representable B z))

{` circle.tex:1507-1518, the right triangle of eq:setbundle-Sc-univ-comp:
   "For the right triangle we apply circle induction to construct an element
   of ∏_{z:S¹} c(z) = ev_U(uc_z).  The base case z ≡ base is exactly the
   abovementioned application of cor:S1groupoid.  For the loop case we observe
   that the following diagram commutes: loop^- ∘ s⁻¹ = (–·loop⁻¹) ∘ loop^-."
   Here z ↦ ev_U(uc_z) is pointed by the base-case identification, and the loop
   case is the equality of the loop coordinates: both loops act on 0 as s⁻¹. `}
def circle_universal_family_infinite (C : CircleSignature) (z : C .carrier) : InfiniteCycles
  ≔ circle_family_infinite_map C (circle_universal_family_map C z)

def circle_universal_family_pointing (C : CircleSignature)
  : Id InfiniteCycles infinite_endomorphism_point (circle_universal_family_infinite C (C .base))
  ≔ subtype_equal Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
      (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
      infinite_endomorphism_point (circle_universal_family_infinite C (C .base))
      (circle_universal_family_integer_path C)

def circle_universal_family_pointed_map (C : CircleSignature)
  : BookPointedMap (circle_pointed C) (InfiniteCycles, infinite_endomorphism_point)
  ≔ (circle_universal_family_infinite C, circle_universal_family_pointing C)

{` The loop case: transport along loop in the family uc_–(base) = (– = base)
   is p ↦ loop⁻¹·p, so the loop of z ↦ ev_U(uc_z), read on ℤ, sends 0 to −1. `}
def circle_universal_family_loop_coordinate (C : CircleSignature)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (circle_universal_family_pointed_map C))) (neg. zero.)
  ≔ let S ≔ C .carrier in let b ≔ C .base in let l ≔ C .loop in
    let pt ≔ infinite_endomorphism_point in
    let x ≔ circle_universal_family_infinite C b in
    let a ≔ circle_universal_family_pointing C in
    let L ≔ refl (circle_universal_family_infinite C) l in
    let F ≔ ((u ↦ u .fst .fst) : InfiniteCycles → Type) in
    let ev ≔ carrier_path_evaluate InfiniteCycles F in
    calc
      infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt x a L)
      = ev x pt (concat InfiniteCycles x x pt L (inverse InfiniteCycles pt x a)) (ev pt x a int_zero)
        by carrier_path_evaluate_concat InfiniteCycles F pt x pt a
          (concat InfiniteCycles x x pt L (inverse InfiniteCycles pt x a)) int_zero
      = ev x pt (inverse InfiniteCycles pt x a) (ev x x L (ev pt x a int_zero))
        by carrier_path_evaluate_concat InfiniteCycles F x x pt L (inverse InfiniteCycles pt x a) (ev pt x a int_zero)
      = ev x pt (inverse InfiniteCycles pt x a) (concat S b b b (inverse S b b l) (refl b))
        by refl (ev x pt (inverse InfiniteCycles pt x a)) (transport_path_to S b b b l (refl b))
      = ev x pt (inverse InfiniteCycles pt x a) (inverse S b b l)
        by refl (ev x pt (inverse InfiniteCycles pt x a)) (concat_p1 S b b (inverse S b b l))
      = ev x pt (inverse InfiniteCycles pt x a) (ev pt x a (neg. zero.))
        by refl (ev x pt (inverse InfiniteCycles pt x a))
          (inverse (Id S b b) (concat S b b b (refl b) (inverse S b b l)) (inverse S b b l) (concat_1p S b b (inverse S b b l)))
      = neg. zero. by transport_inverse_roundtrip InfiniteCycles F pt x a (neg. zero.) ∎

{` c, pointed as in module 260, has the predecessor loop, with coordinate −1. `}
def circle_infinite_map_loop_coordinate (C : CircleSignature)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (pointed_circle_loop_rec C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop))) (neg. zero.)
  ≔ concat Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
        (pointed_circle_loop_rec C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop)))
      (infinite_cycle_loop_coordinate infinite_predecessor_loop) (neg. zero.)
      (refl infinite_cycle_loop_coordinate
        (pointed_circle_loop_rec_beta C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop))
      infinite_predecessor_loop_coordinate

def circle_first_proof_pointed_triangle (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (InfiniteCycles, infinite_endomorphism_point))
      (pointed_circle_loop_rec C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop)
      (circle_universal_family_pointed_map C)
  ≔ let pt ≔ infinite_endomorphism_point in
    let c ≔ pointed_circle_loop_rec C InfiniteCycles pt infinite_predecessor_loop in
    let u ≔ circle_universal_family_pointed_map C in
    equivalence_injective (BookPointedMap (circle_pointed C) (InfiniteCycles, pt)) (Id InfiniteCycles pt pt)
      (pointed_circle_universal_property C InfiniteCycles pt) c u
      (equivalence_injective (Id InfiniteCycles pt pt) Int infinite_cycle_loop_coordinate_equiv
        (pointed_circle_loop_eval C InfiniteCycles pt c) (pointed_circle_loop_eval C InfiniteCycles pt u)
        (concat Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt c)) (neg. zero.)
          (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt u))
          (circle_infinite_map_loop_coordinate C)
          (inverse Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt u)) (neg. zero.)
            (circle_universal_family_loop_coordinate C))))

{` The right triangle: c = ev_U ∘ uc_– as maps S¹ → InfCyc. `}
def circle_first_proof_right_triangle (C : CircleSignature)
  : Id (C .carrier → InfiniteCycles)
      (compose (C .carrier) (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base))) InfiniteCycles
        (circle_family_infinite_map C) (circle_universal_family_map C))
      (circle_infinite_cycle_map C)
  ≔ inverse (C .carrier → InfiniteCycles) (circle_infinite_cycle_map C) (circle_universal_family_infinite C)
      (refl ((u ↦ u .fst) : BookPointedMap (circle_pointed C) (InfiniteCycles, infinite_endomorphism_point)
          → (C .carrier → InfiniteCycles))
        (circle_first_proof_pointed_triangle C))

{` The element of ∏_{z:S¹} c(z) = ev_U(uc_z) of the printed proof. `}
def circle_first_proof_right_triangle_at (C : CircleSignature) (z : C .carrier)
  : Id InfiniteCycles (circle_infinite_cycle_map C z) (circle_universal_family_infinite C z)
  ≔ happly (C .carrier) (_ ↦ InfiniteCycles) (circle_infinite_cycle_map C) (circle_universal_family_infinite C)
      (refl ((u ↦ u .fst) : BookPointedMap (circle_pointed C) (InfiniteCycles, infinite_endomorphism_point)
          → (C .carrier → InfiniteCycles))
        (circle_first_proof_pointed_triangle C)) z

{` circle.tex:1522-1524: "With eq:setbundle-Sc-univ-comp in hand, we see that
   c is an equivalence if and only if either of the two other downward maps are." `}
def circle_first_proof_c_iff_universal_family (C : CircleSignature)
  : Equiv (BookIsEquiv (C .carrier) InfiniteCycles (circle_infinite_cycle_map C))
      (BookIsEquiv (C .carrier) (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
        (circle_universal_family_map C))
  ≔ let B ≔ C .carrier in let M ≔ NativeComponent (B → Type) (Representable B (C .base)) in
    let E ≔ circle_family_component_equiv C in
    let hE ≔ book_equivalence M InfiniteCycles E .equiv in
    iff_equiv (BookIsEquiv B InfiniteCycles (circle_infinite_cycle_map C)) (BookIsEquiv B M (circle_universal_family_map C))
      (book_isequiv_isprop B InfiniteCycles (circle_infinite_cycle_map C))
      (book_isequiv_isprop B M (circle_universal_family_map C))
      (hc ↦ book_two_out_of_three_left B M InfiniteCycles (circle_universal_family_map C) (circle_infinite_cycle_map C)
        (circle_family_infinite_map C) (circle_first_proof_right_triangle C) hc hE)
      (hm ↦ book_two_out_of_three_composite B M InfiniteCycles (circle_universal_family_map C) (circle_infinite_cycle_map C)
        (circle_family_infinite_map C) (circle_first_proof_right_triangle C) hm hE)

def circle_first_proof_universal_family_iff_unit_cover (C : CircleSignature)
  : Equiv (BookIsEquiv (C .carrier) (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
        (circle_universal_family_map C))
      (BookIsEquiv (C .carrier) (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
        (circle_unit_cover_component C))
  ≔ let B ≔ C .carrier in let M ≔ NativeComponent (B → Type) (Representable B (C .base)) in
    let K ≔ NativeComponent (Coverings B) (circle_unit_cover C (C .base)) in
    let hP ≔ book_equivalence K M (circle_unit_preimage_equiv C) .equiv in
    iff_equiv (BookIsEquiv B M (circle_universal_family_map C)) (BookIsEquiv B K (circle_unit_cover_component C))
      (book_isequiv_isprop B M (circle_universal_family_map C))
      (book_isequiv_isprop B K (circle_unit_cover_component C))
      (hm ↦ book_two_out_of_three_left B K M (circle_unit_cover_component C) (circle_universal_family_map C)
        (circle_unit_preimage_map C) (circle_first_proof_left_triangle C) hm hP)
      (hl ↦ book_two_out_of_three_composite B K M (circle_unit_cover_component C) (circle_universal_family_map C)
        (circle_unit_preimage_map C) (circle_first_proof_left_triangle C) hl hP)

{` circle.tex:1526-1545: "We now show that the map (1, cst_–) on the left is an
   equivalence.  Since the codomain is connected, it suffices to show that the
   fiber at (1, cst_base) is contractible ... the identity type is by
   lem:isEq-pair= equivalent to pairs of an equivalence e : 1 → 1 and elements
   of the identity type represented by the triangle ... Since 1 is contractible,
   this just amounts to the identity type base = z, and Σ_{z:S¹}(base = z) is
   indeed contractible."  First lem:isEq-pair= for maps into B. `}
def domain_pathover_equiv (X Y B : Type) (p : Id Type X Y) (f : X → B) (g : Y → B)
  : Equiv (Id (T ↦ T → B) p f g) (Id (X → B) f (x ↦ g (p .trr x)))
  ≔ J Type X
      (Y p ↦ (g : Y → B) → Equiv (Id (T ↦ T → B) p f g) (Id (X → B) f (x ↦ g (p .trr x))))
      (g ↦ id_to_equiv (Id (X → B) f g) (Id (X → B) f (x ↦ g (transport Type (T ↦ T) X X (refl X) x)))
        (refl ((h ↦ Id (X → B) f h) : (X → B) → Type)
          (funext X (_ ↦ B) g (x ↦ g (transport Type (T ↦ T) X X (refl X) x))
            (x ↦ refl g (inverse X (transport Type (T ↦ T) X X (refl X) x) x (transport_refl Type (T ↦ T) X x))))))
      Y p g

def maps_into_paths_equiv (B : Type) (s t : MapsInto B)
  : Equiv (Id (MapsInto B) s t) (Σ (Equiv (s .fst) (t .fst)) (e ↦ Id (s .fst → B) (s .snd) (x ↦ t .snd (e .map x))))
  ≔ compose_equiv (Id (MapsInto B) s t) (SigmaPath Type (T ↦ T → B) s t)
      (Σ (Equiv (s .fst) (t .fst)) (e ↦ Id (s .fst → B) (s .snd) (x ↦ t .snd (e .map x))))
      (canonical_inverse_equiv (SigmaPath Type (T ↦ T → B) s t) (Id (MapsInto B) s t)
        (sigma_path_equiv Type (T ↦ T → B) s t))
      ((w ↦ (transport_univalence_equiv (s .fst) (t .fst) .map (w .fst),
          domain_pathover_equiv (s .fst) (t .fst) B (w .fst) (s .snd) (t .snd) .map (w .snd))),
       sigma_over_equivalence_isequiv (Id Type (s .fst) (t .fst)) (Equiv (s .fst) (t .fst))
        (p ↦ Id (T ↦ T → B) p (s .snd) (t .snd))
        (transport_univalence_equiv (s .fst) (t .fst))
        (e ↦ Id (s .fst → B) (s .snd) (x ↦ t .snd (e .map x)))
        (p ↦ domain_pathover_equiv (s .fst) (t .fst) B p (s .snd) (t .snd)))

def unit_automorphisms_contractible : isContr (Equiv Unit Unit)
  ≔ (identity_equiv Unit, e ↦ equiv_homotopy Unit Unit e (identity_equiv Unit) (u ↦ unit_prop (e .map u) u))

def contractible_factor_equiv (A P : Type) (h : isContr A) : Equiv (Σ A (_ ↦ P)) P
  ≔ quasi_inverse_equiv (Σ A (_ ↦ P)) P (w ↦ w .snd) (p ↦ (h .center, p))
      (w ↦ (inverse A (w .fst) (h .center) (h .contract (w .fst)), refl (w .snd))) (p ↦ refl p)

{` The identity type of one-point coverings: (1, cst_b) = (1, cst_z) ≃ (b = z). `}
def unit_cover_paths_equiv (C : CircleSignature) (b z : C .carrier)
  : Equiv (Id (Coverings (C .carrier)) (circle_unit_cover C b) (circle_unit_cover C z)) (Id (C .carrier) b z)
  ≔ let B ≔ C .carrier in
    let cb ≔ circle_unit_cover C b in let cz ≔ circle_unit_cover C z in
    let bb ≔ coverings_bundle_equiv B in
    let s ≔ ((Unit, constant Unit B b) : MapsInto B) in let t ≔ ((Unit, constant Unit B z) : MapsInto B) in
    compose_equiv (Id (Coverings B) cb cz) (Id (BundledCovering B) (bb .map cb) (bb .map cz)) (Id B b z)
      (equivalence_on_paths (Coverings B) (BundledCovering B) bb cb cz)
      (compose_equiv (Id (BundledCovering B) (bb .map cb) (bb .map cz)) (Id (MapsInto B) s t) (Id B b z)
        (subtype_path_equiv (MapsInto B) (CoveringProperty B) (covering_property_prop B) (bb .map cb) (bb .map cz))
        (compose_equiv (Id (MapsInto B) s t) (Σ (Equiv Unit Unit) (_ ↦ Id (Unit → B) (constant Unit B b) (constant Unit B z)))
          (Id B b z)
          (maps_into_paths_equiv B s t)
          (compose_equiv (Σ (Equiv Unit Unit) (_ ↦ Id (Unit → B) (constant Unit B b) (constant Unit B z)))
            (Id (Unit → B) (constant Unit B b) (constant Unit B z)) (Id B b z)
            (contractible_factor_equiv (Equiv Unit Unit) (Id (Unit → B) (constant Unit B b) (constant Unit B z))
              unit_automorphisms_contractible)
            (equivalence_on_paths (Unit → B) B (unit_evaluation_equiv B) (constant Unit B b) (constant Unit B z)))))

{` The fiber of (1, cst_–) at (1, cst_base) is Σ_{z:S¹}(base = z), contractible. `}
def circle_unit_cover_base_fiber_contractible (C : CircleSignature)
  : isContr (BookFiber (C .carrier) (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
      (circle_unit_cover_component C) (circle_unit_cover_component C (C .base)))
  ≔ let B ≔ C .carrier in let K ≔ NativeComponent (Coverings B) (circle_unit_cover C (C .base)) in
    let L ≔ circle_unit_cover_component C in
    contractible_domain_of_equiv (BookFiber B K L (L (C .base))) (Σ B (z ↦ Id B (C .base) z))
      (family_equiv B (z ↦ Id K (L (C .base)) (L z)) (z ↦ Id B (C .base) z)
        (z ↦ compose_equiv (Id K (L (C .base)) (L z))
          (Id (Coverings B) (circle_unit_cover C (C .base)) (circle_unit_cover C z)) (Id B (C .base) z)
          (subtype_path_equiv (Coverings B) (c ↦ Mere (Id (Coverings B) (circle_unit_cover C (C .base)) c))
            (c ↦ mere_isprop (Id (Coverings B) (circle_unit_cover C (C .base)) c)) (L (C .base)) (L z))
          (unit_cover_paths_equiv C (C .base) z)))
      (native_contraction (Σ B (z ↦ Id B (C .base) z)) (book_pathspace_contractible B (C .base)))

{` Hence (1, cst_–) : S¹ → SetBundle(S¹)_(1, cst_base) is an equivalence. `}
def circle_unit_cover_component_is_equiv (C : CircleSignature)
  : BookIsEquiv (C .carrier) (NativeComponent (Coverings (C .carrier)) (circle_unit_cover C (C .base)))
      (circle_unit_cover_component C)
  ≔ let B ≔ C .carrier in let K ≔ NativeComponent (Coverings B) (circle_unit_cover C (C .base)) in
    let L ≔ circle_unit_cover_component C in
    w ↦ mere_rec (Id K (L (C .base)) w) (BookIsContr (BookFiber B K L w)) (book_iscontr_isprop (BookFiber B K L w))
      (q ↦ transport K (v ↦ BookIsContr (BookFiber B K L v)) (L (C .base)) w q
        (book_contraction (BookFiber B K L (L (C .base))) (circle_unit_cover_base_fiber_contractible C)))
      (native_component_connected (Coverings B) (circle_unit_cover C (C .base)) .snd (L (C .base)) w)

{` The first proof of thm:S1bysymmetries, assembled: c is an equivalence. `}
def circle_infinite_cycle_map_first_proof (C : CircleSignature)
  : BookIsEquiv (C .carrier) InfiniteCycles (circle_infinite_cycle_map C)
  ≔ let B ≔ C .carrier in
    equiv_inverse_map (BookIsEquiv B InfiniteCycles (circle_infinite_cycle_map C))
      (BookIsEquiv B (NativeComponent (B → Type) (Representable B (C .base))) (circle_universal_family_map C))
      (circle_first_proof_c_iff_universal_family C)
      (equiv_inverse_map
        (BookIsEquiv B (NativeComponent (B → Type) (Representable B (C .base))) (circle_universal_family_map C))
        (BookIsEquiv B (NativeComponent (Coverings B) (circle_unit_cover C (C .base))) (circle_unit_cover_component C))
        (circle_first_proof_universal_family_iff_unit_cover C)
        (circle_unit_cover_component_is_equiv C))

{` Instantiations at the circle constructed in modules 220–223. `}
def S1_circle_family_component_equiv
  : Equiv (NativeComponent (constructed_circle .carrier → Type)
      (Representable (constructed_circle .carrier) (constructed_circle .base))) InfiniteCycles
  ≔ circle_family_component_equiv constructed_circle

def S1_circle_first_proof_right_triangle
  : Id (constructed_circle .carrier → InfiniteCycles)
      (compose (constructed_circle .carrier)
        (NativeComponent (constructed_circle .carrier → Type) (Representable (constructed_circle .carrier) (constructed_circle .base)))
        InfiniteCycles (circle_family_infinite_map constructed_circle) (circle_universal_family_map constructed_circle))
      (circle_infinite_cycle_map constructed_circle)
  ≔ circle_first_proof_right_triangle constructed_circle

def S1_circle_unit_cover_component_is_equiv
  : BookIsEquiv (constructed_circle .carrier)
      (NativeComponent (Coverings (constructed_circle .carrier)) (circle_unit_cover constructed_circle (constructed_circle .base)))
      (circle_unit_cover_component constructed_circle)
  ≔ circle_unit_cover_component_is_equiv constructed_circle

def S1_circle_infinite_cycle_map_first_proof
  : BookIsEquiv (constructed_circle .carrier) InfiniteCycles (circle_infinite_cycle_map constructed_circle)
  ≔ circle_infinite_cycle_map_first_proof constructed_circle

{` Part 4. The book's inverse h in thm:fiber-cdg and the sketch before it: circle.tex:2906-2915, 3000-3045. `}

{` circle.tex:3025-3037 (implementation of thm:fiber-cdg): "e′ : Fin m × V → X,
   e′(k,v) :≡ t^k(v), which preserves cycle structure: t e′ = e′ ᵐ√(t^m).
   The map e′ is an equivalence if H_t ⊆ H_{ᵐ√(t^m)}, by xca:map-of-cycles.
   So let n : ℤ, and assume that t^n = id_X.  Then P implies that we may write
   n = qm ...".  Here V is a class of X/m of an ARBITRARY cycle (X,t); module
   272 proved the equivalence only for infinite cycles. `}

{` (t^m restricted to V)^q = id when t^(qm) = id. `}
def class_power_period (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (q : Int)
  (p : PowerPeriod (c .fst .fst .fst) (c .fst .snd) (int_mul q (pos. (suc. n))))
  : PowerPeriod (ClassCarrier n c V) (class_permutation n c V) q
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let M ≔ mod_power n X t in
    let C ≔ ClassCarrier n c V in let P ≔ class_permutation n c V in
    funext C (_ ↦ C) (permutation_power C P q) (identity C) (w ↦
      subtype_equal X (x ↦ V .fst x .fst) (x ↦ V .fst x .snd) (permutation_power C P q w) w
        (concat X (permutation_power C P q w .fst) (permutation_power X M q (w .fst)) (w .fst)
          (class_power_first n c V q w)
          (concat X (permutation_power X M q (w .fst)) (permutation_power X t (int_mul (pos. (suc. n)) q) (w .fst)) (w .fst)
            (inverse X (permutation_power X t (int_mul (pos. (suc. n)) q) (w .fst)) (permutation_power X M q (w .fst))
              (permutation_power_scaled X t (suc. n) q (w .fst)))
            (concat X (permutation_power X t (int_mul (pos. (suc. n)) q) (w .fst))
              (permutation_power X t (int_mul q (pos. (suc. n))) (w .fst)) (w .fst)
              (refl ((z ↦ permutation_power X t z (w .fst)) : Int → X) (int_mul_comm (pos. (suc. n)) q))
              (happly X (_ ↦ X) (permutation_power X t (int_mul q (pos. (suc. n)))) (identity X) p (w .fst))))))

{` "So let n : ℤ, and assume that t^n = id_X.  Then P implies ... = id_{Fin m × V}":
   under P, H_t ⊆ H_{ᵐ√(t^m)}. `}
def class_unwind_periods (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : PeriodInclusion (c .fst .fst .fst) (Product (Fin (suc. n)) (ClassCarrier n c V)) (c .fst .snd)
      (root_finite_equiv n (ClassCarrier n c V) (class_permutation n c V))
  ≔ let C ≔ ClassCarrier n c V in let F ≔ Product (Fin (suc. n)) C in
    let R ≔ root_finite_equiv n C (class_permutation n c V) in
    z hz ↦ mere_rec (MultipleWitness (suc. n) z) (PowerPeriod F R z)
      (power_period_prop F (sigma_set (Fin (suc. n)) (_ ↦ C) (fin_set (suc. n)) (_ ↦ class_carrier_set n c V)) R z)
      (w ↦ transport Int (PowerPeriod F R) (int_mul (w .fst) (pos. (suc. n))) z
        (inverse Int z (int_mul (w .fst) (pos. (suc. n))) (w .snd))
        (root_period_from_scaled n C (class_permutation n c V) (w .fst)
          (class_power_period n c V (w .fst)
            (transport Int (PowerPeriod (c .fst .fst .fst) (c .fst .snd)) z (int_mul (w .fst) (pos. (suc. n))) (w .snd) hz))))
      (pr z hz)

{` "The map e′ is an equivalence if H_t ⊆ H_{ᵐ√(t^m)}", for any cycle (X,t). `}
def class_unwind_is_equiv_of_periods (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  (back : PeriodInclusion (c .fst .fst .fst) (Product (Fin (suc. n)) (ClassCarrier n c V)) (c .fst .snd)
    (root_finite_equiv n (ClassCarrier n c V) (class_permutation n c V)))
  : BookIsEquiv (Product (Fin (suc. n)) (ClassCarrier n c V)) (c .fst .fst .fst) (class_unwind n c V)
  ≔ let C ≔ ClassCarrier n c V in
    book_equivalence (Product (Fin (suc. n)) C) (c .fst .fst .fst)
      (cycle_map_equiv (Product (Fin (suc. n)) C) (c .fst .fst .fst)
        (sigma_set (Fin (suc. n)) (_ ↦ C) (fin_set (suc. n)) (_ ↦ class_carrier_set n c V))
        (c .fst .fst .snd)
        (root_finite_equiv n C (class_permutation n c V)) (c .fst .snd)
        (root_finite_cyclic n C (class_permutation n c V) (class_cyclic n c V))
        (c .snd)
        (class_unwind n c V, class_unwind_commutes n c V) back) .equiv

{` e′ as an equivalence for every cycle satisfying P. `}
def class_unwind_general_equiv (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : Equiv (Product (Fin (suc. n)) (ClassCarrier n c V)) (c .fst .fst .fst)
  ≔ let C ≔ ClassCarrier n c V in
    cycle_map_equiv (Product (Fin (suc. n)) C) (c .fst .fst .fst)
      (sigma_set (Fin (suc. n)) (_ ↦ C) (fin_set (suc. n)) (_ ↦ class_carrier_set n c V))
      (c .fst .fst .snd)
      (root_finite_equiv n C (class_permutation n c V)) (c .fst .snd)
      (root_finite_cyclic n C (class_permutation n c V) (class_cyclic n c V))
      (c .snd)
      (class_unwind n c V, class_unwind_commutes n c V) (class_unwind_periods n c pr V)

def class_unwind_is_equiv (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : BookIsEquiv (Product (Fin (suc. n)) (ClassCarrier n c V)) (c .fst .fst .fst) (class_unwind n c V)
  ≔ class_unwind_is_equiv_of_periods n c V (class_unwind_periods n c pr V)

{` circle.tex:3012-3024: "to define the function h : P × X/m → cdg_m⁻¹(X,t),
   fix an equivalence class V of X/m, and assume that m divides the order of t
   ... Then (V,t^m) is a cycle.  We also need an identification
   (X,t) = cdg_m(V,t^m) ≡ (Fin m × V, ᵐ√(t^m)).  This we define via ... e′".
   The cycle (V,t^m) is class_cycle (module 270). `}
def class_unwind_iso (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : PermutationIsomorphisms (cycle_root n (class_cycle n c V) .fst) (c .fst)
  ≔ (class_unwind_general_equiv n c pr V, class_unwind_commutes n c V)

def class_unwind_path (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : Id Cycles (cycle_root n (class_cycle n c V)) c
  ≔ equiv_inverse_map (Id Cycles (cycle_root n (class_cycle n c V)) c)
      (PermutationIsomorphisms (cycle_root n (class_cycle n c V) .fst) (c .fst))
      (cycle_paths_equiv (cycle_root n (class_cycle n c V)) c) (class_unwind_iso n c pr V)

{` The map h of thm:fiber-cdg: (pr, V) ↦ ((V, t^m), e′⁻¹). `}
def root_fiber_inverse_map (n : Nat) (c : Cycles)
  (b : Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))) : RootFiber n c
  ≔ (class_cycle n c (b .snd),
     inverse Cycles (cycle_root n (class_cycle n c (b .snd))) c (class_unwind_path n c (b .fst) (b .snd)))

{` The identification of h(pr,V) evaluates as e′⁻¹. `}
def root_fiber_inverse_evaluate (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (z : Product (Fin (suc. n)) (ClassCarrier n c V))
  : Id (Product (Fin (suc. n)) (ClassCarrier n c V))
      (cycle_path_evaluate c (cycle_root n (class_cycle n c V))
        (inverse Cycles (cycle_root n (class_cycle n c V)) c (class_unwind_path n c pr V)) (class_unwind n c V z)) z
  ≔ let r ≔ cycle_root n (class_cycle n c V) in let p ≔ class_unwind_path n c pr V in
    let F ≔ Product (Fin (suc. n)) (ClassCarrier n c V) in
    concat F (cycle_path_evaluate c r (inverse Cycles r c p) (class_unwind n c V z))
      (cycle_path_evaluate c r (inverse Cycles r c p) (cycle_path_evaluate r c p z)) z
      (refl (cycle_path_evaluate c r (inverse Cycles r c p))
        (inverse (c .fst .fst .fst) (cycle_path_evaluate r c p z) (class_unwind n c V z)
          (iso_path_evaluate r c (class_unwind_iso n c pr V) z)))
      (cycle_path_evaluate_inverse r c p z)

{` circle.tex:3044: "Straight from these definitions, we see that g∘h = id." `}
def root_fiber_map_inverse_section (n : Nat) (c : Cycles)
  (b : Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
  : Id (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
      (root_fiber_map n c (root_fiber_inverse_map n c b)) b
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in
    let pr ≔ b .fst in let V ≔ b .snd in
    let w ≔ root_fiber_inverse_map n c b in
    let Ve ≔ root_fiber_class n c w in
    let F ≔ Product (Fin (suc. n)) (ClassCarrier n c V) in
    (root_fiber_condition_prop n c (root_path_condition n c (w .fst) (w .snd)) pr,
     mere_rec (BookFiber X Q (quotient_class X R) V) (Id Q Ve V) (quotient_set X R Ve V)
       (a ↦
         let ha ≔ quotient_class_property X R V (a .fst) .map (a .snd) in
         let z0 : F ≔ (inr. star., (a .fst, ha)) in
         concat Q Ve (quotient_class X R (a .fst)) V
           (quotient_path_of_member X R Ve (a .fst)
             (equiv_inverse_map (Ve .fst (a .fst) .fst)
               (Id (Fin (suc. n)) (cycle_path_evaluate c (cycle_root n (w .fst)) (w .snd) (a .fst) .fst) (inr. star.))
               (root_fiber_class_members n c w (a .fst))
               (refl ((u ↦ u .fst) : F → Fin (suc. n)) (root_fiber_inverse_evaluate n c pr V z0))))
           (inverse Q V (quotient_class X R (a .fst)) (a .snd)))
       (quotient_surjective X R V))

{` Paths of cycles are determined by their evaluations. `}
def cycle_path_evaluation_injective (a b : Cycles) (p q : Id Cycles a b)
  (h : (x : a .fst .fst .fst) → Id (b .fst .fst .fst) (cycle_path_evaluate a b p x) (cycle_path_evaluate a b q x))
  : Id (Id Cycles a b) p q
  ≔ let A ≔ a .fst .fst .fst in let B ≔ b .fst .fst .fst in
    let E ≔ cycle_paths_equiv a b in
    equivalence_injective (Id Cycles a b) (PermutationIsomorphisms (a .fst) (b .fst)) E p q
      (subtype_equal (Equiv A B) (i ↦ Commutes A B (a .fst .snd) (b .fst .snd) (i .map))
        (i ↦ commutes_prop A B (b .fst .fst .snd) (a .fst .snd) (b .fst .snd) (i .map))
        (E .map p) (E .map q)
        (equiv_path A B (E .map p .fst) (E .map q .fst) (funext A (_ ↦ B) (E .map p .fst .map) (E .map q .fst .map) h)))

{` Two elements (d1,p1), (d2,p2) of cdg_m⁻¹(X,t) are identified by a path
   a : d1 = d2 whose root, composed with p1, evaluates like p2. `}
def root_fiber_path_by_evaluation (n : Nat) (c : Cycles) (d1 : Cycles) (p1 : Id Cycles c (cycle_root n d1))
  (d2 : Cycles) (a : Id Cycles d1 d2) (p2 : Id Cycles c (cycle_root n d2))
  (h : (x : c .fst .fst .fst) → Id (Product (Fin (suc. n)) (d2 .fst .fst .fst))
      (cycle_path_evaluate c (cycle_root n d2) p2 x)
      (cycle_path_evaluate c (cycle_root n d1) p1 x .fst,
       cycle_path_evaluate d1 d2 a (cycle_path_evaluate c (cycle_root n d1) p1 x .snd)))
  : Id (RootFiber n c) (d1, p1) (d2, p2)
  ≔ J Cycles d1
      (d2 a ↦ (p2 : Id Cycles c (cycle_root n d2))
        → ((x : c .fst .fst .fst) → Id (Product (Fin (suc. n)) (d2 .fst .fst .fst))
            (cycle_path_evaluate c (cycle_root n d2) p2 x)
            (cycle_path_evaluate c (cycle_root n d1) p1 x .fst,
             cycle_path_evaluate d1 d2 a (cycle_path_evaluate c (cycle_root n d1) p1 x .snd)))
        → Id (RootFiber n c) (d1, p1) (d2, p2))
      (p2 h ↦
        let F ≔ Product (Fin (suc. n)) (d1 .fst .fst .fst) in
        (refl d1, cycle_path_evaluation_injective c (cycle_root n d1) p1 p2 (x ↦
          let v ≔ cycle_path_evaluate c (cycle_root n d1) p1 x in
          inverse F (cycle_path_evaluate c (cycle_root n d1) p2 x) v
            (concat F (cycle_path_evaluate c (cycle_root n d1) p2 x)
              (v .fst, cycle_path_evaluate d1 d1 (refl d1) (v .snd)) v
              (h x)
              (refl (v .fst), transport_refl Type (Y ↦ Y) (d1 .fst .fst .fst) (v .snd))))))
      d2 a p2 h

{` The m-th root is natural in maps commuting with the permutations. `}
def root_finite_natural (n : Nat) (A B : Type) (e : A → A) (f : B → B) (h : A → B)
  (hc : (a : A) → Id B (h (e a)) (f (h a))) (k : Fin (suc. n)) (a : A)
  : Id (Product (Fin (suc. n)) B)
      (root_finite n A e (k, a) .fst, h (root_finite n A e (k, a) .snd)) (root_finite n B f (k, h a))
  ≔ let FB ≔ Product (Fin (suc. n)) B in
    let side ≔ ((w ↦ (w .fst, h (w .snd))) : Product (Fin (suc. n)) A → FB) in
    let r ≔ fin_book_below_equiv (suc. n) .map k in
    match le_split (r .fst) n (lt_from_book (r .fst) (suc. n) (r .snd)) [
    | inl. small ↦
        concat FB (side (root_finite n A e (k, a))) (finite_fin_successor n .map k, h a) (root_finite n B f (k, h a))
          (refl side (root_finite_small n A e k small a))
          (inverse FB (root_finite n B f (k, h a)) (finite_fin_successor n .map k, h a)
            (root_finite_small n B f k small (h a)))
    | inr. last ↦
        concat FB (side (root_finite n A e (k, a))) (inr. star., f (h a)) (root_finite n B f (k, h a))
          (concat FB (side (root_finite n A e (k, a))) (inr. star., h (e a)) (inr. star., f (h a))
            (refl side (root_finite_last n A e k last a))
            (refl (inr. star. : Fin (suc. n)), hc a))
          (inverse FB (root_finite n B f (k, h a)) (inr. star., f (h a)) (root_finite_last n B f k last (h a))) ]

{` For (Y,u,e) in the fiber, the class V_e with t^m is isomorphic to (Y,u):
   v ↦ snd(e(v)), with inverse y ↦ e⁻¹(0,y). `}
def root_fiber_class_restrict (n : Nat) (c : Cycles) (w : RootFiber n c)
  (v : ClassCarrier n c (root_fiber_class n c w)) : w .fst .fst .fst .fst
  ≔ cycle_path_evaluate c (cycle_root n (w .fst)) (w .snd) (v .fst) .snd

def root_fiber_class_embed (n : Nat) (c : Cycles) (w : RootFiber n c) (y : w .fst .fst .fst .fst)
  : ClassCarrier n c (root_fiber_class n c w)
  ≔ let X ≔ c .fst .fst .fst in let F ≔ Product (Fin (suc. n)) (w .fst .fst .fst .fst) in
    let E ≔ cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst in
    let x ≔ equiv_inverse_map X F E (inr. star., y) in
    (x, equiv_inverse_map (root_fiber_class n c w .fst x .fst) (Id (Fin (suc. n)) (E .map x .fst) (inr. star.))
          (root_fiber_class_members n c w x)
          (refl ((z ↦ z .fst) : F → Fin (suc. n)) (equiv_counit X F E (inr. star., y))))

def root_fiber_class_equiv (n : Nat) (c : Cycles) (w : RootFiber n c)
  : Equiv (ClassCarrier n c (root_fiber_class n c w)) (w .fst .fst .fst .fst)
  ≔ let X ≔ c .fst .fst .fst in let Y ≔ w .fst .fst .fst .fst in let F ≔ Product (Fin (suc. n)) Y in
    let E ≔ cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst in
    let Ve ≔ root_fiber_class n c w in
    quasi_inverse_equiv (ClassCarrier n c Ve) Y (root_fiber_class_restrict n c w) (root_fiber_class_embed n c w)
      (v ↦ subtype_equal X (x ↦ Ve .fst x .fst) (x ↦ Ve .fst x .snd)
        (root_fiber_class_embed n c w (root_fiber_class_restrict n c w v)) v
        (concat X (equiv_inverse_map X F E (inr. star., E .map (v .fst) .snd))
          (equiv_inverse_map X F E (E .map (v .fst))) (v .fst)
          (refl (equiv_inverse_map X F E)
            (((inverse (Fin (suc. n)) (E .map (v .fst) .fst) (inr. star.)
                (root_fiber_class_members n c w (v .fst) .map (v .snd)),
               refl (E .map (v .fst) .snd))) : Id F (inr. star., E .map (v .fst) .snd) (E .map (v .fst))))
          (equiv_retraction X F E (v .fst))))
      (y ↦ refl ((z ↦ z .snd) : F → Y) (equiv_counit X F E (inr. star., y)))

def root_fiber_class_commutes (n : Nat) (c : Cycles) (w : RootFiber n c)
  : Commutes (ClassCarrier n c (root_fiber_class n c w)) (w .fst .fst .fst .fst)
      (class_permutation n c (root_fiber_class n c w)) (w .fst .fst .snd) (root_fiber_class_restrict n c w)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let Y ≔ w .fst .fst .fst .fst in let u ≔ w .fst .fst .snd in let F ≔ Product (Fin (suc. n)) Y in
    let I ≔ cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) in
    let R ≔ root_finite_equiv n Y u in
    v ↦ refl ((z ↦ z .snd) : F → Y)
      (concat F (I .fst .map (permutation_power X t (pos. (suc. n)) (v .fst)))
        (permutation_power F R (pos. (suc. n)) (I .fst .map (v .fst)))
        (I .fst .map (v .fst) .fst, u .map (I .fst .map (v .fst) .snd))
        (permutation_power_intertwine X F t R (I .fst .map) (I .snd) (pos. (suc. n)) (v .fst))
        (root_finite_full_turn n Y (u .map) (I .fst .map (v .fst))))

def root_fiber_class_iso (n : Nat) (c : Cycles) (w : RootFiber n c)
  : PermutationIsomorphisms (class_cycle n c (root_fiber_class n c w) .fst) (w .fst .fst)
  ≔ (root_fiber_class_equiv n c w, root_fiber_class_commutes n c w)

{` The path (V_e, t^m) = (Y,u) given by the isomorphism above. `}
def root_fiber_class_path (n : Nat) (c : Cycles) (w : RootFiber n c)
  : Id Cycles (class_cycle n c (root_fiber_class n c w)) (w .fst)
  ≔ equiv_inverse_map (Id Cycles (class_cycle n c (root_fiber_class n c w)) (w .fst))
      (PermutationIsomorphisms (class_cycle n c (root_fiber_class n c w) .fst) (w .fst .fst))
      (cycle_paths_equiv (class_cycle n c (root_fiber_class n c w)) (w .fst)) (root_fiber_class_iso n c w)

{` The key step of h∘g = id: for (Y,u,e) in the fiber, e agrees with the
   composite of e′⁻¹ (for V = V_e) and the isomorphism V_e ≅ Y. Both are maps
   of cycles (X,t) → (Fin m × Y, ᵐ√u) that agree on V_e, hence everywhere. `}
def root_fiber_retraction_agree (n : Nat) (c : Cycles) (w : RootFiber n c) (pr : RootFiberCondition n c)
  (x : c .fst .fst .fst)
  : Id (Product (Fin (suc. n)) (w .fst .fst .fst .fst))
      (cycle_path_evaluate c (cycle_root n (w .fst)) (w .snd) x)
      (cycle_path_evaluate c (cycle_root n (class_cycle n c (root_fiber_class n c w)))
         (inverse Cycles (cycle_root n (class_cycle n c (root_fiber_class n c w))) c
           (class_unwind_path n c pr (root_fiber_class n c w))) x .fst,
       cycle_path_evaluate (class_cycle n c (root_fiber_class n c w)) (w .fst) (root_fiber_class_path n c w)
         (cycle_path_evaluate c (cycle_root n (class_cycle n c (root_fiber_class n c w)))
           (inverse Cycles (cycle_root n (class_cycle n c (root_fiber_class n c w))) c
             (class_unwind_path n c pr (root_fiber_class n c w))) x .snd))
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let d ≔ w .fst in let p ≔ w .snd in
    let Y ≔ d .fst .fst .fst in let u ≔ d .fst .snd in
    let Fd ≔ Product (Fin (suc. n)) Y in
    let hFd ≔ cycle_root n d .fst .fst .snd in
    let Rd ≔ root_finite_equiv n Y u in
    let Ve ≔ root_fiber_class n c w in
    let C ≔ ClassCarrier n c Ve in
    let D ≔ class_cycle n c Ve in
    let FD ≔ Product (Fin (suc. n)) C in
    let q ≔ inverse Cycles (cycle_root n D) c (class_unwind_path n c pr Ve) in
    let I ≔ cycle_paths_equiv c (cycle_root n d) .map p in
    let J0 ≔ cycle_paths_equiv c (cycle_root n D) .map q in
    let alpha ≔ root_fiber_class_restrict n c w in
    let a ≔ root_fiber_class_path n c w in
    let side ≔ ((z ↦ (z .fst, alpha (z .snd))) : FD → Fd) in
    let M1 : PermutationMap X Fd t Rd ≔ (I .fst .map, I .snd) in
    let M2 : PermutationMap X Fd t Rd ≔
      (x ↦ side (J0 .fst .map x),
       x ↦ concat Fd (side (J0 .fst .map (t .map x)))
         (side (root_finite n C (class_permutation n c Ve .map) (J0 .fst .map x)))
         (Rd .map (side (J0 .fst .map x)))
         (refl side (J0 .snd x))
         (root_finite_natural n C Y (class_permutation n c Ve .map) (u .map) alpha (root_fiber_class_commutes n c w)
           (J0 .fst .map x .fst) (J0 .fst .map x .snd))) in
    mere_rec C (Id Fd (I .fst .map x) (J0 .fst .map x .fst, cycle_path_evaluate D d a (J0 .fst .map x .snd)))
      (hFd (I .fst .map x) (J0 .fst .map x .fst, cycle_path_evaluate D d a (J0 .fst .map x .snd)))
      (v0 ↦
        let x0 ≔ v0 .fst in
        let z0 : FD ≔ (inr. star., v0) in
        let agree0 : Id Fd (M1 .fst x0) (M2 .fst x0)
          ≔ concat Fd (I .fst .map x0) (inr. star., I .fst .map x0 .snd) (side (J0 .fst .map x0))
              (root_fiber_class_members n c w x0 .map (v0 .snd), refl (I .fst .map x0 .snd))
              (inverse Fd (side (J0 .fst .map x0)) (inr. star., I .fst .map x0 .snd)
                (refl side (root_fiber_inverse_evaluate n c pr Ve z0))) in
        concat Fd (I .fst .map x) (side (J0 .fst .map x))
          (J0 .fst .map x .fst, cycle_path_evaluate D d a (J0 .fst .map x .snd))
          (cycle_map_value_unique X Fd hFd t Rd (c .snd) M1 M2 x0 agree0 x)
          (refl (J0 .fst .map x .fst),
           inverse Y (cycle_path_evaluate D d a (J0 .fst .map x .snd)) (alpha (J0 .fst .map x .snd))
             (iso_path_evaluate D d (root_fiber_class_iso n c w) (J0 .fst .map x .snd))))
      (class_cyclic n c Ve .fst)

{` circle.tex:3045: "We leave to the reader to check that h∘g = id." `}
def root_fiber_inverse_retraction (n : Nat) (c : Cycles) (w : RootFiber n c)
  : Id (RootFiber n c) (root_fiber_inverse_map n c (root_fiber_map n c w)) w
  ≔ let pr ≔ root_path_condition n c (w .fst) (w .snd) in
    let D ≔ class_cycle n c (root_fiber_class n c w) in
    root_fiber_path_by_evaluation n c D
      (inverse Cycles (cycle_root n D) c (class_unwind_path n c pr (root_fiber_class n c w)))
      (w .fst) (root_fiber_class_path n c w) (w .snd) (root_fiber_retraction_agree n c w pr)

{` thm:fiber-cdg by the book's route (lem:weq-iso): h is a two-sided inverse
   of g, hence both are equivalences. `}
def root_fiber_inverse_equiv (n : Nat) (c : Cycles)
  : Equiv (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))) (RootFiber n c)
  ≔ quasi_inverse_equiv (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))) (RootFiber n c)
      (root_fiber_inverse_map n c) (root_fiber_map n c)
      (root_fiber_map_inverse_section n c) (root_fiber_inverse_retraction n c)

def root_fiber_inverse_is_equiv (n : Nat) (c : Cycles)
  : BookIsEquiv (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))) (RootFiber n c)
      (root_fiber_inverse_map n c)
  ≔ book_equivalence (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))) (RootFiber n c)
      (root_fiber_inverse_equiv n c) .equiv

def root_fiber_map_is_equiv_by_inverse (n : Nat) (c : Cycles)
  : BookIsEquiv (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
      (root_fiber_map n c)
  ≔ book_equivalence (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
      (quasi_inverse_equiv (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
        (root_fiber_map n c) (root_fiber_inverse_map n c)
        (root_fiber_inverse_retraction n c) (root_fiber_map_inverse_section n c)) .equiv

{` circle.tex:2906-2915 (before thm:fiber-cdg, infinite cycles): "Let Y be an
   equivalence class of X/m ... Then (Y,t^m) is an infinite cycle and we can
   construct a natural identification i : (X,t) = (Fin m × Y, ᵐ√(t^m)), so that
   (Y,t^m,i) : cdg_m⁻¹(X,t).  The map Y ↦ (Y,t^m,i) is the intended
   equivalence."  For an infinite cycle P holds, and the sketched map is h(P,-). `}
def infinite_root_fiber_condition (n : Nat) (y : CycleComponent zero.) : RootFiberCondition n (y .fst)
  ≔ equiv_inverse_map (RootFiberCondition n (y .fst)) (OrderDivides (principal_order (suc. n)) (cycle_order (y .fst)))
      (root_fiber_condition_divides n (y .fst)) (infinite_component_divides n y)

def infinite_root_fiber_sketch (n : Nat) (y : CycleComponent zero.)
  (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd)) : RootFiber n (y .fst)
  ≔ root_fiber_inverse_map n (y .fst) (infinite_root_fiber_condition n y, V)

def infinite_root_fiber_sketch_is_equiv (n : Nat) (y : CycleComponent zero.)
  : BookIsEquiv (ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd)) (RootFiber n (y .fst))
      (infinite_root_fiber_sketch n y)
  ≔ let c ≔ y .fst in let Q ≔ ModQuotient n (c .fst .fst .fst) (c .fst .snd) in
    let P ≔ RootFiberCondition n c in let pr ≔ infinite_root_fiber_condition n y in
    book_equivalence Q (RootFiber n c)
      (quasi_inverse_equiv Q (RootFiber n c) (infinite_root_fiber_sketch n y) (w ↦ root_fiber_map n c w .snd)
        (V ↦ refl ((b ↦ b .snd) : Product P Q → Q) (root_fiber_map_inverse_section n c (pr, V)))
        (w ↦ concat (RootFiber n c) (infinite_root_fiber_sketch n y (root_fiber_map n c w .snd))
          (root_fiber_inverse_map n c (root_fiber_map n c w)) w
          (refl (root_fiber_inverse_map n c)
            (((root_fiber_condition_prop n c pr (root_fiber_map n c w .fst), refl (root_fiber_map n c w .snd)))
              : Id (Product P Q) (pr, root_fiber_map n c w .snd) (root_fiber_map n c w)))
          (root_fiber_inverse_retraction n c w))) .equiv

{` The same sketch with the book's fiber over Cyc₀, cdg_m : Cyc₀ → Cyc₀
   (circle.tex:2899-2901: "the fiber is Σ_{(Y,u):Cyc₀}((X,t) = (Fin m × Y, ᵐ√u))"),
   where (Y, t^m) lies in Cyc₀ by class_cycle_infinite (module 270). `}
def InfiniteRootFiber (n : Nat) (y : CycleComponent zero.) : Type
  ≔ BookFiber (CycleComponent zero.) (CycleComponent zero.) (cycle_root_component n zero.) y

def infinite_root_fiber_sketch_component (n : Nat) (y : CycleComponent zero.)
  (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd)) : InfiniteRootFiber n y
  ≔ ((class_cycle n (y .fst) V, class_cycle_infinite n y V),
     subtype_equal Cycles (x ↦ Mere (Id Cycles infinite_cycle x)) (x ↦ mere_isprop (Id Cycles infinite_cycle x))
       y (cycle_root_component n zero. (class_cycle n (y .fst) V, class_cycle_infinite n y V))
       (infinite_root_fiber_sketch n y V .snd))

{` Elements of the Cyc₀-fiber are identified by a path of cycles whose root,
   composed with the first identification, evaluates like the second. `}
def infinite_root_fiber_path (n : Nat) (y : CycleComponent zero.) (v1 : CycleComponent zero.)
  (p1 : Id (CycleComponent zero.) y (cycle_root_component n zero. v1))
  (d2 : Cycles) (a : Id Cycles (v1 .fst) d2) (m2 : Mere (Id Cycles infinite_cycle d2))
  (p2 : Id (CycleComponent zero.) y (cycle_root_component n zero. (d2, m2)))
  (h : (x : y .fst .fst .fst .fst) → Id (Product (Fin (suc. n)) (d2 .fst .fst .fst))
      (cycle_path_evaluate (y .fst) (cycle_root n d2) (p2 .fst) x)
      (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .fst,
       cycle_path_evaluate (v1 .fst) d2 a (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .snd)))
  : Id (InfiniteRootFiber n y) (v1, p1) ((d2, m2), p2)
  ≔ let M ≔ ((x ↦ Mere (Id Cycles infinite_cycle x)) : Cycles → Type) in
    let hM ≔ ((x ↦ mere_isprop (Id Cycles infinite_cycle x)) : (x : Cycles) → isProp (M x)) in
    let X ≔ y .fst .fst .fst .fst in
    J Cycles (v1 .fst)
      (d2 a ↦ (m2 : M d2) → (p2 : Id (CycleComponent zero.) y (cycle_root_component n zero. (d2, m2)))
        → ((x : X) → Id (Product (Fin (suc. n)) (d2 .fst .fst .fst))
            (cycle_path_evaluate (y .fst) (cycle_root n d2) (p2 .fst) x)
            (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .fst,
             cycle_path_evaluate (v1 .fst) d2 a (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .snd)))
        → Id (InfiniteRootFiber n y) (v1, p1) ((d2, m2), p2))
      (m2 ↦
        J (M (v1 .fst)) (v1 .snd)
          (m2 _ ↦ (p2 : Id (CycleComponent zero.) y (cycle_root_component n zero. (v1 .fst, m2)))
            → ((x : X) → Id (Product (Fin (suc. n)) (v1 .fst .fst .fst .fst))
                (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p2 .fst) x)
                (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .fst,
                 cycle_path_evaluate (v1 .fst) (v1 .fst) (refl (v1 .fst))
                   (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x .snd)))
            → Id (InfiniteRootFiber n y) (v1, p1) ((v1 .fst, m2), p2))
          (p2 h ↦
            let F ≔ Product (Fin (suc. n)) (v1 .fst .fst .fst .fst) in
            (refl v1,
             equivalence_injective (Id (CycleComponent zero.) y (cycle_root_component n zero. v1))
               (Id Cycles (y .fst) (cycle_root n (v1 .fst)))
               (subtype_path_equiv Cycles M hM y (cycle_root_component n zero. v1)) p1 p2
               (cycle_path_evaluation_injective (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) (p2 .fst) (x ↦
                 let v ≔ cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p1 .fst) x in
                 inverse F (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p2 .fst) x) v
                   (concat F (cycle_path_evaluate (y .fst) (cycle_root n (v1 .fst)) (p2 .fst) x)
                     (v .fst, cycle_path_evaluate (v1 .fst) (v1 .fst) (refl (v1 .fst)) (v .snd)) v
                     (h x)
                     (refl (v .fst), transport_refl Type (Y ↦ Y) (v1 .fst .fst .fst .fst) (v .snd)))))))
          m2 (hM (v1 .fst) (v1 .snd) m2))
      d2 a m2 p2 h

{` The book's sketched map Y ↦ (Y, t^m, i) : X/m → cdg_m⁻¹(X,t), with the
   fiber over Cyc₀, is an equivalence. `}
def infinite_root_fiber_sketch_component_is_equiv (n : Nat) (y : CycleComponent zero.)
  : BookIsEquiv (ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd)) (InfiniteRootFiber n y)
      (infinite_root_fiber_sketch_component n y)
  ≔ let c ≔ y .fst in let Q ≔ ModQuotient n (c .fst .fst .fst) (c .fst .snd) in
    let P ≔ RootFiberCondition n c in let pr ≔ infinite_root_fiber_condition n y in
    let forget ≔ ((a ↦ (a .fst .fst, a .snd .fst)) : InfiniteRootFiber n y → RootFiber n c) in
    book_equivalence Q (InfiniteRootFiber n y)
      (quasi_inverse_equiv Q (InfiniteRootFiber n y) (infinite_root_fiber_sketch_component n y)
        (a ↦ root_fiber_class n c (forget a))
        (V ↦ refl ((b ↦ b .snd) : Product P Q → Q) (root_fiber_map_inverse_section n c (pr, V)))
        (a ↦ let w ≔ forget a in
          infinite_root_fiber_path n y
            (class_cycle n c (root_fiber_class n c w), class_cycle_infinite n y (root_fiber_class n c w))
            (subtype_equal Cycles (x ↦ Mere (Id Cycles infinite_cycle x)) (x ↦ mere_isprop (Id Cycles infinite_cycle x))
              y (cycle_root_component n zero. (class_cycle n c (root_fiber_class n c w), class_cycle_infinite n y (root_fiber_class n c w)))
              (inverse Cycles (cycle_root n (class_cycle n c (root_fiber_class n c w))) c
                (class_unwind_path n c pr (root_fiber_class n c w))))
            (a .fst .fst) (root_fiber_class_path n c w) (a .fst .snd) (a .snd)
            (root_fiber_retraction_agree n c w pr))) .equiv

{` circle.tex:3000-3009 (proof of thm:fiber-cdg, with footnote): "the class
   V_e :≡ [e⁻¹(0,y)] : X/m, for any y : Y.  Note that this doesn't depend on
   y ... As a subset of X, V_e = {x : X | fst(e(x)) = 0}."  Module 140 defines
   V_e as the subset; it is the class of e⁻¹(0,y) for every y, so the book's
   definition agrees with it and does not depend on y. `}
def root_fiber_class_at (n : Nat) (c : Cycles) (w : RootFiber n c) (y : w .fst .fst .fst .fst)
  : Id (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (root_fiber_class n c w)
      (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
        (equiv_inverse_map (c .fst .fst .fst) (Product (Fin (suc. n)) (w .fst .fst .fst .fst))
          (cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst) (inr. star., y)))
  ≔ quotient_path_of_member (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
      (root_fiber_class n c w) (root_fiber_class_embed n c w y .fst) (root_fiber_class_embed n c w y .snd)

def root_fiber_class_independent (n : Nat) (c : Cycles) (w : RootFiber n c) (y y' : w .fst .fst .fst .fst)
  : Id (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
      (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
        (equiv_inverse_map (c .fst .fst .fst) (Product (Fin (suc. n)) (w .fst .fst .fst .fst))
          (cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst) (inr. star., y)))
      (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
        (equiv_inverse_map (c .fst .fst .fst) (Product (Fin (suc. n)) (w .fst .fst .fst .fst))
          (cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst) (inr. star., y')))
  ≔ let Q ≔ ModQuotient n (c .fst .fst .fst) (c .fst .snd) in
    let R ≔ mod_relation n (c .fst .fst .fst) (c .fst .snd) in
    let E ≔ cycle_paths_equiv c (cycle_root n (w .fst)) .map (w .snd) .fst in
    let F ≔ Product (Fin (suc. n)) (w .fst .fst .fst .fst) in
    concat Q (quotient_class (c .fst .fst .fst) R (equiv_inverse_map (c .fst .fst .fst) F E (inr. star., y)))
      (root_fiber_class n c w)
      (quotient_class (c .fst .fst .fst) R (equiv_inverse_map (c .fst .fst .fst) F E (inr. star., y')))
      (inverse Q (root_fiber_class n c w)
        (quotient_class (c .fst .fst .fst) R (equiv_inverse_map (c .fst .fst .fst) F E (inr. star., y)))
        (root_fiber_class_at n c w y))
      (root_fiber_class_at n c w y')

{` Part 5. Quotients X/m and the image of the class map: circle.tex:2897, 2993, 3096, 3375, 3381. `}

{` circle.tex:3096, "Uniqueness of e above also follows from the following
   two exercises."  xca:cancel-surjection is false as printed (module 40,
   surjection_cancellation_counterexample) and is not needed: the right
   triangle i = h e alone determines e, by xca:cancel-injection
   (cancel_injection, module 40). `}
def image_diagonal_unique_by_cancel_injection (A B X : Type) (f : A → B) (h : X → B) (hh : IsEmbedding X B h)
  (e e' : Image A B f → X)
  (beta : Id (Image A B f → B) (image_include A B f) (compose (Image A B f) X B h e))
  (beta' : Id (Image A B f → B) (image_include A B f) (compose (Image A B f) X B h e'))
  : Id (Image A B f → X) e e'
  ≔ let I ≔ Image A B f in
    equiv_inverse_map (Id (I → X) e e') (Id (I → B) (compose I X B h e) (compose I X B h e'))
      (cancel_injection X B I h hh e e')
      (concat (I → B) (compose I X B h e) (image_include A B f) (compose I X B h e')
        (inverse (I → B) (image_include A B f) (compose I X B h e) beta) beta')

{` The equivalences e : im(f) ≃ X of eqn:image-univ-prop with both triangles
   g = e p and i = h e, for a surjection g : A → X and an injection h. `}
def ImageDiamondEquivalences (A B X : Type) (f : A → B) (g : A → X) (h : X → B) : Type
  ≔ Σ (Equiv (Image A B f) X) (e ↦
      Product (Id (A → X) g (compose A (Image A B f) X (e .map) (image_factor A B f)))
        (Id (Image A B f → B) (image_include A B f) (compose (Image A B f) X B h (e .map))))

{` "one can construct a (unique) equivalence e": any two such equivalences are
   equal, using xca:cancel-injection only (the triangle g = e p is not used). `}
def image_diamond_equivalence_unique (A B X : Type) (f : A → B) (g : A → X) (h : X → B) (hh : IsEmbedding X B h)
  (u v : ImageDiamondEquivalences A B X f g h) : Id (Equiv (Image A B f) X) (u .fst) (v .fst)
  ≔ equiv_path (Image A B f) X (u .fst) (v .fst)
      (image_diagonal_unique_by_cancel_injection A B X f h hh (u .fst .map) (v .fst .map) (u .snd .snd) (v .snd .snd))

{` What survives of the second exercise: when X is a set, the restricted
   xca:cancel-surjection (cancel_surjection_into_set, module 40) shows that
   the left triangle g = e p alone also determines e. `}
def image_diagonal_unique_left_set (A B X : Type) (f : A → B) (hx : isSet X) (g : A → X)
  (e e' : Image A B f → X)
  (alpha : Id (A → X) g (compose A (Image A B f) X e (image_factor A B f)))
  (alpha' : Id (A → X) g (compose A (Image A B f) X e' (image_factor A B f)))
  : Id (Image A B f → X) e e'
  ≔ let I ≔ Image A B f in let p ≔ image_factor A B f in
    equiv_inverse_map (Id (I → X) e e') (Id (A → X) (precompose A I X p e) (precompose A I X p e'))
      (cancel_surjection_into_set A I X p (image_factor_surjective A B f) hx e e')
      (concat (A → X) (precompose A I X p e) g (precompose A I X p e')
        (inverse (A → X) g (precompose A I X p e) alpha) alpha')

{` circle.tex:2993, footnote of thm:fiber-cdg: "When X is a decidable set then
   LPO allows for a simpler formulation: Then P is either false, in which case
   cdg_m⁻¹(X,t) is empty, or true, in which case the preimage is X/m."
   LPO is the explicit hypothesis LimitedOmniscience of module 71; it decides
   the order of a decidable cycle (lpo_cycle_order_classification, module 77),
   and divisibility of natural numbers is decidable. `}
def nat_divides_multiple (d k : Nat) (v : NatDivides d k) : Multiples d (pos. k) .fst
  ≔ mere_rec (Σ Nat (q ↦ Id Nat k (mul q d))) (Multiples d (pos. k) .fst) (Multiples d (pos. k) .snd)
      (w ↦ mere (MultipleWitness d (pos. k)) (pos. (w .fst),
        concat Int (pos. k) (pos. (mul (w .fst) d)) (int_mul (pos. (w .fst)) (pos. d))
          (refl ((j ↦ pos. j) : Nat → Int) (w .snd)) (int_mul_naturals (w .fst) d))) v

def nat_divides_decidable (n k : Nat) : Decidable (NatDivides (suc. n) k)
  ≔ decidable_iff (Multiples (suc. n) (pos. k) .fst) (NatDivides (suc. n) k) (multiples_decidable n (pos. k))
      (m ↦ mere_rec (MultipleWitness (suc. n) (pos. k)) (NatDivides (suc. n) k) (nat_divides_prop (suc. n) k)
        (multiple_nat_divides (suc. n) k) m)
      (nat_divides_multiple (suc. n) k)

{` Under LPO, P ≔ (H_t ⊆ mZ) is decidable for a cycle on a decidable set. `}
def lpo_root_fiber_condition_decidable (lpo : LimitedOmniscience) (n : Nat) (c : DecidableCycles)
  : Decidable (RootFiberCondition n (c .fst))
  ≔ let u ≔ lpo_cycle_order_classification lpo c in
    let k ≔ u .fst in
    let D ≔ ((o ↦ OrderDivides (principal_order (suc. n)) o) : Order → Type) in
    decidable_iff (NatDivides (suc. n) k) (RootFiberCondition n (c .fst)) (nat_divides_decidable n k)
      (v ↦ equiv_inverse_map (RootFiberCondition n (c .fst)) (D (cycle_order (c .fst)))
        (root_fiber_condition_divides n (c .fst))
        (transport Order D (principal_order k) (cycle_order (c .fst))
          (inverse Order (cycle_order (c .fst)) (principal_order k) (u .snd))
          (equiv_inverse_map (D (principal_order k)) (NatDivides (suc. n) k) (principal_divides_equiv (suc. n) k) v)))
      (pr ↦ principal_divides_equiv (suc. n) k .map
        (transport Order D (cycle_order (c .fst)) (principal_order k) (u .snd)
          (root_fiber_condition_divides n (c .fst) .map pr)))

{` If P holds, the second component of the book's map g, (Y,u,e) ↦ V_e, is
   an equivalence cdg_m⁻¹(X,t) ≃ X/m (for any cycle). `}
def root_fiber_class_equiv_given (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  : BookIsEquiv (RootFiber n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (root_fiber_class n c)
  ≔ let Q ≔ ModQuotient n (c .fst .fst .fst) (c .fst .snd) in
    let P ≔ RootFiberCondition n c in
    book_equivalence (RootFiber n c) Q
      (compose_equiv (RootFiber n c) (Product P Q) Q
        (native_equivalence (RootFiber n c) (Product P Q) (root_fiber_equiv n c))
        (quasi_inverse_equiv (Product P Q) Q (z ↦ z .snd) (q ↦ (pr, q))
          (z ↦ (root_fiber_condition_prop n c pr (z .fst), refl (z .snd)))
          (q ↦ refl q))) .equiv

{` "P is either false, in which case cdg_m⁻¹(X,t) is empty, or true, in which
   case the preimage is X/m". `}
def RootFiberLPOAlternative (n : Nat) (c : Cycles) : Type
  ≔ Sum (Product (Not (RootFiberCondition n c)) (Not (RootFiber n c)))
      (Product (RootFiberCondition n c)
        (BookIsEquiv (RootFiber n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (root_fiber_class n c)))

def lpo_root_fiber_alternative (lpo : LimitedOmniscience) (n : Nat) (c : DecidableCycles)
  : RootFiberLPOAlternative n (c .fst)
  ≔ match lpo_root_fiber_condition_decidable lpo n c [
  | inl. pr ↦ inr. (pr, root_fiber_class_equiv_given n (c .fst) pr)
  | inr. np ↦ inl. (np, w ↦ np (root_path_condition n (c .fst) (w .fst) (w .snd))) ]

{` circle.tex:3379-3381, "For every infinite cycle (X,t), the set X/m has m
   elements, and the (−1)-image is readily identified with FinSet_m, the
   groupoid of m-element sets (def:groupoidFin)."  FinSet_m is the component
   Set_(Fin m) (BookFiniteSetsAt, module 186). `}
def infinite_quotient_fin_path (n : Nat) (u : CycleComponent zero.)
  : Mere (Id SetTypes (Fin (suc. n), fin_set (suc. n)) (infinite_quotient_set n u))
  ≔ let F : SetTypes ≔ (Fin (suc. n), fin_set (suc. n)) in
    let carrier ≔ ((c ↦ c .fst .fst) : Cycles → SetTypes) in
    mere_rec (Id Cycles (principal_cycle (suc. n)) (QuotientCycle n (u .fst)))
      (Mere (Id SetTypes F (infinite_quotient_set n u)))
      (mere_isprop (Id SetTypes F (infinite_quotient_set n u)))
      (p ↦ mere (Id SetTypes F (infinite_quotient_set n u))
        (concat SetTypes F (Remainder (suc. n), remainder_set (suc. n)) (infinite_quotient_set n u)
          (refl carrier (fin_remainder_cycle_path n)) (refl carrier p)))
      (infinite_quotient_cycle n u .snd)

{` The (−1)-image of –/m : Cyc₀ → Set is FinSet_m, as subtypes of Set: the
   map keeps the underlying set S. `}
def infinite_quotient_image_finsets (n : Nat)
  : Equiv (Image (CycleComponent zero.) SetTypes (infinite_quotient_set n)) (BookFiniteSetsAt (suc. n))
  ≔ let F : SetTypes ≔ (Fin (suc. n), fin_set (suc. n)) in
    let Fib ≔ ((S ↦ BookFiber (CycleComponent zero.) SetTypes (infinite_quotient_set n) S) : SetTypes → Type) in
    family_equiv SetTypes (S ↦ Mere (Fib S)) (S ↦ Mere (Id SetTypes F S))
      (S ↦ iff_equiv (Mere (Fib S)) (Mere (Id SetTypes F S)) (mere_isprop (Fib S)) (mere_isprop (Id SetTypes F S))
        (h ↦ mere_rec (Fib S) (Mere (Id SetTypes F S)) (mere_isprop (Id SetTypes F S))
          (w ↦ mere_rec (Id SetTypes F (infinite_quotient_set n (w .fst))) (Mere (Id SetTypes F S))
            (mere_isprop (Id SetTypes F S))
            (q ↦ mere (Id SetTypes F S)
              (concat SetTypes F (infinite_quotient_set n (w .fst)) S q
                (inverse SetTypes S (infinite_quotient_set n (w .fst)) (w .snd))))
            (infinite_quotient_fin_path n (w .fst)))
          h)
        (h ↦ mere_rec (Id SetTypes F S) (Mere (Fib S)) (mere_isprop (Fib S))
          (q ↦ mere_rec (Id SetTypes F (infinite_quotient_set n infinite_cycle_point)) (Mere (Fib S))
            (mere_isprop (Fib S))
            (r ↦ mere (Fib S) (infinite_cycle_point,
              concat SetTypes S F (infinite_quotient_set n infinite_cycle_point) (inverse SetTypes F S q) r))
            (infinite_quotient_fin_path n infinite_cycle_point))
          h))

def infinite_quotient_image_finsets_carrier (n : Nat)
  (z : Image (CycleComponent zero.) SetTypes (infinite_quotient_set n))
  : Id SetTypes (infinite_quotient_image_finsets n .map z .fst) (image_include (CycleComponent zero.) SetTypes (infinite_quotient_set n) z)
  ≔ refl (z .fst)

{` circle.tex:2896-2897, "let x ∼_m x' if and only if ∃_{r:ℤ}(x' = t^{mr}(x)).
   (Such an r is unique if it exists.)", for an infinite cycle (X,t). `}
def infinite_cycle_component_period_zero (y : CycleComponent zero.) (z : Int)
  (p : PowerPeriod (y .fst .fst .fst .fst) (y .fst .fst .snd) z) : Id Int z int_zero
  ≔ infinite_period_is_zero z
      (transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (y .fst)) (CyclePeriods infinite_cycle)
        (inverse (Subtypes Int) (CyclePeriods infinite_cycle) (CyclePeriods (y .fst))
          (cycle_paths_imply_periods infinite_cycle (y .fst) (y .snd))) p)

def infinite_mod_witness_prop (n : Nat) (y : CycleComponent zero.) (x x' : y .fst .fst .fst .fst)
  : isProp (ModWitness n (y .fst .fst .fst .fst) (y .fst .fst .snd) x x')
  ≔ let X ≔ y .fst .fst .fst .fst in let hX ≔ y .fst .fst .fst .snd in let t ≔ y .fst .fst .snd in
    let m : Int ≔ pos. (suc. n) in
    w w' ↦
      let a ≔ int_mul m (w .fst) in let b ≔ int_mul m (w' .fst) in
      let same : Id X (permutation_power X t a x) (permutation_power X t b x)
        ≔ concat X (permutation_power X t a x) x' (permutation_power X t b x)
            (inverse X x' (permutation_power X t a x) (w .snd)) (w' .snd) in
      let back : Id X (permutation_power X t (int_add a (int_neg b)) x) x
        ≔ calc
          permutation_power X t (int_add a (int_neg b)) x = permutation_power X t (int_neg b) (permutation_power X t a x)
            by permutation_power_add X t a (int_neg b) x
          = permutation_power X t (int_neg b) (permutation_power X t b x)
            by refl (permutation_power X t (int_neg b)) same
          = x by permutation_power_inverse X t b x ∎ in
      let diff_zero ≔ infinite_cycle_component_period_zero y (int_add a (int_neg b))
        (cycle_period_from_point X hX t (y .fst .snd) x (int_add a (int_neg b)) back) in
      let ab : Id Int a b ≔ calc
        a = int_add (int_sub a b) b by inverse Int (int_add (int_sub a b) b) a (int_sub_add a b)
        = int_add int_zero b by refl ((d ↦ int_add d b) : Int → Int) diff_zero
        = b by int_add_zero_left b ∎ in
      subtype_equal Int (r ↦ Id X x' (permutation_power X t (int_mul m r) x))
        (r ↦ hX x' (permutation_power X t (int_mul m r) x)) w w'
        (int_mul_cancel_pos n (w .fst) (w' .fst) (calc
          int_mul (w .fst) m = a by int_mul_comm (w .fst) m
          = b by ab
          = int_mul (w' .fst) m by int_mul_comm m (w' .fst) ∎))

{` circle.tex:3373-3377, "so we have a map –/m : Cyc₀ → Set, which we identify
   with the family R_m : S¹ → Set (def:RmtoS1) by precomposing with the
   equivalence c : S¹ → Cyc₀ from thm:S1bysymmetries."  Here c is the map of
   def:S1toC into InfCyc (circle_infinite_cycle_map, module 94) followed by the
   inverse of the forgetful equivalence Cyc₀ ≃ InfCyc (module 92), and R_m is
   power_circle_family (module 171).  Since c(loop) is the predecessor, the
   monodromy of –/m ∘ c is [x] ↦ [x−1]; the identification with R_m (monodromy
   the successor of Fin m) is the unique pointed one sending [0] to 0 on
   the inverted cycle. `}
def inverse_cycle_periods (c : Cycles) : Id (Subtypes Int) (CyclePeriods (cycle_inverse c)) (CyclePeriods c)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let ti ≔ canonical_inverse_equiv X X t in
    let inv ≔ ((x ↦ equiv_retraction X X t x) : (x : X) → Id X (ti .map (t .map x)) x) in
    funext Int (_ ↦ PropTypes) (CyclePeriods (cycle_inverse c)) (CyclePeriods c)
      (z ↦ proposition_extensionality (CyclePeriods (cycle_inverse c) z) (CyclePeriods c z)
        (p ↦ transport Int (PowerPeriod X t) (int_neg (int_neg z)) z (int_neg_neg z)
          (power_period_neg X t (int_neg z)
            (funext X (_ ↦ X) (permutation_power X t (int_neg z)) (identity X)
              (x ↦ concat X (permutation_power X t (int_neg z) x) (permutation_power X ti z x) x
                (inverse X (permutation_power X ti z x) (permutation_power X t (int_neg z) x)
                  (permutation_power_left_inverse X t ti inv z x))
                (happly X (_ ↦ X) (permutation_power X ti z) (identity X) p x)))))
        (p ↦ funext X (_ ↦ X) (permutation_power X ti z) (identity X)
          (x ↦ concat X (permutation_power X ti z x) (permutation_power X t (int_neg z) x) x
            (permutation_power_left_inverse X t ti inv z x)
            (happly X (_ ↦ X) (permutation_power X t (int_neg z)) (identity X) (power_period_neg X t z p) x))))

{` The explicit inverse of the forgetful equivalence Cyc₀ ≃ InfCyc. `}
def infinite_endomorphism_component_point (t : InfiniteCycles) : CycleComponent zero.
  ≔ (infinite_endomorphism_cycle t, infinite_endomorphism_cycle_component t)

def infinite_forget_inverse_point (t : InfiniteCycles)
  : Id (CycleComponent zero.) (equiv_inverse_map (CycleComponent zero.) InfiniteCycles infinite_cycle_forget_equiv t)
      (infinite_endomorphism_component_point t)
  ≔ inverse_at_known_point (CycleComponent zero.) InfiniteCycles infinite_cycle_forget_equiv
      (infinite_endomorphism_component_point t) t
      (subtype_equal Endomorphisms (s ↦ Mere (Id Endomorphisms integer_endomorphism s))
        (s ↦ mere_isprop (Id Endomorphisms integer_endomorphism s))
        (infinite_cycle_forget_equiv .map (infinite_endomorphism_component_point t)) t (refl (t .fst)))

{` The book's c : S¹ → Cyc₀ and the composite –/m ∘ c. `}
def book_circle_cycle_zero_map (C : CircleSignature) : C .carrier → CycleComponent zero.
  ≔ z ↦ equiv_inverse_map (CycleComponent zero.) InfiniteCycles infinite_cycle_forget_equiv (circle_infinite_cycle_map C z)

def circle_quotient_family (C : CircleSignature) (n : Nat) : C .carrier → SetTypes
  ≔ z ↦ infinite_quotient_set n (book_circle_cycle_zero_map C z)

{` –/m on InfCyc, as the quotient cycle (X/m, t̄). `}
def endomorphism_quotient_cycle (n : Nat) (t : InfiniteCycles) : Cycles
  ≔ QuotientCycle n (infinite_endomorphism_cycle t)

def endomorphism_quotient_set (n : Nat) (t : InfiniteCycles) : SetTypes
  ≔ endomorphism_quotient_cycle n t .fst .fst

def quotient_loop_permutation (n : Nat) (d : FreeLoop InfiniteCycles) : Permutations
  ≔ set_loop_permutation (endomorphism_quotient_set n (d .fst), refl (endomorphism_quotient_set n) (d .snd))

{` Transport of X/m along the predecessor loop c(loop) is [x] ↦ [x−1] = t̄⁻¹. `}
def quotient_predecessor_monodromy (n : Nat)
  : Id Permutations (quotient_loop_permutation n (infinite_endomorphism_point, infinite_predecessor_loop))
      (cycle_inverse (endomorphism_quotient_cycle n infinite_endomorphism_point) .fst)
  ≔ let pt ≔ infinite_endomorphism_point in
    let H ≔ infinite_endomorphism_cycle pt in
    let E ≔ H .fst .snd in
    let R ≔ mod_relation n Int E in
    let Q ≔ ModQuotient n Int E in
    let S ≔ endomorphism_quotient_set n pt in
    let tb ≔ quotient_successor_equiv n H in
    let tau ≔ set_paths_transport_equiv S S .map (refl (endomorphism_quotient_set n) infinite_predecessor_loop) in
    let ev ≔ endomorphism_path_evaluate integer_endomorphism integer_endomorphism (infinite_predecessor_loop .fst) in
    (refl S, equiv_homotopy Q Q tau (canonical_inverse_equiv Q Q tb)
      (quotient_prop_induction Int R (V ↦ Id Q (tau .map V) (equiv_inverse_map Q Q tb V))
        (V ↦ quotient_set Int R (tau .map V) (equiv_inverse_map Q Q tb V))
        (x ↦ concat Q (tau .map (quotient_class Int R x)) (quotient_class Int R (int_pred x))
          (equiv_inverse_map Q Q tb (quotient_class Int R x))
          (concat Q (tau .map (quotient_class Int R x)) (quotient_class Int R (ev x)) (quotient_class Int R (int_pred x))
            (quotient_cycle_ap_evaluate n InfiniteCycles infinite_endomorphism_cycle pt pt infinite_predecessor_loop x)
            (refl (quotient_class Int R)
              (concat Int (ev x) (int_add x (infinite_cycle_loop_coordinate infinite_predecessor_loop)) (int_pred x)
                (endomorphism_integer_loop_translation (infinite_predecessor_loop .fst) x)
                (refl (int_add x) infinite_predecessor_loop_coordinate))))
          (inverse Q (equiv_inverse_map Q Q tb (quotient_class Int R x)) (quotient_class Int R (int_pred x))
            (inverse_at_known_point Q Q tb (quotient_class Int R (int_pred x)) (quotient_class Int R x)
              (refl (quotient_class Int R) (int_succ_pred x)))))))

def endomorphism_quotient_standard (n : Nat) (t : InfiniteCycles)
  : Mere (Id Cycles (endomorphism_quotient_cycle n t) (finite_fin_cycle n))
  ≔ let G ≔ endomorphism_quotient_cycle n t in
    mere_rec (Id Cycles (finite_standard_cycle n) G) (Mere (Id Cycles G (finite_fin_cycle n)))
      (mere_isprop (Id Cycles G (finite_fin_cycle n)))
      (q ↦ mere (Id Cycles G (finite_fin_cycle n))
        (concat Cycles G (finite_standard_cycle n) (finite_fin_cycle n)
          (inverse Cycles (finite_standard_cycle n) G q)
          (inverse Cycles (finite_fin_cycle n) (finite_standard_cycle n) (fin_remainder_cycle_path n))))
      (quotient_cycle_standard n (infinite_endomorphism_cycle t)
        (infinite_component_divides n (infinite_endomorphism_component_point t)))

{` The pointed identification (Z/m, t̄⁻¹) = (Fin m, succ) with [0] ↦ 0. `}
def quotient_inverse_fin_path (n : Nat)
  : Id Cycles (cycle_inverse (endomorphism_quotient_cycle n infinite_endomorphism_point)) (finite_fin_cycle n)
  ≔ let G ≔ endomorphism_quotient_cycle n infinite_endomorphism_point in
    let H ≔ infinite_endomorphism_cycle infinite_endomorphism_point in
    cycle_periods_imply_pointed (cycle_inverse G) (finite_fin_cycle n)
      (concat (Subtypes Int) (CyclePeriods (cycle_inverse G)) (CyclePeriods G) (CyclePeriods (finite_fin_cycle n))
        (inverse_cycle_periods G)
        (cycle_paths_imply_periods G (finite_fin_cycle n) (endomorphism_quotient_standard n infinite_endomorphism_point)))
      (quotient_class Int (mod_relation n Int (H .fst .snd)) int_zero) (inr. star.) .center .fst

{` The monodromy of –/m ∘ c is that of R_m. `}
def circle_quotient_monodromy (C : CircleSignature) (n : Nat)
  : Id Permutations
      (circle_setfamilies_permutations C .map (z ↦ endomorphism_quotient_set n (circle_infinite_cycle_map C z)))
      (power_fiber_set n, finite_fin_successor n)
  ≔ let G ≔ endomorphism_quotient_cycle n infinite_endomorphism_point in
    let pt ≔ infinite_endomorphism_point in
    concat Permutations (quotient_loop_permutation n (circle_eval C InfiniteCycles (circle_infinite_cycle_map C)))
      (quotient_loop_permutation n (pt, infinite_predecessor_loop)) (power_fiber_set n, finite_fin_successor n)
      (refl (quotient_loop_permutation n) (circle_infinite_cycle_boundary C))
      (concat Permutations (quotient_loop_permutation n (pt, infinite_predecessor_loop)) (cycle_inverse G .fst)
        (finite_fin_cycle n .fst)
        (quotient_predecessor_monodromy n)
        (refl ((d ↦ d .fst) : Cycles → Permutations) (quotient_inverse_fin_path n)))

def circle_quotient_power_family_explicit (C : CircleSignature) (n : Nat)
  : Id (C .carrier → SetTypes) (z ↦ endomorphism_quotient_set n (circle_infinite_cycle_map C z)) (power_circle_family C n)
  ≔ let K ≔ ((z ↦ endomorphism_quotient_set n (circle_infinite_cycle_map C z)) : C .carrier → SetTypes) in
    equivalence_injective (C .carrier → SetTypes) Permutations (circle_setfamilies_permutations C) K (power_circle_family C n)
      (concat Permutations (circle_setfamilies_permutations C .map K) (power_fiber_set n, finite_fin_successor n)
        (circle_setfamilies_permutations C .map (power_circle_family C n))
        (circle_quotient_monodromy C n)
        (inverse Permutations (circle_setfamilies_permutations C .map (power_circle_family C n))
          (power_fiber_set n, finite_fin_successor n) (power_circle_monodromy C n)))

{` –/m ∘ c = R_m as families S¹ → Set. `}
def circle_quotient_power_family (C : CircleSignature) (n : Nat)
  : Id (C .carrier → SetTypes) (circle_quotient_family C n) (power_circle_family C n)
  ≔ let K ≔ ((z ↦ endomorphism_quotient_set n (circle_infinite_cycle_map C z)) : C .carrier → SetTypes) in
    concat (C .carrier → SetTypes) (circle_quotient_family C n) K (power_circle_family C n)
      (funext (C .carrier) (_ ↦ SetTypes) (circle_quotient_family C n) K
        (z ↦ refl (infinite_quotient_set n) (infinite_forget_inverse_point (circle_infinite_cycle_map C z))))
      (circle_quotient_power_family_explicit C n)
