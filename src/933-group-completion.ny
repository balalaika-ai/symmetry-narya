export "932-finite-families"

{` Chapter 9 (subgroups.tex), helper for lem:epi-surj (line 161) and
   con:monos-are-equalizers (line 204): every set S acts faithfully on a set
   T, in the form needed by the test homomorphisms of module 934. The book's
   draft embeds the coset set into a group A ("the free (abelian) group on
   G/H") and uses the left translations of A; we give the corresponding
   data directly: a set T with permutations τ_s (s : S) and a point t0 with
   τ_s(t0) = τ_s'(t0) ⇒ s = s'. T is the group completion of the free
   commutative monoid M(S) of module 932, presented by pairs (a, b) of
   finite S-labelled families modulo (a, b) ~ (c, d) iff
   ∃ k, [(a + d) + k] = [(c + b) + k] in M(S); τ_s(a, b) = (a + [s], b),
   t0 = (0, 0). Faithfulness is the cancellation
   [s] + K ≅ [s'] + K ⇒ s = s' for finite families K, proved by following
   the orbit of the extra point under the isomorphism (a return time exists
   by the pigeonhole principle, finite_point_period of module 286). No
   decidable equality on S is needed. `}

def GepiPermRep (S : Type) : Type ≔ sig (
  carrier : Type,
  carrier_set : isSet carrier,
  act : S → Equiv carrier carrier,
  base : carrier,
  faithful : (s s' : S) → Id carrier (act s .map base) (act s' .map base) → Id S s s')

{` The orbit argument. K a finite family, e : K + 1 ≅ K + 1 with labels
   [l, s] and [l, s'] preserved. Following x_n = e^n(new point): either
   s = s' already, or the label (for s') of x_n is s. `}
def gepi_orbit_step (S : Type) (K : GepiFamily S) (s s' : S)
  (e : Equiv (Sum (K .carrier) Unit) (Sum (K .carrier) Unit))
  (lab : (x : Sum (K .carrier) Unit)
         → Id S (gepi_family_sum S K (gepi_singleton S s) .label x)
             (gepi_family_sum S K (gepi_singleton S s') .label (e .map x)))
  (x : Sum (K .carrier) Unit) (h : Id S (gepi_family_sum S K (gepi_singleton S s') .label x) s)
  : Sum (Id S s s') (Id S (gepi_family_sum S K (gepi_singleton S s') .label (e .map x)) s)
  ≔ match x [
  | inl. i ↦ inr. (concat S (gepi_family_sum S K (gepi_singleton S s') .label (e .map (inl. i))) (K .label i) s
      (inverse S (K .label i) (gepi_family_sum S K (gepi_singleton S s') .label (e .map (inl. i))) (lab (inl. i))) h)
  | inr. u ↦ inl. (inverse S s' s h) ]

def gepi_orbit_invariant (S : Type) (K : GepiFamily S) (s s' : S)
  (e : Equiv (Sum (K .carrier) Unit) (Sum (K .carrier) Unit))
  (lab : (x : Sum (K .carrier) Unit)
         → Id S (gepi_family_sum S K (gepi_singleton S s) .label x)
             (gepi_family_sum S K (gepi_singleton S s') .label (e .map x)))
  (n : Nat)
  : Sum (Id S s s')
      (Id S (gepi_family_sum S K (gepi_singleton S s') .label
               (iterate (Sum (K .carrier) Unit) (e .map) (suc. n) (inr. star.))) s)
  ≔ match n [
  | zero. ↦ inr. (inverse S s (gepi_family_sum S K (gepi_singleton S s') .label (e .map (inr. star.)))
      (lab (inr. star.)))
  | suc. n ↦ match gepi_orbit_invariant S K s s' e lab n [
    | inl. p ↦ inl. p
    | inr. h ↦ gepi_orbit_step S K s s' e lab (iterate (Sum (K .carrier) Unit) (e .map) (suc. n) (inr. star.)) h ] ]

def gepi_orbit_cancel (S : Type) (hS : isSet S) (K : GepiFamily S) (s s' : S)
  (e : Equiv (Sum (K .carrier) Unit) (Sum (K .carrier) Unit))
  (lab : (x : Sum (K .carrier) Unit)
         → Id S (gepi_family_sum S K (gepi_singleton S s) .label x)
             (gepi_family_sum S K (gepi_singleton S s') .label (e .map x)))
  : Id S s s'
  ≔ let X ≔ Sum (K .carrier) Unit in
    let L ≔ gepi_family_sum S K (gepi_singleton S s') .label in
    mere_rec (Σ Nat (PointPeriod X (e .map) (inr. star.))) (Id S s s') (hS s s')
      (w ↦ match gepi_orbit_invariant S K s s' e lab (w .fst) [
        | inl. p ↦ p
        | inr. h ↦ inverse S s' s
            (concat S s' (L (iterate X (e .map) (suc. (w .fst)) (inr. star.))) s
              (refl L (inverse X (iterate X (e .map) (suc. (w .fst)) (inr. star.)) (inr. star.) (w .snd))) h) ])
      (finite_point_period X (finite_sum (K .carrier) Unit (K .finite) finite_unit) e (inr. star.))

{` Cancellation in M(S): m + [s] = m + [s'] ⇒ s = s', for a set S. `}
def gepi_singleton_class (S : Type) (s : S) : GepiMonoid S ≔ gepi_monoid_class S (gepi_singleton S s)

def gepi_monoid_cancel (S : Type) (hS : isSet S) (s s' : S) (m : GepiMonoid S)
  (r : Id (GepiMonoid S) (gepi_monoid_plus S m (gepi_singleton_class S s)) (gepi_monoid_plus S m (gepi_singleton_class S s')))
  : Id S s s'
  ≔ let M ≔ GepiMonoid S in
    let R ≔ gepi_family_relation S in
    quotient_prop_induction (GepiFamily S) R
      (m ↦ Id M (gepi_monoid_plus S m (gepi_singleton_class S s)) (gepi_monoid_plus S m (gepi_singleton_class S s'))
           → Id S s s')
      (m ↦ pi_prop (Id M (gepi_monoid_plus S m (gepi_singleton_class S s)) (gepi_monoid_plus S m (gepi_singleton_class S s')))
         (_ ↦ Id S s s') (_ ↦ hS s s'))
      (K r ↦
        let a ≔ gepi_family_sum S K (gepi_singleton S s) in
        let a' ≔ gepi_family_sum S K (gepi_singleton S s') in
        mere_rec (GepiFamilyIso S a a') (Id S s s') (hS s s')
          (e ↦ gepi_orbit_cancel S hS K s s' (e .fst) (e .snd))
          (quotient_effective (GepiFamily S) R a a' .map r))
      m r

{` The group completion T(S), presented on representatives: pairs (a, b)
   of finite families modulo (a, b) ~ (c, d) iff ∃ k, [(a + d) + k] =
   [(c + b) + k] in M(S). (Representatives are families rather than elements
   of M(S): the maps τ_s then never unfold a quotient recursion on a variable
   element, which made the type checker exhaust memory.) `}
def GepiPairs (S : Type) : Type ≔ Product (GepiFamily S) (GepiFamily S)

def GepiDifferenceRel (S : Type) (u v : GepiPairs S) : Type
  ≔ Σ (GepiFamily S) (k ↦ Id (GepiMonoid S)
      (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S (u .fst) (v .snd)) k))
      (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S (v .fst) (u .snd)) k)))

{` Classes of sums as sums of classes (judgmental). `}
def gepi_cl_sum3 (S : Type) (x y k : GepiFamily S)
  : Id (GepiMonoid S) (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S x y) k))
      (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S x) (gepi_monoid_class S y)) (gepi_monoid_class S k))
  ≔ refl (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S x y) k))

def gepi_cl_sum4 (S : Type) (x y z k : GepiFamily S)
  : Id (GepiMonoid S) (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S (gepi_family_sum S x y) z) k))
      (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S x) (gepi_monoid_class S y))
         (gepi_monoid_class S z)) (gepi_monoid_class S k))
  ≔ refl (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S (gepi_family_sum S x y) z) k))

def gepi_cl_sum4r (S : Type) (x y z k : GepiFamily S)
  : Id (GepiMonoid S) (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S x (gepi_family_sum S y z)) k))
      (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S x)
         (gepi_monoid_plus S (gepi_monoid_class S y) (gepi_monoid_class S z))) (gepi_monoid_class S k))
  ≔ refl (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S x (gepi_family_sum S y z)) k))

def gepi_cl_sum_trans (S : Type) (a f c d k l : GepiFamily S)
  : Id (GepiMonoid S)
      (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S a f)
         (gepi_family_sum S (gepi_family_sum S c d) (gepi_family_sum S k l))))
      (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S a) (gepi_monoid_class S f))
         (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S c) (gepi_monoid_class S d))
            (gepi_monoid_plus S (gepi_monoid_class S k) (gepi_monoid_class S l))))
  ≔ refl (gepi_monoid_class S (gepi_family_sum S (gepi_family_sum S a f)
       (gepi_family_sum S (gepi_family_sum S c d) (gepi_family_sum S k l))))

def gepi_difference_trans (S : Type) (u v t : GepiPairs S) (w1 : GepiDifferenceRel S u v) (w2 : GepiDifferenceRel S v t)
  : GepiDifferenceRel S u t
  ≔ let M ≔ GepiMonoid S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    let a ≔ u .fst in let b ≔ u .snd in let c ≔ v .fst in let d ≔ v .snd in let e ≔ t .fst in let f ≔ t .snd in
    let k ≔ w1 .fst in let l ≔ w2 .fst in
    let E1 : Id M (p (p (cl a) (cl d)) (cl k)) (p (p (cl c) (cl b)) (cl k))
      ≔ calc
          p (p (cl a) (cl d)) (cl k)
          = cl (sm (sm a d) k) by inverse M (cl (sm (sm a d) k)) (p (p (cl a) (cl d)) (cl k)) (gepi_cl_sum3 S a d k)
          = cl (sm (sm c b) k) by w1 .snd
          = p (p (cl c) (cl b)) (cl k) by gepi_cl_sum3 S c b k ∎ in
    let E2 : Id M (p (p (cl c) (cl f)) (cl l)) (p (p (cl e) (cl d)) (cl l))
      ≔ calc
          p (p (cl c) (cl f)) (cl l)
          = cl (sm (sm c f) l) by inverse M (cl (sm (sm c f) l)) (p (p (cl c) (cl f)) (cl l)) (gepi_cl_sum3 S c f l)
          = cl (sm (sm e d) l) by w2 .snd
          = p (p (cl e) (cl d)) (cl l) by gepi_cl_sum3 S e d l ∎ in
    let N ≔ sm (sm c d) (sm k l) in
    (N,
     calc
       cl (sm (sm a f) N)
       = p (p (cl a) (cl f)) (p (p (cl c) (cl d)) (p (cl k) (cl l))) by gepi_cl_sum_trans S a f c d k l
       = p (p (cl e) (cl b)) (p (p (cl c) (cl d)) (p (cl k) (cl l)))
         by gepi_completion_trans_algebra M p (gepi_monoid_assoc S) (gepi_monoid_comm S)
              (cl a) (cl b) (cl c) (cl d) (cl e) (cl f) (cl k) (cl l) E1 E2
       = cl (sm (sm e b) N)
         by inverse M (cl (sm (sm e b) N)) (p (p (cl e) (cl b)) (p (p (cl c) (cl d)) (p (cl k) (cl l))))
              (gepi_cl_sum_trans S e b c d k l) ∎)

def gepi_completion_relation (S : Type) : EquivalenceRelation (GepiPairs S)
  ≔ let M ≔ GepiMonoid S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    ((u v ↦ (Mere (GepiDifferenceRel S u v), mere_isprop (GepiDifferenceRel S u v))),
     (u ↦ mere (GepiDifferenceRel S u u) (u .fst, refl (cl (sm (sm (u .fst) (u .snd)) (u .fst))))),
     (u v ↦ trunc_map native_truncation (GepiDifferenceRel S u v) (GepiDifferenceRel S v u)
        (w ↦ (w .fst, inverse M (cl (sm (sm (u .fst) (v .snd)) (w .fst))) (cl (sm (sm (v .fst) (u .snd)) (w .fst))) (w .snd)))),
     (u v t r1 r2 ↦ mere_rec (GepiDifferenceRel S u v) (Mere (GepiDifferenceRel S u t)) (mere_isprop (GepiDifferenceRel S u t))
        (w1 ↦ trunc_map native_truncation (GepiDifferenceRel S v t) (GepiDifferenceRel S u t)
          (w2 ↦ gepi_difference_trans S u v t w1 w2) r2) r1))

def GepiCompletion (S : Type) : Type ≔ Quotient (GepiPairs S) (gepi_completion_relation S)

def gepi_completion_class (S : Type) (u : GepiPairs S) : GepiCompletion S
  ≔ quotient_class (GepiPairs S) (gepi_completion_relation S) u

def gepi_completion_set (S : Type) : isSet (GepiCompletion S)
  ≔ quotient_set (GepiPairs S) (gepi_completion_relation S)

{` Automorphisms of a set quotient induced by maps of representatives that
   preserve the relation and are mutually inverse up to the relation. Stated
   for arbitrary maps, so that no concrete quotient recursion is unfolded on
   a variable. `}
def gepi_quotient_lift (A : Type) (R : EquivalenceRelation A) (F : A → A)
  (rF : (x y : A) → Rel A R x y → Rel A R (F x) (F y)) : Quotient A R → Quotient A R
  ≔ quotient_rec A (Quotient A R) R (quotient_set A R) (a ↦ quotient_class A R (F a))
      (x y r ↦ quotient_encode A R (F x) (F y) (rF x y r))

def gepi_quotient_auto (A : Type) (R : EquivalenceRelation A) (F G : A → A)
  (rF : (x y : A) → Rel A R x y → Rel A R (F x) (F y)) (rG : (x y : A) → Rel A R x y → Rel A R (G x) (G y))
  (gf : (a : A) → Rel A R (G (F a)) a) (fg : (a : A) → Rel A R (F (G a)) a)
  : Equiv (Quotient A R) (Quotient A R)
  ≔ let Q ≔ Quotient A R in
    let f ≔ gepi_quotient_lift A R F rF in
    let g ≔ gepi_quotient_lift A R G rG in
    quasi_inverse_equiv Q Q f g
      (x ↦ quotient_prop_induction A R (y ↦ Id Q (g (f y)) y) (y ↦ quotient_set A R (g (f y)) y)
         (a ↦ quotient_encode A R (G (F a)) a (gf a)) x)
      (x ↦ quotient_prop_induction A R (y ↦ Id Q (f (g y)) y) (y ↦ quotient_set A R (f (g y)) y)
         (a ↦ quotient_encode A R (F (G a)) a (fg a)) x)

def gepi_quotient_lift_class (A : Type) (R : EquivalenceRelation A) (F : A → A)
  (rF : (x y : A) → Rel A R x y → Rel A R (F x) (F y)) (a : A)
  : Id (Quotient A R) (gepi_quotient_lift A R F rF (quotient_class A R a)) (quotient_class A R (F a))
  ≔ refl (quotient_class A R (F a))

{` τ_s on representatives: (a, b) ↦ (a + [s], b), inverse (a, b) ↦ (a, b + [s]). `}
def gepi_pair_up (S : Type) (s : S) (u : GepiPairs S) : GepiPairs S
  ≔ (gepi_family_sum S (u .fst) (gepi_singleton S s), u .snd)

def gepi_pair_down (S : Type) (s : S) (u : GepiPairs S) : GepiPairs S
  ≔ (u .fst, gepi_family_sum S (u .snd) (gepi_singleton S s))

def gepi_pair_up_respects (S : Type) (s : S) (u v : GepiPairs S) (w : GepiDifferenceRel S u v)
  : GepiDifferenceRel S (gepi_pair_up S s u) (gepi_pair_up S s v)
  ≔ let M ≔ GepiMonoid S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    let η ≔ gepi_singleton_class S s in
    let sl ≔ gepi_shift_left_summand M p (gepi_monoid_assoc S) (gepi_monoid_comm S) in
    let k ≔ w .fst in
    (k,
     calc
       cl (sm (sm (sm (u .fst) (gepi_singleton S s)) (v .snd)) k)
       = p (p (p (cl (u .fst)) η) (cl (v .snd))) (cl k) by gepi_cl_sum4 S (u .fst) (gepi_singleton S s) (v .snd) k
       = p (p (p (cl (u .fst)) (cl (v .snd))) (cl k)) η by sl (cl (u .fst)) η (cl (v .snd)) (cl k)
       = p (cl (sm (sm (u .fst) (v .snd)) k)) η
         by refl ((x ↦ p x η) : M → M)
              (inverse M (cl (sm (sm (u .fst) (v .snd)) k)) (p (p (cl (u .fst)) (cl (v .snd))) (cl k))
                (gepi_cl_sum3 S (u .fst) (v .snd) k))
       = p (cl (sm (sm (v .fst) (u .snd)) k)) η by refl ((x ↦ p x η) : M → M) (w .snd)
       = p (p (p (cl (v .fst)) (cl (u .snd))) (cl k)) η
         by refl ((x ↦ p x η) : M → M) (gepi_cl_sum3 S (v .fst) (u .snd) k)
       = p (p (p (cl (v .fst)) η) (cl (u .snd))) (cl k)
         by inverse M (p (p (p (cl (v .fst)) η) (cl (u .snd))) (cl k)) (p (p (p (cl (v .fst)) (cl (u .snd))) (cl k)) η)
              (sl (cl (v .fst)) η (cl (u .snd)) (cl k))
       = cl (sm (sm (sm (v .fst) (gepi_singleton S s)) (u .snd)) k)
         by inverse M (cl (sm (sm (sm (v .fst) (gepi_singleton S s)) (u .snd)) k))
              (p (p (p (cl (v .fst)) η) (cl (u .snd))) (cl k))
              (gepi_cl_sum4 S (v .fst) (gepi_singleton S s) (u .snd) k) ∎)

def gepi_pair_down_respects (S : Type) (s : S) (u v : GepiPairs S) (w : GepiDifferenceRel S u v)
  : GepiDifferenceRel S (gepi_pair_down S s u) (gepi_pair_down S s v)
  ≔ let M ≔ GepiMonoid S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    let η ≔ gepi_singleton_class S s in
    let sr ≔ gepi_shift_right_summand M p (gepi_monoid_assoc S) (gepi_monoid_comm S) in
    let k ≔ w .fst in
    (k,
     calc
       cl (sm (sm (u .fst) (sm (v .snd) (gepi_singleton S s))) k)
       = p (p (cl (u .fst)) (p (cl (v .snd)) η)) (cl k) by gepi_cl_sum4r S (u .fst) (v .snd) (gepi_singleton S s) k
       = p (p (p (cl (u .fst)) (cl (v .snd))) (cl k)) η by sr (cl (u .fst)) (cl (v .snd)) η (cl k)
       = p (cl (sm (sm (u .fst) (v .snd)) k)) η
         by refl ((x ↦ p x η) : M → M)
              (inverse M (cl (sm (sm (u .fst) (v .snd)) k)) (p (p (cl (u .fst)) (cl (v .snd))) (cl k))
                (gepi_cl_sum3 S (u .fst) (v .snd) k))
       = p (cl (sm (sm (v .fst) (u .snd)) k)) η by refl ((x ↦ p x η) : M → M) (w .snd)
       = p (p (p (cl (v .fst)) (cl (u .snd))) (cl k)) η
         by refl ((x ↦ p x η) : M → M) (gepi_cl_sum3 S (v .fst) (u .snd) k)
       = p (p (cl (v .fst)) (p (cl (u .snd)) η)) (cl k)
         by inverse M (p (p (cl (v .fst)) (p (cl (u .snd)) η)) (cl k)) (p (p (p (cl (v .fst)) (cl (u .snd))) (cl k)) η)
              (sr (cl (v .fst)) (cl (u .snd)) η (cl k))
       = cl (sm (sm (v .fst) (sm (u .snd) (gepi_singleton S s))) k)
         by inverse M (cl (sm (sm (v .fst) (sm (u .snd) (gepi_singleton S s))) k))
              (p (p (cl (v .fst)) (p (cl (u .snd)) η)) (cl k))
              (gepi_cl_sum4r S (v .fst) (u .snd) (gepi_singleton S s) k) ∎)

{` (a + [s], b + [s]) ~ (a, b), by an explicit isomorphism of families. `}
def gepi_pair_both (S : Type) (s : S) (u : GepiPairs S)
  : GepiDifferenceRel S (gepi_family_sum S (u .fst) (gepi_singleton S s), gepi_family_sum S (u .snd) (gepi_singleton S s)) u
  ≔ let sm ≔ gepi_family_sum S in
    let a ≔ u .fst in let b ≔ u .snd in let η ≔ gepi_singleton S s in
    let e0 ≔ gepi_empty_family S in
    let iso : GepiFamilyIso S (sm (sm a η) b) (sm a (sm b η))
      ≔ gepi_family_iso_compose S (sm (sm a η) b) (sm a (sm η b)) (sm a (sm b η))
          (gepi_family_iso_assoc S a η b)
          (gepi_family_iso_sum S a a (sm η b) (sm b η) (gepi_family_iso_refl S a) (gepi_family_iso_comm S η b)) in
    (e0, gepi_monoid_iso_path S (sm (sm (sm a η) b) e0) (sm (sm a (sm b η)) e0)
           (gepi_family_iso_sum S (sm (sm a η) b) (sm a (sm b η)) e0 e0 iso (gepi_family_iso_refl S e0)))

def gepi_completion_act (S : Type) (s : S) : Equiv (GepiCompletion S) (GepiCompletion S)
  ≔ gepi_quotient_auto (GepiPairs S) (gepi_completion_relation S) (gepi_pair_up S s) (gepi_pair_down S s)
      (u v ↦ trunc_map native_truncation (GepiDifferenceRel S u v) (GepiDifferenceRel S (gepi_pair_up S s u) (gepi_pair_up S s v))
         (gepi_pair_up_respects S s u v))
      (u v ↦ trunc_map native_truncation (GepiDifferenceRel S u v) (GepiDifferenceRel S (gepi_pair_down S s u) (gepi_pair_down S s v))
         (gepi_pair_down_respects S s u v))
      (u ↦ mere (GepiDifferenceRel S (gepi_pair_down S s (gepi_pair_up S s u)) u) (gepi_pair_both S s u))
      (u ↦ mere (GepiDifferenceRel S (gepi_pair_up S s (gepi_pair_down S s u)) u) (gepi_pair_both S s u))

def gepi_completion_base (S : Type) : GepiCompletion S
  ≔ gepi_completion_class S (gepi_empty_family S, gepi_empty_family S)

{` Faithfulness at the base point: τ_s(t0) = τ_s'(t0) gives
   [((0 + [s]) + 0) + k] = [((0 + [s']) + 0) + k], i.e. m + [s] = m + [s']
   for m = [(0 + 0) + k], hence s = s'. `}
def gepi_completion_faithful (S : Type) (hS : isSet S) (s s' : S)
  (r : Id (GepiCompletion S) (gepi_completion_act S s .map (gepi_completion_base S))
         (gepi_completion_act S s' .map (gepi_completion_base S)))
  : Id S s s'
  ≔ let M ≔ GepiMonoid S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    let z ≔ gepi_empty_family S in
    let sl ≔ gepi_shift_left_summand M p (gepi_monoid_assoc S) (gepi_monoid_comm S) in
    let u : GepiPairs S ≔ gepi_pair_up S s (z, z) in
    let v : GepiPairs S ≔ gepi_pair_up S s' (z, z) in
    let r' : Id (GepiCompletion S) (gepi_completion_class S u) (gepi_completion_class S v) ≔ r in
    mere_rec (GepiDifferenceRel S u v) (Id S s s') (hS s s')
      (w ↦ gepi_monoid_cancel S hS s s' (cl (sm (sm z z) (w .fst)))
         (calc
            p (cl (sm (sm z z) (w .fst))) (gepi_singleton_class S s)
            = p (p (p (cl z) (cl z)) (cl (w .fst))) (gepi_singleton_class S s)
              by refl ((x ↦ p x (gepi_singleton_class S s)) : M → M) (gepi_cl_sum3 S z z (w .fst))
            = p (p (p (cl z) (gepi_singleton_class S s)) (cl z)) (cl (w .fst))
              by inverse M (p (p (p (cl z) (gepi_singleton_class S s)) (cl z)) (cl (w .fst)))
                   (p (p (p (cl z) (cl z)) (cl (w .fst))) (gepi_singleton_class S s))
                   (sl (cl z) (gepi_singleton_class S s) (cl z) (cl (w .fst)))
            = cl (sm (sm (sm z (gepi_singleton S s)) z) (w .fst))
              by inverse M (cl (sm (sm (sm z (gepi_singleton S s)) z) (w .fst)))
                   (p (p (p (cl z) (gepi_singleton_class S s)) (cl z)) (cl (w .fst)))
                   (gepi_cl_sum4 S z (gepi_singleton S s) z (w .fst))
            = cl (sm (sm (sm z (gepi_singleton S s')) z) (w .fst)) by w .snd
            = p (p (p (cl z) (gepi_singleton_class S s')) (cl z)) (cl (w .fst))
              by gepi_cl_sum4 S z (gepi_singleton S s') z (w .fst)
            = p (p (p (cl z) (cl z)) (cl (w .fst))) (gepi_singleton_class S s')
              by sl (cl z) (gepi_singleton_class S s') (cl z) (cl (w .fst))
            = p (cl (sm (sm z z) (w .fst))) (gepi_singleton_class S s')
              by refl ((x ↦ p x (gepi_singleton_class S s')) : M → M)
                   (inverse M (cl (sm (sm z z) (w .fst))) (p (p (cl z) (cl z)) (cl (w .fst))) (gepi_cl_sum3 S z z (w .fst))) ∎))
      (quotient_effective (GepiPairs S) (gepi_completion_relation S) u v .map r')

{` Every set S acts faithfully (at a point) on a set. `}
def gepi_perm_rep (S : Type) (hS : isSet S) : GepiPermRep S
  ≔ (GepiCompletion S, gepi_completion_set S, gepi_completion_act S, gepi_completion_base S,
     gepi_completion_faithful S hS)
