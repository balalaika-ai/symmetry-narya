export "1004-mckay-set"
export "1011-cyclic-group-homs"
export "1026-delooped-action-fixed-points"

{` Chapter 10 (fingp.tex 124–202), thm:cauchys (Cauchy's theorem): if p is a
   prime dividing the order of a finite group G, then G has a subgroup which
   is cyclic of order p.

   Route. p = b+1. The rotation r of McKay's set X = McKaySet G b
   (module 1004) is a permutation with r^p = id, so cyclic_hom_of_element
   (module 1011) gives an action f : C_p → Σ_X sending the generator to r.
   Delooping f (action_to_gset, rem:GSet=SetHomG; module 1026) gives a
   C_p-set with underlying set X, of cardinality |G|^b, divisible by p;
   its fixed points are the points fixed by every f(σ), i.e. (every σ is
   generator^k) the rotation-fixed tuples, i.e. Σ_g (g^p = e). With
   |C_p| = p^1, lem:fixedptsize (p_group_fixed_points_divisible, module 1023)
   gives p | |{g | g^p = e}|; e is in that set, so it has at least p
   elements (the book's "at least p fixed points"), and since p > 1 there
   is g ≠ e with g^p = e (decidable: USym G is a finite set, so it has
   decidable equality, and existential quantification over a finite set is
   decidable). By prime_order_powers_nontrivial g^k ≠ e for 0 < k < p, and
   cyclic_prime_subgroup (module 1011) is the subgroup.

   Deviation: the book defines the C_p-set directly on BC_p,
   X(S,j) = Σ_{g : S → USym G} Π_q μ(q)(g) = e. We deloop the rotation action
   instead; by rem:GSet=SetHomG (module 560) both describe the same C_p-set
   up to equivalence. The book's "product along every rotation" condition is
   McKayConditionRotations (equivalent to the single product, module 1004). `}

{` The rotation as a symmetry r of Σ_X with r^p = e. `}
def cauchy_rotation_set (G : Group) (b : Nat) : SetTypes ≔ (McKaySet G b, mckay_set_is_set G b)

def cauchy_rotation_symmetry (G : Group) (b : Nat) : USym (permutation_group (cauchy_rotation_set G b))
  ≔ permutation_symmetry (cauchy_rotation_set G b) (mckay_rotate_equiv G b)

def cauchy_rotation_power_action (G : Group) (b : Nat) (k : Nat) (x : McKaySet G b)
  : Id (McKaySet G b)
      (permutation_action (cauchy_rotation_set G b)
        (usym_power (permutation_group (cauchy_rotation_set G b)) (cauchy_rotation_symmetry G b) k) x)
      (iterate (McKaySet G b) (mckay_rotate G b) k x)
  ≔ let S ≔ cauchy_rotation_set G b in let P ≔ permutation_group S in let ρ ≔ cauchy_rotation_symmetry G b in
    match k [
    | zero. ↦ permutation_action_unit S x
    | suc. k ↦ concat (McKaySet G b) (permutation_action S (usym_mul P ρ (usym_power P ρ k)) x)
        (permutation_action S ρ (permutation_action S (usym_power P ρ k) x))
        (iterate (McKaySet G b) (mckay_rotate G b) (suc. k) x)
        (permutation_action_mul S ρ (usym_power P ρ k) x)
        (refl (mckay_rotate G b) (cauchy_rotation_power_action G b k x)) ]

def cauchy_rotation_period (G : Group) (b : Nat)
  : Id (USym (permutation_group (cauchy_rotation_set G b)))
      (usym_power (permutation_group (cauchy_rotation_set G b)) (cauchy_rotation_symmetry G b) (suc. b))
      (usym_unit (permutation_group (cauchy_rotation_set G b)))
  ≔ let S ≔ cauchy_rotation_set G b in let P ≔ permutation_group S in let M ≔ McKaySet G b in
    permutation_symmetries_ext S (usym_power P (cauchy_rotation_symmetry G b) (suc. b)) (usym_unit P)
      (x ↦ concat M (permutation_action S (usym_power P (cauchy_rotation_symmetry G b) (suc. b)) x)
        (iterate M (mckay_rotate G b) (suc. b) x) (permutation_action S (usym_unit P) x)
        (cauchy_rotation_power_action G b (suc. b) x)
        (concat M (iterate M (mckay_rotate G b) (suc. b) x) x (permutation_action S (usym_unit P) x)
          (mckay_rotate_period G b x) (inverse M (permutation_action S (usym_unit P) x) x (permutation_action_unit S x))))

{` The C_p-action on McKay's set: generator ↦ rotation. `}
def cauchy_rotation_action (G : Group) (b : Nat) : GroupActionOnSet (cyclic_group (suc. b)) (cauchy_rotation_set G b)
  ≔ cyclic_hom_of_element b (permutation_group (cauchy_rotation_set G b)) (cauchy_rotation_symmetry G b)
      (cauchy_rotation_period G b)

def cauchy_iterate_fixed (A : Type) (f : A → A) (x : A) (p : Id A (f x) x) (k : Nat) : Id A (iterate A f k x) x
  ≔ match k [
  | zero. ↦ refl x
  | suc. k ↦ concat A (f (iterate A f k x)) (f x) x (refl f (cauchy_iterate_fixed A f x p k)) p ]

{` A point is fixed by the action iff it is fixed by the rotation. `}
def cauchy_fixed_iff_forward (G : Group) (b : Nat) (x : McKaySet G b)
  (h : (g : USym (cyclic_group (suc. b))) → Id (McKaySet G b)
         (permutation_action (cauchy_rotation_set G b)
           (usym_hom (cyclic_group (suc. b)) (permutation_group (cauchy_rotation_set G b)) (cauchy_rotation_action G b) g) x) x)
  : Id (McKaySet G b) (mckay_rotate G b x) x
  ≔ let S ≔ cauchy_rotation_set G b in let P ≔ permutation_group S in let C ≔ cyclic_group (suc. b) in
    let gen ≔ cyclic_group_generator b in
    concat (McKaySet G b) (mckay_rotate G b x) (permutation_action S (usym_hom C P (cauchy_rotation_action G b) gen) x) x
      (refl ((y ↦ permutation_action S y x) : USym P → McKaySet G b)
        (inverse (USym P) (usym_hom C P (cauchy_rotation_action G b) gen) (cauchy_rotation_symmetry G b)
          (cyclic_hom_generator b P (cauchy_rotation_symmetry G b) (cauchy_rotation_period G b))))
      (h gen)

def cauchy_fixed_iff_backward (G : Group) (b : Nat) (x : McKaySet G b) (fx : Id (McKaySet G b) (mckay_rotate G b x) x)
  (g : USym (cyclic_group (suc. b)))
  : Id (McKaySet G b)
      (permutation_action (cauchy_rotation_set G b)
        (usym_hom (cyclic_group (suc. b)) (permutation_group (cauchy_rotation_set G b)) (cauchy_rotation_action G b) g) x) x
  ≔ let S ≔ cauchy_rotation_set G b in let P ≔ permutation_group S in let C ≔ cyclic_group (suc. b) in
    let M ≔ McKaySet G b in let f ≔ cauchy_rotation_action G b in
    let w ≔ cyclic_symmetry_power_index b g in
    let k ≔ w .fst in
    let gk ≔ usym_power C (cyclic_group_generator b) k in
    calc
      permutation_action S (usym_hom C P f g) x = permutation_action S (usym_hom C P f gk) x
        by refl ((y ↦ permutation_action S (usym_hom C P f y) x) : USym C → M) (inverse (USym C) gk g (w .snd .snd))
      = permutation_action S (usym_power P (cauchy_rotation_symmetry G b) k) x
        by refl ((y ↦ permutation_action S y x) : USym P → M)
          (cyclic_hom_generator_power b P (cauchy_rotation_symmetry G b) (cauchy_rotation_period G b) k)
      = iterate M (mckay_rotate G b) k x by cauchy_rotation_power_action G b k x
      = x by cauchy_iterate_fixed M (mckay_rotate G b) x fx k ∎

def cauchy_action_fixed_equiv (G : Group) (b : Nat)
  : Equiv (ActionFixedPoints (cyclic_group (suc. b)) (cauchy_rotation_set G b) (cauchy_rotation_action G b))
      (McKayFixedPoints G b)
  ≔ let S ≔ cauchy_rotation_set G b in let P ≔ permutation_group S in let C ≔ cyclic_group (suc. b) in
    let M ≔ McKaySet G b in let f ≔ cauchy_rotation_action G b in
    family_equiv M (x ↦ (g : USym C) → Id M (permutation_action S (usym_hom C P f g) x) x)
      (x ↦ Id M (mckay_rotate G b x) x)
      (x ↦ iff_equiv ((g : USym C) → Id M (permutation_action S (usym_hom C P f g) x) x) (Id M (mckay_rotate G b x) x)
        (pi_prop (USym C) (g ↦ Id M (permutation_action S (usym_hom C P f g) x) x)
          (g ↦ mckay_set_is_set G b (permutation_action S (usym_hom C P f g) x) x))
        (mckay_set_is_set G b (mckay_rotate G b x) x)
        (cauchy_fixed_iff_forward G b x) (cauchy_fixed_iff_backward G b x))

{` {g | g^p = e} is finite (decidable subset of the finite set USym G). `}
def cauchy_period_elements_finite (G : Group) (b : Nat) (hG : IsFiniteGroup G) : IsFinite (McKayPeriodElements G b)
  ≔ finite_decidable_subset (USym G) hG (g ↦ Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
      (g ↦ usym_set G (usym_power G g (suc. b)) (usym_unit G))
      (g ↦ finite_decidable_equality (USym G) hG (usym_power G g (suc. b)) (usym_unit G))

{` The key count: p | |{g | g^p = e}| (lem:fixedptsize applied to the
   delooped rotation action). `}
def cauchy_period_elements_divisible (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG)) (hQ : IsFinite (McKayPeriodElements G b))
  : NatDivides (suc. b) (cardinality (McKayPeriodElements G b) hQ)
  ≔ let C ≔ cyclic_group (suc. b) in let hC ≔ cyclic_group_finite b in
    let S ≔ cauchy_rotation_set G b in let f ≔ cauchy_rotation_action G b in
    let X ≔ action_to_gset C S f in
    let hS ≔ mckay_set_finite G b hG in
    let hX : IsFiniteGSet C X
      ≔ finite_of_equiv (gset_underlying C X) (S .fst)
          (canonical_inverse_equiv (S .fst) (gset_underlying C X) (delooped_underlying_equiv C S f)) hS in
    let hc : Id Nat (group_card C hC) (nat_power (suc. b) (suc. zero.))
      ≔ concat Nat (group_card C hC) (suc. b) (nat_power (suc. b) (suc. zero.))
          (cyclic_group_card b hC) (inverse Nat (nat_power (suc. b) (suc. zero.)) (suc. b) (nat_power_one (suc. b))) in
    let hdX : NatDivides (suc. b) (gset_card C X hX)
      ≔ transport Nat (NatDivides (suc. b)) (cardinality (S .fst) hS) (gset_card C X hX) (delooped_card C S f hS)
          (mckay_set_card_divisible (suc. b) G b hG hS (prime_gt_one (suc. b) hp) hd) in
    let GF ≔ GSetFixedPoints C X in
    let hGF ≔ gset_fixed_points_finite C hC X hX in
    let AF ≔ ActionFixedPoints C S f in
    let hA ≔ finite_of_equiv AF GF (delooped_fixed_points_equiv C S f) hGF in
    let Q ≔ McKayPeriodElements G b in
    let eAQ ≔ compose_equiv AF (McKayFixedPoints G b) Q (cauchy_action_fixed_equiv G b) (mckay_fixed_points_equiv G b) in
    let cQ : Id Nat (cardinality GF hGF) (cardinality Q hQ)
      ≔ concat Nat (cardinality GF hGF) (cardinality AF hA) (cardinality Q hQ)
          (inverse Nat (cardinality AF hA) (cardinality GF hGF) (cardinality_equiv AF GF (delooped_fixed_points_equiv C S f) hA hGF))
          (cardinality_equiv AF Q eAQ hA hQ) in
    transport Nat (NatDivides (suc. b)) (cardinality GF hGF) (cardinality Q hQ) cQ
      (p_group_fixed_points_divisible (suc. b) hp (suc. zero.) C hC hc X hX hdX)

{` "There are at least p fixed points": p ≤ |{g | g^p = e}|. `}
def cauchy_card_nonzero (A : Type) (h : IsFinite A) (a : A) (z : Id Nat (cardinality A h) zero.) : Empty
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) Empty empty_prop
      (q ↦ transport Nat Fin (cardinality A h) zero. z (id_to_equiv A (Fin (cardinality A h)) q .map a))
      (cardinality_spec A h)

def cauchy_divides_nonzero_le (d n : Nat) : NatDivides d n → (Id Nat n zero. → Empty) → Le d n
  ≔ match n [
  | zero. ↦ _ nz ↦ absurd (Le d zero.) (nz (refl (zero. : Nat)))
  | suc. k ↦ hd _ ↦ nat_divides_le d k hd ]

def cauchy_at_least_p_elements (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG)) (hQ : IsFinite (McKayPeriodElements G b))
  : Le (suc. b) (cardinality (McKayPeriodElements G b) hQ)
  ≔ cauchy_divides_nonzero_le (suc. b) (cardinality (McKayPeriodElements G b) hQ)
      (cauchy_period_elements_divisible b hp G hG hd hQ)
      (cauchy_card_nonzero (McKayPeriodElements G b) hQ (mckay_period_unit G b))

{` An element g ≠ e with g^p = e (the intermediate form of the theorem). `}
def cauchy_all_unit_absurd (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG))
  (all : (y : McKayPeriodElements G b) → Id (USym G) (y .fst) (usym_unit G)) : Empty
  ≔ let Q ≔ McKayPeriodElements G b in
    let hQ ≔ cauchy_period_elements_finite G b hG in
    let qp : isProp Q
      ≔ y y' ↦ subtype_equal (USym G) (g ↦ Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
          (g ↦ usym_set G (usym_power G g (suc. b)) (usym_unit G)) y y'
          (concat (USym G) (y .fst) (usym_unit G) (y' .fst) (all y) (inverse (USym G) (y' .fst) (usym_unit G) (all y'))) in
    prime_ne_one (suc. b) hp
      (nat_divides_one (suc. b)
        (transport Nat (NatDivides (suc. b)) (cardinality Q hQ) (suc. zero.)
          (inhabited_prop_cardinality Q qp hQ (mckay_period_unit G b))
          (cauchy_period_elements_divisible b hp G hG hd hQ)))

def cauchy_unit_decide (G : Group) (hG : IsFiniteGroup G) (g : USym G) : Decidable (Not (Id (USym G) g (usym_unit G)))
  ≔ match finite_decidable_equality (USym G) hG g (usym_unit G) [
  | inl. p ↦ inr. (n ↦ n p)
  | inr. n ↦ inl. n ]

def cauchy_nontrivial_element (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG))
  : Mere (Σ (USym G) (g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G)))))
  ≔ let Q ≔ McKayPeriodElements G b in
    let T ≔ Σ (USym G) (g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G)))) in
    let N : Q → Type ≔ y ↦ Not (Id (USym G) (y .fst) (usym_unit G)) in
    match finite_quantifiers Q (cauchy_period_elements_finite G b hG) N (y ↦ negation_prop (Id (USym G) (y .fst) (usym_unit G)))
      (y ↦ cauchy_unit_decide G hG (y .fst)) .snd [
    | inl. m ↦ mere_rec (Σ Q N) (Mere T) (mere_isprop T) (w ↦ mere T (w .fst .fst, (w .fst .snd, w .snd))) m
    | inr. no ↦ absurd (Mere T) (cauchy_all_unit_absurd b hp G hG hd
        (y ↦ match finite_decidable_equality (USym G) hG (y .fst) (usym_unit G) [
          | inl. p ↦ p
          | inr. n ↦ absurd (Id (USym G) (y .fst) (usym_unit G)) (no (mere (Σ Q N) (y, n))) ])) ]

{` thm:cauchys: a subgroup of G whose underlying group is C_p. `}
def cauchy_theorem (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG))
  : Mere (Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group (suc. b))))
  ≔ let T ≔ Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group (suc. b))) in
    mere_rec (Σ (USym G) (g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G)))))
      (Mere T) (mere_isprop T)
      (w ↦ mere T (cyclic_prime_subgroup b hp G (w .fst) (w .snd .fst) (w .snd .snd),
        cyclic_prime_subgroup_group_path b hp G (w .fst) (w .snd .fst) (w .snd .snd)))
      (cauchy_nontrivial_element b hp G hG hd)

{` The same with the book's literal C_p = Aut_Cyc(Fin p, s) (cyclic_group_fin). `}
def cauchy_theorem_fin (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG))
  : Mere (Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group_fin b)))
  ≔ let T ≔ Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group_fin b)) in
    mere_rec (Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group (suc. b)))) (Mere T) (mere_isprop T)
      (w ↦ mere T (w .fst, concat Group (subgroup_group G (w .fst)) (cyclic_group (suc. b)) (cyclic_group_fin b)
        (w .snd) (inverse Group (cyclic_group_fin b) (cyclic_group (suc. b)) (cyclic_group_fin_path b))))
      (cauchy_theorem b hp G hG hd)

{` Litmus: |Σ_3| = 6, so Cauchy gives subgroups of Σ_3 that are cyclic of
   order 3 and of order 2. `}
def sigma3_card_divides (d q : Nat) (e : Id Nat (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) (mul q d))
  : NatDivides d (group_card (symmetric_group three) (symmetric_group_finite three))
  ≔ let six : Nat ≔ suc. (suc. (suc. (suc. (suc. (suc. zero.))))) in
    let c ≔ group_card (symmetric_group three) (symmetric_group_finite three) in
    transport Nat (NatDivides d) six c (inverse Nat c six symmetric_group_three_card) (nat_divides_intro d six q e)

def sigma3_cauchy_three
  : Mere (Σ (Subgroups (symmetric_group three))
      (S ↦ Id Group (subgroup_group (symmetric_group three) S) (cyclic_group (suc. (suc. (suc. zero.))))))
  ≔ cauchy_theorem (suc. (suc. zero.)) nat_prime_three (symmetric_group three) (symmetric_group_finite three)
      (sigma3_card_divides (suc. (suc. (suc. zero.))) (suc. (suc. zero.)) (refl (mul (suc. (suc. zero.)) (suc. (suc. (suc. zero.))))))

def sigma3_cauchy_two
  : Mere (Σ (Subgroups (symmetric_group three))
      (S ↦ Id Group (subgroup_group (symmetric_group three) S) (cyclic_group (suc. (suc. zero.)))))
  ≔ cauchy_theorem (suc. zero.) nat_prime_two (symmetric_group three) (symmetric_group_finite three)
      (sigma3_card_divides (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) (refl (mul (suc. (suc. (suc. zero.))) (suc. (suc. zero.)))))
