export "1034-sylow-three"
export "1005-cauchy-theorem"
export "903-normal-subgroups"

{` Chapter 10, tools for the example at fingp.tex 27–33 (Sylow subgroups of
   Σ_3, Σ_4, Σ_6; modules 1014–1017):
   - explicit permutations of order 3 (f∘f∘f = id) as symmetries of Σ_S,
     with g^3 = e, and g ≠ e when f moves a point;
   - membership in the cyclic subgroup ⟨g⟩ (cyclic_subgroup_of_element,
     module 1011): a symmetry t fixes its point iff t = g^k for some k < n
     (via lem:E-preserves-symms, mono_preserves_symmetries of module 507);
   - a cyclic subgroup of prime order p with p^1 the largest power of p
     dividing |G| is a p-Sylow subgroup;
   - if there is exactly one p-Sylow subgroup, every p-Sylow subgroup is it
     and it is normal (it is fixed by conjugation since conjugates of Sylow
     subgroups are Sylow; normal_iff_fixed, module 903);
   - arithmetic: a ≡ b (mod p) and a = b + c give p | c; a finite type of
     cardinality 1 is a proposition. `}

{` Arithmetic. `}
def fingp_le_add_left_term (x y : Nat) : Le y (add x y)
  ≔ match y [
  | zero. ↦ star.
  | suc. y ↦ fingp_le_add_left_term x y ]

def fingp_congruent_diff_left (p b c k : Nat) (e : Id Nat (add b c) (add b (mul k p))) : NatDivides p c
  ≔ nat_divides_intro p c k (add_cancel_left b c (mul k p) e)

def fingp_congruent_diff_right (p b c k : Nat) (e : Id Nat b (add (add b c) (mul k p))) : NatDivides p c
  ≔ let z : Id Nat (add c (mul k p)) zero.
      ≔ inverse Nat zero. (add c (mul k p))
          (add_cancel_left b zero. (add c (mul k p))
            (concat Nat b (add (add b c) (mul k p)) (add b (add c (mul k p))) e (add_assoc b c (mul k p)))) in
    let cz : Id Nat c zero.
      ≔ nat_add_zero_right (mul k p) c (concat Nat (add (mul k p) c) (add c (mul k p)) zero. (add_comm (mul k p) c) z) in
    transport Nat (NatDivides p) zero. c (inverse Nat c zero. cz) (nat_divides_zero p)

def fingp_congruent_divides_diff (p a b c : Nat) (e : Id Nat a (add b c)) (h : NatCongruent p a b) : NatDivides p c
  ≔ mere_rec (Σ Nat (k ↦ Sum (Id Nat a (add b (mul k p))) (Id Nat b (add a (mul k p))))) (NatDivides p c)
      (nat_divides_prop p c)
      (w ↦ match w .snd [
        | inl. e1 ↦ fingp_congruent_diff_left p b c (w .fst)
            (concat Nat (add b c) a (add b (mul (w .fst) p)) (inverse Nat a (add b c) e) e1)
        | inr. e2 ↦ fingp_congruent_diff_right p b c (w .fst)
            (concat Nat b (add a (mul (w .fst) p)) (add (add b c) (mul (w .fst) p)) e2
              (refl ((x ↦ add x (mul (w .fst) p)) : Nat → Nat) e)) ])
      h

{` A finite type with exactly one element is a proposition. `}
def fingp_card_one_eq (A : Type) (h : IsFinite A) (q : Id Nat (cardinality A h) (suc. zero.)) (x y : A) : Id A x y
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) (Id A x y) (finite_sethood A h x y)
      (r ↦ equivalence_injective A (Fin (cardinality A h)) (id_to_equiv A (Fin (cardinality A h)) r) x y
        (transport Nat (n ↦ isProp (Fin n)) (suc. zero.) (cardinality A h) (inverse Nat (cardinality A h) (suc. zero.) q)
          fingp_fin_one_prop (id_to_equiv A (Fin (cardinality A h)) r .map x) (id_to_equiv A (Fin (cardinality A h)) r .map y)))
      (cardinality_spec A h)

{` IsLargestPrimePower decided by computation. `}
def fingp_largest_power_decide (p n m : Nat)
  (e1 : Id Bool (decision_bool (NatDivides (nat_power p n) m) (nat_divides_decidable_any (nat_power p n) m)) true.)
  (e2 : Id Bool (decision_bool (NatDivides (nat_power p (suc. n)) m) (nat_divides_decidable_any (nat_power p (suc. n)) m)) false.)
  : IsLargestPrimePower p n m
  ≔ (decision_bool_reflect (NatDivides (nat_power p n) m) (nat_divides_decidable_any (nat_power p n) m) e1,
     nat_decision_false_reflect (NatDivides (nat_power p (suc. n)) m) (nat_divides_decidable_any (nat_power p (suc. n)) m) e2)

{` Explicit permutations of order 3. `}
def perm3_equiv (A : Type) (f : A → A) (h : (x : A) → Id A (f (f (f x))) x) : Equiv A A
  ≔ quasi_inverse_equiv A A f (x ↦ f (f x)) h h

def perm_symmetry_power_action (S : SetTypes) (e : Equiv (S .fst) (S .fst)) (k : Nat) (x : S .fst)
  : Id (S .fst) (permutation_action S (usym_power (permutation_group S) (permutation_symmetry S e) k) x)
      (iterate (S .fst) (e .map) k x)
  ≔ let P ≔ permutation_group S in let ρ ≔ permutation_symmetry S e in
    match k [
    | zero. ↦ permutation_action_unit S x
    | suc. k ↦ concat (S .fst) (permutation_action S (usym_mul P ρ (usym_power P ρ k)) x)
        (permutation_action S ρ (permutation_action S (usym_power P ρ k) x))
        (iterate (S .fst) (e .map) (suc. k) x)
        (permutation_action_mul S ρ (usym_power P ρ k) x)
        (refl (e .map) (perm_symmetry_power_action S e k x)) ]

def perm3_symmetry_cube (S : SetTypes) (f : S .fst → S .fst) (h : (x : S .fst) → Id (S .fst) (f (f (f x))) x)
  : Id (USym (permutation_group S))
      (usym_power (permutation_group S) (permutation_symmetry S (perm3_equiv (S .fst) f h)) (suc. (suc. (suc. zero.))))
      (usym_unit (permutation_group S))
  ≔ let P ≔ permutation_group S in let ρ ≔ permutation_symmetry S (perm3_equiv (S .fst) f h) in
    permutation_symmetries_ext S (usym_power P ρ (suc. (suc. (suc. zero.)))) (usym_unit P)
      (x ↦ concat (S .fst) (permutation_action S (usym_power P ρ (suc. (suc. (suc. zero.)))) x) x
        (permutation_action S (usym_unit P) x)
        (concat (S .fst) (permutation_action S (usym_power P ρ (suc. (suc. (suc. zero.)))) x) (f (f (f x))) x
          (perm_symmetry_power_action S (perm3_equiv (S .fst) f h) (suc. (suc. (suc. zero.))) x) (h x))
        (inverse (S .fst) (permutation_action S (usym_unit P) x) x (permutation_action_unit S x)))

def perm_symmetry_ne_unit (S : SetTypes) (e : Equiv (S .fst) (S .fst)) (x : S .fst) (ne : Not (Id (S .fst) (e .map x) x))
  : Not (Id (USym (permutation_group S)) (permutation_symmetry S e) (usym_unit (permutation_group S)))
  ≔ q ↦ ne (concat (S .fst) (e .map x) (permutation_action S (usym_unit (permutation_group S)) x) x
      (refl ((y ↦ permutation_action S y x) : USym (permutation_group S) → S .fst) q)
      (permutation_action_unit S x))

{` Membership in the cyclic subgroup ⟨g⟩. `}
def cyclic_subgroup_member_power (b : Nat) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k (suc. b) → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (t : USym G)
  (r : Id (gset_underlying G (cyclic_subgroup_of_element b G g h hyp .gset))
     (gset_usym_act G (cyclic_subgroup_of_element b G g h hyp .gset) t (cyclic_subgroup_of_element b G g h hyp .point))
     (cyclic_subgroup_of_element b G g h hyp .point))
  : Mere (Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym G) t (usym_power G g k))))
  ≔ let m ≔ cyclic_mono_of_element b G g h hyp in
    let S ≔ cyclic_subgroup_of_element b G g h hyp in
    let C ≔ cyclic_group (suc. b) in
    let f ≔ cyclic_hom_of_element b G g h in
    let T ≔ Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym G) t (usym_power G g k))) in
    mere_rec (Σ (USym C) (c ↦ Id (USym G) t (usym_hom C G f c))) (Mere T) (mere_isprop T)
      (w ↦ let v ≔ cyclic_symmetry_power_index b (w .fst) in
        mere T (v .fst, (v .snd .fst,
          concat (USym G) t (usym_hom C G f (w .fst)) (usym_power G g (v .fst)) (w .snd)
            (concat (USym G) (usym_hom C G f (w .fst)) (usym_hom C G f (usym_power C (cyclic_group_generator b) (v .fst)))
              (usym_power G g (v .fst))
              (refl (usym_hom C G f) (inverse (USym C) (usym_power C (cyclic_group_generator b) (v .fst)) (w .fst) (v .snd .snd)))
              (cyclic_hom_generator_power b G g h (v .fst))))))
      (mono_preserves_symmetries G S m (inverse (GroupMonos G) (subgroup_to_mono G S) m (mono_subgroup_roundtrip G m)) t .fst r)

def cyclic_subgroup_power_member (b : Nat) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k (suc. b) → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (k : Nat)
  : Id (gset_underlying G (cyclic_subgroup_of_element b G g h hyp .gset))
      (gset_usym_act G (cyclic_subgroup_of_element b G g h hyp .gset) (usym_power G g k) (cyclic_subgroup_of_element b G g h hyp .point))
      (cyclic_subgroup_of_element b G g h hyp .point)
  ≔ let m ≔ cyclic_mono_of_element b G g h hyp in
    let S ≔ cyclic_subgroup_of_element b G g h hyp in
    let C ≔ cyclic_group (suc. b) in
    let f ≔ cyclic_hom_of_element b G g h in
    mono_preserves_symmetries G S m (inverse (GroupMonos G) (subgroup_to_mono G S) m (mono_subgroup_roundtrip G m))
      (usym_power G g k) .snd
      (mere (Σ (USym C) (c ↦ Id (USym G) (usym_power G g k) (usym_hom C G f c)))
        (usym_power C (cyclic_group_generator b) k,
         inverse (USym G) (usym_hom C G f (usym_power C (cyclic_group_generator b) k)) (usym_power G g k)
           (cyclic_hom_generator_power b G g h k)))

{` Sylow subgroups from cardinalities. `}
def fingp_sylow_of_card (p : Nat) (G : Group) (hG : IsFiniteGroup G) (T : Subgroups G)
  (hT : IsFiniteGroup (subgroup_group G T)) (n m : Nat) (hc : Id Nat (group_card G hG) m)
  (e : Id Nat (group_card (subgroup_group G T) hT) (nat_power p n)) (hl : IsLargestPrimePower p n m)
  : IsSylowSubgroup p G T
  ≔ (hG, (hT, (n, (e, transport Nat (IsLargestPrimePower p n) m (group_card G hG) (inverse Nat (group_card G hG) m hc) hl))))

def cyclic_prime_subgroup_finite (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  : IsFiniteGroup (subgroup_group G (cyclic_prime_subgroup b hp G g h ne))
  ≔ group_finite_path (cyclic_group (suc. b)) (subgroup_group G (cyclic_prime_subgroup b hp G g h ne))
      (inverse Group (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)) (cyclic_group (suc. b))
        (cyclic_prime_subgroup_group_path b hp G g h ne))
      (cyclic_group_finite b)

def cyclic_prime_subgroup_card (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  (hS : IsFiniteGroup (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)))
  : Id Nat (group_card (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)) hS) (suc. b)
  ≔ concat Nat (group_card (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)) hS)
      (group_card (cyclic_group (suc. b)) (cyclic_group_finite b)) (suc. b)
      (group_card_path (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)) (cyclic_group (suc. b))
        (cyclic_prime_subgroup_group_path b hp G g h ne) hS (cyclic_group_finite b))
      (cyclic_group_card b (cyclic_group_finite b))

def cyclic_prime_sylow (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  (m : Nat) (hc : Id Nat (group_card G hG) m) (hl : IsLargestPrimePower (suc. b) (suc. zero.) m)
  : IsSylowSubgroup (suc. b) G (cyclic_prime_subgroup b hp G g h ne)
  ≔ let hS ≔ cyclic_prime_subgroup_finite b hp G g h ne in
    fingp_sylow_of_card (suc. b) G hG (cyclic_prime_subgroup b hp G g h ne) hS (suc. zero.) m hc
      (concat Nat (group_card (subgroup_group G (cyclic_prime_subgroup b hp G g h ne)) hS) (suc. b)
        (nat_power (suc. b) (suc. zero.))
        (cyclic_prime_subgroup_card b hp G g h ne hS) (inverse Nat (nat_power (suc. b) (suc. zero.)) (suc. b) (nat_power_one (suc. b))))
      hl

{` A unique Sylow subgroup: every Sylow subgroup equals it, and it is normal. `}
def sylow_card_one_unique (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  (c1 : Id Nat (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) (suc. zero.))
  (T : Subgroups G) (sT : IsSylowSubgroup p G T) : Id (Subgroups G) T P
  ≔ refl ((Q ↦ Q .fst) : SylowSubgroups p G → Subgroups G)
      (fingp_card_one_eq (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP) c1 (T, sT) (P, sP))

def sylow_card_one_normal (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  (c1 : Id Nat (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) (suc. zero.))
  : IsNormalSubgroup G P
  ≔ fixed_normal_subgroup G P
      (g ↦ let Q ≔ gset_usym_act G (sylow_gset p G) g (P, sP) in
        concat (Subgroups G) (subgroup_conjugate G g P) (Q .fst) P
          (inverse (Subgroups G) (Q .fst) (subgroup_conjugate G g P) (sylow_gset_act p G g (P, sP)))
          (sylow_card_one_unique p hp G P sP c1 (Q .fst) (Q .snd)))
