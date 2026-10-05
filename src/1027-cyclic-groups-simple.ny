export "1030-subgroup-containment"
export "1012-finite-group-orders"
export "1011-cyclic-group-homs"
export "59-quotient-presentations"
export "70-classical-principles"

{` Chapter 10, cor:cyclicgroupsaresimple (fingp.tex 87-93): for p prime,
   the cyclic group C_p = cyclic_group p has no non-trivial proper
   subgroups.

   * For a finite subgroup H (equivalently a decidable one, module 1020),
     |H| divides p by lem:Lagrangeascounting, so |H| = 1 (H is trivial) or
     |H| = p (H = C_p): cyclic_prime_subgroup_cases.
   * As printed, for every subgroup: there is no subgroup that is both
     non-trivial and proper (cyclic_prime_no_nontrivial_proper). The book's
     proof applies Lagrange, which needs H finite; constructively not every
     subgroup of C_2 = Σ_2 is finite (module 1024), so the statement is
     proved for all subgroups without Lagrange: under the double negation
     of "some g ≠ e fixes the point", either such a g generates C_p and the
     subgroup is everything (not proper), or the stabilizer is {e} and the
     subgroup is trivial.

   Supporting lemma: in a group of prime order p every g ≠ e with g^p = e
   generates (prime_order_element_generates). `}

def fingp_remainder_finite (n : Nat) : IsFinite (Remainder n)
  ≔ finite_of_equiv (Remainder n) (Fin n) (canonical_inverse_equiv (Fin n) (Remainder n) (fin_book_below_equiv n))
      (fin_is_finite n)

def fingp_remainder_card (n : Nat) : Id Nat (cardinality (Remainder n) (fingp_remainder_finite n)) n
  ≔ concat Nat (cardinality (Remainder n) (fingp_remainder_finite n)) (cardinality (Fin n) (fin_is_finite n)) n
      (cardinality_equiv (Remainder n) (Fin n) (canonical_inverse_equiv (Fin n) (Remainder n) (fin_book_below_equiv n))
        (fingp_remainder_finite n) (fin_is_finite n))
      (standard_cardinality n)

{` A symmetry fixing x fixes x under all its powers. `}
def stabilizer_power_fixed (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G)
  (r : Id (gset_underlying G X) (gset_usym_act G X g x) x) (k : Nat)
  : Id (gset_underlying G X) (gset_usym_act G X (usym_power G g k) x) x
  ≔ let Xu ≔ gset_underlying G X in
    match k [
    | zero. ↦ concat Xu (gset_usym_act G X (usym_power G g zero.) x) (gset_usym_act G X (usym_unit G) x) x
        (map_path (USym G) Xu (h ↦ gset_usym_act G X h x) (usym_power G g zero.) (usym_unit G) (usym_power_zero G g))
        (gset_act_unit G X x)
    | suc. k ↦ concat Xu (gset_usym_act G X (usym_power G g (suc. k)) x)
        (gset_usym_act G X (usym_mul G g (usym_power G g k)) x) x
        (map_path (USym G) Xu (h ↦ gset_usym_act G X h x) (usym_power G g (suc. k)) (usym_mul G g (usym_power G g k))
          (usym_power_suc G g k))
        (concat Xu (gset_usym_act G X (usym_mul G g (usym_power G g k)) x)
          (gset_usym_act G X g (gset_usym_act G X (usym_power G g k) x)) x
          (gset_act_mul G X g (usym_power G g k) x)
          (concat Xu (gset_usym_act G X g (gset_usym_act G X (usym_power G g k) x)) (gset_usym_act G X g x) x
            (map_path Xu Xu (gset_usym_act G X g) (gset_usym_act G X (usym_power G g k) x) x
              (stabilizer_power_fixed G X x g r k))
            r)) ]

def fingp_usym_point (G : Group) (P : USym G → Type) (u : Σ (USym G) P) : USym G ≔ u .fst

{` In a finite group of order p = b+1 (p prime), a symmetry g ≠ e with
   g^p = e generates: every t is g^r for some r < p. The powers g^r, r < p,
   are distinct, so they form a subset of USym G with p elements. `}
def prime_order_element_generates (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (suc. b)) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  (t : USym G) : Mere (Σ (Remainder (suc. b)) (r ↦ Id (USym G) t (usym_power G g (r .fst))))
  ≔ let U ≔ USym G in
    let n : Nat ≔ suc. b in
    let Rm ≔ Remainder n in
    let P : U → Type ≔ t' ↦ Mere (Σ Rm (r ↦ Id U t' (usym_power G g (r .fst)))) in
    let Q : U → Type ≔ _ ↦ Unit in
    let hP : (t' : U) → isProp (P t') ≔ t' ↦ mere_isprop (Σ Rm (r ↦ Id U t' (usym_power G g (r .fst)))) in
    let dU ≔ finite_group_decidable_equality G hG in
    let dP : (t' : U) → Decidable (P t')
      ≔ t' ↦ finite_quantifiers Rm (fingp_remainder_finite n) (r ↦ Id U t' (usym_power G g (r .fst)))
          (r ↦ usym_set G t' (usym_power G g (r .fst))) (r ↦ dU t' (usym_power G g (r .fst))) .snd in
    let f : Rm → Σ U P
      ≔ r ↦ (usym_power G g (r .fst), mere (Σ Rm (r' ↦ Id U (usym_power G g (r .fst)) (usym_power G g (r' .fst))))
          (r, refl (usym_power G g (r .fst)))) in
    let hyp ≔ prime_order_powers_nontrivial n hp G g h ne in
    let inj : PathReflecting Rm (Σ U P) f
      ≔ r r' e ↦ subtype_equal Nat (k ↦ BookLt k n) (k ↦ book_lt_prop k n) r r'
          (usym_power_injective_below G g n hyp (r .fst) (r' .fst) (r .snd) (r' .snd)
            (map_path (Σ U P) U (fingp_usym_point G P) (f r) (f r') e)) in
    let hSP : isSet (Σ U P) ≔ sigma_set U P (usym_set G) (t' ↦ prop_is_set (P t') (hP t')) in
    let surj : Surjective Rm (Σ U P) f
      ≔ u ↦ mere_rec (Σ Rm (r ↦ Id U (u .fst) (usym_power G g (r .fst)))) (Mere (BookFiber Rm (Σ U P) f u))
          (mere_isprop (BookFiber Rm (Σ U P) f u))
          (w ↦ mere (BookFiber Rm (Σ U P) f u) (w .fst, subtype_equal U P hP u (f (w .fst)) (w .snd)))
          (u .snd) in
    let eqv ≔ set_bijection_equiv Rm (Σ U P) hSP f inj surj in
    let fP : IsFinite (Σ U P) ≔ finite_decidable_subset U hG P hP dP in
    let eQ : Equiv (Σ U Q) U
      ≔ quasi_inverse_equiv (Σ U Q) U (fingp_usym_point G Q) (t' ↦ (t', star.))
          (u ↦ subtype_equal U Q (_ ↦ unit_prop) (u .fst, star.) u (refl (u .fst))) (t' ↦ refl t') in
    let fQ : IsFinite (Σ U Q) ≔ finite_of_equiv (Σ U Q) U eQ hG in
    let ce : Id Nat (cardinality (Σ U P) fP) (cardinality (Σ U Q) fQ)
      ≔ calc
          cardinality (Σ U P) fP
          = cardinality Rm (fingp_remainder_finite n)
            by inverse Nat (cardinality Rm (fingp_remainder_finite n)) (cardinality (Σ U P) fP)
              (cardinality_equiv Rm (Σ U P) eqv (fingp_remainder_finite n) fP)
          = n by fingp_remainder_card n
          = group_card G hG by inverse Nat (group_card G hG) n hc
          = cardinality (Σ U Q) fQ
            by inverse Nat (cardinality (Σ U Q) fQ) (group_card G hG) (cardinality_equiv (Σ U Q) U eQ fQ hG) ∎ in
    finite_subset_card_eq_full U P Q hP (_ ↦ unit_prop) dP (_ _ ↦ star.) fP fQ ce t star.

{` In C_{b+1} every symmetry t satisfies t^(b+1) = e. `}
def cyclic_group_power_order (b : Nat) (t : USym (cyclic_group (suc. b)))
  : Id (USym (cyclic_group (suc. b))) (usym_power (cyclic_group (suc. b)) t (suc. b)) (usym_unit (cyclic_group (suc. b)))
  ≔ let C ≔ cyclic_group (suc. b) in
    let s ≔ cyclic_group_generator b in
    let w ≔ cyclic_symmetry_power_index b t in
    let k ≔ w .fst in
    let p : Nat ≔ suc. b in
    calc
      usym_power C t p
      = usym_power C (usym_power C s k) p
        by map_path (USym C) (USym C) (u ↦ usym_power C u p) t (usym_power C s k)
          (inverse (USym C) (usym_power C s k) t (w .snd .snd))
      = usym_power C s (mul k p) by inverse (USym C) (usym_power C s (mul k p)) (usym_power C (usym_power C s k) p)
          (usym_power_mul C s k p)
      = usym_power C s (mul p k) by map_path Nat (USym C) (usym_power C s) (mul k p) (mul p k) (mul_comm k p)
      = usym_power C (usym_power C s p) k by usym_power_mul C s p k
      = usym_power C (usym_unit C) k
        by map_path (USym C) (USym C) (u ↦ usym_power C u k) (usym_power C s p) (usym_unit C) (cyclic_group_generator_order b)
      = usym_unit C by usym_power_unit C k ∎

{` cor:cyclicgroupsaresimple for finite (decidable) subgroups: a finite
   subgroup of C_p is trivial or the full subgroup. `}
def cyclic_prime_subgroup_cases (b : Nat) (hp : NatIsPrime (suc. b)) (S : Subgroups (cyclic_group (suc. b)))
  (hS : IsFiniteGroup (subgroup_group (cyclic_group (suc. b)) S))
  : Sum (IsTrivialSubgroup (cyclic_group (suc. b)) S) (Id (Subgroups (cyclic_group (suc. b))) S (group_full_subgroup (cyclic_group (suc. b))))
  ≔ let C ≔ cyclic_group (suc. b) in
    let hC ≔ cyclic_group_finite b in
    let H ≔ subgroup_group C S in
    match prime_divisors (suc. b) hp (group_card H hS)
      (transport Nat (k ↦ NatDivides (group_card H hS) k) (group_card C hC) (suc. b) (cyclic_group_card b hC)
        (lagrange_subgroup_divides C hC S hS)) [
    | inl. one ↦ inl. (usym_contractible_trivial_group H (finite_card_one_contractible (USym H) hS one))
    | inr. full ↦ inr. (lagrange_counting_equal_order C hC S hS
        (concat Nat (group_card H hS) (suc. b) (group_card C hC) full
          (inverse Nat (group_card C hC) (suc. b) (cyclic_group_card b hC)))) ]

{` Contractibility transported back along an equivalence. `}
def fingp_contr_equiv_back (A B : Type) (e : Equiv A B) (c : BookIsContr B) : BookIsContr A
  ≔ (equiv_inverse_map A B e (c .center),
     a ↦ concat A (equiv_inverse_map A B e (c .center)) (equiv_inverse_map A B e (e .map a)) a
       (map_path B A (equiv_inverse_map A B e) (c .center) (e .map a) (c .contract (e .map a)))
       (equiv_retraction A B e a))

{` If no g ≠ e fixes the point, the subgroup is trivial (finite G). `}
def stabilizer_trivial_subgroup (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (no : Not (Mere (Σ (USym G) (g ↦ Product (Not (Id (USym G) g (usym_unit G)))
    (Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point))))))
  : IsTrivialSubgroup G S
  ≔ let X ≔ S .gset in
    let Xu ≔ gset_underlying G X in
    let x0 ≔ S .point in
    let St ≔ GSetStabilizer G X x0 in
    let D ≔ Σ (USym G) (g ↦ Product (Not (Id (USym G) g (usym_unit G))) (Id Xu (gset_usym_act G X g x0) x0)) in
    let c : BookIsContr St
      ≔ ((usym_unit G, gset_act_unit G X x0),
         a ↦ subtype_equal (USym G) (g ↦ Id Xu (gset_usym_act G X g x0) x0)
           (g ↦ gset_underlying_set G X (gset_usym_act G X g x0) x0) (usym_unit G, gset_act_unit G X x0) a
           (match finite_group_decidable_equality G hG (a .fst) (usym_unit G) [
            | inl. q ↦ inverse (USym G) (a .fst) (usym_unit G) q
            | inr. nq ↦ absurd (Id (USym G) (usym_unit G) (a .fst)) (no (mere D (a .fst, (nq, a .snd)))) ])) in
    usym_contractible_trivial_group (subgroup_group G S)
      (fingp_contr_equiv_back (USym (subgroup_group G S)) St (subgroup_usym_stabilizer_equiv G S) c)

{` If some g ≠ e of C_p fixes the point, the G-set of the subgroup is a
   single point (the subgroup is not proper). `}
def cyclic_prime_fixed_contractible (b : Nat) (hp : NatIsPrime (suc. b)) (S : Subgroups (cyclic_group (suc. b)))
  (m : Mere (Σ (USym (cyclic_group (suc. b))) (g ↦ Product (Not (Id (USym (cyclic_group (suc. b))) g (usym_unit (cyclic_group (suc. b)))))
    (Id (gset_underlying (cyclic_group (suc. b)) (S .gset)) (gset_usym_act (cyclic_group (suc. b)) (S .gset) g (S .point)) (S .point)))))
  : BookIsContr (gset_underlying (cyclic_group (suc. b)) (S .gset))
  ≔ let C ≔ cyclic_group (suc. b) in
    let hC ≔ cyclic_group_finite b in
    let X ≔ S .gset in
    let Xu ≔ gset_underlying C X in
    let x0 ≔ S .point in
    let D ≔ Σ (USym C) (g ↦ Product (Not (Id (USym C) g (usym_unit C))) (Id Xu (gset_usym_act C X g x0) x0)) in
    (x0, y ↦ mere_rec D (Id Xu x0 y) (gset_underlying_set C X x0 y)
      (w ↦ mere_rec (GSetTransporter C X x0 y) (Id Xu x0 y) (gset_underlying_set C X x0 y)
        (v ↦ mere_rec (Σ (Remainder (suc. b)) (r ↦ Id (USym C) (v .fst) (usym_power C (w .fst) (r .fst))))
          (Id Xu x0 y) (gset_underlying_set C X x0 y)
          (u ↦ calc
            x0
            = gset_usym_act C X (usym_power C (w .fst) (u .fst .fst)) x0
              by inverse Xu (gset_usym_act C X (usym_power C (w .fst) (u .fst .fst)) x0) x0
                (stabilizer_power_fixed C X x0 (w .fst) (w .snd .snd) (u .fst .fst))
            = gset_usym_act C X (v .fst) x0
              by map_path (USym C) Xu (h ↦ gset_usym_act C X h x0) (usym_power C (w .fst) (u .fst .fst)) (v .fst)
                (inverse (USym C) (v .fst) (usym_power C (w .fst) (u .fst .fst)) (u .snd))
            = y by inverse Xu y (gset_usym_act C X (v .fst) x0) (v .snd) ∎)
          (prime_order_element_generates b hp C hC (cyclic_group_card b hC) (w .fst) (cyclic_group_power_order b (w .fst))
            (w .snd .fst) (v .fst)))
        (subgroup_point_reach C S y))
      m)

{` cor:cyclicgroupsaresimple as printed: C_p has no subgroup that is both
   non-trivial and proper. `}
def cyclic_prime_no_nontrivial_proper (b : Nat) (hp : NatIsPrime (suc. b)) (S : Subgroups (cyclic_group (suc. b)))
  : Not (Product (Not (IsTrivialSubgroup (cyclic_group (suc. b)) S)) (IsProperSubgroup (cyclic_group (suc. b)) S))
  ≔ np ↦
    let C ≔ cyclic_group (suc. b) in
    let X ≔ S .gset in
    let Xu ≔ gset_underlying C X in
    let D ≔ Mere (Σ (USym C) (g ↦ Product (Not (Id (USym C) g (usym_unit C)))
      (Id Xu (gset_usym_act C X g (S .point)) (S .point)))) in
    double_negated_decidability D (d ↦ match d [
      | inl. m ↦ np .snd (cyclic_prime_fixed_contractible b hp S m)
      | inr. no ↦ np .fst (stabilizer_trivial_subgroup C (cyclic_group_finite b) S no) ])

{` Litmus: C_2 and C_3 have no non-trivial proper subgroups. `}
def cyclic_two_no_nontrivial_proper (S : Subgroups (cyclic_group (suc. (suc. zero.))))
  : Not (Product (Not (IsTrivialSubgroup (cyclic_group (suc. (suc. zero.))) S))
      (IsProperSubgroup (cyclic_group (suc. (suc. zero.))) S))
  ≔ cyclic_prime_no_nontrivial_proper (suc. zero.) nat_prime_two S

def cyclic_three_no_nontrivial_proper (S : Subgroups (cyclic_group (suc. (suc. (suc. zero.)))))
  : Not (Product (Not (IsTrivialSubgroup (cyclic_group (suc. (suc. (suc. zero.)))) S))
      (IsProperSubgroup (cyclic_group (suc. (suc. (suc. zero.)))) S))
  ≔ cyclic_prime_no_nontrivial_proper (suc. (suc. zero.)) nat_prime_three S
