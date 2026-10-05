export "1013-sylow-example-tools"
export "1028-coprime-subgroup-kernel"

{` Chapter 10, the example at fingp.tex 27-33: a counting
   argument for subgroups of prime order.

   For a finite group G and a prime p = b+1, let Sub_p(G) be the set of
   subgroups of order p. Every g ≠ e with g^p = e generates a subgroup ⟨g⟩
   of order p, and a subgroup T of order p is ⟨t⟩ for each of its p - 1
   symmetries t ≠ e. Hence (order_p_period_count)

       |{g : USym G | g^p = e}| = 1 + |Sub_p(G)| · (p - 1),

   and when p divides |G| (McKay: p | |{g | g^p = e}|, module 1005) the
   number of subgroups of order p is ≡ 1 (mod p)
   (order_p_subgroups_congruent). Sub_p(G) is finite (it has decidable
   equality and is the image of the finite set of g ≠ e with g^p = e). `}

{` Membership of t in the subgroup S: t fixes the point. `}
def SubgroupHasMember (G : Group) (S : Subgroups G) (t : USym G) : Type
  ≔ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) t (S .point)) (S .point)

def subgroup_has_member_prop (G : Group) (S : Subgroups G) (t : USym G) : isProp (SubgroupHasMember G S t)
  ≔ gset_underlying_set G (S .gset) (gset_usym_act G (S .gset) t (S .point)) (S .point)

{` Subgroups of order k (finite, with k elements). `}
def FiniteOrderSubgroups (G : Group) (k : Nat) : Type
  ≔ Σ (Subgroups G) (S ↦ Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k))

def finite_order_data_prop (G : Group) (k : Nat) (S : Subgroups G)
  : isProp (Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k))
  ≔ sigma_prop (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k)
      (is_finite_group_prop (subgroup_group G S)) (hS ↦ nat_set (group_card (subgroup_group G S) hS) k)

def finite_order_subgroups_set (G : Group) (k : Nat) : isSet (FiniteOrderSubgroups G k)
  ≔ sigma_set (Subgroups G)
      (S ↦ Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k))
      (subgroups_set G)
      (S ↦ prop_is_set (Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k))
        (finite_order_data_prop G k S))

def finite_order_subgroups_path (G : Group) (k : Nat) (T T' : FiniteOrderSubgroups G k)
  (p : Id (Subgroups G) (T .fst) (T' .fst)) : Id (FiniteOrderSubgroups G k) T T'
  ≔ subtype_equal (Subgroups G)
      (S ↦ Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) k))
      (finite_order_data_prop G k) T T' p

{` Powers of a member are members. `}
def subgroup_has_member_power (G : Group) (S : Subgroups G) (t : USym G) (m : SubgroupHasMember G S t) (k : Nat)
  : SubgroupHasMember G S (usym_power G t k)
  ≔ match k [
  | zero. ↦ gset_act_unit G (S .gset) (S .point)
  | suc. k ↦
    let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    let x ≔ S .point in
    calc
      gset_usym_act G X (usym_mul G t (usym_power G t k)) x
      = gset_usym_act G X t (gset_usym_act G X (usym_power G t k) x) by gset_act_mul G X t (usym_power G t k) x
      = gset_usym_act G X t x
        by map_path Y Y (gset_usym_act G X t) (gset_usym_act G X (usym_power G t k) x) x (subgroup_has_member_power G S t m k)
      = x by m ∎ ]

{` A member t of a finite subgroup T of order c has t^c = e. `}
def subgroup_has_member_card_unit (G : Group) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S)) (c : Nat)
  (e : Id Nat (group_card (subgroup_group G S) hS) c) (t : USym G) (m : SubgroupHasMember G S t)
  : Id (USym G) (usym_power G t c) (usym_unit G)
  ≔ let K ≔ subgroup_group G S in
    let i ≔ subgroup_inclusion G S in
    let St ≔ GSetStabilizer G (S .gset) (S .point) in
    let E ≔ subgroup_usym_stabilizer_equiv G S in
    let h ≔ equiv_inverse_map (USym K) St E (t, m) in
    let hi : Id (USym G) (usym_hom K G i h) t
      ≔ concat (USym G) (usym_hom K G i h) (E .map h .fst) t (subgroup_inclusion_usym G S h)
          (map_path St (USym G) (fingp_usym_point G (g' ↦ Id (gset_underlying G (S .gset))
            (gset_usym_act G (S .gset) g' (S .point)) (S .point))) (E .map h) (t, m) (equiv_counit (USym K) St E (t, m))) in
    let hc : Id (USym K) (usym_power K h c) (usym_unit K)
      ≔ transport Nat (n ↦ Id (USym K) (usym_power K h n) (usym_unit K)) (group_card K hS) c e
          (usym_power_card_unit K hS h) in
    calc
      usym_power G t c
      = usym_power G (usym_hom K G i h) c
        by map_path (USym G) (USym G) (x ↦ usym_power G x c) t (usym_hom K G i h) (inverse (USym G) (usym_hom K G i h) t hi)
      = usym_hom K G i (usym_power K h c) by inverse (USym G) (usym_hom K G i (usym_power K h c)) (usym_power G (usym_hom K G i h) c)
          (usym_hom_power K G i h c)
      = usym_hom K G i (usym_unit K) by map_path (USym K) (USym G) (usym_hom K G i) (usym_power K h c) (usym_unit K) hc
      = usym_unit G by usym_hom_unit K G i ∎

{` The symmetries g ≠ e with g^p = e, and the subgroup ⟨g⟩ of order p. `}
def NontrivialPeriodElements (G : Group) (b : Nat) : Type
  ≔ Σ (USym G) (g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G))))

def nontrivial_period_prop (G : Group) (b : Nat) (g : USym G)
  : isProp (Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G))))
  ≔ product_prop (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G)))
      (usym_set G (usym_power G g (suc. b)) (usym_unit G)) (negation_prop (Id (USym G) g (usym_unit G)))

def generated_order_p_subgroup (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (u : NontrivialPeriodElements G b)
  : FiniteOrderSubgroups G (suc. b)
  ≔ let g ≔ u .fst in let h ≔ u .snd .fst in let ne ≔ u .snd .snd in
    let hS ≔ cyclic_prime_subgroup_finite b hp G g h ne in
    (cyclic_prime_subgroup b hp G g h ne, (hS, cyclic_prime_subgroup_card b hp G g h ne hS))

def generated_subgroup_member (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (u : NontrivialPeriodElements G b)
  : SubgroupHasMember G (generated_order_p_subgroup b hp G u .fst) (u .fst)
  ≔ let g ≔ u .fst in let h ≔ u .snd .fst in let ne ≔ u .snd .snd in
    let S ≔ cyclic_prime_subgroup b hp G g h ne in
    transport (USym G) (SubgroupHasMember G S) (usym_power G g (suc. zero.)) g (usym_power_one G g)
      (cyclic_subgroup_power_member b G g h (prime_order_powers_nontrivial (suc. b) hp G g h ne) (suc. zero.))

{` A member t ≠ e of a subgroup T of order p generates T. `}
def generated_subgroup_of_member (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (T : FiniteOrderSubgroups G (suc. b)) (t : USym G) (m : SubgroupHasMember G (T .fst) t) (ne : Not (Id (USym G) t (usym_unit G)))
  : Id (FiniteOrderSubgroups G (suc. b))
      (generated_order_p_subgroup b hp G (t, (subgroup_has_member_card_unit G (T .fst) (T .snd .fst) (suc. b) (T .snd .snd) t m, ne))) T
  ≔ let h ≔ subgroup_has_member_card_unit G (T .fst) (T .snd .fst) (suc. b) (T .snd .snd) t m in
    let C ≔ generated_order_p_subgroup b hp G (t, (h, ne)) in
    let le : SubgroupLe G (C .fst) (T .fst)
      ≔ s r ↦ mere_rec (Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym G) s (usym_power G t k))))
            (SubgroupHasMember G (T .fst) s) (subgroup_has_member_prop G (T .fst) s)
            (w ↦ transport (USym G) (SubgroupHasMember G (T .fst)) (usym_power G t (w .fst)) s
                   (inverse (USym G) s (usym_power G t (w .fst)) (w .snd .snd))
                   (subgroup_has_member_power G (T .fst) t m (w .fst)))
            (cyclic_subgroup_member_power b G t h (prime_order_powers_nontrivial (suc. b) hp G t h ne) s r) in
    finite_order_subgroups_path G (suc. b) C T
      (subgroup_le_card_eq G hG (C .fst) (T .fst) (C .snd .fst) (T .snd .fst) le
        (concat Nat (group_card (subgroup_group G (C .fst)) (C .snd .fst)) (suc. b)
          (group_card (subgroup_group G (T .fst)) (T .snd .fst)) (C .snd .snd)
          (inverse Nat (group_card (subgroup_group G (T .fst)) (T .snd .fst)) (suc. b) (T .snd .snd))))

{` The nontrivial members of T, and the fibers of u ↦ ⟨u⟩. `}
def NontrivialMembers (G : Group) (S : Subgroups G) : Type
  ≔ Σ (USym G) (t ↦ Product (SubgroupHasMember G S t) (Not (Id (USym G) t (usym_unit G))))

def generated_fiber_members_equiv (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (T : FiniteOrderSubgroups G (suc. b))
  : Equiv (BookFiber (NontrivialPeriodElements G b) (FiniteOrderSubgroups G (suc. b)) (generated_order_p_subgroup b hp G) T)
      (NontrivialMembers G (T .fst))
  ≔ let Sp ≔ FiniteOrderSubgroups G (suc. b) in
    let Pd : USym G → Type
      ≔ g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G))) in
    let F : USym G → Type ≔ g ↦ Σ (Pd g) (pn ↦ Id Sp T (generated_order_p_subgroup b hp G (g, pn))) in
    let M : USym G → Type ≔ g ↦ Product (SubgroupHasMember G (T .fst) g) (Not (Id (USym G) g (usym_unit G))) in
    compose_equiv (BookFiber (NontrivialPeriodElements G b) Sp (generated_order_p_subgroup b hp G) T) (Σ (USym G) F)
      (NontrivialMembers G (T .fst))
      (sigma_assoc (USym G) Pd (g pn ↦ Id Sp T (generated_order_p_subgroup b hp G (g, pn))))
      (family_equiv (USym G) F M (g ↦ iff_equiv (F g) (M g)
        (sigma_prop (Pd g) (pn ↦ Id Sp T (generated_order_p_subgroup b hp G (g, pn))) (nontrivial_period_prop G b g)
          (pn ↦ finite_order_subgroups_set G (suc. b) T (generated_order_p_subgroup b hp G (g, pn))))
        (product_prop (SubgroupHasMember G (T .fst) g) (Not (Id (USym G) g (usym_unit G))) (subgroup_has_member_prop G (T .fst) g)
          (negation_prop (Id (USym G) g (usym_unit G))))
        (w ↦ (transport Sp (T' ↦ SubgroupHasMember G (T' .fst) g) (generated_order_p_subgroup b hp G (g, w .fst)) T
                (inverse Sp T (generated_order_p_subgroup b hp G (g, w .fst)) (w .snd))
                (generated_subgroup_member b hp G (g, w .fst)),
              w .fst .snd))
        (m ↦ ((subgroup_has_member_card_unit G (T .fst) (T .snd .fst) (suc. b) (T .snd .snd) g (m .fst), m .snd),
              inverse Sp (generated_order_p_subgroup b hp G
                  (g, (subgroup_has_member_card_unit G (T .fst) (T .snd .fst) (suc. b) (T .snd .snd) g (m .fst), m .snd))) T
                (generated_subgroup_of_member b hp G hG T g (m .fst) (m .snd))))))

{` Decidability and finiteness. `}
def subgroup_has_member_decidable (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  (t : USym G) : Decidable (SubgroupHasMember G S t)
  ≔ subgroup_gset_decidable_equality G hG S hS (gset_usym_act G (S .gset) t (S .point)) (S .point)

def usym_ne_unit_decidable (G : Group) (hG : IsFiniteGroup G) (t : USym G) : Decidable (Not (Id (USym G) t (usym_unit G)))
  ≔ match finite_decidable_equality (USym G) hG t (usym_unit G) [
  | inl. e ↦ inr. (n ↦ n e)
  | inr. n ↦ inl. n ]

def nontrivial_members_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  : IsFinite (NontrivialMembers G S)
  ≔ finite_decidable_subset (USym G) hG (t ↦ Product (SubgroupHasMember G S t) (Not (Id (USym G) t (usym_unit G))))
      (t ↦ product_prop (SubgroupHasMember G S t) (Not (Id (USym G) t (usym_unit G))) (subgroup_has_member_prop G S t)
        (negation_prop (Id (USym G) t (usym_unit G))))
      (t ↦ match subgroup_has_member_decidable G hG S hS t [
        | inl. m ↦ match usym_ne_unit_decidable G hG t [
          | inl. n ↦ inl. (m, n)
          | inr. nn ↦ inr. (w ↦ nn (w .snd)) ]
        | inr. nm ↦ inr. (w ↦ nm (w .fst)) ])

def nontrivial_period_finite (G : Group) (hG : IsFiniteGroup G) (b : Nat) : IsFinite (NontrivialPeriodElements G b)
  ≔ finite_decidable_subset (USym G) hG
      (g ↦ Product (Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (Not (Id (USym G) g (usym_unit G))))
      (nontrivial_period_prop G b)
      (g ↦ match finite_decidable_equality (USym G) hG (usym_power G g (suc. b)) (usym_unit G) [
        | inl. h ↦ match usym_ne_unit_decidable G hG g [
          | inl. n ↦ inl. (h, n)
          | inr. nn ↦ inr. (w ↦ nn (w .snd)) ]
        | inr. nh ↦ inr. (w ↦ nh (w .fst)) ])

{` A subgroup with c elements: the stabilizer splits as {e} + nontrivial members. `}
def subgroup_unit_member_contr (G : Group) (S : Subgroups G)
  : BookIsContr (Σ (GSetStabilizer G (S .gset) (S .point)) (s ↦ Id (USym G) (s .fst) (usym_unit G)))
  ≔ let St ≔ GSetStabilizer G (S .gset) (S .point) in
    let c0 : Σ St (s ↦ Id (USym G) (s .fst) (usym_unit G))
      ≔ ((usym_unit G, gset_act_unit G (S .gset) (S .point)), refl (usym_unit G)) in
    (c0, w ↦ subtype_equal St (s ↦ Id (USym G) (s .fst) (usym_unit G)) (s ↦ usym_set G (s .fst) (usym_unit G)) c0 w
       (subtype_equal (USym G) (SubgroupHasMember G S) (subgroup_has_member_prop G S) (c0 .fst) (w .fst)
         (inverse (USym G) (w .fst .fst) (usym_unit G) (w .snd))))

def nontrivial_members_card (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  (b : Nat) (e : Id Nat (group_card (subgroup_group G S) hS) (suc. b)) (hN : IsFinite (NontrivialMembers G S))
  : Id Nat (cardinality (NontrivialMembers G S) hN) b
  ≔ let St ≔ GSetStabilizer G (S .gset) (S .point) in
    let Pe : St → Type ≔ s ↦ Id (USym G) (s .fst) (usym_unit G) in
    let A ≔ Σ St Pe in
    let B ≔ Σ St (s ↦ Not (Pe s)) in
    let N ≔ NontrivialMembers G S in
    let eStab ≔ subgroup_usym_stabilizer_equiv G S in
    let hSt : IsFinite St ≔ finite_of_equiv St (USym (subgroup_group G S)) (canonical_inverse_equiv (USym (subgroup_group G S)) St eStab) hS in
    let spl ≔ fingp_decidable_split_equiv St Pe (s ↦ usym_set G (s .fst) (usym_unit G))
      (s ↦ finite_decidable_equality (USym G) hG (s .fst) (usym_unit G)) in
    let hA : IsFinite A ≔ finite_of_equiv A (Fin (suc. zero.)) (fingp_contractible_fin_one_equiv A (subgroup_unit_member_contr G S))
          (fin_is_finite (suc. zero.)) in
    let eBN : Equiv B N
      ≔ quasi_inverse_equiv B N (w ↦ (w .fst .fst, (w .fst .snd, w .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd))
          (w ↦ refl w) (w ↦ refl w) in
    let hB : IsFinite B ≔ finite_of_equiv B N eBN hN in
    let hAB : IsFinite (Sum A B) ≔ finite_of_equiv (Sum A B) St (canonical_inverse_equiv St (Sum A B) spl) hSt in
    let cSt : Id Nat (cardinality St hSt) (suc. b)
      ≔ concat Nat (cardinality St hSt) (group_card (subgroup_group G S) hS) (suc. b)
          (cardinality_equiv St (USym (subgroup_group G S)) (canonical_inverse_equiv (USym (subgroup_group G S)) St eStab) hSt hS) e in
    let cA : Id Nat (cardinality A hA) (suc. zero.)
      ≔ cardinality_equiv A (Fin (suc. zero.)) (fingp_contractible_fin_one_equiv A (subgroup_unit_member_contr G S)) hA
          (fin_is_finite (suc. zero.)) in
    let total : Id Nat (add (suc. zero.) (cardinality B hB)) (add (suc. zero.) b)
      ≔ calc
          add (suc. zero.) (cardinality B hB)
          = add (cardinality A hA) (cardinality B hB)
            by map_path Nat Nat (x ↦ add x (cardinality B hB)) (suc. zero.) (cardinality A hA) (inverse Nat (cardinality A hA) (suc. zero.) cA)
          = cardinality (Sum A B) hAB by inverse Nat (cardinality (Sum A B) hAB) (add (cardinality A hA) (cardinality B hB))
              (cardinality_sum A B hA hB hAB)
          = cardinality St hSt by inverse Nat (cardinality St hSt) (cardinality (Sum A B) hAB) (cardinality_equiv St (Sum A B) spl hSt hAB)
          = suc. b by cSt
          = add (suc. zero.) b by add_comm b (suc. zero.) ∎ in
    concat Nat (cardinality N hN) (cardinality B hB) b
      (cardinality_equiv N B (canonical_inverse_equiv B N eBN) hN hB)
      (add_cancel_left (suc. zero.) (cardinality B hB) b total)

{` Sub_p(G) has decidable equality and is finite. `}
def finite_order_subgroups_decidable (G : Group) (hG : IsFiniteGroup G) (k : Nat) : DecidableEquality (FiniteOrderSubgroups G k)
  ≔ T T' ↦
    let dX ≔ subgroup_gset_decidable_equality G hG (T .fst) (T .snd .fst) in
    let dY ≔ subgroup_gset_decidable_equality G hG (T' .fst) (T' .snd .fst) in
    match subgroup_fixes_decidable G hG (T .fst) dX (T' .fst .gset) dY (T' .fst .point) [
    | inl. c ↦ match subgroup_fixes_decidable G hG (T' .fst) dY (T .fst .gset) dX (T .fst .point) [
      | inl. d ↦ inl. (finite_order_subgroups_path G k T T' (subgroup_le_antisym G (T .fst) (T' .fst) c d))
      | inr. nd ↦ inr. (q ↦ nd (subgroup_path_fixes G (T' .fst) (T .fst)
                          (inverse (Subgroups G) (T .fst) (T' .fst) (refl ((x ↦ x .fst) : FiniteOrderSubgroups G k → Subgroups G) q)))) ]
    | inr. nc ↦ inr. (q ↦ nc (subgroup_path_fixes G (T .fst) (T' .fst)
                        (refl ((x ↦ x .fst) : FiniteOrderSubgroups G k → Subgroups G) q))) ]

def order_p_subgroups_finite (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  : IsFinite (FiniteOrderSubgroups G (suc. b))
  ≔ let E ≔ NontrivialPeriodElements G b in
    let Sp ≔ FiniteOrderSubgroups G (suc. b) in
    let f ≔ generated_order_p_subgroup b hp G in
    finite_surjection_target E Sp (nontrivial_period_finite G hG b) (finite_order_subgroups_decidable G hG (suc. b)) f
      (T ↦
        let N ≔ NontrivialMembers G (T .fst) in
        let hN ≔ nontrivial_members_finite G hG (T .fst) (T .snd .fst) in
        let cN ≔ nontrivial_members_card G hG (T .fst) (T .snd .fst) b (T .snd .snd) hN in
        let e ≔ generated_fiber_members_equiv b hp G hG T in
        mere_rec N (Mere (BookFiber E Sp f T)) (mere_isprop (BookFiber E Sp f T))
          (n ↦ mere (BookFiber E Sp f T) (equiv_inverse_map (BookFiber E Sp f T) N e n))
          (finite_card_nonzero_inhabited N hN
            (z ↦ match b [
              | zero. ↦ match hp .fst []
              | suc. b' ↦ nat_zero_ne_suc b' (concat Nat zero. (cardinality N hN) (suc. b')
                                                (inverse Nat (cardinality N hN) zero. z) cN) ])))

{` |{g | g^p = e}| = 1 + |Sub_p(G)| · (p - 1). `}
def order_p_period_count (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hQ : IsFinite (McKayPeriodElements G b)) (hS : IsFinite (FiniteOrderSubgroups G (suc. b)))
  : Id Nat (cardinality (McKayPeriodElements G b) hQ) (add (suc. zero.) (mul (cardinality (FiniteOrderSubgroups G (suc. b)) hS) b))
  ≔ let Q ≔ McKayPeriodElements G b in
    let E ≔ NontrivialPeriodElements G b in
    let Sp ≔ FiniteOrderSubgroups G (suc. b) in
    let f ≔ generated_order_p_subgroup b hp G in
    let Fib : Sp → Type ≔ T ↦ BookFiber E Sp f T in
    let hE ≔ nontrivial_period_finite G hG b in
    let hFib : (T : Sp) → IsFinite (Fib T)
      ≔ T ↦ finite_of_equiv (Fib T) (NontrivialMembers G (T .fst)) (generated_fiber_members_equiv b hp G hG T)
              (nontrivial_members_finite G hG (T .fst) (T .snd .fst)) in
    let eSum : Equiv (Σ Sp Fib) E ≔ sum_of_fibers_equiv E Sp f in
    let hSum : IsFinite (Σ Sp Fib) ≔ finite_of_equiv (Σ Sp Fib) E eSum hE in
    let cE : Id Nat (cardinality E hE) (mul (cardinality Sp hS) b)
      ≔ concat Nat (cardinality E hE) (cardinality (Σ Sp Fib) hSum) (mul (cardinality Sp hS) b)
          (cardinality_equiv E (Σ Sp Fib) (canonical_inverse_equiv (Σ Sp Fib) E eSum) hE hSum)
          (cardinality_sigma_constant Sp hS Fib hFib hSum b
            (T ↦ concat Nat (cardinality (Fib T) (hFib T)) (cardinality (NontrivialMembers G (T .fst))
                     (nontrivial_members_finite G hG (T .fst) (T .snd .fst))) b
                   (cardinality_equiv (Fib T) (NontrivialMembers G (T .fst)) (generated_fiber_members_equiv b hp G hG T) (hFib T)
                     (nontrivial_members_finite G hG (T .fst) (T .snd .fst)))
                   (nontrivial_members_card G hG (T .fst) (T .snd .fst) b (T .snd .snd)
                     (nontrivial_members_finite G hG (T .fst) (T .snd .fst))))) in
    let Pe : Q → Type ≔ u ↦ Id (USym G) (u .fst) (usym_unit G) in
    let A ≔ Σ Q Pe in
    let B ≔ Σ Q (u ↦ Not (Pe u)) in
    let spl ≔ fingp_decidable_split_equiv Q Pe (u ↦ usym_set G (u .fst) (usym_unit G))
      (u ↦ finite_decidable_equality (USym G) hG (u .fst) (usym_unit G)) in
    let c0 : A ≔ ((usym_unit G, usym_power_unit G (suc. b)), refl (usym_unit G)) in
    let cA : BookIsContr A
      ≔ (c0, w ↦ subtype_equal Q Pe (u ↦ usym_set G (u .fst) (usym_unit G)) c0 w
           (subtype_equal (USym G) (g ↦ Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
             (g ↦ usym_set G (usym_power G g (suc. b)) (usym_unit G)) (c0 .fst) (w .fst)
             (inverse (USym G) (w .fst .fst) (usym_unit G) (w .snd)))) in
    let hA : IsFinite A ≔ finite_of_equiv A (Fin (suc. zero.)) (fingp_contractible_fin_one_equiv A cA) (fin_is_finite (suc. zero.)) in
    let eBE : Equiv B E
      ≔ quasi_inverse_equiv B E (w ↦ (w .fst .fst, (w .fst .snd, w .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd))
          (w ↦ refl w) (w ↦ refl w) in
    let hB : IsFinite B ≔ finite_of_equiv B E eBE hE in
    let hAB : IsFinite (Sum A B) ≔ finite_of_equiv (Sum A B) Q (canonical_inverse_equiv Q (Sum A B) spl) hQ in
    calc
      cardinality Q hQ
      = cardinality (Sum A B) hAB by cardinality_equiv Q (Sum A B) spl hQ hAB
      = add (cardinality A hA) (cardinality B hB) by cardinality_sum A B hA hB hAB
      = add (suc. zero.) (cardinality B hB)
        by map_path Nat Nat (x ↦ add x (cardinality B hB)) (cardinality A hA) (suc. zero.)
             (cardinality_equiv A (Fin (suc. zero.)) (fingp_contractible_fin_one_equiv A cA) hA (fin_is_finite (suc. zero.)))
      = add (suc. zero.) (cardinality E hE) by map_path Nat Nat (add (suc. zero.)) (cardinality B hB) (cardinality E hE)
          (cardinality_equiv B E eBE hB hE)
      = add (suc. zero.) (mul (cardinality Sp hS) b) by map_path Nat Nat (add (suc. zero.)) (cardinality E hE) (mul (cardinality Sp hS) b) cE ∎

{` Arithmetic: a + k·p = c + l·p implies a ≡ c (mod p). `}
def nat_congruent_of_shift (p a c k l : Nat) (e : Id Nat (add a (mul k p)) (add c (mul l p))) : NatCongruent p a c
  ≔ match k, l [
  | zero., l ↦ nat_congruent_intro p a c l
      (concat Nat a (add a (mul zero. p)) (add c (mul l p))
        (inverse Nat (add a (mul zero. p)) a (map_path Nat Nat (add a) (mul zero. p) zero. (mul_zero_left p))) e)
  | suc. k, zero. ↦ nat_congruent_sym p c a (nat_congruent_intro p c a (suc. k)
      (concat Nat c (add c (mul zero. p)) (add a (mul (suc. k) p))
        (inverse Nat (add c (mul zero. p)) c (map_path Nat Nat (add c) (mul zero. p) zero. (mul_zero_left p)))
        (inverse Nat (add a (mul (suc. k) p)) (add c (mul zero. p)) e)))
  | suc. k, suc. l ↦ nat_congruent_of_shift p a c k l
      (add_cancel_right p (add a (mul k p)) (add c (mul l p))
        (calc
          add (add a (mul k p)) p
          = add a (add (mul k p) p) by add_assoc a (mul k p) p
          = add a (mul (suc. k) p) by map_path Nat Nat (add a) (add (mul k p) p) (mul (suc. k) p)
              (inverse Nat (mul (suc. k) p) (add (mul k p) p) (mul_suc_left k p))
          = add c (mul (suc. l) p) by e
          = add c (add (mul l p) p) by map_path Nat Nat (add c) (mul (suc. l) p) (add (mul l p) p) (mul_suc_left l p)
          = add (add c (mul l p)) p by inverse Nat (add (add c (mul l p)) p) (add c (add (mul l p) p)) (add_assoc c (mul l p) p) ∎)) ]

{` p | 1 + s·(p-1) implies s ≡ 1 (mod p). `}
def nat_congruent_one_of_divides (b s : Nat) (d : NatDivides (suc. b) (add (suc. zero.) (mul s b)))
  : NatCongruent (suc. b) s (suc. zero.)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat (add (suc. zero.) (mul s b)) (mul q (suc. b))))
      (NatCongruent (suc. b) s (suc. zero.)) (nat_congruent_prop (suc. b) s (suc. zero.))
      (u ↦ nat_congruent_of_shift (suc. b) s (suc. zero.) (u .fst) s
        (calc
          add s (mul (u .fst) (suc. b))
          = add s (add (suc. zero.) (mul s b))
            by map_path Nat Nat (add s) (mul (u .fst) (suc. b)) (add (suc. zero.) (mul s b))
                 (inverse Nat (add (suc. zero.) (mul s b)) (mul (u .fst) (suc. b)) (u .snd))
          = add (add s (suc. zero.)) (mul s b) by inverse Nat (add (add s (suc. zero.)) (mul s b)) (add s (add (suc. zero.) (mul s b)))
              (add_assoc s (suc. zero.) (mul s b))
          = add (add (suc. zero.) s) (mul s b) by map_path Nat Nat (x ↦ add x (mul s b)) (add s (suc. zero.)) (add (suc. zero.) s)
              (add_comm s (suc. zero.))
          = add (suc. zero.) (add s (mul s b)) by add_assoc (suc. zero.) s (mul s b)
          = add (suc. zero.) (add (mul s b) s) by map_path Nat Nat (add (suc. zero.)) (add s (mul s b)) (add (mul s b) s)
              (add_comm s (mul s b)) ∎))
      d

{` The number of subgroups of order p is ≡ 1 (mod p) when p | |G|. `}
def order_p_subgroups_congruent (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hd : NatDivides (suc. b) (group_card G hG)) (hS : IsFinite (FiniteOrderSubgroups G (suc. b)))
  : NatCongruent (suc. b) (cardinality (FiniteOrderSubgroups G (suc. b)) hS) (suc. zero.)
  ≔ let hQ ≔ cauchy_period_elements_finite G b hG in
    nat_congruent_one_of_divides b (cardinality (FiniteOrderSubgroups G (suc. b)) hS)
      (transport Nat (NatDivides (suc. b)) (cardinality (McKayPeriodElements G b) hQ)
        (add (suc. zero.) (mul (cardinality (FiniteOrderSubgroups G (suc. b)) hS) b))
        (order_p_period_count b hp G hG hQ hS)
        (cauchy_period_elements_divisible b hp G hG hd hQ))
