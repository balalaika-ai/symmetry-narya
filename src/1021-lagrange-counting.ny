export "1020-finite-subgroup-counting"

{` Chapter 10, lem:Lagrangeascounting (fingp.tex 69): for a subgroup
   (X, pt) of a finite group G with underlying group H,
   |G| = |G/H| · |H|, where G/H is the set X(sh_G) (equivalently, for the
   monomorphism i : H → G, the preimage Bi⁻¹(sh_G)), and |H| = |G| forces
   H = G as subgroups of G.

   Deviation: the book asserts that G/H and H are finite for every
   subgroup of a finite group. That cannot be proved constructively
   (module 1022 shows it is equivalent to excluded middle); the lemma
   assumes that H is finite, which by module 1020 is equivalent to the
   finiteness of G/H and to the decidability of the subgroup. `}

{` The full subgroup: G as a subgroup of G, E(G, id). `}
def group_hom_id_mono (G : Group) : IsGroupMono G G (group_hom_id G)
  ≔ let f ≔ usym_hom G G (group_hom_id G) in
    path_reflecting_set_embedding (USym G) (USym G) (usym_set G) f
      (g h e ↦ concat (USym G) g (f g) h (inverse (USym G) (f g) g (usym_hom_id G g))
        (concat (USym G) (f g) (f h) h e (usym_hom_id G h)))

def group_full_subgroup (G : Group) : Subgroups G
  ≔ mono_to_subgroup G (G, (group_hom_id G, group_hom_id_mono G))

def group_full_subgroup_fibers_contractible (G : Group) (z : BG G .carrier)
  : BookIsContr (group_full_subgroup G .gset z .fst)
  ≔ book_contraction (Σ (BG G .carrier) (a ↦ Id (BG G .carrier) z a)) (iscontr_idfrom (BG G .carrier) z)

{` A subgroup whose G-set has a contractible underlying set (a non-proper
   subgroup, def:triv-proper-Mono) is the full subgroup. `}
def subgroup_full_of_contractible (G : Group) (S : Subgroups G)
  (c : BookIsContr (gset_underlying G (S .gset))) : Id (Subgroups G) S (group_full_subgroup G)
  ≔ let B ≔ BG G .carrier in
    let X ≔ S .gset in
    let F ≔ group_full_subgroup G .gset in
    let cX : (z : B) → BookIsContr (X z .fst)
      ≔ connected_based_elim native_truncation B (bg_connected G) (shape G) (z ↦ BookIsContr (X z .fst))
          (z ↦ book_iscontr_isprop (X z .fst)) c in
    let cF : (z : B) → BookIsContr (F z .fst) ≔ group_full_subgroup_fibers_contractible G in
    let e : (z : B) → Equiv (X z .fst) (F z .fst)
      ≔ z ↦ (_ ↦ cF z .center, contractible_map_equiv (X z .fst) (F z .fst) (_ ↦ cF z .center) (cX z) (cF z)) in
    subgroup_path G S (group_full_subgroup G)
      (pointed_gset_path G X F (S .point) (group_full_subgroup G .point) e
        (contractible_prop (F (shape G) .fst) (native_contraction (F (shape G) .fst) (cF (shape G)))
          (e (shape G) .map (S .point)) (group_full_subgroup G .point)))

{` Small arithmetic and counting helpers. `}
def fingp_fin_inhabited_positive (n : Nat) : Fin n → Lt zero. n
  ≔ match n [ zero. ↦ i ↦ match i [] | suc. k ↦ _ ↦ star. ]

def fingp_fin_one_prop : isProp (Fin (suc. zero.))
  ≔ x y ↦ match x [
    | inl. e ↦ match e []
    | inr. a ↦ match y [
      | inl. e ↦ match e []
      | inr. b ↦ inr. (unit_prop a b) ] ]

def finite_inhabited_card_positive (A : Type) (h : IsFinite A) (a : A) : Lt zero. (cardinality A h)
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) (Lt zero. (cardinality A h)) (le_prop (suc. zero.) (cardinality A h))
      (p ↦ fingp_fin_inhabited_positive (cardinality A h) (id_to_equiv A (Fin (cardinality A h)) p .map a))
      (cardinality_spec A h)

def finite_group_card_positive (G : Group) (hG : IsFiniteGroup G) : Lt zero. (group_card G hG)
  ≔ finite_inhabited_card_positive (USym G) hG (usym_unit G)

def fingp_mul_self_one (q m : Nat) : Lt zero. m → Id Nat m (mul q m) → Id Nat q (suc. zero.)
  ≔ match q [
  | zero. ↦ match m [
    | zero. ↦ pos _ ↦ match pos []
    | suc. m' ↦ _ e ↦ absurd (Id Nat zero. (suc. zero.))
        (nat_zero_ne_suc m' (inverse Nat (suc. m') zero.
          (concat Nat (suc. m') (mul zero. (suc. m')) zero. e (mul_zero_left (suc. m'))))) ]
  | suc. q' ↦ match q' [
    | zero. ↦ _ _ ↦ refl (suc. zero. : Nat)
    | suc. k ↦ match m [
      | zero. ↦ pos _ ↦ match pos []
      | suc. m' ↦ _ e ↦
        let t ≔ mul (suc. k) (suc. m') in
        let z : Id Nat zero. t
          ≔ add_cancel_right (suc. m') zero. t
              (concat Nat (add zero. (suc. m')) (suc. m') (add t (suc. m'))
                (add_zero_left (suc. m'))
                (concat Nat (suc. m') (mul (suc. (suc. k)) (suc. m')) (add t (suc. m')) e
                  (mul_suc_left (suc. k) (suc. m')))) in
        absurd (Id Nat (suc. (suc. k)) (suc. zero.))
          (nat_zero_ne_suc (add (mul k (suc. m')) m') (concat Nat zero. t (suc. (add (mul k (suc. m')) m')) z
            (mul_suc_left k (suc. m')))) ] ] ]

def finite_card_one_contractible (A : Type) (h : IsFinite A) (q : Id Nat (cardinality A h) (suc. zero.))
  : BookIsContr A
  ≔ let hp : isProp A
      ≔ mere_rec (Id Type A (Fin (cardinality A h))) (isProp A) (isprop_isprop A)
          (p ↦ transport Type isProp (Fin (cardinality A h)) A (inverse Type A (Fin (cardinality A h)) p)
            (transport Nat (n ↦ isProp (Fin n)) (suc. zero.) (cardinality A h) (inverse Nat (cardinality A h) (suc. zero.) q)
              fingp_fin_one_prop))
          (cardinality_spec A h) in
    mere_rec A (BookIsContr A) (book_iscontr_isprop A) (a ↦ (a, b ↦ hp a b)) (cardinality_one_inhabited A h q)

{` lem:Lagrangeascounting, first statement: |G| = |G/H| · |H| with
   G/H = X(sh_G), for a subgroup (X, pt) with finite underlying group H. `}
def lagrange_counting (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S))
  : Id Nat (group_card G hG) (mul (gset_card G (S .gset) (subgroup_gset_finite G hG S hH)) (group_card (subgroup_group G S) hH))
  ≔ let X ≔ S .gset in
    let hX ≔ subgroup_gset_finite G hG S hH in
    let St ≔ GSetStabilizer G X (S .point) in
    let hSt ≔ gset_stabilizer_finite G hG X (finite_decidable_equality (gset_underlying G X) hX) (S .point) in
    concat Nat (group_card G hG) (mul (gset_card G X hX) (cardinality St hSt))
      (mul (gset_card G X hX) (group_card (subgroup_group G S) hH))
      (gset_orbit_card_identity G hG X hX (S .point) (subgroup_point_reach G S))
      (refl (mul (gset_card G X hX))
        (cardinality_equiv St (USym (subgroup_group G S))
          (canonical_inverse_equiv (USym (subgroup_group G S)) St (subgroup_usym_stabilizer_equiv G S)) hSt hH))

{` Consequences: |H| and |G/H| divide |G|. `}
def lagrange_subgroup_divides (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S)) : NatDivides (group_card (subgroup_group G S) hH) (group_card G hG)
  ≔ mere (Σ Nat (q ↦ Id Nat (group_card G hG) (mul q (group_card (subgroup_group G S) hH))))
      (gset_card G (S .gset) (subgroup_gset_finite G hG S hH), lagrange_counting G hG S hH)

def lagrange_index_divides (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S))
  : NatDivides (gset_card G (S .gset) (subgroup_gset_finite G hG S hH)) (group_card G hG)
  ≔ let i ≔ gset_card G (S .gset) (subgroup_gset_finite G hG S hH) in
    let h ≔ group_card (subgroup_group G S) hH in
    mere (Σ Nat (q ↦ Id Nat (group_card G hG) (mul q i)))
      (h, concat Nat (group_card G hG) (mul i h) (mul h i) (lagrange_counting G hG S hH) (mul_comm i h))

{` lem:Lagrangeascounting, second statement: if |H| = |G| then H = G as
   subgroups of G. As in the book's proof, |G/H| = 1, so G/H = X(sh_G) is
   contractible. `}
def lagrange_index_one (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S)) (e : Id Nat (group_card (subgroup_group G S) hH) (group_card G hG))
  : Id Nat (gset_card G (S .gset) (subgroup_gset_finite G hG S hH)) (suc. zero.)
  ≔ let i ≔ gset_card G (S .gset) (subgroup_gset_finite G hG S hH) in
    fingp_mul_self_one i (group_card G hG) (finite_group_card_positive G hG)
      (concat Nat (group_card G hG) (mul i (group_card (subgroup_group G S) hH)) (mul i (group_card G hG))
        (lagrange_counting G hG S hH) (refl (mul i) e))

def lagrange_counting_equal_order (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S)) (e : Id Nat (group_card (subgroup_group G S) hH) (group_card G hG))
  : Id (Subgroups G) S (group_full_subgroup G)
  ≔ subgroup_full_of_contractible G S
      (finite_card_one_contractible (gset_underlying G (S .gset)) (subgroup_gset_finite G hG S hH)
        (lagrange_index_one G hG S hH e))

{` Invariance of finiteness and cardinality under identifications of groups. `}
def group_finite_path (G H : Group) (p : Id Group G H) (hG : IsFiniteGroup G) : IsFiniteGroup H
  ≔ transport Group IsFiniteGroup G H p hG

def group_card_path (G H : Group) (p : Id Group G H) (hG : IsFiniteGroup G) (hH : IsFiniteGroup H)
  : Id Nat (group_card G hG) (group_card H hH)
  ≔ cardinality_equiv (USym G) (USym H) (id_to_equiv (USym G) (USym H) (refl USym p)) hG hH

{` lem:Lagrangeascounting for a monomorphism i : Hom(H, G) with H finite:
   |G| = |Bi⁻¹(sh_G)| · |H| (the book's proof: "the preimage Bi⁻¹(pt) is
   equivalent to the set G/H"). The set Bi⁻¹(sh_G) is the underlying set
   of E(H, i) and is finite. `}
def lagrange_counting_mono (G : Group) (hG : IsFiniteGroup G) (m : GroupMonos G) (hH : IsFiniteGroup (m .fst))
  : Id Nat (group_card G hG)
      (mul (gset_card G (mono_gset G m)
             (subgroup_gset_finite G hG (mono_to_subgroup G m)
               (group_finite_path (m .fst) (subgroup_group G (mono_to_subgroup G m))
                 (inverse Group (subgroup_group G (mono_to_subgroup G m)) (m .fst) (mono_subgroup_group_path G m)) hH)))
        (group_card (m .fst) hH))
  ≔ let S ≔ mono_to_subgroup G m in
    let hS ≔ group_finite_path (m .fst) (subgroup_group G S)
      (inverse Group (subgroup_group G S) (m .fst) (mono_subgroup_group_path G m)) hH in
    let i ≔ gset_card G (mono_gset G m) (subgroup_gset_finite G hG S hS) in
    concat Nat (group_card G hG) (mul i (group_card (subgroup_group G S) hS)) (mul i (group_card (m .fst) hH))
      (lagrange_counting G hG S hS)
      (refl (mul i) (group_card_path (subgroup_group G S) (m .fst) (mono_subgroup_group_path G m) hS hH))

{` Litmus: the full subgroup has a contractible G-set (index 1). `}
def group_full_subgroup_contractible_set (G : Group)
  : BookIsContr (gset_underlying G (group_full_subgroup G .gset))
  ≔ group_full_subgroup_fibers_contractible G (shape G)
