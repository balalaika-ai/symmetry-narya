export "1031-gset-automorphisms-conjugates"
export "561-gset-coverings-subsets"

{` Chapter 10, supporting material for thm:sylow3 (fingp.tex 292-307): a
   variant of lem:fixedptsize for a decidable subset A of a finite G-set
   that is closed under the action. If |G| = p^n and p does not divide
   the number of elements of A, then A contains a fixed point. The subset
   is made into a G-set by xca:SubGX-closedSubXshG (gsubset_extend of
   module 561). The second form is for a subgroup S acting on a G-set
   through the restricted action. `}

{` The underlying set of the G-subset extending a closed subset Q is
   equivalent to Σ_x Q(x). `}
def closed_subset_gset (H : Group) (Z : GSet H) (Q : GSetClosedSubsets H Z) : GSet H
  ≔ gsubset_gset H Z (gsubset_extend H Z Q)

def closed_subset_point (H : Group) (Z : GSet H) (Q : GSetClosedSubsets H Z)
  (u : gset_underlying H (closed_subset_gset H Z Q)) : gset_underlying H Z
  ≔ u .fst

def closed_subset_underlying_equiv (H : Group) (Z : GSet H) (Q : GSetClosedSubsets H Z)
  : Equiv (gset_underlying H (closed_subset_gset H Z Q)) (Σ (gset_underlying H Z) (x ↦ Q .fst x .fst))
  ≔ let B ≔ BG H .carrier in
    let Zu ≔ gset_underlying H Z in
    let E ≔ gsubset_extend H Z Q in
    let U ≔ gset_underlying H (closed_subset_gset H Z Q) in
    let fwd : U → Σ Zu (x ↦ Q .fst x .fst)
      ≔ u ↦ (u .fst, transport Zu (x ↦ Q .fst x .fst) (gset_act H Z (shape H) (shape H) (refl (shape H)) (u .fst))
              (u .fst) (gset_act_refl H Z (shape H) (u .fst)) (u .snd (refl (shape H)))) in
    let bwd : Σ Zu (x ↦ Q .fst x .fst) → U
      ≔ v ↦ (v .fst, r ↦ Q .snd (v .fst) (v .snd) r) in
    quasi_inverse_equiv U (Σ Zu (x ↦ Q .fst x .fst)) fwd bwd
      (u ↦ subtype_equal Zu (x ↦ E (shape H) x .fst) (x ↦ E (shape H) x .snd) (bwd (fwd u)) u (refl (u .fst)))
      (v ↦ subtype_equal Zu (x ↦ Q .fst x .fst) (x ↦ Q .fst x .snd) (fwd (bwd v)) v (refl (v .fst)))

def p_group_closed_subset_fixed_point (p : Nat) (hp : NatIsPrime p) (n : Nat) (H : Group) (hH : IsFiniteGroup H)
  (hc : Id Nat (group_card H hH) (nat_power p n)) (Z : GSet H) (hZ : IsFiniteGSet H Z)
  (Q : GSetClosedSubsets H Z) (dQ : (x : gset_underlying H Z) → Decidable (Q .fst x .fst))
  (nd : Not (NatDivides p (cardinality (Σ (gset_underlying H Z) (x ↦ Q .fst x .fst))
    (finite_decidable_subset (gset_underlying H Z) hZ (x ↦ Q .fst x .fst) (x ↦ Q .fst x .snd) dQ))))
  : Mere (Σ (gset_underlying H Z)
      (x ↦ Product (Q .fst x .fst) ((h : USym H) → Id (gset_underlying H Z) (gset_usym_act H Z h x) x)))
  ≔ let Zu ≔ gset_underlying H Z in
    let Zq ≔ closed_subset_gset H Z Q in
    let U ≔ gset_underlying H Zq in
    let A ≔ Σ Zu (x ↦ Q .fst x .fst) in
    let hA ≔ finite_decidable_subset Zu hZ (x ↦ Q .fst x .fst) (x ↦ Q .fst x .snd) dQ in
    let e ≔ closed_subset_underlying_equiv H Z Q in
    let hU : IsFiniteGSet H Zq ≔ finite_of_equiv U A e hA in
    let ce : Id Nat (gset_card H Zq hU) (cardinality A hA) ≔ cardinality_equiv U A e hU hA in
    let R ≔ Σ Zu (x ↦ Product (Q .fst x .fst) ((h : USym H) → Id Zu (gset_usym_act H Z h x) x)) in
    mere_rec (GSetFixedPoints H Zq) (Mere R) (mere_isprop R)
      (w ↦ mere R (w .fst .fst, (e .map (w .fst) .snd,
        h ↦ map_path U Zu (closed_subset_point H Z Q) (gset_usym_act H Zq h (w .fst)) (w .fst) (w .snd h))))
      (p_group_fixed_point_exists p hp n H hH hc Zq hU
        (d ↦ nd (transport Nat (NatDivides p) (gset_card H Zq hU) (cardinality A hA) ce d)))

{` The same for a finite p-subgroup S of G acting on a finite G-set Y:
   a decidable subset A of Y(sh_G), closed under the symmetries of S, with
   p ∤ |A| contains a point fixed by S. `}
def subgroup_closed_subset_fixed_point (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group)
  (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  (hc : Id Nat (group_card (subgroup_group G S) hS) (nat_power p n)) (Y : GSet G) (hY : IsFiniteGSet G Y)
  (A : gset_underlying G Y → Type) (hA : (y : gset_underlying G Y) → isProp (A y))
  (dA : (y : gset_underlying G Y) → Decidable (A y))
  (cl : (y : gset_underlying G Y) → A y → (g : USym G)
     → Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)
     → A (gset_usym_act G Y g y))
  (nd : Not (NatDivides p (cardinality (Σ (gset_underlying G Y) A) (finite_decidable_subset (gset_underlying G Y) hY A hA dA))))
  : Mere (Σ (gset_underlying G Y) (y ↦ Product (A y) (SubgroupFixes G S Y y)))
  ≔ let H ≔ subgroup_group G S in
    let Z ≔ subgroup_restricted_gset G S Y in
    let Yu ≔ gset_underlying G Y in
    let E ≔ subgroup_usym_stabilizer_equiv G S in
    let Q : GSetClosedSubsets H Z
      ≔ (y ↦ (A y, hA y), y a h ↦ cl y a (E .map h .fst) (E .map h .snd)) in
    let R ≔ Σ Yu (y ↦ Product (A y) (SubgroupFixes G S Y y)) in
    mere_rec (Σ Yu (y ↦ Product (A y) ((h : USym H) → Id Yu (gset_usym_act H Z h y) y))) (Mere R) (mere_isprop R)
      (w ↦ mere R (w .fst, (w .snd .fst, subgroup_restricted_fixes G S Y (w .fst) (w .snd .snd))))
      (p_group_closed_subset_fixed_point p hp n H hS hc Z hY Q dA nd)
