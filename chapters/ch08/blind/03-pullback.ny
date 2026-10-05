{` Blind statements for chapter 8 (congp.tex), section "The pullback". `}
export "01-semidirect"
export "../../../src/594-circle-power-subgroups"
export "../../../src/666-pullbacks"
export "../../../src/80-circle-degree-action"
export "../../../src/148-order-gcd-lcm"

{` ex:pullbackandgcd. P ≔ S¹ ×_{S¹} S¹, the pullback of (−)^a and (−)^b (degree maps dg_a, dg_b). `}
def BlindCirclePullback (C : CircleSignature) (a b : Nat) : Type
  ≔ TypePullback (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C a) (circle_degree_map C b)

{` (1) For a, b > 0 the pullback has gcd(a,b) components. `}
def blind_ex_pullbackandgcd_components : Type
  ≔ (C : CircleSignature) (a b : Nat) → Not (Id Nat a zero.) → Not (Id Nat b zero.)
    → BookEquiv (SetTrunc (BlindCirclePullback C a b)) (Fin (nat_gcd a b))

{` (2) The square: with d = gcd(a,b), a = d a', b = d b', there is an equivalence S¹ × C_d ≃ P whose
   composites with the two projections are, on each copy k, z ↦ z^{b'} (the book's ζ^k z^{b'}; a rotation
   is homotopic to the identity) and z ↦ z^{a'}. The underlying set of C_d is Fin d. `}
def blind_ex_pullbackandgcd_square : Type
  ≔ (C : CircleSignature) (a b d a' b' : Nat) → Not (Id Nat a zero.) → Not (Id Nat b zero.)
    → Id Nat d (nat_gcd a b) → Id Nat a (mul d a') → Id Nat b (mul d b')
    → Σ (BookEquiv (Product (C .carrier) (Fin d)) (BlindCirclePullback C a b)) (e ↦
        (k : Fin d)
        → Product (Id (C .carrier → C .carrier) (z ↦ e .map (z, k) .fst .fst) (circle_degree_map C b'))
                  (Id (C .carrier → C .carrier) (z ↦ e .map (z, k) .fst .snd) (circle_degree_map C a')))

{` (3) Each component of P, with the composite map P → S¹, (z,w,_) ↦ z^a, is a copy of the
   lcm(a,b)-fold covering. `}
def blind_ex_pullbackandgcd_lcm : Type
  ≔ (C : CircleSignature) (a b : Nat) → Not (Id Nat a zero.) → Not (Id Nat b zero.)
    → (u : BlindCirclePullback C a b)
    → Mere (Σ (BookEquiv (C .carrier) (NativeComponent (BlindCirclePullback C a b) u)) (e ↦
         Id (C .carrier → C .carrier) (z ↦ circle_degree_map C a (e .map z .fst .fst .fst))
           (circle_degree_map C (nat_lcm a b))))

{` def:intersectionand unionofsets. A ∩ B ≔ P × Q, A ∪ B ≔ P ∨ Q (the printed "A(s) ∨ B(s)" read as P(s) ∨ Q(s)). `}
def BlindSetIntersection (S : SetTypes) (P Q : Subtypes (S .fst)) : Subtypes (S .fst)
  ≔ s ↦ (Product (P s .fst) (Q s .fst), product_prop (P s .fst) (Q s .fst) (P s .snd) (Q s .snd))

def BlindSetUnion (S : SetTypes) (P Q : Subtypes (S .fst)) : Subtypes (S .fst)
  ≔ s ↦ (Mere (Sum (P s .fst) (Q s .fst)), mere_isprop (Sum (P s .fst) (Q s .fst)))

def BlindSubsetType (S : SetTypes) (P : Subtypes (S .fst)) : Type ≔ Σ (S .fst) (s ↦ P s .fst)

def blind_subset_incl (S : SetTypes) (P : Subtypes (S .fst)) : BlindSubsetType S P → S .fst ≔ u ↦ u .fst

{` xca:intersectionpullbackofsets (1): A ×_S B ≃ A ∩ B, over S. `}
def blind_xca_intersectionpullbackofsets : Type
  ≔ (S : SetTypes) (P Q : Subtypes (S .fst))
    → Σ (BookEquiv (TypePullback (BlindSubsetType S P) (BlindSubsetType S Q) (S .fst)
                      (blind_subset_incl S P) (blind_subset_incl S Q))
                   (BlindSubsetType S (BlindSetIntersection S P Q))) (e ↦
        (t : TypePullback (BlindSubsetType S P) (BlindSubsetType S Q) (S .fst) (blind_subset_incl S P) (blind_subset_incl S Q))
        → Id (S .fst) (e .map t .fst) (t .fst .fst .fst))

{` xca:cardinalityintersectionunion (2): S finite ⇒ Card A + Card B = Card(A ∪ B) + Card(A ∩ B).
   The finiteness of the four subsets, presupposed by "cardinality", is taken as hypotheses. `}
def blind_xca_cardinalityintersectionunion : Type
  ≔ (S : SetTypes) (hS : IsFinite (S .fst)) (P Q : Subtypes (S .fst))
    (hA : IsFinite (BlindSubsetType S P)) (hB : IsFinite (BlindSubsetType S Q))
    (hU : IsFinite (BlindSubsetType S (BlindSetUnion S P Q))) (hI : IsFinite (BlindSubsetType S (BlindSetIntersection S P Q)))
    → Id Nat (add (cardinality (BlindSubsetType S P) hA) (cardinality (BlindSubsetType S Q) hB))
             (add (cardinality (BlindSubsetType S (BlindSetUnion S P Q)) hU)
                  (cardinality (BlindSubsetType S (BlindSetIntersection S P Q)) hI))

{` def:intersectionofgroups. H ×_G H' ≔ the component of (sh_H, sh_{H'}, p_{f'} p_f⁻¹) in BH ×_{BG} BH'
   (p_f⁻¹ first, then p_{f'}). `}
def BlindGroupPullbackType (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Type
  ≔ TypePullback (BG H .carrier) (BG H' .carrier) (BG G .carrier) (hom_function H G f) (hom_function H' G f')

def blind_group_pullback_point (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : BlindGroupPullbackType H H' G f f'
  ≔ ((shape H, shape H'),
     concat (BG G .carrier) (hom_function H G f (shape H)) (shape G) (hom_function H' G f' (shape H'))
       (inverse (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_point H G f)) (hom_point H' G f'))

def blind_group_pullback_groupoid (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : isGroupoid (BlindGroupPullbackType H H' G f f')
  ≔ blind_sigma_groupoid (Product (BG H .carrier) (BG H' .carrier))
      (bc ↦ Id (BG G .carrier) (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd)))
      (groupoid_product (BG H .carrier) (BG H' .carrier) (bg_groupoid H) (bg_groupoid H'))
      (bc ↦ set_is_groupoid (Id (BG G .carrier) (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd)))
              (bg_groupoid G (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd))))

def blind_group_pullback (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Group
  ≔ automorphism_group (BlindGroupPullbackType H H' G f f') (blind_group_pullback_groupoid H H' G f f')
      (blind_group_pullback_point H H' G f f')

def blind_group_pullback_proj1 (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : GroupHom (blind_group_pullback H H' G f f') H
  ≔ mkhom (blind_group_pullback H H' G f f') H (c ↦ c .fst .fst .fst, refl (shape H))

def blind_group_pullback_proj2 (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : GroupHom (blind_group_pullback H H' G f f') H'
  ≔ mkhom (blind_group_pullback H H' G f f') H' (c ↦ c .fst .fst .snd, refl (shape H'))

{` The intersection H ∩ H' of two monomorphisms into G is their pullback. `}
def blind_mono_intersection (G : Group) (m m' : GroupMonos G) : Group
  ≔ blind_group_pullback (m .fst) (m' .fst) G (m .snd .fst) (m' .snd .fst)

{` congp.tex:471. aZ ⊂ Z is the subgroup (R_a, 0) for a > 0 and (R, 0) (the trivial subgroup) for a = 0
   (ex:Rm0-subgroup). With L = lcm(a,b): aZ ∩ bZ = LZ as monomorphisms into Z, i.e. an isomorphism
   of the intersection with LZ commuting with the inclusions. `}
def blind_multiples_subgroup (C : CircleSignature) (a : Nat) : Subgroups (circle_group C)
  ≔ match a [ zero. ↦ rsub_subgroup C | suc. k ↦ rmsub_subgroup C k ]

def blind_multiples_mono (C : CircleSignature) (a : Nat) : GroupMonos (circle_group C)
  ≔ subgroup_to_mono (circle_group C) (blind_multiples_subgroup C a)

def blind_multiples_intersection_incl (C : CircleSignature) (a b : Nat)
  : GroupHom (blind_mono_intersection (circle_group C) (blind_multiples_mono C a) (blind_multiples_mono C b)) (circle_group C)
  ≔ group_hom_compose (blind_mono_intersection (circle_group C) (blind_multiples_mono C a) (blind_multiples_mono C b))
      (blind_multiples_mono C a .fst) (circle_group C)
      (blind_group_pullback_proj1 (blind_multiples_mono C a .fst) (blind_multiples_mono C b .fst) (circle_group C)
        (blind_multiples_mono C a .snd .fst) (blind_multiples_mono C b .snd .fst))
      (blind_multiples_mono C a .snd .fst)

def blind_ex_lcm_intersection : Type
  ≔ (C : CircleSignature) (a b : Nat)
    → Σ (GroupIso (blind_mono_intersection (circle_group C) (blind_multiples_mono C a) (blind_multiples_mono C b))
                  (blind_multiples_mono C (nat_lcm a b) .fst)) (phi ↦
        Id (GroupHom (blind_mono_intersection (circle_group C) (blind_multiples_mono C a) (blind_multiples_mono C b)) (circle_group C))
          (blind_multiples_intersection_incl C a b)
          (group_hom_compose (blind_mono_intersection (circle_group C) (blind_multiples_mono C a) (blind_multiples_mono C b))
             (blind_multiples_mono C (nat_lcm a b) .fst) (circle_group C) (phi .fst)
             (blind_multiples_mono C (nat_lcm a b) .snd .fst)))

{` congp.tex:479 (1). Hom(K,H) ×_{Hom(K,G)} Hom(K,H') ≃ Hom(K, H ×_G H'), induced by the projections
   (stated in the direction g ↦ (π₁ ∘ g, π₂ ∘ g, _)). `}
def BlindHomPullback (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group) : Type
  ≔ TypePullback (GroupHom K H) (GroupHom K H') (GroupHom K G)
      (h ↦ group_hom_compose K H G h f) (h' ↦ group_hom_compose K H' G h' f')

def blind_xca_pullback_homs : Type
  ≔ (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
    → Σ (BookEquiv (GroupHom K (blind_group_pullback H H' G f f')) (BlindHomPullback H H' G f f' K)) (e ↦
        (g : GroupHom K (blind_group_pullback H H' G f f'))
        → Product
            (Id (GroupHom K H) (e .map g .fst .fst)
              (group_hom_compose K (blind_group_pullback H H' G f f') H g (blind_group_pullback_proj1 H H' G f f')))
            (Id (GroupHom K H') (e .map g .fst .snd)
              (group_hom_compose K (blind_group_pullback H H' G f f') H' g (blind_group_pullback_proj2 H H' G f f'))))

{` congp.tex:479 (2). USym H ×_{USym G} USym H' ≃ (sh = sh) in H ×_G H', compatible with the projections. `}
def BlindUSymPullback (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Type
  ≔ TypePullback (USym H) (USym H') (USym G) (usym_hom H G f) (usym_hom H' G f')

def BlindUSymPullbackEquiv (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Type
  ≔ Σ (BookEquiv (USym (blind_group_pullback H H' G f f')) (BlindUSymPullback H H' G f f')) (e ↦
      (w : USym (blind_group_pullback H H' G f f'))
      → Product
          (Id (USym H) (e .map w .fst .fst)
            (usym_hom (blind_group_pullback H H' G f f') H (blind_group_pullback_proj1 H H' G f f') w))
          (Id (USym H') (e .map w .fst .snd)
            (usym_hom (blind_group_pullback H H' G f f') H' (blind_group_pullback_proj2 H H' G f f') w)))

def blind_xca_pullback_usym : Type
  ≔ (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) → BlindUSymPullbackEquiv H H' G f f'

{` congp.tex:479 (3), the abstract-group version: the equivalence is an isomorphism of abstract groups
   when the pullback set carries the componentwise multiplication (the third component is a path in a set). `}
def blind_xca_pullback_abstract : Type
  ≔ (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
    → Σ (BlindUSymPullbackEquiv H H' G f f') (E ↦
        (w w' : USym (blind_group_pullback H H' G f f'))
        → Id (Product (USym H) (USym H'))
            (E .fst .map (usym_mul (blind_group_pullback H H' G f f') w w') .fst)
            (usym_mul H (E .fst .map w .fst .fst) (E .fst .map w' .fst .fst),
             usym_mul H' (E .fst .map w .fst .snd) (E .fst .map w' .fst .snd)))

{` congp.tex:497 (remark). The pullback of classifying types need not be connected. `}
def blind_rem_pullback_not_connected : Type
  ≔ Not ((H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) → Connected (BlindGroupPullbackType H H' G f f'))
