export "1030-subgroup-containment"

{` Chapter 10, supporting material for the Sylow theorems (fingp.tex
   227-307). For a finite subgroup S = (X, x) of a finite group G:

   * the automorphisms X = X of the G-set X correspond to the points y of
     X(sh_G) fixed by S (subgroup_aut_fixed_equiv); this is the Weyl group
     W_G S = Aut(X) of the book (lem:WGHisHfixofG/H: |W_G S| = |(G/S)^S|),
     defined here as the automorphism group of X in the groupoid of G-sets;
   * if |S| = p^n, the number of points of a finite G-set Y fixed by S is
     congruent to |Y(sh_G)| mod p (lem:fixedptsize for the restricted
     action, subgroup_fixed_set_congruence);
   * the conjugates of S, i.e. the subgroups (X, y) for y : X(sh_G) (the
     orbit of S under conjugation), form a finite set, and
     |X(sh_G)| = |conjugates of S| · |Aut(X)|, so the number of conjugates
     divides the index |X(sh_G)| = |G|/|S|. `}

{` Σ_y ((X, x) = (X, y)) ≃ (X = X): identifications of pointed G-sets out
   of (X, x) are identifications X = X with their value at x. `}
def gset_aut_pointed_sum_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (Σ (gset_underlying G X) (y ↦ Id (PointedGSet G) (X, x) (X, y))) (Id (GSet G) X X)
  ≔ let Y ≔ gset_underlying G X in
    let A ≔ Id (GSet G) X X in
    let ev ≔ gset_path_eval G X X (shape G) x in
    compose_equiv (Σ Y (y ↦ Id (PointedGSet G) (X, x) (X, y))) (Σ Y (y ↦ BookFiber A Y ev y)) A
      (family_equiv Y (y ↦ Id (PointedGSet G) (X, x) (X, y)) (y ↦ BookFiber A Y ev y)
        (y ↦ compose_equiv (Id (PointedGSet G) (X, x) (X, y)) (Fiber A Y ev y) (BookFiber A Y ev y)
          (pointed_gset_path_fiber_equiv G (X, x) (X, y)) (fiber_conventions_equiv A Y ev y)))
      (sum_of_fibers_equiv A Y ev)

def subgroup_pointed (G : Group) (T : Subgroups G) : PointedGSet G ≔ (T .gset, T .point)

{` Identifications of subgroups are identifications of the pointed G-sets
   (transitivity is a proposition). `}
def subgroup_path_pointed_equiv (G : Group) (S T : Subgroups G)
  : Equiv (Id (Subgroups G) S T) (Id (PointedGSet G) (subgroup_pointed G S) (subgroup_pointed G T))
  ≔ iff_equiv (Id (Subgroups G) S T) (Id (PointedGSet G) (subgroup_pointed G S) (subgroup_pointed G T))
      (subgroups_set G S T)
      (pointed_gset_paths_prop G (subgroup_pointed G S) (subgroup_pointed G T) (S .transitive))
      (map_path (Subgroups G) (PointedGSet G) (subgroup_pointed G) S T)
      (subgroup_path G S T)

{` For a finite subgroup S = (X, x) of a finite group: (X, x) = (X, y) as
   pointed G-sets iff S fixes y. `}
def subgroup_fixes_pointed_path (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y : gset_underlying G (S .gset))
  (f : SubgroupFixes G S (S .gset) y)
  : Id (PointedGSet G) (S .gset, S .point) (S .gset, y)
  ≔ map_path (Subgroups G) (PointedGSet G) (subgroup_pointed G) S (subgroup_at G S y)
      (subgroup_at_path_of_fixes G hG S hS y f)

def pointed_path_subgroup_fixes (G : Group) (S : Subgroups G) (y : gset_underlying G (S .gset))
  (p : Id (PointedGSet G) (S .gset, S .point) (S .gset, y)) : SubgroupFixes G S (S .gset) y
  ≔ let w ≔ pointed_gset_path_fiber_equiv G (S .gset, S .point) (S .gset, y) .map p in
    gset_hom_subgroup_fixes G S (S .gset) y (gset_path_to_hom G (S .gset) (S .gset) (w .fst)) (w .snd)

{` The points of Y(sh_G) fixed by S. `}
def SubgroupFixedSet (G : Group) (S : Subgroups G) (Y : GSet G) : Type
  ≔ Σ (gset_underlying G Y) (SubgroupFixes G S Y)

def subgroup_fixed_set_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (dS : DecidableEquality (gset_underlying G (S .gset))) (Y : GSet G) (hY : IsFiniteGSet G Y)
  : IsFinite (SubgroupFixedSet G S Y)
  ≔ finite_decidable_subset (gset_underlying G Y) hY (SubgroupFixes G S Y) (subgroup_fixes_prop G S Y)
      (subgroup_fixes_decidable G hG S dS Y (finite_decidable_equality (gset_underlying G Y) hY))

{` Automorphisms of X ≃ points of X fixed by S. `}
def subgroup_aut_fixed_equiv (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S))
  : Equiv (Id (GSet G) (S .gset) (S .gset)) (SubgroupFixedSet G S (S .gset))
  ≔ let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    compose_equiv (Id (GSet G) X X) (Σ Y (y ↦ Id (PointedGSet G) (X, S .point) (X, y))) (SubgroupFixedSet G S X)
      (canonical_inverse_equiv (Σ Y (y ↦ Id (PointedGSet G) (X, S .point) (X, y))) (Id (GSet G) X X)
        (gset_aut_pointed_sum_equiv G X (S .point)))
      (family_equiv Y (y ↦ Id (PointedGSet G) (X, S .point) (X, y)) (SubgroupFixes G S X)
        (y ↦ iff_equiv (Id (PointedGSet G) (X, S .point) (X, y)) (SubgroupFixes G S X y)
          (pointed_gset_paths_prop G (X, S .point) (X, y) (S .transitive)) (subgroup_fixes_prop G S X y)
          (pointed_path_subgroup_fixes G S y) (subgroup_fixes_pointed_path G hG S hS y)))

{` The fixed set of S is the fixed-point set of the restricted action. `}
def subgroup_fixed_set_restricted_equiv (G : Group) (S : Subgroups G) (Y : GSet G)
  : Equiv (SubgroupFixedSet G S Y) (GSetFixedPoints (subgroup_group G S) (subgroup_restricted_gset G S Y))
  ≔ let H ≔ subgroup_group G S in
    let Yr ≔ subgroup_restricted_gset G S Y in
    family_equiv (gset_underlying G Y) (SubgroupFixes G S Y)
      (y ↦ (h : USym H) → Id (gset_underlying G Y) (gset_usym_act H Yr h y) y)
      (y ↦ iff_equiv (SubgroupFixes G S Y y) ((h : USym H) → Id (gset_underlying G Y) (gset_usym_act H Yr h y) y)
        (subgroup_fixes_prop G S Y y) (gset_fixed_points_prop H Yr y)
        (subgroup_fixes_restricted G S Y y) (subgroup_restricted_fixes G S Y y))

{` lem:fixedptsize for the restricted action: if |S| = p^n then
   |Y(sh_G)| ≡ |points fixed by S| (mod p). `}
def subgroup_fixed_set_congruence (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  (hc : Id Nat (group_card (subgroup_group G S) hS) (nat_power p n))
  (dS : DecidableEquality (gset_underlying G (S .gset))) (Y : GSet G) (hY : IsFiniteGSet G Y)
  : NatCongruent p (gset_card G Y hY) (cardinality (SubgroupFixedSet G S Y) (subgroup_fixed_set_finite G hG S dS Y hY))
  ≔ let H ≔ subgroup_group G S in
    let Yr ≔ subgroup_restricted_gset G S Y in
    let F ≔ GSetFixedPoints H Yr in
    let hF ≔ gset_fixed_points_finite H hS Yr hY in
    let hFix ≔ subgroup_fixed_set_finite G hG S dS Y hY in
    transport Nat (k ↦ NatCongruent p (gset_card G Y hY) k) (cardinality F hF)
      (cardinality (SubgroupFixedSet G S Y) hFix)
      (cardinality_equiv F (SubgroupFixedSet G S Y)
        (canonical_inverse_equiv (SubgroupFixedSet G S Y) F (subgroup_fixed_set_restricted_equiv G S Y)) hF hFix)
      (p_group_fixed_point_congruence p hp n H hS hc Yr hY)

def subgroup_fixed_set_not_divisible (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  (hc : Id Nat (group_card (subgroup_group G S) hS) (nat_power p n))
  (dS : DecidableEquality (gset_underlying G (S .gset))) (Y : GSet G) (hY : IsFiniteGSet G Y)
  (nd : Not (NatDivides p (gset_card G Y hY)))
  : Not (NatDivides p (cardinality (SubgroupFixedSet G S Y) (subgroup_fixed_set_finite G hG S dS Y hY)))
  ≔ d ↦ nd (nat_congruent_divides_iff p (gset_card G Y hY)
      (cardinality (SubgroupFixedSet G S Y) (subgroup_fixed_set_finite G hG S dS Y hY))
      (subgroup_fixed_set_congruence p hp n G hG S hS hc dS Y hY) .snd d)

{` The Weyl group W_G S: automorphisms of the G-set of S. `}
def subgroup_weyl_group (G : Group) (S : Subgroups G) : Group
  ≔ automorphism_group (GSet G) (gset_groupoid G) (S .gset)

def subgroup_weyl_usym_equiv (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S))
  : Equiv (USym (subgroup_weyl_group G S)) (SubgroupFixedSet G S (S .gset))
  ≔ compose_equiv (USym (subgroup_weyl_group G S)) (Id (GSet G) (S .gset) (S .gset)) (SubgroupFixedSet G S (S .gset))
      (automorphism_group_usym_equiv (GSet G) (gset_groupoid G) (S .gset))
      (subgroup_aut_fixed_equiv G hG S hS)

def subgroup_aut_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) : IsFinite (Id (GSet G) (S .gset) (S .gset))
  ≔ finite_of_equiv (Id (GSet G) (S .gset) (S .gset)) (SubgroupFixedSet G S (S .gset))
      (subgroup_aut_fixed_equiv G hG S hS)
      (subgroup_fixed_set_finite G hG S (subgroup_gset_decidable_equality G hG S hS) (S .gset)
        (subgroup_gset_finite G hG S hS))

def subgroup_weyl_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) : IsFiniteGroup (subgroup_weyl_group G S)
  ≔ finite_of_equiv (USym (subgroup_weyl_group G S)) (Id (GSet G) (S .gset) (S .gset))
      (automorphism_group_usym_equiv (GSet G) (gset_groupoid G) (S .gset)) (subgroup_aut_finite G hG S hS)

{` lem:WGHisHfixofG/H: |W_G S| = |(G/S)^S|. `}
def subgroup_weyl_card (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S))
  : Id Nat (group_card (subgroup_weyl_group G S) (subgroup_weyl_finite G hG S hS))
      (cardinality (SubgroupFixedSet G S (S .gset))
        (subgroup_fixed_set_finite G hG S (subgroup_gset_decidable_equality G hG S hS) (S .gset)
          (subgroup_gset_finite G hG S hS)))
  ≔ cardinality_equiv (USym (subgroup_weyl_group G S)) (SubgroupFixedSet G S (S .gset))
      (subgroup_weyl_usym_equiv G hG S hS) (subgroup_weyl_finite G hG S hS)
      (subgroup_fixed_set_finite G hG S (subgroup_gset_decidable_equality G hG S hS) (S .gset)
        (subgroup_gset_finite G hG S hS))

{` The conjugates of S: the subgroups of the form (X, y). `}
def SubgroupConjugates (G : Group) (S : Subgroups G) : Type
  ≔ Σ (Subgroups G) (T ↦ Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))

def subgroup_conjugates_set (G : Group) (S : Subgroups G) : isSet (SubgroupConjugates G S)
  ≔ sigma_set (Subgroups G)
      (T ↦ Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))
      (subgroups_set G)
      (T ↦ prop_is_set (Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))
        (mere_isprop (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T))))

def subgroup_conjugates_path (G : Group) (S : Subgroups G) (c c' : SubgroupConjugates G S)
  (p : Id (Subgroups G) (c .fst) (c' .fst)) : Id (SubgroupConjugates G S) c c'
  ≔ subtype_equal (Subgroups G)
      (T ↦ Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))
      (T ↦ mere_isprop (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))
      c c' p

def subgroup_conjugate_class (G : Group) (S : Subgroups G) (y : gset_underlying G (S .gset))
  : SubgroupConjugates G S
  ≔ (subgroup_at G S y,
     mere (Σ (gset_underlying G (S .gset)) (y' ↦ Id (Subgroups G) (subgroup_at G S y') (subgroup_at G S y)))
       (y, refl (subgroup_at G S y)))

def subgroup_conjugate_class_surjective (G : Group) (S : Subgroups G)
  : Surjective (gset_underlying G (S .gset)) (SubgroupConjugates G S) (subgroup_conjugate_class G S)
  ≔ c ↦
    let Y ≔ gset_underlying G (S .gset) in
    mere_rec (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G S y) (c .fst)))
      (Mere (BookFiber Y (SubgroupConjugates G S) (subgroup_conjugate_class G S) c))
      (mere_isprop (BookFiber Y (SubgroupConjugates G S) (subgroup_conjugate_class G S) c))
      (w ↦ mere (BookFiber Y (SubgroupConjugates G S) (subgroup_conjugate_class G S) c)
        (w .fst, subgroup_conjugates_path G S c (subgroup_conjugate_class G S (w .fst))
          (inverse (Subgroups G) (subgroup_at G S (w .fst)) (c .fst) (w .snd))))
      (c .snd)

{` (X, y) = (X, y') is decidable. `}
def subgroup_at_path_decidable (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y y' : gset_underlying G (S .gset))
  : Decidable (Id (Subgroups G) (subgroup_at G S y) (subgroup_at G S y'))
  ≔ let S1 ≔ subgroup_at G S y in
    let dX ≔ subgroup_gset_decidable_equality G hG S hS in
    match subgroup_fixes_decidable G hG S1 dX (S .gset) dX y' [
    | inl. f ↦ inl. (subgroup_at_path_of_fixes G hG S1 (subgroup_at_finite G hG S hS y) y' f)
    | inr. nf ↦ inr. (q ↦ nf (subgroup_path_fixes G S1 (subgroup_at G S y') q)) ]

def subgroup_conjugates_decidable_equality (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) : DecidableEquality (SubgroupConjugates G S)
  ≔ c c' ↦
    let Y ≔ gset_underlying G (S .gset) in
    let C ≔ SubgroupConjugates G S in
    let D ≔ Decidable (Id C c c') in
    let hD ≔ decidability_prop (Id C c c') (subgroup_conjugates_set G S c c') in
    mere_rec (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G S y) (c .fst))) D hD
      (w ↦ mere_rec (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G S y) (c' .fst))) D hD
        (w' ↦ match subgroup_at_path_decidable G hG S hS (w .fst) (w' .fst) [
          | inl. q ↦ inl. (subgroup_conjugates_path G S c c'
              (concat (Subgroups G) (c .fst) (subgroup_at G S (w .fst)) (c' .fst)
                (inverse (Subgroups G) (subgroup_at G S (w .fst)) (c .fst) (w .snd))
                (concat (Subgroups G) (subgroup_at G S (w .fst)) (subgroup_at G S (w' .fst)) (c' .fst) q (w' .snd))))
          | inr. nq ↦ inr. (r ↦ nq
              (concat (Subgroups G) (subgroup_at G S (w .fst)) (c .fst) (subgroup_at G S (w' .fst)) (w .snd)
                (concat (Subgroups G) (c .fst) (c' .fst) (subgroup_at G S (w' .fst))
                  (map_path C (Subgroups G) (u ↦ u .fst) c c' r)
                  (inverse (Subgroups G) (subgroup_at G S (w' .fst)) (c' .fst) (w' .snd))))) ])
        (c' .snd))
      (c .snd)

def subgroup_conjugates_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) : IsFinite (SubgroupConjugates G S)
  ≔ finite_surjection_target (gset_underlying G (S .gset)) (SubgroupConjugates G S) (subgroup_gset_finite G hG S hS)
      (subgroup_conjugates_decidable_equality G hG S hS) (subgroup_conjugate_class G S)
      (subgroup_conjugate_class_surjective G S)

{` The fiber of y ↦ (X, y) over (X, y) is equivalent to Aut(X). `}
def subgroup_conjugate_fiber_equiv (G : Group) (S : Subgroups G) (y : gset_underlying G (S .gset))
  : Equiv (BookFiber (gset_underlying G (S .gset)) (SubgroupConjugates G S) (subgroup_conjugate_class G S)
        (subgroup_conjugate_class G S y))
      (Id (GSet G) (S .gset) (S .gset))
  ≔ let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    let C ≔ SubgroupConjugates G S in
    let cl ≔ subgroup_conjugate_class G S in
    compose_equiv (BookFiber Y C cl (cl y)) (Σ Y (y' ↦ Id (PointedGSet G) (X, y) (X, y'))) (Id (GSet G) X X)
      (family_equiv Y (y' ↦ Id C (cl y) (cl y')) (y' ↦ Id (PointedGSet G) (X, y) (X, y'))
        (y' ↦ compose_equiv (Id C (cl y) (cl y')) (Id (Subgroups G) (subgroup_at G S y) (subgroup_at G S y'))
          (Id (PointedGSet G) (X, y) (X, y'))
          (subtype_path_equiv (Subgroups G)
            (T ↦ Mere (Σ Y (y'' ↦ Id (Subgroups G) (subgroup_at G S y'') T)))
            (T ↦ mere_isprop (Σ Y (y'' ↦ Id (Subgroups G) (subgroup_at G S y'') T)))
            (cl y) (cl y'))
          (subgroup_path_pointed_equiv G (subgroup_at G S y) (subgroup_at G S y'))))
      (gset_aut_pointed_sum_equiv G X y)

def subgroup_conjugate_fiber_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (c : SubgroupConjugates G S)
  : IsFinite (BookFiber (gset_underlying G (S .gset)) (SubgroupConjugates G S) (subgroup_conjugate_class G S) c)
  ≔ let Y ≔ gset_underlying G (S .gset) in
    let C ≔ SubgroupConjugates G S in
    finite_decidable_subset Y (subgroup_gset_finite G hG S hS) (y ↦ Id C c (subgroup_conjugate_class G S y))
      (y ↦ subgroup_conjugates_set G S c (subgroup_conjugate_class G S y))
      (y ↦ subgroup_conjugates_decidable_equality G hG S hS c (subgroup_conjugate_class G S y))

def subgroup_conjugate_fiber_card (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (c : SubgroupConjugates G S)
  : Id Nat (cardinality (BookFiber (gset_underlying G (S .gset)) (SubgroupConjugates G S) (subgroup_conjugate_class G S) c)
        (subgroup_conjugate_fiber_finite G hG S hS c))
      (cardinality (Id (GSet G) (S .gset) (S .gset)) (subgroup_aut_finite G hG S hS))
  ≔ let Y ≔ gset_underlying G (S .gset) in
    let C ≔ SubgroupConjugates G S in
    let cl ≔ subgroup_conjugate_class G S in
    let A ≔ Id (GSet G) (S .gset) (S .gset) in
    let m ≔ cardinality A (subgroup_aut_finite G hG S hS) in
    let Goal : C → Type
      ≔ c' ↦ Id Nat (cardinality (BookFiber Y C cl c') (subgroup_conjugate_fiber_finite G hG S hS c')) m in
    mere_rec (BookFiber Y C cl c) (Goal c)
      (nat_set (cardinality (BookFiber Y C cl c) (subgroup_conjugate_fiber_finite G hG S hS c)) m)
      (w ↦ transport C Goal (cl (w .fst)) c (inverse C c (cl (w .fst)) (w .snd))
        (cardinality_equiv (BookFiber Y C cl (cl (w .fst))) A (subgroup_conjugate_fiber_equiv G S (w .fst))
          (subgroup_conjugate_fiber_finite G hG S hS (cl (w .fst))) (subgroup_aut_finite G hG S hS)))
      (subgroup_conjugate_class_surjective G S c)

{` |X(sh_G)| = |conjugates of S| · |Aut(X)|. `}
def subgroup_conjugates_card_mul (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S))
  : Id Nat (gset_card G (S .gset) (subgroup_gset_finite G hG S hS))
      (mul (cardinality (SubgroupConjugates G S) (subgroup_conjugates_finite G hG S hS))
        (cardinality (Id (GSet G) (S .gset) (S .gset)) (subgroup_aut_finite G hG S hS)))
  ≔ let Y ≔ gset_underlying G (S .gset) in
    let hY ≔ subgroup_gset_finite G hG S hS in
    let C ≔ SubgroupConjugates G S in
    let hC ≔ subgroup_conjugates_finite G hG S hS in
    let cl ≔ subgroup_conjugate_class G S in
    let F : C → Type ≔ c ↦ BookFiber Y C cl c in
    let E ≔ sum_of_fibers_equiv Y C cl in
    let hT ≔ finite_of_equiv (Σ C F) Y E hY in
    concat Nat (gset_card G (S .gset) hY) (cardinality (Σ C F) hT)
      (mul (cardinality C hC) (cardinality (Id (GSet G) (S .gset) (S .gset)) (subgroup_aut_finite G hG S hS)))
      (cardinality_equiv Y (Σ C F) (canonical_inverse_equiv (Σ C F) Y E) hY hT)
      (cardinality_sigma_constant C hC F (subgroup_conjugate_fiber_finite G hG S hS) hT
        (cardinality (Id (GSet G) (S .gset) (S .gset)) (subgroup_aut_finite G hG S hS))
        (subgroup_conjugate_fiber_card G hG S hS))

{` The number of conjugates divides the index |X(sh_G)| = |G|/|S|. `}
def subgroup_conjugates_divides_index (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S))
  : NatDivides (cardinality (SubgroupConjugates G S) (subgroup_conjugates_finite G hG S hS))
      (gset_card G (S .gset) (subgroup_gset_finite G hG S hS))
  ≔ let c ≔ cardinality (SubgroupConjugates G S) (subgroup_conjugates_finite G hG S hS) in
    let m ≔ cardinality (Id (GSet G) (S .gset) (S .gset)) (subgroup_aut_finite G hG S hS) in
    nat_divides_intro c (gset_card G (S .gset) (subgroup_gset_finite G hG S hS)) m
      (concat Nat (gset_card G (S .gset) (subgroup_gset_finite G hG S hS)) (mul c m) (mul m c)
        (subgroup_conjugates_card_mul G hG S hS) (mul_comm c m))
