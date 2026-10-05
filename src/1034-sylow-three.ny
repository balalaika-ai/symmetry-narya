export "1033-sylow-subgroups"

{` Chapter 10, thm:sylow3 (fingp.tex 292-307). Let P = (X, x) be a
   p-Sylow subgroup of G (p prime). Then the set Syl_G^p of p-Sylow
   subgroups is finite and

   1. |Syl_G^p| divides |G|/|P|: Syl_G^p is the set of conjugates of P
      (thm:sylow2), and |X(sh_G)| = |conjugates| · |Aut(X)| (module 1031),
      where |X(sh_G)| = |G|/|P| by lem:Lagrangeascounting;
   2. |Syl_G^p| ≡ 1 (mod p): restrict the action of G on Syl_G^p to P. As
      in the book, the only fixed point is P: if P normalizes a Sylow
      subgroup Q = (X, y), then the set of points of X fixed by Q (the
      points y' with (X, y') = Q) is closed under the symmetries of P and
      has cardinality prime to p (lem:fixedptsize for Q), so it contains a
      point fixed by P, which gives P = Q. The book argues instead with the
      normalizer N_G Q, in which Q is normal and P is a Sylow subgroup; the
      counting argument here avoids normalizers and quotient groups.
      Then lem:fixedptsize for P gives |Syl_G^p| ≡ 1 (mod p). `}

def sylow_point (p : Nat) (G : Group) (Q : SylowSubgroups p G) : Subgroups G ≔ Q .fst

def sylow_subgroups_finite (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G)
  (sP : IsSylowSubgroup p G P) : IsFinite (SylowSubgroups p G)
  ≔ finite_of_equiv (SylowSubgroups p G) (SubgroupConjugates G P) (sylow_conjugates_equiv p hp G P sP)
      (subgroup_conjugates_finite G (sylow_group_finite p G P sP) P (sylow_subgroup_finite p G P sP))

def sylow_subgroups_card_conjugates (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G)
  (sP : IsSylowSubgroup p G P)
  : Id Nat (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP))
      (cardinality (SubgroupConjugates G P)
        (subgroup_conjugates_finite G (sylow_group_finite p G P sP) P (sylow_subgroup_finite p G P sP)))
  ≔ cardinality_equiv (SylowSubgroups p G) (SubgroupConjugates G P) (sylow_conjugates_equiv p hp G P sP)
      (sylow_subgroups_finite p hp G P sP)
      (subgroup_conjugates_finite G (sylow_group_finite p G P sP) P (sylow_subgroup_finite p G P sP))

{` thm:sylow3 (1): |Syl_G^p| divides m = |X(sh_G)|, where |G| = m · |P|. `}
def sylow_three_divides (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Σ Nat (m ↦ Product
      (Id Nat (group_card G (sylow_group_finite p G P sP)) (mul m (group_card (subgroup_group G P) (sylow_subgroup_finite p G P sP))))
      (NatDivides (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) m))
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    (gset_card G (P .gset) (subgroup_gset_finite G hG P hP),
     (lagrange_counting G hG P hP,
      transport Nat (k ↦ NatDivides k (gset_card G (P .gset) (subgroup_gset_finite G hG P hP)))
        (cardinality (SubgroupConjugates G P) (subgroup_conjugates_finite G hG P hP))
        (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP))
        (inverse Nat (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP))
          (cardinality (SubgroupConjugates G P) (subgroup_conjugates_finite G hG P hP))
          (sylow_subgroups_card_conjugates p hp G P sP))
        (subgroup_conjugates_divides_index G hG P hP)))

{` The core of (2): if P normalizes Q = (X, y), then P = Q. `}
def sylow_normalized_equal_at (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G)
  (sP : IsSylowSubgroup p G P) (y : gset_underlying G (P .gset))
  (fix : (g : USym G) → Id (gset_underlying G (P .gset)) (gset_usym_act G (P .gset) g (P .point)) (P .point)
     → Id (Subgroups G) (subgroup_conjugate G g (subgroup_at G P y)) (subgroup_at G P y))
  : Id (Subgroups G) P (subgroup_at G P y)
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    let n ≔ sylow_exponent p G P sP in
    let X ≔ P .gset in
    let Yu ≔ gset_underlying G X in
    let hX ≔ subgroup_gset_finite G hG P hP in
    let dX ≔ subgroup_gset_decidable_equality G hG P hP in
    let Q ≔ subgroup_at G P y in
    let hQ ≔ subgroup_at_finite G hG P hP y in
    let hcQ : Id Nat (group_card (subgroup_group G Q) hQ) (nat_power p n)
      ≔ concat Nat (group_card (subgroup_group G Q) hQ) (group_card (subgroup_group G P) hP) (nat_power p n)
          (subgroup_at_card G hG P hP y) (sylow_subgroup_card p G P sP) in
    let A : Yu → Type ≔ y' ↦ SubgroupFixes G Q X y' in
    let hA : (y' : Yu) → isProp (A y') ≔ y' ↦ subgroup_fixes_prop G Q X y' in
    let dA : (y' : Yu) → Decidable (A y') ≔ subgroup_fixes_decidable G hG Q dX X (finite_decidable_equality Yu hX) in
    let cl : (y' : Yu) → A y' → (g : USym G) → Id Yu (gset_usym_act G X g (P .point)) (P .point)
        → A (gset_usym_act G X g y')
      ≔ y' a g r ↦
        let e1 : Id (Subgroups G) Q (subgroup_at G P y') ≔ subgroup_at_path_of_fixes G hG Q hQ y' a in
        let e2 : Id (Subgroups G) (subgroup_at G P (gset_usym_act G X g y')) Q
          ≔ calc
              subgroup_at G P (gset_usym_act G X g y')
              = subgroup_conjugate G g (subgroup_at G P y')
                by inverse (Subgroups G) (subgroup_conjugate G g (subgroup_at G P y'))
                  (subgroup_at G P (gset_usym_act G X g y')) (subgroup_conjugate_at G g (subgroup_at G P y'))
              = subgroup_conjugate G g Q
                by map_path (Subgroups G) (Subgroups G) (subgroup_conjugate G g) (subgroup_at G P y') Q
                  (inverse (Subgroups G) Q (subgroup_at G P y') e1)
              = Q by fix g r ∎ in
        subgroup_path_fixes G Q (subgroup_at G P (gset_usym_act G X g y'))
          (inverse (Subgroups G) (subgroup_at G P (gset_usym_act G X g y')) Q e2) in
    let nd ≔ subgroup_fixed_set_not_divisible p hp n G hG Q hQ hcQ dX X hX (sylow_index_not_divisible p G P sP) in
    mere_rec (Σ Yu (y'' ↦ Product (A y'') (SubgroupFixes G P X y''))) (Id (Subgroups G) P Q) (subgroups_set G P Q)
      (v ↦ concat (Subgroups G) P (subgroup_at G P (v .fst)) Q
        (subgroup_at_path_of_fixes G hG P hP (v .fst) (v .snd .snd))
        (inverse (Subgroups G) Q (subgroup_at G P (v .fst)) (subgroup_at_path_of_fixes G hG Q hQ (v .fst) (v .snd .fst))))
      (subgroup_closed_subset_fixed_point p hp n G P hP (sylow_subgroup_card p G P sP) X hX A hA dA cl nd)

{` If P normalizes a p-Sylow subgroup Q (g · Q = Q for every symmetry g of
   P), then P = Q. `}
def sylow_normalized_equal (p : Nat) (hp : NatIsPrime p) (G : Group) (P Q : Subgroups G)
  (sP : IsSylowSubgroup p G P) (sQ : IsSylowSubgroup p G Q)
  (fix : (g : USym G) → Id (gset_underlying G (P .gset)) (gset_usym_act G (P .gset) g (P .point)) (P .point)
     → Id (Subgroups G) (subgroup_conjugate G g Q) Q)
  : Id (Subgroups G) P Q
  ≔ let Yu ≔ gset_underlying G (P .gset) in
    mere_rec (Σ Yu (y ↦ Id (Subgroups G) (subgroup_at G P y) Q)) (Id (Subgroups G) P Q) (subgroups_set G P Q)
      (w ↦ let Q' ≔ subgroup_at G P (w .fst) in
        concat (Subgroups G) P Q' Q
          (sylow_normalized_equal_at p hp G P sP (w .fst)
            (g r ↦ calc
              subgroup_conjugate G g Q'
              = subgroup_conjugate G g Q by map_path (Subgroups G) (Subgroups G) (subgroup_conjugate G g) Q' Q (w .snd)
              = Q by fix g r
              = Q' by inverse (Subgroups G) Q' Q (w .snd) ∎))
          (w .snd))
      (sylow_subgroup_is_at p hp G P Q sP sQ)

{` The action of G on Syl_G^p is conjugation of the underlying subgroup. `}
def sylow_gset_act (p : Nat) (G : Group) (g : USym G) (Q : SylowSubgroups p G)
  : Id (Subgroups G) (sylow_point p G (gset_usym_act G (sylow_gset p G) g Q)) (subgroup_conjugate G g (Q .fst))
  ≔ subgroups_gset_usym_act G g (Q .fst)

def sylow_subgroups_path (p : Nat) (G : Group) (Q Q' : SylowSubgroups p G)
  (e : Id (Subgroups G) (Q .fst) (Q' .fst)) : Id (SylowSubgroups p G) Q Q'
  ≔ subtype_equal (Subgroups G) (IsSylowSubgroup p G) (is_sylow_subgroup_prop p G) Q Q' e

{` The points of Syl_G^p fixed by P: exactly P. `}
def sylow_fixed_by_self (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : SubgroupFixes G P (sylow_gset p G) (P, sP)
  ≔ g r ↦ sylow_subgroups_path p G (gset_usym_act G (sylow_gset p G) g (P, sP)) (P, sP)
      (concat (Subgroups G) (sylow_point p G (gset_usym_act G (sylow_gset p G) g (P, sP))) (subgroup_conjugate G g P) P
        (sylow_gset_act p G g (P, sP))
        (concat (Subgroups G) (subgroup_conjugate G g P) (subgroup_at G P (gset_usym_act G (P .gset) g (P .point))) P
          (subgroup_conjugate_at G g P)
          (map_path (gset_underlying G (P .gset)) (Subgroups G) (subgroup_at G P)
            (gset_usym_act G (P .gset) g (P .point)) (P .point) r)))

def sylow_fixed_is_self (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  (u : SubgroupFixedSet G P (sylow_gset p G)) : Id (SubgroupFixedSet G P (sylow_gset p G)) u ((P, sP), sylow_fixed_by_self p G P sP)
  ≔ let Q ≔ u .fst in
    subtype_equal (SylowSubgroups p G) (SubgroupFixes G P (sylow_gset p G)) (subgroup_fixes_prop G P (sylow_gset p G))
      u ((P, sP), sylow_fixed_by_self p G P sP)
      (sylow_subgroups_path p G Q (P, sP)
        (inverse (Subgroups G) P (Q .fst)
          (sylow_normalized_equal p hp G P (Q .fst) sP (Q .snd)
            (g r ↦ concat (Subgroups G) (subgroup_conjugate G g (Q .fst))
              (sylow_point p G (gset_usym_act G (sylow_gset p G) g Q)) (Q .fst)
              (inverse (Subgroups G) (sylow_point p G (gset_usym_act G (sylow_gset p G) g Q)) (subgroup_conjugate G g (Q .fst))
                (sylow_gset_act p G g Q))
              (map_path (SylowSubgroups p G) (Subgroups G) (sylow_point p G) (gset_usym_act G (sylow_gset p G) g Q) Q
                (u .snd g r))))))

def sylow_fixed_prop (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : isProp (SubgroupFixedSet G P (sylow_gset p G))
  ≔ u v ↦ concat (SubgroupFixedSet G P (sylow_gset p G)) u ((P, sP), sylow_fixed_by_self p G P sP) v
      (sylow_fixed_is_self p hp G P sP u)
      (inverse (SubgroupFixedSet G P (sylow_gset p G)) v ((P, sP), sylow_fixed_by_self p G P sP)
        (sylow_fixed_is_self p hp G P sP v))

{` thm:sylow3 (2): |Syl_G^p| ≡ 1 (mod p). `}
def sylow_three_congruence (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : NatCongruent p (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) (suc. zero.)
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    let Y ≔ sylow_gset p G in
    let hY : IsFiniteGSet G Y ≔ sylow_subgroups_finite p hp G P sP in
    let dP ≔ subgroup_gset_decidable_equality G hG P hP in
    let F ≔ SubgroupFixedSet G P Y in
    let hF ≔ subgroup_fixed_set_finite G hG P dP Y hY in
    transport Nat (k ↦ NatCongruent p (gset_card G Y hY) k) (cardinality F hF) (suc. zero.)
      (inhabited_prop_cardinality F (sylow_fixed_prop p hp G P sP) hF ((P, sP), sylow_fixed_by_self p G P sP))
      (subgroup_fixed_set_congruence p hp (sylow_exponent p G P sP) G hG P hP (sylow_subgroup_card p G P sP) dP Y hY)

{` thm:sylow3, both parts. `}
def sylow_three (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Product
      (Σ Nat (m ↦ Product
        (Id Nat (group_card G (sylow_group_finite p G P sP)) (mul m (group_card (subgroup_group G P) (sylow_subgroup_finite p G P sP))))
        (NatDivides (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) m)))
      (NatCongruent p (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) (suc. zero.))
  ≔ (sylow_three_divides p hp G P sP, sylow_three_congruence p hp G P sP)
