export "1032-p-group-closed-subsets"
export "902-subgroup-gsets"

{` Chapter 10, sec:sylow (fingp.tex 261-287): def:sylowsubgroup,
   lem:numberofconjofSylow and thm:sylow2.

   def:sylowsubgroup. A p-Sylow subgroup of G is a subgroup S such that G
   and S are finite and |S| = p^n where p^n is the largest power of p
   dividing |G| (IsSylowSubgroup, a proposition). Syl_G^p is the G-subset
   of the G-set Sub_G of subgroups (subgroups_gset, module 902; G acts by
   conjugation, g · (X, x) = (X, g · x)) given at z : BG by the Sylow
   subgroups of group_at G z (sylow_gsubset); its underlying set is
   Σ_{S : Sub(G)} S is p-Sylow.

   Conjugates. For S = (X, x) the conjugate g · S is subgroups_move g S =
   (X, g · x); every conjugate is (X, y) = subgroup_at S y for some y and
   conversely (subgroup_conjugate_at, subgroup_at_conjugate). The set of
   conjugates SubgroupConjugates G S of module 1031 is therefore the orbit
   of S in Sub(G).

   lem:numberofconjofSylow: the number of conjugates of a p-Sylow subgroup
   P is not divisible by p (it divides the index |X(sh_G)| = |G|/|P|, which
   is prime to p).

   thm:sylow2: a subgroup H of order p^s is contained in a conjugate of a
   p-Sylow subgroup P (the restricted action of H on X(sh_G) has a fixed
   point because p ∤ |X(sh_G)|); any two p-Sylow subgroups are conjugate.
   The second form of the book ("Syl is a transitive G-set") also needs
   that a Sylow subgroup exists; it is in module 1035 after thm:sylow1. `}

{` The exponent of a Sylow subgroup: |S| = p^n with p^n the largest power of
   p dividing |G|. At most one n. `}
def SylowExponent (p m c : Nat) : Type
  ≔ Σ Nat (n ↦ Product (Id Nat c (nat_power p n)) (IsLargestPrimePower p n m))

def sylow_exponent_prop (p m c : Nat) : isProp (SylowExponent p m c)
  ≔ u v ↦ subtype_equal Nat (n ↦ Product (Id Nat c (nat_power p n)) (IsLargestPrimePower p n m))
      (n ↦ product_prop (Id Nat c (nat_power p n)) (IsLargestPrimePower p n m) (nat_set c (nat_power p n))
        (is_largest_prime_power_prop p n m))
      u v (largest_prime_power_unique p m (u .fst) (v .fst) (u .snd .snd) (v .snd .snd))

{` def:sylowsubgroup. `}
def IsSylowSubgroup (p : Nat) (G : Group) (S : Subgroups G) : Type
  ≔ Σ (IsFiniteGroup G) (hG ↦ Σ (IsFiniteGroup (subgroup_group G S))
      (hS ↦ SylowExponent p (group_card G hG) (group_card (subgroup_group G S) hS)))

def is_sylow_subgroup_prop (p : Nat) (G : Group) (S : Subgroups G) : isProp (IsSylowSubgroup p G S)
  ≔ sigma_prop (IsFiniteGroup G)
      (hG ↦ Σ (IsFiniteGroup (subgroup_group G S))
        (hS ↦ SylowExponent p (group_card G hG) (group_card (subgroup_group G S) hS)))
      (is_finite_group_prop G)
      (hG ↦ sigma_prop (IsFiniteGroup (subgroup_group G S))
        (hS ↦ SylowExponent p (group_card G hG) (group_card (subgroup_group G S) hS))
        (is_finite_group_prop (subgroup_group G S))
        (hS ↦ sylow_exponent_prop p (group_card G hG) (group_card (subgroup_group G S) hS)))

{` Syl_G^p as a G-subset of Sub_G, its G-set, and its underlying set. `}
def sylow_gsubset (p : Nat) (G : Group) : GSubsets G (subgroups_gset G)
  ≔ z S ↦ (IsSylowSubgroup p (group_at G z) S, is_sylow_subgroup_prop p (group_at G z) S)

def sylow_gset (p : Nat) (G : Group) : GSet G ≔ gsubset_gset G (subgroups_gset G) (sylow_gsubset p G)

def SylowSubgroups (p : Nat) (G : Group) : Type ≔ Σ (Subgroups G) (IsSylowSubgroup p G)

def sylow_gset_underlying (p : Nat) (G : Group)
  : Id Type (gset_underlying G (sylow_gset p G)) (SylowSubgroups p G)
  ≔ refl (SylowSubgroups p G)

{` Conjugation of subgroups, g · S, and its description as (X, g · x). `}
def subgroup_conjugate (G : Group) (g : USym G) (S : Subgroups G) : Subgroups G
  ≔ subgroups_move G (shape G) (shape G) g S

def subgroup_conjugate_at (G : Group) (g : USym G) (S : Subgroups G)
  : Id (Subgroups G) (subgroup_conjugate G g S) (subgroup_at G S (gset_usym_act G (S .gset) g (S .point)))
  ≔ subgroup_path G (subgroup_conjugate G g S) (subgroup_at G S (gset_usym_act G (S .gset) g (S .point)))
      (refl (subgroup_pointed G (subgroup_at G S (gset_usym_act G (S .gset) g (S .point)))))

def subgroup_at_conjugate (G : Group) (S : Subgroups G) (y : gset_underlying G (S .gset))
  : Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) (subgroup_at G S y)))
  ≔ let X ≔ S .gset in
    let R ≔ Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) (subgroup_at G S y)) in
    mere_rec (GSetTransporter G X (S .point) y) (Mere R) (mere_isprop R)
      (w ↦ mere R (w .fst,
        concat (Subgroups G) (subgroup_conjugate G (w .fst) S) (subgroup_at G S (gset_usym_act G X (w .fst) (S .point)))
          (subgroup_at G S y) (subgroup_conjugate_at G (w .fst) S)
          (map_path (gset_underlying G X) (Subgroups G) (subgroup_at G S) (gset_usym_act G X (w .fst) (S .point)) y
            (inverse (gset_underlying G X) y (gset_usym_act G X (w .fst) (S .point)) (w .snd)))))
      (subgroup_point_reach G S y)

{` The conjugates of S in the sense of module 1031 are exactly the
   subgroups g · S. `}
def subgroup_conjugates_orbit_iff (G : Group) (S T : Subgroups G)
  : Product (Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T))
             → Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T)))
            (Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T))
             → Mere (Σ (gset_underlying G (S .gset)) (y ↦ Id (Subgroups G) (subgroup_at G S y) T)))
  ≔ let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    let A ≔ Σ Y (y ↦ Id (Subgroups G) (subgroup_at G S y) T) in
    let B ≔ Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T) in
    (m ↦ mere_rec A (Mere B) (mere_isprop B)
        (w ↦ mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) (subgroup_at G S (w .fst))))
          (Mere B) (mere_isprop B)
          (v ↦ mere B (v .fst, concat (Subgroups G) (subgroup_conjugate G (v .fst) S) (subgroup_at G S (w .fst)) T
            (v .snd) (w .snd)))
          (subgroup_at_conjugate G S (w .fst)))
        m,
     m ↦ mere_rec B (Mere A) (mere_isprop A)
        (v ↦ mere A (gset_usym_act G X (v .fst) (S .point),
          concat (Subgroups G) (subgroup_at G S (gset_usym_act G X (v .fst) (S .point))) (subgroup_conjugate G (v .fst) S) T
            (inverse (Subgroups G) (subgroup_conjugate G (v .fst) S) (subgroup_at G S (gset_usym_act G X (v .fst) (S .point)))
              (subgroup_conjugate_at G (v .fst) S))
            (v .snd)))
        m)

{` Arithmetic: if p | a then p^(n+1) | a · p^n. `}
def fingp_power_succ_divides (p n a : Nat) (d : NatDivides p a) : NatDivides (nat_power p (suc. n)) (mul a (nat_power p n))
  ≔ mere_rec (Σ Nat (q ↦ Id Nat a (mul q p))) (NatDivides (nat_power p (suc. n)) (mul a (nat_power p n)))
      (nat_divides_prop (nat_power p (suc. n)) (mul a (nat_power p n)))
      (w ↦ nat_divides_intro (nat_power p (suc. n)) (mul a (nat_power p n)) (w .fst)
        (calc
          mul a (nat_power p n)
          = mul (mul (w .fst) p) (nat_power p n)
            by map_path Nat Nat (k ↦ mul k (nat_power p n)) a (mul (w .fst) p) (w .snd)
          = mul (w .fst) (mul p (nat_power p n)) by mul_assoc (w .fst) p (nat_power p n)
          = mul (w .fst) (mul (nat_power p n) p)
            by map_path Nat Nat (mul (w .fst)) (mul p (nat_power p n)) (mul (nat_power p n) p) (mul_comm p (nat_power p n)) ∎))
      d

{` Data of a p-Sylow subgroup, with G's finiteness taken from it. `}
def sylow_group_finite (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P) : IsFiniteGroup G
  ≔ sP .fst

def sylow_subgroup_finite (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : IsFiniteGroup (subgroup_group G P)
  ≔ sP .snd .fst

def sylow_exponent (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P) : Nat
  ≔ sP .snd .snd .fst

def sylow_subgroup_card (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Id Nat (group_card (subgroup_group G P) (sylow_subgroup_finite p G P sP)) (nat_power p (sylow_exponent p G P sP))
  ≔ sP .snd .snd .snd .fst

{` The index |X(sh_G)| = |G|/|P| of a p-Sylow subgroup is prime to p. `}
def sylow_index_not_divisible (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Not (NatDivides p (gset_card G (P .gset)
      (subgroup_gset_finite G (sylow_group_finite p G P sP) P (sylow_subgroup_finite p G P sP))))
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    let n ≔ sylow_exponent p G P sP in
    let a ≔ gset_card G (P .gset) (subgroup_gset_finite G hG P hP) in
    d ↦ sP .snd .snd .snd .snd .snd
      (transport Nat (k ↦ NatDivides (nat_power p (suc. n)) k) (mul a (nat_power p n)) (group_card G hG)
        (calc
          mul a (nat_power p n)
          = mul a (group_card (subgroup_group G P) hP)
            by map_path Nat Nat (mul a) (nat_power p n) (group_card (subgroup_group G P) hP)
              (inverse Nat (group_card (subgroup_group G P) hP) (nat_power p n) (sylow_subgroup_card p G P sP))
          = group_card G hG by inverse Nat (group_card G hG) (mul a (group_card (subgroup_group G P) hP))
              (lagrange_counting G hG P hP) ∎)
        (fingp_power_succ_divides p n a d))

{` lem:numberofconjofSylow: the number of conjugates of a p-Sylow subgroup
   is not divisible by p. `}
def sylow_conjugates_not_divisible (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Not (NatDivides p (cardinality (SubgroupConjugates G P)
      (subgroup_conjugates_finite G (sylow_group_finite p G P sP) P (sylow_subgroup_finite p G P sP))))
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    d ↦ sylow_index_not_divisible p G P sP
      (nat_divides_trans p (cardinality (SubgroupConjugates G P) (subgroup_conjugates_finite G hG P hP))
        (gset_card G (P .gset) (subgroup_gset_finite G hG P hP)) d (subgroup_conjugates_divides_index G hG P hP))

{` Group cardinalities do not depend on the finiteness proof. `}
def fingp_group_card_irrel (G : Group) (h h' : IsFiniteGroup G) : Id Nat (group_card G h) (group_card G h')
  ≔ map_path (IsFiniteGroup G) Nat (group_card G) h h' (is_finite_group_prop G h h')

{` The subgroups (X, y) of a p-Sylow subgroup P = (X, x) are p-Sylow. `}
def sylow_subgroup_at (p : Nat) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  (y : gset_underlying G (P .gset)) : IsSylowSubgroup p G (subgroup_at G P y)
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    (hG, (subgroup_at_finite G hG P hP y,
     (sylow_exponent p G P sP,
      (concat Nat (group_card (subgroup_group G (subgroup_at G P y)) (subgroup_at_finite G hG P hP y))
         (group_card (subgroup_group G P) hP) (nat_power p (sylow_exponent p G P sP))
         (subgroup_at_card G hG P hP y) (sylow_subgroup_card p G P sP),
       sP .snd .snd .snd .snd))))

def sylow_subgroup_path (p : Nat) (G : Group) (S T : Subgroups G) (e : Id (Subgroups G) S T)
  (sS : IsSylowSubgroup p G S) : IsSylowSubgroup p G T
  ≔ transport (Subgroups G) (IsSylowSubgroup p G) S T e sS

{` thm:sylow2, second claim, in the form: a finite subgroup H of order p^s
   fixes a point y of the G-set X of P, i.e. H ⊆ (X, y). `}
def sylow_contains_subgroup_at (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G)
  (sP : IsSylowSubgroup p G P) (H : Subgroups G) (hH : IsFiniteGroup (subgroup_group G H)) (s : Nat)
  (hc : Id Nat (group_card (subgroup_group G H) hH) (nat_power p s))
  : Mere (Σ (gset_underlying G (P .gset)) (y ↦ SubgroupLe G H (subgroup_at G P y)))
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    let X ≔ P .gset in
    let R ≔ Σ (gset_underlying G X) (y ↦ SubgroupLe G H (subgroup_at G P y)) in
    let Z ≔ subgroup_restricted_gset G H X in
    mere_rec (GSetFixedPoints (subgroup_group G H) Z) (Mere R) (mere_isprop R)
      (w ↦ mere R (w .fst, subgroup_restricted_fixes G H X (w .fst) (w .snd)))
      (p_group_fixed_point_exists p hp s (subgroup_group G H) hH hc Z (subgroup_gset_finite G hG P hP)
        (sylow_index_not_divisible p G P sP))

{` thm:sylow2, second claim: H is contained in a conjugate g · P. `}
def sylow_contains_conjugate (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G)
  (sP : IsSylowSubgroup p G P) (H : Subgroups G) (hH : IsFiniteGroup (subgroup_group G H)) (s : Nat)
  (hc : Id Nat (group_card (subgroup_group G H) hH) (nat_power p s))
  : Mere (Σ (USym G) (g ↦ SubgroupLe G H (subgroup_conjugate G g P)))
  ≔ let R ≔ Σ (USym G) (g ↦ SubgroupLe G H (subgroup_conjugate G g P)) in
    mere_rec (Σ (gset_underlying G (P .gset)) (y ↦ SubgroupLe G H (subgroup_at G P y))) (Mere R) (mere_isprop R)
      (w ↦ mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g P) (subgroup_at G P (w .fst))))
        (Mere R) (mere_isprop R)
        (v ↦ mere R (v .fst, transport (Subgroups G) (T ↦ SubgroupLe G H T) (subgroup_at G P (w .fst))
          (subgroup_conjugate G (v .fst) P)
          (inverse (Subgroups G) (subgroup_conjugate G (v .fst) P) (subgroup_at G P (w .fst)) (v .snd)) (w .snd)))
        (subgroup_at_conjugate G P (w .fst)))
      (sylow_contains_subgroup_at p hp G P sP H hH s hc)

{` Any p-Sylow subgroup Q is (X, y) for some y. `}
def sylow_subgroup_is_at (p : Nat) (hp : NatIsPrime p) (G : Group) (P Q : Subgroups G)
  (sP : IsSylowSubgroup p G P) (sQ : IsSylowSubgroup p G Q)
  : Mere (Σ (gset_underlying G (P .gset)) (y ↦ Id (Subgroups G) (subgroup_at G P y) Q))
  ≔ let hG ≔ sylow_group_finite p G P sP in
    let hP ≔ sylow_subgroup_finite p G P sP in
    let hQ ≔ sylow_subgroup_finite p G Q sQ in
    let nQ ≔ sylow_exponent p G Q sQ in
    let R ≔ Σ (gset_underlying G (P .gset)) (y ↦ Id (Subgroups G) (subgroup_at G P y) Q) in
    let same : Id Nat nQ (sylow_exponent p G P sP)
      ≔ largest_prime_power_unique p (group_card G hG) nQ (sylow_exponent p G P sP)
          (transport Nat (IsLargestPrimePower p nQ) (group_card G (sQ .fst)) (group_card G hG)
            (fingp_group_card_irrel G (sQ .fst) hG) (sQ .snd .snd .snd .snd))
          (sP .snd .snd .snd .snd) in
    mere_rec (Σ (gset_underlying G (P .gset)) (y ↦ SubgroupLe G Q (subgroup_at G P y))) (Mere R) (mere_isprop R)
      (w ↦ mere R (w .fst, inverse (Subgroups G) Q (subgroup_at G P (w .fst))
        (subgroup_le_card_eq G hG Q (subgroup_at G P (w .fst)) hQ (subgroup_at_finite G hG P hP (w .fst)) (w .snd)
          (calc
            group_card (subgroup_group G Q) hQ
            = nat_power p nQ by sylow_subgroup_card p G Q sQ
            = nat_power p (sylow_exponent p G P sP)
              by map_path Nat Nat (nat_power p) nQ (sylow_exponent p G P sP) same
            = group_card (subgroup_group G P) hP
              by inverse Nat (group_card (subgroup_group G P) hP) (nat_power p (sylow_exponent p G P sP))
                (sylow_subgroup_card p G P sP)
            = group_card (subgroup_group G (subgroup_at G P (w .fst))) (subgroup_at_finite G hG P hP (w .fst))
              by inverse Nat (group_card (subgroup_group G (subgroup_at G P (w .fst))) (subgroup_at_finite G hG P hP (w .fst)))
                (group_card (subgroup_group G P) hP) (subgroup_at_card G hG P hP (w .fst)) ∎))))
      (sylow_contains_subgroup_at p hp G P sP Q hQ nQ (sylow_subgroup_card p G Q sQ))

{` thm:sylow2, first claim: any two p-Sylow subgroups are conjugate. `}
def sylow_subgroups_conjugate (p : Nat) (hp : NatIsPrime p) (G : Group) (P Q : Subgroups G)
  (sP : IsSylowSubgroup p G P) (sQ : IsSylowSubgroup p G Q)
  : Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g P) Q))
  ≔ subgroup_conjugates_orbit_iff G P Q .fst (sylow_subgroup_is_at p hp G P Q sP sQ)

{` The p-Sylow subgroups are exactly the conjugates of P. `}
def sylow_conjugates_equiv (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  : Equiv (SylowSubgroups p G) (SubgroupConjugates G P)
  ≔ let Y ≔ gset_underlying G (P .gset) in
    family_equiv (Subgroups G) (IsSylowSubgroup p G)
      (T ↦ Mere (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
      (T ↦ iff_equiv (IsSylowSubgroup p G T) (Mere (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
        (is_sylow_subgroup_prop p G T) (mere_isprop (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
        (sT ↦ sylow_subgroup_is_at p hp G P T sP sT)
        (m ↦ mere_rec (Σ Y (y ↦ Id (Subgroups G) (subgroup_at G P y) T)) (IsSylowSubgroup p G T)
          (is_sylow_subgroup_prop p G T)
          (w ↦ sylow_subgroup_path p G (subgroup_at G P (w .fst)) T (w .snd) (sylow_subgroup_at p G P sP (w .fst)))
          m))
