{` Blind statements for chapter 10 (fingp.tex), section "Sylow's Theorems". `}
export "03-cauchy"
export "../../../src/903-normal-subgroups"

{` thm:sylow1. p prime, n : N, G finite with p^n | |G|: G has a subgroup of order p^n. `}
def blind_sylow1 : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (n : Nat) (G : Group) (hG : BlindIsFiniteGroup G)
    → NatDivides (blind_pow p n) (blind_group_order G hG)
    → Mere (Σ (Subgroups G) (S ↦ BlindHasOrder (subgroup_group G S) (blind_pow p n)))

{` def:sylowsubgroup. p^n is the largest power of p dividing the order of the finite group G. `}
def BlindLargestPowerDividing (G : Group) (p n : Nat) : Type
  ≔ Σ (BlindIsFiniteGroup G) (hG ↦
      Product (NatDivides (blind_pow p n) (blind_group_order G hG))
              (Not (NatDivides (blind_pow p (suc. n)) (blind_group_order G hG))))

{` def:sylowsubgroup. A p-Sylow subgroup: a subgroup of order p^n, p^n the largest power of p dividing |G|. `}
def BlindIsSylow (G : Group) (p : Nat) (S : Subgroups G) : Type
  ≔ Σ Nat (n ↦ Product (BlindLargestPowerDividing G p n) (BlindHasOrder (subgroup_group G S) (blind_pow p n)))

{` def:sylowsubgroup. Syl_G^p, the G-subset of Sub(G) of p-Sylow subgroups (at z : BG, of the group
   (BG, z)); truncated to make it a proposition. `}
def blind_sylow_gsubset (G : Group) (p : Nat) : GSubsets G (subgroups_gset G)
  ≔ z S ↦ (Mere (BlindIsSylow (group_at G z) p S), mere_isprop (BlindIsSylow (group_at G z) p S))

def blind_sylow_gset (G : Group) (p : Nat) : GSet G ≔ gsubset_gset G (subgroups_gset G) (blind_sylow_gsubset G p)

def BlindSylowSet (G : Group) (p : Nat) : Type ≔ gset_underlying G (blind_sylow_gset G p)

{` Conjugation of subgroups: the action of G on the G-set Sub(G). `}
def blind_conj_subgroup (G : Group) (g : USym G) (S : Subgroups G) : Subgroups G
  ≔ gset_usym_act G (subgroups_gset G) g S

def BlindConjugate (G : Group) (S T : Subgroups G) : Type
  ≔ Mere (Σ (USym G) (g ↦ Id (Subgroups G) (blind_conj_subgroup G g S) T))

{` lem:numberofconjofSylow (p prime, as everywhere in the section). The set of conjugates of a p-Sylow
   subgroup P (its orbit G · P in Sub(G)) is finite of cardinality not divisible by p. `}
def blind_numberofconjofsylow : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G) (P : Subgroups G)
    → BlindIsSylow G p P
    → Σ (IsFinite (OrbitUnderlying G (subgroups_gset G) P))
        (h ↦ Not (NatDivides p (cardinality (OrbitUnderlying G (subgroups_gset G) P) h)))

{` thm:sylow2 (1). Any two p-Sylow subgroups are conjugate. `}
def blind_sylow2_conjugate : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G) (P Q : Subgroups G)
    → BlindIsSylow G p P → BlindIsSylow G p Q → BlindConjugate G P Q

{` thm:sylow2 (1), "in other words": the G-set Syl_G^p is transitive. `}
def blind_sylow2_transitive : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G) → IsTransitive G (blind_sylow_gset G p)

{` thm:sylow2 (2). A subgroup H of order p^s is conjugate to a subgroup of a p-Sylow subgroup P. `}
def blind_sylow2_subconjugate : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G) (H : Subgroups G) (s : Nat)
    → BlindHasOrder (subgroup_group G H) (blind_pow p s)
    → (P : Subgroups G) → BlindIsSylow G p P
    → Mere (Σ (USym G) (g ↦ BlindSubgroupLe G (blind_conj_subgroup G g H) P))

{` thm:sylow3. G finite, P a p-Sylow subgroup (p prime). Syl_G^p is finite and its cardinality k
   (1) divides |G|/|P|: k | q whenever |G| = q · |P|, and (2) is 1 modulo p. `}
def blind_sylow3 : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G) (P : Subgroups G)
    → BlindIsSylow G p P
    → Σ (IsFinite (BlindSylowSet G p)) (h ↦
        Product
          ((q : Nat) (hP : BlindIsFiniteGroup (subgroup_group G P))
             → Id Nat (blind_group_order G hG) (mul q (blind_group_order (subgroup_group G P) hP))
             → NatDivides (cardinality (BlindSylowSet G p) h) q)
          (Σ Nat (t ↦ Id Nat (cardinality (BlindSylowSet G p) h) (suc. (mul t p)))))
