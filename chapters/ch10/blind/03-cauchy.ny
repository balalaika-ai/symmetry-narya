{` Blind statements for chapter 10 (fingp.tex), section "Cauchy's theorem". `}
export "02-lagrange"

{` X^G ≔ Π_{z:BG} X(z), the set of fixed points of a G-set. `}
def BlindFixedPoints (G : Group) (X : GSet G) : Type ≔ (z : BG G .carrier) → X z .fst

{` lem:fixedptsize. p prime, |G| = p^n with n positive, X a non-empty finite G-set with p | |X(sh_G)|; then
   X^G is finite and p | |X^G|. `}
def blind_fixedptsize : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (n : Nat) (G : Group) (hG : BlindHasOrder G (blind_pow p (suc. n)))
    (X : GSet G) (ne : Mere (gset_underlying G X)) (hX : IsFinite (gset_underlying G X))
    → NatDivides p (cardinality (gset_underlying G X) hX)
    → Σ (IsFinite (BlindFixedPoints G X)) (hF ↦ NatDivides p (cardinality (BlindFixedPoints G X) hF))

{` thm:cauchys. p prime, G finite with p | |G|: G has a subgroup which is cyclic of order p (its underlying
   group is C_p). `}
def blind_cauchys : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindIsFiniteGroup G)
    → NatDivides p (blind_group_order G hG)
    → Mere (Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) (cyclic_group p)))

{` def:center (symmetry.tex): Z(G) ≔ Π_{z:BG} (z = z), the symmetries of the center. `}
def BlindCenter (G : Group) : Type ≔ (z : BG G .carrier) → Id (BG G .carrier) z z

{` lem:nontrivcenter (printed "finite subgroup", read: finite group). |G| = p^n, p prime, n positive: Z(G) is
   nontrivial, i.e. its set of symmetries Π_z (z = z) is not contractible (a group is trivial iff its
   symmetries are contractible). `}
def blind_nontrivcenter : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (n : Nat) (G : Group) (hG : BlindHasOrder G (blind_pow p (suc. n)))
    → Not (BookIsContr (BlindCenter G))

{` Stronger form: some element of Z(G) differs from the unit z ↦ refl z. `}
def blind_nontrivcenter_element : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (n : Nat) (G : Group) (hG : BlindHasOrder G (blind_pow p (suc. n)))
    → Mere (Σ (BlindCenter G) (c ↦ Not (Id (BlindCenter G) c (z ↦ refl z))))

{` A group is cyclic if it is C_m for some m. `}
def BlindIsCyclic (G : Group) : Type ≔ Mere (Σ Nat (m ↦ Id Group G (cyclic_group m)))

{` cor:orderpsquaredgroups (p prime, as everywhere in the section). A noncyclic group of order p^2 is of the
   form C_p × C_p. `}
def blind_orderpsquaredgroups : Type
  ≔ (p : Nat) (hp : BlindIsPrime p) (G : Group) (hG : BlindHasOrder G (blind_pow p 2))
    → Not (BlindIsCyclic G)
    → Mere (Id Group G (product_group (cyclic_group p) (cyclic_group p)))
