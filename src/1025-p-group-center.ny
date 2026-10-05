export "1023-p-group-fixed-points"
export "1202-group-center"

{` Chapter 10, lem:nontrivcenter (fingp.tex 203): a group of cardinality
   p^n with p prime and n positive has a nontrivial center. As in the
   book's proof, the fixed points of the adjoint G-set Ad_G(z) = (z = z)
   are the central symmetries, and the center Z(G) of chapter 12
   (group_center, module 1202) has USym Z(G) ≃ {g | g central}. By
   lem:fixedptsize the number of central symmetries is divisible by p.

   The printed "finite subgroup of cardinality p^n" means a finite group;
   "nontrivial" is proved in the strong form: there is (merely) a central
   symmetry different from e, and Z(G) is not the trivial group. `}

{` A symmetry is fixed by the adjoint action iff it is central. `}
def adjoint_fixed_central (G : Group) (g : USym G)
  (f : (h : USym G) → Id (USym G) (gset_usym_act G (adjoint_gset G) h g) g) : CentralSymmetry G g
  ≔ h ↦
    let B ≔ BG G .carrier in
    let a ≔ shape G in
    let e : Id (Id B a a) (concat B a a a (inverse B a a h) (concat B a a a g h)) g
      ≔ concat (Id B a a) (concat B a a a (inverse B a a h) (concat B a a a g h))
          (gset_usym_act G (adjoint_gset G) h g) g
          (inverse (Id B a a) (gset_usym_act G (adjoint_gset G) h g)
            (concat B a a a (inverse B a a h) (concat B a a a g h)) (adjoint_gset_act G a a h g))
          (f h) in
    calc
      concat B a a a h g
      = concat B a a a h (concat B a a a (inverse B a a h) (concat B a a a g h))
        by refl (concat B a a a h) (inverse (Id B a a) (concat B a a a (inverse B a a h) (concat B a a a g h)) g e)
      = concat B a a a (concat B a a a h (inverse B a a h)) (concat B a a a g h)
        by inverse (Id B a a) (concat B a a a (concat B a a a h (inverse B a a h)) (concat B a a a g h))
          (concat B a a a h (concat B a a a (inverse B a a h) (concat B a a a g h)))
          (concat_assoc B a a a a h (inverse B a a h) (concat B a a a g h))
      = concat B a a a (refl a) (concat B a a a g h)
        by refl ((r ↦ concat B a a a r (concat B a a a g h)) : Id B a a → Id B a a) (concat_inverse_right B a a h)
      = concat B a a a g h by concat_1p B a a (concat B a a a g h) ∎

def central_adjoint_fixed (G : Group) (g : USym G) (c : CentralSymmetry G g) (h : USym G)
  : Id (USym G) (gset_usym_act G (adjoint_gset G) h g) g
  ≔ let B ≔ BG G .carrier in
    let a ≔ shape G in
    calc
      gset_usym_act G (adjoint_gset G) h g
      = concat B a a a (inverse B a a h) (concat B a a a g h) by adjoint_gset_act G a a h g
      = concat B a a a (inverse B a a h) (concat B a a a h g)
        by refl (concat B a a a (inverse B a a h)) (inverse (Id B a a) (concat B a a a h g) (concat B a a a g h) (c h))
      = concat B a a a (concat B a a a (inverse B a a h) h) g
        by inverse (Id B a a) (concat B a a a (concat B a a a (inverse B a a h) h) g)
          (concat B a a a (inverse B a a h) (concat B a a a h g)) (concat_assoc B a a a a (inverse B a a h) h g)
      = concat B a a a (refl a) g
        by refl ((r ↦ concat B a a a r g) : Id B a a → Id B a a) (concat_inverse_left B a a h)
      = g by concat_1p B a a g ∎

{` The fixed points of Ad_G are the abstract center Σ_g Π_h gh = hg. `}
def adjoint_fixed_center_equiv (G : Group) : Equiv (GSetFixedPoints G (adjoint_gset G)) (AbstractCenter G)
  ≔ family_equiv (USym G) (g ↦ (h : USym G) → Id (USym G) (gset_usym_act G (adjoint_gset G) h g) g) (CentralSymmetry G)
      (g ↦ iff_equiv ((h : USym G) → Id (USym G) (gset_usym_act G (adjoint_gset G) h g) g) (CentralSymmetry G g)
        (gset_fixed_points_prop G (adjoint_gset G) g) (central_symmetry_prop G g)
        (adjoint_fixed_central G g) (central_adjoint_fixed G g))

def center_usym_fixed_equiv (G : Group) : Equiv (USym (group_center G)) (GSetFixedPoints G (adjoint_gset G))
  ≔ compose_equiv (USym (group_center G)) (AbstractCenter G) (GSetFixedPoints G (adjoint_gset G))
      (native_equivalence (USym (group_center G)) (AbstractCenter G) (center_usym_equiv G))
      (canonical_inverse_equiv (GSetFixedPoints G (adjoint_gset G)) (AbstractCenter G) (adjoint_fixed_center_equiv G))

{` The center of a finite group is finite, |Z(G)| = number of central symmetries. `}
def center_finite (G : Group) (hG : IsFiniteGroup G) : IsFiniteGroup (group_center G)
  ≔ finite_of_equiv (USym (group_center G)) (GSetFixedPoints G (adjoint_gset G)) (center_usym_fixed_equiv G)
      (gset_fixed_points_finite G hG (adjoint_gset G) hG)

def center_card_fixed (G : Group) (hG : IsFiniteGroup G)
  : Id Nat (group_card (group_center G) (center_finite G hG))
      (cardinality (GSetFixedPoints G (adjoint_gset G)) (gset_fixed_points_finite G hG (adjoint_gset G) hG))
  ≔ cardinality_equiv (USym (group_center G)) (GSetFixedPoints G (adjoint_gset G)) (center_usym_fixed_equiv G)
      (center_finite G hG) (gset_fixed_points_finite G hG (adjoint_gset G) hG)

def nat_prime_divides_power (p n : Nat) : NatDivides p (nat_power p (suc. n))
  ≔ mere (Σ Nat (q ↦ Id Nat (nat_power p (suc. n)) (mul q p))) (nat_power p n, refl (nat_power p (suc. n)))

def fingp_divides_one (d : Nat) (h : NatDivides d (suc. zero.)) : Id Nat d (suc. zero.)
  ≔ nat_divides_antisym d (suc. zero.) h (nat_one_divides d)

{` lem:nontrivcenter, counting form: p divides |Z(G)|. `}
def p_group_center_divisible (p : Nat) (hp : NatIsPrime p) (n : Nat) (hn : Lt zero. n) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) : NatDivides p (group_card (group_center G) (center_finite G hG))
  ≔ let Ad ≔ adjoint_gset G in
    let hd : NatDivides p (gset_card G Ad hG)
      ≔ transport Nat (NatDivides p) (nat_power p n) (group_card G hG) (inverse Nat (group_card G hG) (nat_power p n) hc)
          ((match n [ zero. ↦ l ↦ match l [] | suc. m ↦ _ ↦ nat_prime_divides_power p m ]
             : Lt zero. n → NatDivides p (nat_power p n)) hn) in
    transport Nat (NatDivides p) (cardinality (GSetFixedPoints G Ad) (gset_fixed_points_finite G hG Ad hG))
      (group_card (group_center G) (center_finite G hG))
      (inverse Nat (group_card (group_center G) (center_finite G hG))
        (cardinality (GSetFixedPoints G Ad) (gset_fixed_points_finite G hG Ad hG)) (center_card_fixed G hG))
      (p_group_fixed_points_divisible p hp n G hG hc Ad hG hd)

{` lem:nontrivcenter: there is a central symmetry other than e. `}
def p_group_center_nontrivial_element (p : Nat) (hp : NatIsPrime p) (n : Nat) (hn : Lt zero. n) (G : Group)
  (hG : IsFiniteGroup G) (hc : Id Nat (group_card G hG) (nat_power p n))
  : Mere (Σ (USym G) (g ↦ Product (CentralSymmetry G g) (Not (Id (USym G) g (usym_unit G)))))
  ≔ let P : USym G → Type ≔ g ↦ Product (CentralSymmetry G g) (Not (Id (USym G) g (usym_unit G))) in
    let dG ≔ finite_group_decidable_equality G hG in
    let dC : (g : USym G) → Decidable (CentralSymmetry G g)
      ≔ g ↦ finite_quantifiers (USym G) hG (h ↦ Id (USym G) (usym_mul G g h) (usym_mul G h g))
          (h ↦ usym_set G (usym_mul G g h) (usym_mul G h g)) (h ↦ dG (usym_mul G g h) (usym_mul G h g)) .fst in
    let dP : (g : USym G) → Decidable (P g)
      ≔ g ↦ match dC g [
        | inr. nc ↦ inr. (u ↦ nc (u .fst))
        | inl. c ↦ match dG g (usym_unit G) [
          | inl. e ↦ inr. (u ↦ u .snd e)
          | inr. ne ↦ inl. (c, ne) ] ] in
    let hZ ≔ center_finite G hG in
    match finite_quantifiers (USym G) hG P
      (g ↦ product_prop (CentralSymmetry G g) (Not (Id (USym G) g (usym_unit G))) (central_symmetry_prop G g)
        (negation_prop (Id (USym G) g (usym_unit G)))) dP .snd [
    | inl. t ↦ t
    | inr. no ↦
      let only_unit : (c : AbstractCenter G) → Id (USym G) (c .fst) (usym_unit G)
        ≔ c ↦ match dG (c .fst) (usym_unit G) [
          | inl. e ↦ e
          | inr. ne ↦ absurd (Id (USym G) (c .fst) (usym_unit G)) (no (mere (Σ (USym G) P) (c .fst, (c .snd, ne)))) ] in
      let B ≔ BG G .carrier in
      let a ≔ shape G in
      let unit_central : CentralSymmetry G (usym_unit G)
        ≔ h ↦ concat (Id B a a) (concat B a a a h (refl a)) h (concat B a a a (refl a) h)
            (concat_p1 B a a h) (inverse (Id B a a) (concat B a a a (refl a) h) h (concat_1p B a a h)) in
      let cZ : isProp (AbstractCenter G)
        ≔ c c' ↦ subtype_equal (USym G) (CentralSymmetry G) (central_symmetry_prop G) c c'
            (concat (USym G) (c .fst) (usym_unit G) (c' .fst) (only_unit c)
              (inverse (USym G) (c' .fst) (usym_unit G) (only_unit c'))) in
      let hA ≔ finite_of_equiv (AbstractCenter G) (USym (group_center G))
        (canonical_inverse_equiv (USym (group_center G)) (AbstractCenter G)
          (native_equivalence (USym (group_center G)) (AbstractCenter G) (center_usym_equiv G))) hZ in
      let one : Id Nat (group_card (group_center G) hZ) (suc. zero.)
        ≔ concat Nat (group_card (group_center G) hZ) (cardinality (AbstractCenter G) hA) (suc. zero.)
            (cardinality_equiv (USym (group_center G)) (AbstractCenter G)
              (native_equivalence (USym (group_center G)) (AbstractCenter G) (center_usym_equiv G)) hZ hA)
            (inhabited_prop_cardinality (AbstractCenter G) cZ hA (usym_unit G, unit_central)) in
      absurd (Mere (Σ (USym G) P))
        (prime_ne_one p hp (fingp_divides_one p (transport Nat (NatDivides p) (group_card (group_center G) hZ) (suc. zero.) one
          (p_group_center_divisible p hp n hn G hG hc)))) ]

{` lem:nontrivcenter: Z(G) is not the trivial group. `}
def p_group_center_not_trivial (p : Nat) (hp : NatIsPrime p) (n : Nat) (hn : Lt zero. n) (G : Group)
  (hG : IsFiniteGroup G) (hc : Id Nat (group_card G hG) (nat_power p n)) : Not (IsTrivialGroup (group_center G))
  ≔ t ↦
    let hZ ≔ center_finite G hG in
    let cU ≔ is_trivial_group_usym_contractible (group_center G) t in
    let one : Id Nat (group_card (group_center G) hZ) (suc. zero.)
      ≔ inhabited_prop_cardinality (USym (group_center G))
          (contractible_prop (USym (group_center G)) (native_contraction (USym (group_center G)) cU)) hZ
          (usym_unit (group_center G)) in
    prime_ne_one p hp (fingp_divides_one p (transport Nat (NatDivides p) (group_card (group_center G) hZ) (suc. zero.) one
      (p_group_center_divisible p hp n hn G hG hc)))
