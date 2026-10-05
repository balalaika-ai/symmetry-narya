export "912-weyl-fixed-points"

{` Chapter 9 (subgroups.tex), lem:WGHisHfixofG/H (line 2157): a formal
   counterexample to the printed statement (e : (X = X) → (G/H)^H is an
   equivalence for every group G and subgroup H).

   G ≔ Σ_A, the permutations of the set A ≔ ℕ ⊔ ℕ. The G-set X sends a set Y
   in the component of A to the injections j : ℕ → Y that extend to a
   bijection A ≃ Y along inl (merely), pointed by inl : ℕ → A; it is
   transitive. Its subgroup H (the stabilizer of inl) consists of the
   permutations fixing the left copy pointwise. "Drop the first value",
   j ↦ j ∘ suc, is a G-map X → X (the extension e becomes e ∘ t for the shift
   t : inl n ↦ inl (n+1), inr 0 ↦ inl 0, inr (m+1) ↦ inr m), hence an H-fixed
   point of G/H; it identifies inl with (0_L 0_R) ∘ inl, so it is not
   injective and not the transport along any f : X = X. Group-theoretically:
   t⁻¹ H t ⊊ H, so the coset tH is H-fixed although t ∉ N_G(H). `}

def weyl_cx_set : SetTypes ≔ (Sum Nat Nat, sum_set Nat Nat nat_set nat_set)

def weyl_cx_group : Group ≔ permutation_group weyl_cx_set

{` The shift t and the transposition (inl 0, inr 0) of ℕ ⊔ ℕ. `}
def weyl_cx_shift : Sum Nat Nat → Sum Nat Nat ≔ [
  | inl. n ↦ inl. (suc. n)
  | inr. zero. ↦ inl. zero.
  | inr. (suc. m) ↦ inr. m ]

def weyl_cx_shift_inv : Sum Nat Nat → Sum Nat Nat ≔ [
  | inl. zero. ↦ inr. zero.
  | inl. (suc. n) ↦ inl. n
  | inr. m ↦ inr. (suc. m) ]

def weyl_cx_shift_retr (x : Sum Nat Nat) : Id (Sum Nat Nat) (weyl_cx_shift_inv (weyl_cx_shift x)) x
  ≔ match x [
  | inl. n ↦ refl (inl. n : Sum Nat Nat)
  | inr. zero. ↦ refl (inr. zero. : Sum Nat Nat)
  | inr. (suc. m) ↦ refl (inr. (suc. m) : Sum Nat Nat) ]

def weyl_cx_shift_sect (x : Sum Nat Nat) : Id (Sum Nat Nat) (weyl_cx_shift (weyl_cx_shift_inv x)) x
  ≔ match x [
  | inl. zero. ↦ refl (inl. zero. : Sum Nat Nat)
  | inl. (suc. n) ↦ refl (inl. (suc. n) : Sum Nat Nat)
  | inr. m ↦ refl (inr. m : Sum Nat Nat) ]

def weyl_cx_shift_equiv : Equiv (Sum Nat Nat) (Sum Nat Nat)
  ≔ quasi_inverse_equiv (Sum Nat Nat) (Sum Nat Nat) weyl_cx_shift weyl_cx_shift_inv weyl_cx_shift_retr weyl_cx_shift_sect

def weyl_cx_swap : Sum Nat Nat → Sum Nat Nat ≔ [
  | inl. zero. ↦ inr. zero.
  | inl. (suc. n) ↦ inl. (suc. n)
  | inr. zero. ↦ inl. zero.
  | inr. (suc. m) ↦ inr. (suc. m) ]

def weyl_cx_swap_involutive (x : Sum Nat Nat) : Id (Sum Nat Nat) (weyl_cx_swap (weyl_cx_swap x)) x
  ≔ match x [
  | inl. zero. ↦ refl (inl. zero. : Sum Nat Nat)
  | inl. (suc. n) ↦ refl (inl. (suc. n) : Sum Nat Nat)
  | inr. zero. ↦ refl (inr. zero. : Sum Nat Nat)
  | inr. (suc. m) ↦ refl (inr. (suc. m) : Sum Nat Nat) ]

def weyl_cx_swap_equiv : Equiv (Sum Nat Nat) (Sum Nat Nat)
  ≔ quasi_inverse_equiv (Sum Nat Nat) (Sum Nat Nat) weyl_cx_swap weyl_cx_swap weyl_cx_swap_involutive weyl_cx_swap_involutive

{` The G-set X. `}
def WeylCxExtension (Y : Type) (j : Nat → Y) : Type
  ≔ Σ (Equiv (Sum Nat Nat) Y) (e ↦ Id (Nat → Y) j (n ↦ e .map (inl. n)))

def WeylCxExtends (Y : Type) (j : Nat → Y) : Type ≔ Mere (WeylCxExtension Y j)

def weyl_cx_injections (Y : SetTypes) : SetTypes
  ≔ (Σ (Nat → Y .fst) (WeylCxExtends (Y .fst)),
     sigma_set (Nat → Y .fst) (WeylCxExtends (Y .fst)) (pi_set Nat (_ ↦ Y .fst) (_ ↦ Y .snd))
       (j ↦ prop_is_set (WeylCxExtends (Y .fst) j) (mere_isprop (WeylCxExtension (Y .fst) j))))

def weyl_cx_gset : GSet weyl_cx_group ≔ z ↦ weyl_cx_injections (z .fst)

def WeylCxPoints : Type ≔ gset_underlying weyl_cx_group weyl_cx_gset

def weyl_cx_points_path (u v : WeylCxPoints) (p : Id (Nat → Sum Nat Nat) (u .fst) (v .fst)) : Id WeylCxPoints u v
  ≔ subtype_equal (Nat → Sum Nat Nat) (WeylCxExtends (Sum Nat Nat))
      (j ↦ mere_isprop (WeylCxExtension (Sum Nat Nat) j)) u v p

{` The base point inl and its image under the transposition. `}
def weyl_cx_incl : WeylCxPoints
  ≔ ((n ↦ inl. n),
     mere (WeylCxExtension (Sum Nat Nat) (n ↦ inl. n))
       (identity_equiv (Sum Nat Nat), refl ((n ↦ inl. n) : Nat → Sum Nat Nat)))

def weyl_cx_swapped : WeylCxPoints
  ≔ ((n ↦ weyl_cx_swap (inl. n)),
     mere (WeylCxExtension (Sum Nat Nat) (n ↦ weyl_cx_swap (inl. n)))
       (weyl_cx_swap_equiv, refl ((n ↦ weyl_cx_swap (inl. n)) : Nat → Sum Nat Nat)))

def weyl_cx_left_code : Sum Nat Nat → Type ≔ [ inl. _ ↦ Unit | inr. _ ↦ Empty ]

def weyl_cx_incl_ne_swapped (p : Id WeylCxPoints weyl_cx_incl weyl_cx_swapped) : Empty
  ≔ transport (Sum Nat Nat) weyl_cx_left_code (inl. zero.) (inr. zero.)
      (refl ((u ↦ u .fst zero.) : WeylCxPoints → Sum Nat Nat) p) star.

{` X is transitive: y = (j, |e|) is moved to inl by the permutation e⁻¹. `}
def weyl_cx_transitive_at (y : WeylCxPoints) (w : WeylCxExtension (Sum Nat Nat) (y .fst))
  : Id WeylCxPoints weyl_cx_incl
      (gset_usym_act weyl_cx_group weyl_cx_gset
        (permutation_symmetry weyl_cx_set (canonical_inverse_equiv (Sum Nat Nat) (Sum Nat Nat) (w .fst))) y)
  ≔ let A ≔ Sum Nat Nat in
    let e ≔ w .fst in let ei ≔ equiv_inverse_map A A e in
    let g ≔ permutation_symmetry weyl_cx_set (canonical_inverse_equiv A A e) in
    let N ≔ refl ((_ ↦ Nat) : BG weyl_cx_group .carrier → Type) g in
    weyl_cx_points_path weyl_cx_incl (gset_usym_act weyl_cx_group weyl_cx_gset g y)
      (funext Nat (_ ↦ A) (n ↦ inl. n) (n ↦ ei (y .fst (N .trl n)))
        (n ↦ calc
          (inl. n : A) = ei (e .map (inl. n)) by equiv_unit A A e (inl. n)
          = ei (y .fst n) by refl ei (inverse A (y .fst n) (e .map (inl. n)) (w .snd (refl n)))
          = ei (y .fst (N .trl n))
            by refl ((k ↦ ei (y .fst k)) : Nat → A) (inverse Nat (N .trl n) n (N .liftl n)) ∎))

def weyl_cx_transitive : IsTransitive weyl_cx_group weyl_cx_gset
  ≔ let G ≔ weyl_cx_group in let X ≔ weyl_cx_gset in
    let R : WeylCxPoints → Type ≔ y ↦ Σ (USym G) (g ↦ Id WeylCxPoints weyl_cx_incl (gset_usym_act G X g y)) in
    mere (Σ WeylCxPoints (x ↦ (y : WeylCxPoints) → Mere (Σ (USym G) (g ↦ Id WeylCxPoints x (gset_usym_act G X g y)))))
      (weyl_cx_incl,
       y ↦ mere_rec (WeylCxExtension (Sum Nat Nat) (y .fst)) (Mere (R y)) (mere_isprop (R y))
         (w ↦ mere (R y)
           (permutation_symmetry weyl_cx_set (canonical_inverse_equiv (Sum Nat Nat) (Sum Nat Nat) (w .fst)),
            weyl_cx_transitive_at y w))
         (y .snd))

def weyl_cx_subgroup : Subgroups weyl_cx_group ≔ (weyl_cx_gset, weyl_cx_incl, weyl_cx_transitive)

{` The G-map "drop the first value", j ↦ j ∘ suc. `}
def weyl_cx_drop (Y : SetTypes) (u : weyl_cx_injections Y .fst) : weyl_cx_injections Y .fst
  ≔ let j' : Nat → Y .fst ≔ n ↦ u .fst (suc. n) in
    (j',
     mere_rec (WeylCxExtension (Y .fst) (u .fst)) (WeylCxExtends (Y .fst) j') (mere_isprop (WeylCxExtension (Y .fst) j'))
       (w ↦ mere (WeylCxExtension (Y .fst) j')
         (compose_equiv (Sum Nat Nat) (Sum Nat Nat) (Y .fst) weyl_cx_shift_equiv (w .fst),
          refl ((k ↦ (n ↦ k (suc. n))) : (Nat → Y .fst) → (Nat → Y .fst)) (w .snd)))
       (u .snd))

def weyl_cx_drop_hom : GSetHom weyl_cx_group weyl_cx_gset weyl_cx_gset ≔ z u ↦ weyl_cx_drop (z .fst) u

def weyl_cx_drop_identifies
  : Id WeylCxPoints (weyl_cx_drop weyl_cx_set weyl_cx_incl) (weyl_cx_drop weyl_cx_set weyl_cx_swapped)
  ≔ weyl_cx_points_path (weyl_cx_drop weyl_cx_set weyl_cx_incl) (weyl_cx_drop weyl_cx_set weyl_cx_swapped)
      (refl ((n ↦ inl. (suc. n)) : Nat → Sum Nat Nat))

{` The H-fixed point of G/H given by the G-map drop. `}
def weyl_cx_fixed_point
  : InvariantMaps (subgroup_group weyl_cx_group weyl_cx_subgroup)
      (gset_restrict (subgroup_group weyl_cx_group weyl_cx_subgroup) weyl_cx_group
        (subgroup_inclusion weyl_cx_group weyl_cx_subgroup) weyl_cx_gset)
  ≔ u ↦ weyl_cx_drop_hom (u .fst) (u .snd)

{` e is not surjective for this G and H: the fixed point drop is not in its image. `}
def weyl_fixed_map_not_surjective
  : Not (Surjective (Id (GSet weyl_cx_group) weyl_cx_gset weyl_cx_gset)
      (InvariantMaps (subgroup_group weyl_cx_group weyl_cx_subgroup)
        (gset_restrict (subgroup_group weyl_cx_group weyl_cx_subgroup) weyl_cx_group
          (subgroup_inclusion weyl_cx_group weyl_cx_subgroup) weyl_cx_gset))
      (weyl_fixed_map weyl_cx_group weyl_cx_subgroup))
  ≔ sur ↦
    let G ≔ weyl_cx_group in let S ≔ weyl_cx_subgroup in let X ≔ weyl_cx_gset in
    let H ≔ subgroup_group G S in
    let I ≔ InvariantMaps H (gset_restrict H G (subgroup_inclusion G S) X) in
    let s ≔ weyl_cx_fixed_point in
    let P ≔ WeylCxPoints in
    mere_rec (BookFiber (Id (GSet G) X X) I (weyl_fixed_map G S) s) Empty empty_prop
      (fb ↦
        let f ≔ fb .fst in
        let T ≔ gset_path_transport G X X f (shape G) in
        let q1 : Id P (s (shape G, weyl_cx_incl)) (T weyl_cx_incl) ≔ fb .snd (refl ((shape G, weyl_cx_incl) : ActionType G X)) in
        let q2 : Id P (s (shape G, weyl_cx_swapped)) (T weyl_cx_swapped)
          ≔ fb .snd (refl ((shape G, weyl_cx_swapped) : ActionType G X)) in
        weyl_cx_incl_ne_swapped
          (equivalence_injective P P (gset_path_equiv G X X .map f (shape G)) weyl_cx_incl weyl_cx_swapped
            (calc
              T weyl_cx_incl = s (shape G, weyl_cx_incl) by inverse P (s (shape G, weyl_cx_incl)) (T weyl_cx_incl) q1
              = s (shape G, weyl_cx_swapped) by weyl_cx_drop_identifies
              = T weyl_cx_swapped by q2 ∎)))
      (sur s)

{` lem:WGHisHfixofG/H as printed: for every G and H, ω ↦ e(ω) is an equivalence
   USym W_GH ≃ (G/H)^H. `}
def weyl_fixed_printed : Type
  ≔ (G : Group) (S : Subgroups G)
    → BookIsEquiv (USym (weyl_group G S))
        (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
        (ω ↦ weyl_fixed_map G S (ω .fst))

def weyl_fixed_printed_refuted : Not weyl_fixed_printed
  ≔ P ↦
    let G ≔ weyl_cx_group in let S ≔ weyl_cx_subgroup in
    let I ≔ InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)) in
    weyl_fixed_map_not_surjective
      (b ↦ let c ≔ P G S b .center in
        mere (BookFiber (Id (GSet G) (S .gset) (S .gset)) I (weyl_fixed_map G S) b) (c .fst .fst, c .snd))
