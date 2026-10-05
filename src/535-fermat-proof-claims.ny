export "533-fermat-fixed-sets"

{` Chapter 5, the remaining claims of the proof of Fermat's Little Theorem
   (p = m+1 prime, X(S, t) = (S → Fin n)):
   - "(C_p)_f can only be trivial or all of C_p": Card((C_p)_f) is 1 or p;
     "all of C_p" (every symmetry fixes f) happens exactly for the
     constant functions;
   - "Otherwise select k with f(k) ≠ f(0), and surely s^k · f ≠ f": for
     the symmetry g with g_*(0) = k (the book's s^k, cor:id-m-cycle);
     a non-constant f has such a k (footnote: the set is finite, hence
     decidable);
   - footnote: such a symmetry is not in the image of USym(i_f). `}

{` Card((C_p)_f) divides p, so it is 1 or p. `}
def fermat_stabilizer_dichotomy (m n : Nat) (hp : NatIsPrime (suc. m)) (f : Fin (suc. m) → Fin n)
  : Sum (Id Nat (group_card (subgroup_group (fermat_group m) (fermat_orbit_subgroup m n f))
            (lagrange_subgroup_finite (fermat_group m) (fermat_orbit_subgroup m n f) (fermat_group_finite m)
              (fermat_orbit_finite m n f))) (suc. zero.))
        (Id Nat (group_card (subgroup_group (fermat_group m) (fermat_orbit_subgroup m n f))
            (lagrange_subgroup_finite (fermat_group m) (fermat_orbit_subgroup m n f) (fermat_group_finite m)
              (fermat_orbit_finite m n f))) (suc. m))
  ≔ let G ≔ fermat_group m in
    let S ≔ fermat_orbit_subgroup m n f in
    let a ≔ gset_card G (S .gset) (fermat_orbit_finite m n f) in
    let b ≔ group_card (subgroup_group G S)
              (lagrange_subgroup_finite G S (fermat_group_finite m) (fermat_orbit_finite m n f)) in
    hp .snd b (nat_divides_intro b (suc. m) a (fermat_lagrange m n f))

{` "All of C_p" (every symmetry fixes f) iff f is one of the constant functions. `}
def fermat_constant_iff_fixed_by_all (m n : Nat) (f : Fin (suc. m) → Fin n)
  : Product (FermatConstant m n f →
             (g : USym (fermat_group m)) → Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f)
      (((g : USym (fermat_group m)) → Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f)
       → FermatConstant m n f)
  ≔ (c g ↦ fermat_constant_fixed_by m n f c g, fermat_fixed_by_all_constant m n f)

{` The symmetry s^k: the g with g_*(0) = k. `}
def fermat_power_symmetry (m : Nat) (k : Fin (suc. m)) : USym (fermat_group m)
  ≔ equiv_inverse_map (USym (fermat_group m)) (Fin (suc. m)) (cyclic_group_fin_usym_equiv m) k

{` If f(k) ≠ f(0), then s^k · f ≠ f. `}
def fermat_power_symmetry_moves (m n : Nat) (f : Fin (suc. m) → Fin n) (k : Fin (suc. m))
  (ne : Not (Id (Fin n) (f k) (f (inr. star.))))
  : Not (Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) (fermat_power_symmetry m k) f) f)
  ≔ q ↦
    let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let g ≔ fermat_power_symmetry m k in
    let r : Id (Fin (suc. m)) (fermat_rotation m g (inr. star.)) k
      ≔ equiv_counit (USym G) (Fin (suc. m)) (cyclic_group_fin_usym_equiv m) k in
    ne (calc
      f k
      = f (fermat_rotation m g (inr. star.)) by refl f (inverse (Fin (suc. m)) (fermat_rotation m g (inr. star.)) k r)
      = gset_usym_act G X g f (fermat_rotation m g (inr. star.))
        by refl ((φ ↦ φ (fermat_rotation m g (inr. star.))) : (Fin (suc. m) → Fin n) → Fin n)
          (inverse (Fin (suc. m) → Fin n) (gset_usym_act G X g f) f q)
      = f (inr. star.) by fermat_action_rotation m n g f (inr. star.) ∎)

{` Footnote "The set Fin p → Fin n is finite, hence decidable": a
   non-constant f merely has a k with f(k) ≠ f(0). `}
def fermat_nonconstant_witness (m n : Nat) (f : Fin (suc. m) → Fin n) (nc : Not (FermatConstant m n f))
  : Mere (Σ (Fin (suc. m)) (k ↦ Not (Id (Fin n) (f k) (f (inr. star.)))))
  ≔ let P ≔ (k ↦ Not (Id (Fin n) (f k) (f (inr. star.)))) : Fin (suc. m) → Type in
    let dec ≔ (k ↦ fin_decidable_equality n (f k) (f (inr. star.))) : (k : Fin (suc. m)) → Decidable (Id (Fin n) (f k) (f (inr. star.))) in
    match finite_quantifiers (Fin (suc. m)) (fin_is_finite (suc. m)) P
        (k ↦ pi_prop (Id (Fin n) (f k) (f (inr. star.))) (_ ↦ Empty) (_ ↦ empty_prop))
        (k ↦ match dec k [ inl. e ↦ inr. (h ↦ h e) | inr. ne ↦ inl. ne ]) .snd [
    | inl. w ↦ w
    | inr. nw ↦ absurd (Mere (Σ (Fin (suc. m)) P))
        (nc (k ↦ match dec k [
          | inl. e ↦ e
          | inr. ne ↦ absurd (Id (Fin n) (f k) (f (inr. star.))) (nw (mere (Σ (Fin (suc. m)) P) (k, ne))) ])) ]

{` Symmetries in the image of USym(i_x) fix x: Ω(Bi_x)(s) is s.1.1 (the
   pointing of Bi_x is refl, loops_map_refl_pointing), which fixes x by
   the second component of s.1 (rem:path-in-action-type). `}
def stabilizer_image_fixes (G : Group) (X : GSet G) (x : gset_underlying G X) (s : USym (stabilizer_group G X x))
  : Id (gset_underlying G X)
      (gset_usym_act G X (usym_hom (stabilizer_group G X x) G (stabilizer_inclusion G X x) s) x) x
  ≔ let T ≔ ActionType G X in
    let B ≔ BG G .carrier in
    let F ≔ (z ↦ X z .fst) : B → Type in
    let c ≔ component_point T (shape G, x) in
    let hp : Id (USym G) (usym_hom (stabilizer_group G X x) G (stabilizer_inclusion G X x) s) (s .fst .fst)
      ≔ loops_map_refl_pointing (NativeComponent T (shape G, x)) B (u ↦ u .fst .fst) c (refl s) in
    transport (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)
      (s .fst .fst) (usym_hom (stabilizer_group G X x) G (stabilizer_inclusion G X x) s)
      (inverse (USym G) (usym_hom (stabilizer_group G X x) G (stabilizer_inclusion G X x) s) (s .fst .fst) hp)
      (pathover_transport_equiv B F (shape G) (shape G) (s .fst .fst) x x .map (s .fst .snd))

{` Footnote: s^k (with f(k) ≠ f(0)) is not in the image of USym(i_f), where
   i_f : (C_p)_f → C_p is the stabilizer inclusion. `}
def fermat_power_symmetry_not_in_stabilizer (m n : Nat) (f : Fin (suc. m) → Fin n) (k : Fin (suc. m))
  (ne : Not (Id (Fin n) (f k) (f (inr. star.))))
  : Not (Σ (USym (stabilizer_group (fermat_group m) (fermat_gset m n) f))
          (s ↦ Id (USym (fermat_group m))
            (usym_hom (stabilizer_group (fermat_group m) (fermat_gset m n) f) (fermat_group m)
              (stabilizer_inclusion (fermat_group m) (fermat_gset m n) f) s)
            (fermat_power_symmetry m k)))
  ≔ t ↦
    let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let Gf ≔ stabilizer_group G X f in
    fermat_power_symmetry_moves m n f k ne
      (transport (USym G) (g ↦ Id (Fin (suc. m) → Fin n) (gset_usym_act G X g f) f)
        (usym_hom Gf G (stabilizer_inclusion G X f) (t .fst)) (fermat_power_symmetry m k) (t .snd)
        (stabilizer_image_fixes G X f (t .fst)))
