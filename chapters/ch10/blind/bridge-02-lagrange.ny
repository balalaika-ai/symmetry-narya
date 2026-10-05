export "02-lagrange"
export "bridge-01-finite-groups"
export "../../../src/1021-lagrange-counting"
export "../../../src/1024-subgroup-finiteness-lem"
export "../../../src/1027-cyclic-groups-simple"
export "../../../src/1028-coprime-subgroup-kernel"
export "../../../src/938-mono-cover-kernels"
export "../../../src/824-integer-intersection"

{` Bridges for fingp.tex, sec:Lagrangecounting: lem:Lagrangeascounting,
   cor:cyclicgroupsaresimple, cor:whatSylow2needs.

   The blind G/H is the underlying set of coker(i) = ‖Bi⁻¹(sh_G)‖₀; for a
   monomorphism Bi⁻¹(sh_G) (our mono_gset) is already a set, so the two agree
   up to set_trunc_of_set_equiv. The blind lem:Lagrangeascounting (1) claims
   finiteness of H for every subgroup of a finite group; this is equivalent to
   excluded middle (both directions below, via module 1024), so it is bridged
   only under the hypothesis "H finite" (our lemma) or under LEM. `}

{` The blind cosets are the set truncation of our G/H = Bi⁻¹(sh_G). `}
def bridge_def_cosets (G : Group) (m : GroupMonos G)
  : Equiv (BlindCosets G m) (gset_underlying G (mono_gset G m))
  ≔ set_trunc_of_set_equiv (gset_underlying G (mono_gset G m)) (mono_gset G m (shape G) .snd)

def bridge_mono_subgroup_finite (G : Group) (m : GroupMonos G) (hH : IsFiniteGroup (m .fst))
  : IsFiniteGroup (subgroup_group G (mono_to_subgroup G m))
  ≔ group_finite_path (m .fst) (subgroup_group G (mono_to_subgroup G m))
      (inverse Group (subgroup_group G (mono_to_subgroup G m)) (m .fst) (mono_subgroup_group_path G m)) hH

{` lem:Lagrangeascounting (1) for a subgroup H that is finite. `}
def bridge_lagrangeascounting_finite (G : Group) (hG : IsFiniteGroup G) (m : GroupMonos G) (hH : IsFiniteGroup (m .fst))
  : Σ (IsFinite (BlindCosets G m)) (hQ ↦ Σ (BlindIsFiniteGroup (m .fst)) (hH' ↦
      Id Nat (blind_group_order G hG) (mul (cardinality (BlindCosets G m) hQ) (blind_group_order (m .fst) hH'))))
  ≔ let X ≔ gset_underlying G (mono_gset G m) in
    let Q ≔ BlindCosets G m in
    let e ≔ bridge_def_cosets G m in
    let hX : IsFinite X ≔ subgroup_gset_finite G hG (mono_to_subgroup G m) (bridge_mono_subgroup_finite G m hH) in
    let hQ : IsFinite Q ≔ finite_of_equiv Q X e hX in
    (hQ, (hH,
      concat Nat (group_card G hG) (mul (cardinality X hX) (group_card (m .fst) hH))
        (mul (cardinality Q hQ) (group_card (m .fst) hH))
        (lagrange_counting_mono G hG m hH)
        (refl ((x ↦ mul x (group_card (m .fst) hH)) : Nat → Nat)
          (inverse Nat (cardinality Q hQ) (cardinality X hX) (cardinality_equiv Q X e hQ hX)))))

{` The literal blind statement holds under excluded middle ... `}
def bridge_lagrangeascounting_of_lem (lem : ExcludedMiddle) : blind_lagrangeascounting
  ≔ G hG m ↦ bridge_lagrangeascounting_finite G hG m
      (group_finite_path (subgroup_group G (mono_to_subgroup G m)) (m .fst) (mono_subgroup_group_path G m)
        (excluded_middle_subgroups_finite lem G hG (mono_to_subgroup G m)))

{` ... and implies it (it makes every subgroup of a finite group finite). `}
def bridge_lagrangeascounting_lem (b : blind_lagrangeascounting) : ExcludedMiddle
  ≔ subgroups_finite_excluded_middle (G hG S ↦ b G hG (subgroup_to_mono G S) .snd .fst)

{` The blind full subgroup (image of id_G) is ours (G-set with contractible
   underlying set). `}
def bridge_set_trunc_contr (A : Type) (c : BookIsContr A) : BookIsContr (SetTrunc A)
  ≔ equiv_inverse_map (BookIsContr (SetTrunc A)) (BookIsContr A)
      (book_contractibility_equiv (SetTrunc A) A
        (set_trunc_of_set_equiv A (prop_is_set A (contractible_prop A (native_contraction A c))))) c

def bridge_def_full_subgroup (G : Group) : Id (Subgroups G) (blind_full_subgroup G) (group_full_subgroup G)
  ≔ subgroup_full_of_contractible G (blind_full_subgroup G)
      (bridge_set_trunc_contr (Σ (BG G .carrier) (a ↦ Id (BG G .carrier) (shape G) a))
        (book_pathspace_contractible (BG G .carrier) (shape G)))

{` lem:Lagrangeascounting (2). `}
def bridge_lagrangeascounting_full : blind_lagrangeascounting_full
  ≔ G hG m hH e ↦
    let S ≔ mono_to_subgroup G m in
    let hS ≔ bridge_mono_subgroup_finite G m hH in
    concat (Subgroups G) S (group_full_subgroup G) (blind_full_subgroup G)
      (lagrange_counting_equal_order G hG S hS
        (concat Nat (group_card (subgroup_group G S) hS) (group_card (m .fst) hH) (group_card G hG)
          (group_card_path (subgroup_group G S) (m .fst) (mono_subgroup_group_path G m) hS hH) e))
      (inverse (Subgroups G) (blind_full_subgroup G) (group_full_subgroup G) (bridge_def_full_subgroup G))

{` cor:cyclicgroupsaresimple: a prime is a successor. `}
def bridge_cyclicgroupsaresimple : blind_cyclicgroupsaresimple
  ≔ p hp ↦ match p [
  | zero. ↦ match hp .fst []
  | suc. b ↦ np ↦ cyclic_prime_no_nontrivial_proper b hp (np .fst) (np .snd) ]

{` cor:whatSylow2needs. Our element-wise lemma (f∘i sends every symmetry of
   H to e) makes f∘i the trivial homomorphism, and the universal property of
   the kernel (chapter 9, module 938) factors i through ker f. Surjectivity
   of f is not needed for the factorization. `}
def bridge_usym_hom_trivial (L H : Group) (l : USym L)
  : Id (USym H) (usym_hom L H (EqmcTrivialHom L H) l) (usym_unit H)
  ≔ let B ≔ BG H .carrier in let s ≔ shape H in
    calc
      concat B s s s (refl s) (concat B s s s (refl s) (inverse B s s (refl s)))
      = concat B s s s (refl s) (inverse B s s (refl s)) by concat_1p B s s (concat B s s s (refl s) (inverse B s s (refl s)))
      = inverse B s s (refl s) by concat_1p B s s (inverse B s s (refl s))
      = refl s by inverse_refl B s ∎

def bridge_whatsylow2needs : blind_whatsylow2needs
  ≔ G G' f surj m hH hG' cop ↦
    let H ≔ m .fst in
    let i ≔ m .snd .fst in
    let fi ≔ group_hom_compose H G G' i f in
    let r : Id (GroupHom H G') fi (EqmcTrivialHom H G')
      ≔ pbg_hom_ext_usym H G' fi (EqmcTrivialHom H G') (h ↦
          concat (USym G') (usym_hom H G' fi h) (usym_unit G') (usym_hom H G' (EqmcTrivialHom H G') h)
            (coprime_hom_trivial H G' hH hG' cop fi h)
            (inverse (USym G') (usym_hom H G' (EqmcTrivialHom H G') h) (usym_unit G') (bridge_usym_hom_trivial H G' h))) in
    let k ≔ eqmc_kernel_lift G G' f H i r in
    (k .fst, inverse (GroupHom H G) i (group_hom_compose H (kernel_group G G' f) G (k .fst) (kernel_inclusion G G' f)) (k .snd))
