{` Blind statements for chapter 9 (subgroups.tex): exa:fibersofcomposites, xca:fibersofcomposites and the
   linear-algebra example after xca at subgroups.tex:1160. `}
export "02-kernels"
export "../../../src/418-cyclic-group-images"
export "../../../src/457-sign-permutations"

def blind_four : Nat ≔ suc. three
def blind_six : Nat ≔ suc. (suc. blind_four)

{` The groups of the examples: C_4 = Aut_Cyc(4, s), Σ_4, Σ_2. `}
def BlindC4 : Group ≔ cyclic_group_fin three
def BlindS4 : Group ≔ symmetric_group blind_four
def BlindS2 : Group ≔ sign_sigma_two

{` s : the generating symmetry of (4, s) in BC_4 (the cyclic successor of Fin 4). `}
def blind_c4_gen : USym BlindC4 ≔ cyclic_fin_generator three

{` f1 ≔ B mod_4 : BZ →* BC_4, f2 ≔ Bsgn ∘ prj : BC_4 →* BΣ_2 and the composite. `}
def blind_mod4 (C : CircleSignature) : GroupHom (circle_group C) BlindC4 ≔ mod_hom C three

def blind_sgnprj : GroupHom BlindC4 BlindS2
  ≔ group_hom_compose BlindC4 BlindS4 BlindS2 (cyclic_forget_hom three) (sign_hom blind_four)

def blind_comp4 (C : CircleSignature) : GroupHom (circle_group C) BlindS2
  ≔ blind_f21 (circle_group C) BlindC4 BlindS2 (blind_mod4 C) blind_sgnprj

{` The G-set z ↦ (sh_{G'} = Bf(z)) associated with f; g lies in the stabilizer group of its point Bf_pt
   iff g · Bf_pt = Bf_pt. `}
def BlindFixesPoint (G G' : Group) (f : GroupHom G G') (g : USym G) : Type
  ≔ Id (gset_underlying G (gset_restrict G G' f (principal_gset G')))
      (gset_usym_act G (gset_restrict G G' f (principal_gset G')) g (hom_point G G' f))
      (hom_point G G' f)

{` g is loop^{n k} for some integer k. `}
def BlindLoopMultiple (C : CircleSignature) (n : Int) (g : USym (circle_group C)) : Type
  ≔ Mere (Σ Int (k ↦ Id (USym (circle_group C)) g (circle_power C (int_mul n k))))

{` exa:fibersofcomposites, first paragraph: for sets X0, X1, X2 all fibers are subsets (the first projections
   are injections). `}
def blind_exa_foc_sets : Type
  ≔ (D : BlindTwoPtdMaps) → isSet (D .X0) → isSet (D .X1) → isSet (D .X2)
    → Product (IsEmbedding (BlindFib01 D) (D .X0) (u ↦ u .fst))
        (Product (IsEmbedding (BlindFib12 D) (D .X1) (u ↦ u .fst))
                 (IsEmbedding (BlindFib02 D) (D .X0) (u ↦ u .fst)))

{` exa:fibersofcomposites: s on Fin 4 is the odd cyclic permutation (0 1 2 3). `}
def blind_exa_foc_generator_odd : Type
  ≔ Id Sign (permutation_sign_at blind_four (standard_shape blind_four) (finite_fin_successor three)) minus.

{` exa:fibersofcomposites: the three fibers f1^{-1}(x1), f2^{-1}(x2), (f2 f1)^{-1}(x2) are connected. `}
def blind_exa_foc_fibers_connected : Type
  ≔ (C : CircleSignature)
    → Product (Connected (BlindHomFiber (circle_group C) BlindC4 (blind_mod4 C) (shape BlindC4)))
        (Product (Connected (BlindHomFiber BlindC4 BlindS2 blind_sgnprj (shape BlindS2)))
                 (Connected (BlindHomFiber (circle_group C) BlindS2 (blind_comp4 C) (shape BlindS2))))

{` exa:fibersofcomposites: the stabilizer of refl_{(4,s)} in the Z-set of B mod_4 picks out loop^{4k}. `}
def blind_exa_foc_mod4_stabilizer : Type
  ≔ (C : CircleSignature) (g : USym (circle_group C))
    → BlindIff (BlindFixesPoint (circle_group C) BlindC4 (blind_mod4 C) g) (BlindLoopMultiple C (pos. blind_four) g)

{` exa:fibersofcomposites: for the C_4-set of Bsgn prj one gets the symmetries s^k with k = 0, 2. `}
def blind_exa_foc_sgnprj_stabilizer : Type
  ≔ (h : USym BlindC4)
    → BlindIff (BlindFixesPoint BlindC4 BlindS2 blind_sgnprj h)
        (Sum (Id (USym BlindC4) h (usym_unit BlindC4)) (Id (USym BlindC4) h (usym_mul BlindC4 blind_c4_gen blind_c4_gen)))

{` exa:fibersofcomposites: for the composite one gets loop^{2k}. `}
def blind_exa_foc_composite_stabilizer : Type
  ≔ (C : CircleSignature) (g : USym (circle_group C))
    → BlindIff (BlindFixesPoint (circle_group C) BlindS2 (blind_comp4 C) g) (BlindLoopMultiple C (pos. two) g)

{` exa:fibersofcomposites: F1 : Ker(f2 f1) → Ker(f2) sends the symmetry over loop^{2k} to the one over s^{2k}. `}
def blind_exa_foc_F1_symmetries : Type
  ≔ (C : CircleSignature)
    → let K21 ≔ BlindKer (circle_group C) BlindS2 (blind_comp4 C) in
      let K2 ≔ BlindKer BlindC4 BlindS2 blind_sgnprj in
      (g : USym K21) (k : Int)
      → Id (USym (circle_group C)) (usym_hom K21 (circle_group C) (blind_kermap (circle_group C) BlindS2 (blind_comp4 C)) g)
           (circle_power C (int_mul (pos. two) k))
      → Id (USym BlindC4)
           (usym_hom K2 BlindC4 (blind_kermap BlindC4 BlindS2 blind_sgnprj)
             (usym_hom K21 K2 (blind_cor_F1 (circle_group C) BlindC4 BlindS2 (blind_mod4 C) blind_sgnprj) g))
           (loop_power (BG BlindC4 .carrier) (shape BlindC4) blind_c4_gen (int_mul (pos. two) k))

{` xca:fibersofcomposites: the case R_4 : BZ →* BΣ_4 followed by Bsgn : BΣ_4 →* BΣ_2. `}
def blind_R4 (C : CircleSignature) : GroupHom (circle_group C) BlindS4 ≔ power_finset_hom C three
def blind_sgn4 : GroupHom BlindS4 BlindS2 ≔ sign_hom blind_four
def blind_compR4 (C : CircleSignature) : GroupHom (circle_group C) BlindS2
  ≔ blind_f21 (circle_group C) BlindS4 BlindS2 (blind_R4 C) blind_sgn4

{` The stabilizer for R_4 picks out loop^{4k}. `}
def blind_xca_foc_R4_stabilizer : Type
  ≔ (C : CircleSignature) (g : USym (circle_group C))
    → BlindIff (BlindFixesPoint (circle_group C) BlindS4 (blind_R4 C) g) (BlindLoopMultiple C (pos. blind_four) g)

{` The stabilizer for Bsgn consists of the even permutations of 4. `}
def blind_xca_foc_sgn_stabilizer : Type
  ≔ (h : USym BlindS4)
    → BlindIff (BlindFixesPoint BlindS4 BlindS2 blind_sgn4 h)
        (Id Sign (permutation_sign_at blind_four (standard_shape blind_four) (symmetric_group_usym_equiv blind_four .map h)) plus.)

{` The stabilizer for the composite picks out loop^{2k}. `}
def blind_xca_foc_composite_stabilizer : Type
  ≔ (C : CircleSignature) (g : USym (circle_group C))
    → BlindIff (BlindFixesPoint (circle_group C) BlindS2 (blind_compR4 C) g) (BlindLoopMultiple C (pos. two) g)

{` Unlike the example, the fiber of R_4 is not connected: coker(R_4)(sh) has 6 = 24/4 elements; the fibers of Bsgn
   and of the composite are connected. `}
def blind_xca_foc_R4_coker : Type
  ≔ (C : CircleSignature) → BookEquiv (gset_underlying BlindS4 (blind_coker (circle_group C) BlindS4 (blind_R4 C))) (Fin blind_six)

def blind_xca_foc_R4_fiber_not_connected : Type
  ≔ (C : CircleSignature) → Not (Connected (BlindHomFiber (circle_group C) BlindS4 (blind_R4 C) (shape BlindS4)))

def blind_xca_foc_other_fibers_connected : Type
  ≔ (C : CircleSignature)
    → Product (Connected (BlindHomFiber BlindS4 BlindS2 blind_sgn4 (shape BlindS2)))
        (Connected (BlindHomFiber (circle_group C) BlindS2 (blind_compR4 C) (shape BlindS2)))

{` F1 : Ker(sgn R_4) → Ker(sgn) sends the symmetry over loop^{2k} to the one over s^{2k}, s the 4-cycle. `}
def blind_xca_foc_F1_symmetries : Type
  ≔ (C : CircleSignature)
    → let K21 ≔ BlindKer (circle_group C) BlindS2 (blind_compR4 C) in
      let K2 ≔ BlindKer BlindS4 BlindS2 blind_sgn4 in
      (g : USym K21) (k : Int)
      → Id (USym (circle_group C)) (usym_hom K21 (circle_group C) (blind_kermap (circle_group C) BlindS2 (blind_compR4 C)) g)
           (circle_power C (int_mul (pos. two) k))
      → Id (USym BlindS4)
           (usym_hom K2 BlindS4 (blind_kermap BlindS4 BlindS2 blind_sgn4)
             (usym_hom K21 K2 (blind_cor_F1 (circle_group C) BlindS4 BlindS2 (blind_R4 C) blind_sgn4) g))
           (loop_power (BG BlindS4 .carrier) (shape BlindS4) (finite_successor_symmetry three) (int_mul (pos. two) k))

{` Linear-algebra example (subgroups.tex:1186), restricted to 1×1 matrices (m) with m ≥ 0: the homomorphism
   Z → Z classified by deg_m (pointed by its computation rule). Nonzero determinant ⇔ monomorphism, and the
   cokernel has |det| = m elements. `}
def blind_deg_hom (C : CircleSignature) (m : Nat) : GroupHom (circle_group C) (circle_group C)
  ≔ mkhom (circle_group C) (circle_group C)
      (circle_degree_map C m,
       inverse (C .carrier) (circle_degree_map C m (C .base)) (C .base) (circle_degree_boundary C m .fst))

def blind_linalg_mono_iff_nonzero : Type
  ≔ (C : CircleSignature) (m : Nat)
    → BlindIff (BlindIsMono (circle_group C) (circle_group C) (blind_deg_hom C m)) (Not (Id Nat m zero.))

def blind_linalg_coker_card : Type
  ≔ (C : CircleSignature) (n : Nat)
    → BookEquiv (gset_underlying (circle_group C) (blind_coker (circle_group C) (circle_group C) (blind_deg_hom C (suc. n))))
        (Fin (suc. n))
