export "11-concrete-rings"
export "../../../src/1351-integer-concrete-ring"

{` Bridges for the example at fields.tex 1177, the ring structure (1_ℤ = id non-trivial; the blind
   existential statement about μ). The blind statement asks for some μ with the printed unit law and
   Ω(ev)(Ω(ptw_*(USym μ (loopʲ)))(loopᵏ)) = loop^{jk}; our integer_concrete_mu satisfies both: the expression is
   USym(ℓ_{loopʲ})(loopᵏ) with ℓ = hom_of_symmetry ∘ USym μ = integer_mixed_left (integer_concrete_left_spec), i.e.
   loopʲ · loopᵏ = loop^{jk} (integer_concrete_mul_powers). The footnote claims about s and e_z are in
   bridge-11c; the comparison of the book's explicit Bμ with this μ is in modules 1390-1392. `}

def b11b_ptw_agree (X Y : Pointed) (p : Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map p) (constant_loops_pointed_equiv X Y .map p)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) p)

def b11b_ev_compose (G : AbelianGroup) (k : BookPointedMap (BG (G .fst)) (Omega (BB (G .fst))))
  : BookPointedMap (BG (G .fst)) (BG (G .fst))
  ≔ book_pointed_compose (BG (G .fst)) (Omega (BB (G .fst))) (BG (G .fst)) k (bb_loops_evaluation_pointed (G .fst))

def b11b_mu (C : CircleSignature) : GroupHom (blind_Z C) (blind_grphom (blind_Z C) (circle_abelian_group C))
  ≔ integer_concrete_mu C

{` The printed unit law for (ℤ, id, μ), from the first law of integer_concrete_ring. `}
def b11b_unit_law (C : CircleSignature) : BlindConcRingUnitLaw C (blind_exa_Zring_data C (b11b_mu C))
  ≔ let Z ≔ circle_group C in let G ≔ circle_abelian_group C in let H ≔ abelian_hom_group Z G in
    let s ≔ usym_hom Z H (group_hom_compose Z Z H (group_hom_id Z) (integer_concrete_mu C)) (C .loop) in
    let P ≔ BookPointedMap (BG Z) (BG Z) in
    concat P (blind_concring_unit_map C (blind_exa_Zring_data C (b11b_mu C)) (C .loop))
      (hom_B Z Z (hom_of_symmetry Z G s)) (book_pointed_identity (BG Z))
      (refl (b11b_ev_compose G) (b11b_ptw_agree (BG Z) (BB Z) (s .fst)))
      (refl (hom_B Z Z) (integer_concrete_ring C .props .fst .fst))

{` The blind computation for our μ. `}
def b11b_mu_powers (C : CircleSignature) (j k : Int)
  : Id (USym (circle_group C))
      (loops_map (Omega (BB (circle_group C))) (BG (circle_group C)) (bb_loops_evaluation_pointed (circle_group C))
        (loops_map (BG (circle_group C)) (Omega (BB (circle_group C)))
          (blind_ptw_loops (BG (circle_group C)) (BB (circle_group C)) .map
            (usym_hom (circle_group C) (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_concrete_mu C)
              (loop_power (C .carrier) (C .base) (C .loop) j) .fst))
          (loop_power (C .carrier) (C .base) (C .loop) k)))
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul j k))
  ≔ let Z ≔ circle_group C in let G ≔ circle_abelian_group C in let H ≔ abelian_hom_group Z G in
    let lj ≔ loop_power (C .carrier) (C .base) (C .loop) j in
    let lk ≔ loop_power (C .carrier) (C .base) (C .loop) k in
    let p ≔ usym_hom Z H (integer_concrete_mu C) lj in
    let K ≔ blind_ptw_loops (BG Z) (BB Z) .map (p .fst) in
    let K' ≔ constant_loops_pointed_equiv (BG Z) (BB Z) .map (p .fst) in
    let ev ≔ bb_loops_evaluation_pointed Z in
    let U ≔ USym Z in
    calc
      loops_map (Omega (BB Z)) (BG Z) ev (loops_map (BG Z) (Omega (BB Z)) K lk)
      = loops_map (BG Z) (BG Z) (b11b_ev_compose G K) lk
        by inverse U (loops_map (BG Z) (BG Z) (b11b_ev_compose G K) lk)
          (loops_map (Omega (BB Z)) (BG Z) ev (loops_map (BG Z) (Omega (BB Z)) K lk))
          (loops_map_compose_pointwise (BG Z) (Omega (BB Z)) (BG Z) K ev lk)
      = usym_hom Z Z (hom_of_symmetry Z G p) lk
        by map_path (BookPointedMap (BG Z) (Omega (BB Z))) U (k ↦ loops_map (BG Z) (BG Z) (b11b_ev_compose G k) lk) K K'
          (b11b_ptw_agree (BG Z) (BB Z) (p .fst))
      = usym_hom Z Z (integer_mixed_left C lj) lk
        by map_path (GroupHom Z Z) U (f ↦ usym_hom Z Z f lk) (hom_of_symmetry Z G p) (integer_mixed_left C lj)
          (inverse (GroupHom Z Z) (integer_mixed_left C lj) (hom_of_symmetry Z G p) (integer_concrete_left_spec C lj))
      = loop_power (C .carrier) (C .base) (C .loop) (int_mul j k) by integer_concrete_mul_powers C j k ∎

def bridge_exa_Zring_mu : blind_exa_Zring_mu ≔ C ↦ (b11b_mu C, (b11b_unit_law C, b11b_mu_powers C))

def bridge_exa_Zring_one_nontrivial : blind_exa_Zring_one_nontrivial ≔ C ↦ integer_concrete_ring_non_trivial C

def bridge_def_Zring_data (C : CircleSignature)
  : Id (BlindConcRingData C) (blind_exa_Zring_data C (b11b_mu C))
      (integer_concrete_ring C .group, integer_concrete_ring C .one, integer_concrete_ring C .mu)
  ≔ refl (blind_exa_Zring_data C (b11b_mu C))
