export "11-concrete-rings"
export "../../../src/1350-concrete-rings"

{` Bridges for sec:concrings, def:ring (1143) and xca:Rconcring->URabstring (1222). The blind ptw_* is the
   162 form (pointed_map_path_equiv), ours the explicit form; they agree by pointed_map_path_equiv_ptw (as in
   bridge-10, repeated here to keep the imports small). `}

def b11a_ptw_agree (X Y : Pointed) (p : Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map p) (constant_loops_pointed_equiv X Y .map p)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) p)

{` The one costly definitional comparison, made once for an arbitrary abelian group: the blind composite
   (ev ∘ ptw_* of module 162) is the classifying map of hom_of_symmetry. `}
def b11a_classifying (G : AbelianGroup) (p : USym (abelian_hom_group (G .fst) G))
  : Id (BookPointedMap (BG (G .fst)) (BG (G .fst)))
      (book_pointed_compose (BG (G .fst)) (Omega (BB (G .fst))) (BG (G .fst))
        (blind_ptw_loops (BG (G .fst)) (BB (G .fst)) .map (p .fst)) (bb_loops_evaluation_pointed (G .fst)))
      (hom_B (G .fst) (G .fst) (hom_of_symmetry (G .fst) G p))
  ≔ refl ((k ↦ book_pointed_compose (BG (G .fst)) (Omega (BB (G .fst))) (BG (G .fst)) k (bb_loops_evaluation_pointed (G .fst)))
          : BookPointedMap (BG (G .fst)) (Omega (BB (G .fst))) → BookPointedMap (BG (G .fst)) (BG (G .fst)))
      (b11a_ptw_agree (BG (G .fst)) (BB (G .fst)) (p .fst))

{` The blind product g · h is USym(ev ∘ USym μ (g))(h) (module 1350's a · b with ℓ = hom_of_symmetry ∘ USym μ). `}
def b11a_mul_value (C : CircleSignature) (D : BlindConcRingData C) (g h : USym (D .grp .fst))
  : Id (USym (D .grp .fst)) (blind_concring_mul C D g h)
      (usym_hom (D .grp .fst) (D .grp .fst)
        (hom_of_symmetry (D .grp .fst) (D .grp) (usym_hom (D .grp .fst) (abelian_hom_group (D .grp .fst) (D .grp)) (D .mu) g)) h)
  ≔ let R ≔ D .grp .fst in
    map_path (BookPointedMap (BG R) (BG R)) (USym R) (k ↦ loops_map (BG R) (BG R) k h)
      (book_pointed_compose (BG R) (Omega (BB R)) (BG R)
        (blind_ptw_loops (BG R) (BB R) .map (usym_hom R (abelian_hom_group R (D .grp)) (D .mu) g .fst)) (bb_loops_evaluation_pointed R))
      (hom_B R R (hom_of_symmetry R (D .grp) (usym_hom R (abelian_hom_group R (D .grp)) (D .mu) g)))
      (b11a_classifying (D .grp) (usym_hom R (abelian_hom_group R (D .grp)) (D .mu) g))

{` def:ring (1143). Our ConcreteRing carries the blind data (group, 1_R, μ) plus the completed laws. The blind
   unit-law map (ptw_* of module 162 followed by ev ∘ -) is the classifying map of our hom_of_symmetry by
   b10_ptw_agree, so the blind printed unit law is equivalent to our first law. `}
def b11_data (C : CircleSignature) (R : ConcreteRing C) : BlindConcRingData C ≔ (R .group, R .one, R .mu)

def b11_unit_symmetry (C : CircleSignature) (D : BlindConcRingData C) (g : USym (circle_group C))
  : USym (abelian_hom_group (D .grp .fst) (D .grp))
  ≔ usym_hom (circle_group C) (abelian_hom_group (D .grp .fst) (D .grp))
      (group_hom_compose (circle_group C) (D .grp .fst) (abelian_hom_group (D .grp .fst) (D .grp)) (D .one) (D .mu)) g

def b11_ev_compose (G : AbelianGroup) (k : BookPointedMap (BG (G .fst)) (Omega (BB (G .fst))))
  : BookPointedMap (BG (G .fst)) (BG (G .fst))
  ≔ book_pointed_compose (BG (G .fst)) (Omega (BB (G .fst))) (BG (G .fst)) k (bb_loops_evaluation_pointed (G .fst))

{` The blind map is the classifying map of hom_of_symmetry (pointed maps). `}
def b11_unit_map_agree (C : CircleSignature) (D : BlindConcRingData C) (g : USym (circle_group C))
  : Id (BookPointedMap (BG (D .grp .fst)) (BG (D .grp .fst))) (blind_concring_unit_map C D g)
      (hom_B (D .grp .fst) (D .grp .fst) (hom_of_symmetry (D .grp .fst) (D .grp) (b11_unit_symmetry C D g)))
  ≔ b11a_classifying (D .grp) (b11_unit_symmetry C D g)

{` Record η for homomorphisms, generically (so that no concrete homomorphism is unfolded). `}
def b11a_hom_eta (G H : Group) (f : GroupHom G H) : Id (GroupHom G H) (mkhom G H (hom_B G H f)) f ≔ refl f

def b11_unit_law_to (C : CircleSignature) (D : BlindConcRingData C) (h : BlindConcRingUnitLaw C D)
  : Id (GroupHom (D .grp .fst) (D .grp .fst)) (hom_of_symmetry (D .grp .fst) (D .grp) (b11_unit_symmetry C D (C .loop)))
      (group_hom_id (D .grp .fst))
  ≔ let R ≔ D .grp .fst in let P ≔ BookPointedMap (BG R) (BG R) in
    let f ≔ hom_of_symmetry R (D .grp) (b11_unit_symmetry C D (C .loop)) in
    concat (GroupHom R R) f (mkhom R R (hom_B R R f)) (group_hom_id R)
      (inverse (GroupHom R R) (mkhom R R (hom_B R R f)) f (b11a_hom_eta R R f))
      (refl (mkhom R R)
        (concat P (hom_B R R f) (blind_concring_unit_map C D (C .loop)) (book_pointed_identity (BG R))
          (inverse P (blind_concring_unit_map C D (C .loop)) (hom_B R R f) (b11_unit_map_agree C D (C .loop)))
          h))

def b11_unit_law_from (C : CircleSignature) (D : BlindConcRingData C)
  (h : Id (GroupHom (D .grp .fst) (D .grp .fst)) (hom_of_symmetry (D .grp .fst) (D .grp) (b11_unit_symmetry C D (C .loop)))
      (group_hom_id (D .grp .fst)))
  : BlindConcRingUnitLaw C D
  ≔ let R ≔ D .grp .fst in let P ≔ BookPointedMap (BG R) (BG R) in
    concat P (blind_concring_unit_map C D (C .loop))
      (hom_B R R (hom_of_symmetry R (D .grp) (b11_unit_symmetry C D (C .loop)))) (book_pointed_identity (BG R))
      (b11_unit_map_agree C D (C .loop)) (refl (hom_B R R) h)

{` Our ring satisfies the blind (printed) unit law. `}
def bridge_def_conc_ring_unit_law (C : CircleSignature) (R : ConcreteRing C) : BlindConcRingUnitLaw C (b11_data C R)
  ≔ b11_unit_law_from C (b11_data C R) (R .props .fst .fst)

def bridge_def_conc_ring_non_trivial (C : CircleSignature) (R : ConcreteRing C)
  : Id Type (BlindConcRingNonTrivial C (b11_data C R)) (IsNonTrivialConcreteRing C R)
  ≔ refl (IsNonTrivialConcreteRing C R)

{` Converse for 1143: blind data with the printed unit law give the first law of ConcreteRingProps. `}
def bridge_def_conc_ring_unit_law_converse (C : CircleSignature) (D : BlindConcRingData C) (h : BlindConcRingUnitLaw C D)
  : Id (GroupHom (D .grp .fst) (D .grp .fst))
      (hom_of_symmetry (D .grp .fst) (D .grp)
        (usym_hom (circle_group C) (abelian_hom_group (D .grp .fst) (D .grp))
          (group_hom_compose (circle_group C) (D .grp .fst) (abelian_hom_group (D .grp .fst) (D .grp)) (D .one) (D .mu))
          (circle_group_loop C)))
      (group_hom_id (D .grp .fst))
  ≔ b11_unit_law_to C D h

{` Corrected variant: adding the right unit law and associativity (the laws our ConcreteRing completes) as
   hypotheses, the conclusion holds. The left unit law comes from the printed law (evaluation_left_unit), the
   distributive laws need no hypothesis (module 1350). `}
def b11a_mul (C : CircleSignature) (D : BlindConcRingData C) (g h : USym (D .grp .fst)) : USym (D .grp .fst)
  ≔ usym_hom (D .grp .fst) (D .grp .fst)
      (hom_of_symmetry (D .grp .fst) (D .grp) (usym_hom (D .grp .fst) (abelian_hom_group (D .grp .fst) (D .grp)) (D .mu) g)) h

def BlindConcRingCorrectedConclusion (C : CircleSignature) (D : BlindConcRingData C)
  (mul : USym (D .grp .fst) → USym (D .grp .fst) → USym (D .grp .fst)) : Type
  ≔ let R ≔ D .grp .fst in let one ≔ usym_hom (blind_Z C) R (D .one) (C .loop) in
    ((a : USym R) → Id (USym R) (mul a one) a)
    → ((a b c : USym R) → Id (USym R) (mul a (mul b c)) (mul (mul a b) c))
    → Product (MonoidLaws (USym R) one mul) (BlindDistrLaws (USym R) mul (usym_mul R))

def blind_xca_Rconcring_URabstring_corrected : Type
  ≔ (C : CircleSignature) (D : BlindConcRingData C) → BlindConcRingUnitLaw C D
    → BlindConcRingCorrectedConclusion C D (blind_concring_mul C D)

def b11a_corrected_ours (C : CircleSignature) (D : BlindConcRingData C) (u : BlindConcRingUnitLaw C D)
  : BlindConcRingCorrectedConclusion C D (b11a_mul C D)
  ≔ let R ≔ D .grp .fst in let H ≔ abelian_hom_group R (D .grp) in let Z ≔ circle_group C in
    let ev ≔ hom_of_symmetry R (D .grp) in
    let ℓ ≔ (x ↦ ev (usym_hom R H (D .mu) x)) : USym R → GroupHom R R in
    let one ≔ usym_hom Z R (D .one) (C .loop) in
    let lu ≔ evaluation_left_unit Z R H (D .one) (D .mu) ev (C .loop) (b11_unit_law_to C D u) ℓ (x ↦ refl (ℓ x)) in
    ru as ↦
     ((usym_set R,
       (a ↦ (ru a,
             concat (USym R) (usym_hom R R (ℓ one) a) (usym_hom R R (group_hom_id R) a) a
               (map_path (GroupHom R R) (USym R) (f ↦ usym_hom R R f a) (ℓ one) (group_hom_id R) lu)
               (usym_hom_id R a)),
        as)),
      (a b c ↦ usym_hom_mul R R (ℓ a) b c,
       evaluation_rdistr R H (D .mu) ev (abelian_hom_usym_mul R (D .grp)) ℓ (x ↦ refl (ℓ x))))

def bridge_xca_Rconcring_URabstring_corrected : blind_xca_Rconcring_URabstring_corrected
  ≔ C D u ↦
    let S ≔ USym (D .grp .fst) in
    transport (S → S → S) (BlindConcRingCorrectedConclusion C D) (b11a_mul C D) (blind_concring_mul C D)
      (funext S (_ ↦ S → S) (b11a_mul C D) (blind_concring_mul C D)
        (a ↦ funext S (_ ↦ S) (b11a_mul C D a) (blind_concring_mul C D a)
          (b ↦ inverse S (blind_concring_mul C D a b) (b11a_mul C D a b) (b11a_mul_value C D a b))))
      (b11a_corrected_ours C D u)
