export "bridge-03-kernel-examples"
export "../../../src/951-kernels-of-composites"
export "../../../src/994-composite-fibers-stabilizers"

{` Bridges for exa:fibersofcomposites (687) and xca:fibersofcomposites (764): the stabilizer
   characterizations ("picks out loop^{nk}", "s^k with k = 0, 2", "the even permutations") and F1 on symmetries.
   The full "iff" statements are ours (module 994, *_stabilizer_iff; the blind BlindFixesPoint, BlindIff and
   BlindLoopMultiple are our KernelGsetFixes, Product and CircleLoopMultiple by definition). `}

{` exa:fibersofcomposites: the three stabilizers. `}
def bridge_exa_foc_mod4_stabilizer : blind_exa_foc_mod4_stabilizer ≔ C g ↦ foc_mod4_stabilizer_iff C g

def bridge_exa_foc_sgnprj_stabilizer : blind_exa_foc_sgnprj_stabilizer ≔ h ↦ foc_sgnprj_stabilizer_iff h

def bridge_exa_foc_composite_stabilizer : blind_exa_foc_composite_stabilizer ≔ C g ↦ foc_composite_stabilizer_iff C g

{` xca:fibersofcomposites: the stabilizers of R_4, of Bsgn (the even permutations) and of the composite. `}
def bridge_xca_foc_R4_stabilizer : blind_xca_foc_R4_stabilizer ≔ C g ↦ xr_R4_stabilizer_iff C g

def bridge_xca_foc_sgn_stabilizer : blind_xca_foc_sgn_stabilizer ≔ h ↦ xr_sgn_stabilizer_iff h

def bridge_xca_foc_composite_stabilizer : blind_xca_foc_composite_stabilizer ≔ C g ↦ xr_sR4_stabilizer_iff C g

{` F1 on symmetries. The blind F1 differs from ours (kc_F1, module 951) only in the pointing path of the fibers
   (the same argument as bridge-02); the lower square kc_lower_square transfers. `}
def bridge9w_fiber_path_base (X1 X2 : Type) (hX2 : isGroupoid X2) (f2 : X1 → X2) (x2 : X2) (x1 : X1) (p2 : Id X2 x2 (f2 x1))
  : Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (x1, concat X2 x2 (f2 x1) (f2 x1) p2 (refl (f2 x1))))
      (blind_fiber_path X1 X2 f2 x2 x1 p2 x1 (refl x1))
      (refl x1, mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)
  ≔ let q ≔ concat X2 x2 (f2 x1) (f2 x1) p2 (refl (f2 x1)) in
    let F ≔ BookFiber X1 X2 f2 x2 in
    let P ≔ (a'' u' ↦ Id F (x1, p2) (a'', concat X2 x2 (f2 x1) (f2 a'') p2 (refl f2 u'))) : (a'' : X1) → Id X1 x1 a'' → Type in
    let s1 ≔ inverse (Id X2 x2 (f2 x1)) q p2 (concat_p1 X2 x2 (f2 x1) p2) in
    let b0 : Id F (x1, p2) (x1, q) ≔ (refl x1, s1) in
    let pr ≔ (s ↦ (refl x1, s)) : Id (Id X2 x2 (f2 x1)) p2 q → Id F (x1, p2) (x1, q) in
    concat (Id F (x1, p2) (x1, q)) (J X1 x1 P b0 x1 (refl x1)) b0 (refl x1, mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)
      (inverse (Id F (x1, p2) (x1, q)) b0 (J X1 x1 P b0 x1 (refl x1)) (Jβ X1 x1 P b0))
      (refl pr (hX2 x2 (f2 x1) p2 q s1 (mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)))

def bridge9w_fiber_path_agree (X1 X2 : Type) (hX2 : isGroupoid X2) (f2 : X1 → X2) (x2 : X2) (x1 : X1) (p2 : Id X2 x2 (f2 x1))
  (a' : X1) (u : Id X1 x1 a')
  : Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (a', concat X2 x2 (f2 x1) (f2 a') p2 (refl f2 u)))
      (blind_fiber_path X1 X2 f2 x2 x1 p2 a' u)
      (u, mapped_pathover_append X1 X2 f2 x2 x1 a' u p2)
  ≔ J X1 x1 (a'' u' ↦ Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (a'', concat X2 x2 (f2 x1) (f2 a'') p2 (refl f2 u')))
                 (blind_fiber_path X1 X2 f2 x2 x1 p2 a'' u')
                 (u', mapped_pathover_append X1 X2 f2 x2 x1 a'' u' p2))
      (bridge9w_fiber_path_base X1 X2 hX2 f2 x2 x1 p2) a' u

def bridge9w_F1_point_type (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : Type
  ≔ Id (HomFiber G1 G2 f2 (shape G2)) (kernel_shape G1 G2 f2)
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2)
        (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)))

def bridge9w_F1_at (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (kp : bridge9w_F1_point_type G0 G1 G2 f1 f2)
  : GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2)
  ≔ ch9w2_aut_hom (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (HomFiber G1 G2 f2 (shape G2))
      (hom_fiber_groupoid G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (hom_fiber_groupoid G1 G2 f2 (shape G2))
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2))
      (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_shape G1 G2 f2) kp

def bridge9w_blind_kp (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : bridge9w_F1_point_type G0 G1 G2 f1 f2
  ≔ blind_fiber_path (BG G1 .carrier) (BG G2 .carrier) (hom_function G1 G2 f2) (shape G2)
      (shape G1) (hom_point G1 G2 f2) (hom_function G0 G1 f1 (shape G0)) (hom_point G0 G1 f1)

def bridge9w_kp_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (bridge9w_F1_point_type G0 G1 G2 f1 f2) (kc_F1_point G0 G1 G2 f1 f2) (bridge9w_blind_kp G0 G1 G2 f1 f2)
  ≔ inverse (bridge9w_F1_point_type G0 G1 G2 f1 f2) (bridge9w_blind_kp G0 G1 G2 f1 f2) (kc_F1_point G0 G1 G2 f1 f2)
      (bridge9w_fiber_path_agree (BG G1 .carrier) (BG G2 .carrier) (bg_groupoid G2) (hom_function G1 G2 f2) (shape G2)
        (shape G1) (hom_point G1 G2 f2) (hom_function G0 G1 f1 (shape G0)) (hom_point G0 G1 f1))

{` The lower square for the blind F1: ker_{f2} ∘ F1 = f1 ∘ ker_{f2 f1}. `}
def bridge9w_blind_square (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G1)
      (group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
      (group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) G1
        (blind_cor_F1 G0 G1 G2 f1 f2) (kernel_inclusion G1 G2 f2))
  ≔ let K21 ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let K2 ≔ kernel_group G1 G2 f2 in
    transport (bridge9w_F1_point_type G0 G1 G2 f1 f2)
      (kp ↦ Id (GroupHom K21 G1)
        (group_hom_compose K21 G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
        (group_hom_compose K21 K2 G1 (bridge9w_F1_at G0 G1 G2 f1 f2 kp) (kernel_inclusion G1 G2 f2)))
      (kc_F1_point G0 G1 G2 f1 f2) (bridge9w_blind_kp G0 G1 G2 f1 f2) (bridge9w_kp_path G0 G1 G2 f1 f2)
      (kc_lower_square G0 G1 G2 f1 f2)

{` Generic: for g over loop^{2k}, ker_{f2}(F1 g) = f1(loop)^{2k}. `}
def bridge9w_F1_symmetries (C : CircleSignature) (G1 G2 : Group) (f1 : GroupHom (circle_group C) G1) (f2 : GroupHom G1 G2)
  (a : USym G1) (hl : Id (USym G1) (usym_hom (circle_group C) G1 f1 (C .loop)) a)
  (g : USym (kernel_group (circle_group C) G2 (kc_compose (circle_group C) G1 G2 f1 f2))) (k : Int)
  (e : Id (USym (circle_group C))
         (usym_hom (kernel_group (circle_group C) G2 (kc_compose (circle_group C) G1 G2 f1 f2)) (circle_group C)
           (kernel_inclusion (circle_group C) G2 (kc_compose (circle_group C) G1 G2 f1 f2)) g)
         (circle_power C (int_mul (pos. two) k)))
  : Id (USym G1)
      (usym_hom (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2)
        (usym_hom (kernel_group (circle_group C) G2 (kc_compose (circle_group C) G1 G2 f1 f2)) (kernel_group G1 G2 f2)
          (blind_cor_F1 (circle_group C) G1 G2 f1 f2) g))
      (loop_power (BG G1 .carrier) (shape G1) a (int_mul (pos. two) k))
  ≔ let Z ≔ circle_group C in
    let K21 ≔ kernel_group Z G2 (kc_compose Z G1 G2 f1 f2) in
    let K2 ≔ kernel_group G1 G2 f2 in
    let k21 ≔ kernel_inclusion Z G2 (kc_compose Z G1 G2 f1 f2) in
    let k2 ≔ kernel_inclusion G1 G2 f2 in
    let F1 ≔ blind_cor_F1 Z G1 G2 f1 f2 in
    let U ≔ USym G1 in
    calc
      usym_hom K2 G1 k2 (usym_hom K21 K2 F1 g) = usym_hom K21 G1 (group_hom_compose K21 K2 G1 F1 k2) g
        by inverse U (usym_hom K21 G1 (group_hom_compose K21 K2 G1 F1 k2) g) (usym_hom K2 G1 k2 (usym_hom K21 K2 F1 g))
             (happly (USym K21) (_ ↦ U) (usym_hom K21 G1 (group_hom_compose K21 K2 G1 F1 k2))
               (x ↦ usym_hom K2 G1 k2 (usym_hom K21 K2 F1 x)) (usym_hom_compose K21 K2 G1 F1 k2) g)
      = usym_hom K21 G1 (group_hom_compose K21 Z G1 k21 f1) g
        by refl ((φ ↦ usym_hom K21 G1 φ g) : GroupHom K21 G1 → U)
             (inverse (GroupHom K21 G1) (group_hom_compose K21 Z G1 k21 f1) (group_hom_compose K21 K2 G1 F1 k2)
               (bridge9w_blind_square Z G1 G2 f1 f2))
      = usym_hom Z G1 f1 (usym_hom K21 Z k21 g)
        by happly (USym K21) (_ ↦ U) (usym_hom K21 G1 (group_hom_compose K21 Z G1 k21 f1))
             (x ↦ usym_hom Z G1 f1 (usym_hom K21 Z k21 x)) (usym_hom_compose K21 Z G1 k21 f1) g
      = usym_hom Z G1 f1 (circle_power C (int_mul (pos. two) k)) by refl (usym_hom Z G1 f1) e
      = loop_power (BG G1 .carrier) (shape G1) a (int_mul (pos. two) k)
        by foc_phi_power C G1 f1 a hl (int_mul (pos. two) k) ∎

def bridge_exa_foc_F1_symmetries : blind_exa_foc_F1_symmetries
  ≔ C ↦ bridge9w_F1_symmetries C BlindC4 BlindS2 (blind_mod4 C) blind_sgnprj blind_c4_gen (mod_hom_loop C three)

def bridge_xca_foc_F1_symmetries : blind_xca_foc_F1_symmetries
  ≔ C ↦ bridge9w_F1_symmetries C BlindS4 BlindS2 (blind_R4 C) blind_sgn4 (finite_successor_symmetry three) (power_finset_loop C three)
