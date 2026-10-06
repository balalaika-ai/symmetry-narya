export "913-conjugate-fixed-points"
export "955-inner-automorphisms-kernel"
export "975-sigma3-symmetries"
export "583-fixed-point-subgroups"
export "524-fixed-elements"
export "505-gset-core-litmus"
export "507-subgroups-monos-equiv"

{` Chapter 9 (subgroups.tex). The remark on inn (line 1887) is false as
   printed. For lem:thereisaconjugate (line 1840), the reading of g⁻¹Bf_pt as
   "first g⁻¹, then Bf_pt" makes the lemma false. Both are refuted here with
   Σ_3 acting on Fin 3 and g = (0 1 2) (sigma3_sym cyc.). The lemma in the
   reading that its proof uses is conjugate_fixed_point_iff (913); the
   corrected remark is inn_usym_usym (955). `}

{` An H-fixed point is fixed by the image of every symmetry of H. `}
def subgroup_fixed_point_usym_fixed (G : Group) (X : GSet G) (m : GroupMonos G) (y : gset_underlying G X)
  (u : IsSubgroupFixedPoint G X m y) (h : USym (m .fst))
  : Id (gset_underlying G X) (gset_usym_act G X (usym_hom (m .fst) G (m .snd .fst) h) y) y
  ≔ let H ≔ m .fst in let f ≔ m .snd .fst in
    let B ≔ BG G .carrier in let s0 ≔ shape G in
    let F ≔ hom_function H G f in let F0 ≔ F (shape H) in
    let p ≔ hom_point H G f in let pi ≔ inverse B s0 F0 p in
    let A ≔ gset_underlying G X in
    let a ≔ u .fst (shape H) in
    let l ≔ refl F h in
    let fixa : Id (X F0 .fst) (gset_act G X F0 F0 l a) a
      ≔ inverse (X F0 .fst) a (gset_act G X F0 F0 l a)
          (invariant_map_fixed_by_loops H (gset_restrict H G f X) (u .fst) (shape H) h) in
    let q1 : Id (X F0 .fst) (gset_act G X s0 F0 p y) a
      ≔ concat (X F0 .fst) (gset_act G X s0 F0 p y) (gset_act G X s0 F0 p (gset_act G X F0 s0 pi a)) a
          (refl (gset_act G X s0 F0 p) (u .snd)) (gset_act_inverse_right G X s0 F0 p a) in
    calc
      gset_act G X s0 s0 (concat B s0 F0 s0 p (concat B F0 F0 s0 l pi)) y
      = gset_act G X F0 s0 (concat B F0 F0 s0 l pi) (gset_act G X s0 F0 p y)
        by gset_act_concat G X s0 F0 s0 p (concat B F0 F0 s0 l pi) y
      = gset_act G X F0 s0 pi (gset_act G X F0 F0 l (gset_act G X s0 F0 p y))
        by gset_act_concat G X F0 F0 s0 l pi (gset_act G X s0 F0 p y)
      = gset_act G X F0 s0 pi (gset_act G X F0 F0 l a)
        by refl ((b ↦ gset_act G X F0 s0 pi (gset_act G X F0 F0 l b)) : X F0 .fst → A) q1
      = gset_act G X F0 s0 pi a by refl (gset_act G X F0 s0 pi) fixa
      = y by inverse A y (gset_act G X F0 s0 pi a) (u .snd) ∎

{` T_0 = Stab(0) ⊆ Σ_3 as a monomorphism, and 0 is a T_0-fixed point (s(v) ≔ v.snd). `}
def sigma3_t0_mono : GroupMonos (symmetric_group three)
  ≔ subgroup_to_mono (symmetric_group three) (fixed_point_subgroup two fin3_zero)

def sigma3_t0_zero_fixed
  : IsSubgroupFixedPoint (symmetric_group three) (standard_symmetric_gset three) sigma3_t0_mono fin3_zero
  ≔ let G ≔ symmetric_group three in let X ≔ standard_symmetric_gset three in
    let B ≔ BG G .carrier in let s0 ≔ shape G in
    ((v ↦ v .snd),
     inverse (Fin three) (gset_act G X s0 s0 (inverse B s0 s0 (refl s0)) fin3_zero) fin3_zero
       (concat (Fin three) (gset_act G X s0 s0 (inverse B s0 s0 (refl s0)) fin3_zero) (gset_act G X s0 s0 (refl s0) fin3_zero)
          fin3_zero
          (refl ((r ↦ gset_act G X s0 s0 r fin3_zero) : Id B s0 s0 → Fin three) (inverse_refl B s0))
          (gset_act_refl G X s0 fin3_zero)))

{` lem:thereisaconjugate with the conjugate gH ≔ (H, F, g⁻¹ Bf_pt) read as
   "first g⁻¹, then Bf_pt" (conjugate_mono by g⁻¹). The other well-typed
   reading, which the proof of the book uses, is conjugate_fixed_point_iff
   (913). `}
def thereisaconjugate_printed : Type
  ≔ (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) (m : GroupMonos G)
    → Product (IsSubgroupFixedPoint G X m (gset_usym_act G X g x)
                 → IsSubgroupFixedPoint G X (conjugate_mono G (usym_inv G g) m) x)
        (IsSubgroupFixedPoint G X (conjugate_mono G (usym_inv G g) m) x
           → IsSubgroupFixedPoint G X m (gset_usym_act G X g x))

{` Counterexample: Σ_3 on Fin 3, H = T_0, g = (0 1 2), x = 2. Then g·2 = 0 is
   T_0-fixed, so the printed statement makes 2 fixed by the conjugate by g⁻¹,
   i.e. g⁻¹·2 = 1 a T_0-fixed point; but (1 2) ∈ T_0 moves 1. `}
def thereisaconjugate_printed_refuted : Not thereisaconjugate_printed
  ≔ P ↦
    let G ≔ symmetric_group three in let X ≔ standard_symmetric_gset three in
    let m ≔ sigma3_t0_mono in
    let g ≔ sigma3_sym cyc. in let gi ≔ usym_inv G g in
    let x : Fin three ≔ fin3_two in
    let fx : IsSubgroupFixedPoint G X (conjugate_mono G gi m) x ≔ P G X x g m .fst sigma3_t0_zero_fixed in
    let y ≔ gset_usym_act G X gi x in
    let fy : IsSubgroupFixedPoint G X m y ≔ conjugate_fixed_point_iff G X x gi m .snd fx in
    let y1 : Id (Fin three) y fin3_one ≔ gset_act_inv_left G X g fin3_one in
    let t ≔ sigma3_sigma in
    mere_rec (Σ (USym (m .fst)) (h ↦ Id (USym G) t (usym_hom (m .fst) G (m .snd .fst) h))) Empty empty_prop
      (w ↦
        let e : Id (Fin three) (gset_usym_act G X t y) y
          ≔ concat (Fin three) (gset_usym_act G X t y) (gset_usym_act G X (usym_hom (m .fst) G (m .snd .fst) (w .fst)) y) y
              (refl ((k ↦ gset_usym_act G X k y) : USym G → Fin three) (w .snd))
              (subgroup_fixed_point_usym_fixed G X m y fy (w .fst)) in
        let e1 : Id (Fin three) fin3_two fin3_one
          ≔ transport (Fin three) (z ↦ Id (Fin three) (gset_usym_act G X t z) z) y fin3_one y1 e in
        fin3_two_not_one e1)
      (subgroup_fixes_picked_out G (fixed_point_subgroup two fin3_zero) t (refl fin3_zero))

{` Remark at line 1887 as printed: USym(USym inn(g)) is h ↦ g⁻¹ h g. `}
def inn_usym_printed : Type
  ≔ (G : Group) (g h : USym G)
    → Id (USym G) (usym_hom G G (inn_symmetry_iso G g .fst) h) (usym_mul G (usym_inv G g) (usym_mul G h g))

{` If (g h) g⁻¹ = g⁻¹ (h g), then g g h = h g g on every G-set. `}
def conjugation_flip_act (G : Group) (X : GSet G) (g h : USym G)
  (E : Id (USym G) (usym_mul G (usym_mul G g h) (usym_inv G g)) (usym_mul G (usym_inv G g) (usym_mul G h g)))
  (j : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X g (gset_usym_act G X g (gset_usym_act G X h j)))
      (gset_usym_act G X h (gset_usym_act G X g (gset_usym_act G X g j)))
  ≔ let s ≔ shape G in let U ≔ gset_underlying G X in
    let a : USym G → U → U ≔ k x ↦ gset_usym_act G X k x in
    let gi ≔ usym_inv G g in
    let i ≔ a g j in
    let Y ≔ a h (a g i) in
    let lhs : Id U (a (usym_mul G (usym_mul G g h) gi) i) (a g (a h j))
      ≔ calc
          a (usym_mul G (usym_mul G g h) gi) i = a (usym_mul G g h) (a gi i) by gset_act_concat G X s s s gi (usym_mul G g h) i
          = a g (a h (a gi i)) by gset_act_concat G X s s s h g (a gi i)
          = a g (a h j) by refl ((x ↦ a g (a h x)) : U → U) (gset_act_inv_left G X g j) ∎ in
    let rhs : Id U (a (usym_mul G gi (usym_mul G h g)) i) (a gi Y)
      ≔ calc
          a (usym_mul G gi (usym_mul G h g)) i = a gi (a (usym_mul G h g) i) by gset_act_concat G X s s s (usym_mul G h g) gi i
          = a gi Y by refl (a gi) (gset_act_concat G X s s s g h i) ∎ in
    let mid : Id U (a g (a h j)) (a gi Y)
      ≔ calc
          a g (a h j) = a (usym_mul G (usym_mul G g h) gi) i by inverse U (a (usym_mul G (usym_mul G g h) gi) i) (a g (a h j)) lhs
          = a (usym_mul G gi (usym_mul G h g)) i by refl ((k ↦ a k i) : USym G → U) E
          = a gi Y by rhs ∎ in
    calc
      a g (a g (a h j)) = a g (a gi Y) by refl (a g) mid
      = Y by gset_act_inv_right G X g Y ∎

{` Counterexample: Σ_3, g = (0 1 2), h = (0 1). With inn_usym_usym the printed
   formula gives g h g⁻¹ = g⁻¹ h g, hence g g h = h g g; at 0 this is 0 = 2. `}
def inn_usym_printed_refuted : Not inn_usym_printed
  ≔ P ↦
    let G ≔ symmetric_group three in
    let g ≔ sigma3_sym cyc. in
    let h ≔ sigma3_tau in
    let E : Id (USym G) (usym_mul G (usym_mul G g h) (usym_inv G g)) (usym_mul G (usym_inv G g) (usym_mul G h g))
      ≔ concat (USym G) (usym_mul G (usym_mul G g h) (usym_inv G g)) (usym_hom G G (inn_symmetry_iso G g .fst) h)
          (usym_mul G (usym_inv G g) (usym_mul G h g))
          (inverse (USym G) (usym_hom G G (inn_symmetry_iso G g .fst) h) (usym_mul G (usym_mul G g h) (usym_inv G g))
            (inn_usym_usym G g h))
          (P G g h) in
    let p : Id (Fin three) fin3_zero fin3_two ≔ conjugation_flip_act G (standard_symmetric_gset three) g h E fin3_zero in
    transport (Fin three) fin3_two_code fin3_two fin3_zero (inverse (Fin three) fin3_zero fin3_two p) star.
