export "903-normal-subgroups"
export "127-symmetries-of-circle"

{` Chapter 9 (subgroups.tex), the running text before lem:thereisaconjugate
   (H-fixed points of a G-set through a homomorphism) and
   lem:thereisaconjugate.

   For a monomorphism m = (H, f, !) with F ≔ Bf÷ and p ≔ Bf_pt : sh_G = F(sh_H),
   x : X(sh_G) is an H-fixed point if there is s : Π_{v:BH} X(F v) with
   x = X(p⁻¹)(s(sh_H)) (the fixed points of the restricted H-set F^*X,
   moved to X(sh_G)). `}

def IsSubgroupFixedPoint (G : Group) (X : GSet G) (m : GroupMonos G) (x : gset_underlying G X) : Type
  ≔ let H ≔ m .fst in let f ≔ m .snd .fst in
    Σ (InvariantMaps H (gset_restrict H G f X))
      (s ↦ Id (gset_underlying G X) x
        (gset_act G X (hom_function H G f (shape H)) (shape G)
          (inverse (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_point H G f)) (s (shape H))))

{` The conjugate (H, F, g p) of m (pointing: first g, then p). It is the
   conjugate of m by g⁻¹ for the G-set action of Mono(G)
   (rem:action-Mono(G) moves the pointing p to g⁻¹ followed by p). `}
def conjugate_mono (G : Group) (g : USym G) (m : GroupMonos G) : GroupMonos G
  ≔ let H ≔ m .fst in let f ≔ m .snd .fst in
    let k ≔ mkhom H G (hom_function H G f,
      concat (BG G .carrier) (shape G) (shape G) (hom_function H G f (shape H)) g (hom_point H G f)) in
    (H, (k, covering_group_mono H G k (group_mono_covering H G f (m .snd .snd))))

{` lem:thereisaconjugate: g · x is a fixed point for the H-action iff x is
   a fixed point for the conjugate (H, F, g p).

   Notation: the book writes the conjugate as gH ≔ (H, F, g⁻¹Bf_pt). As a
   composite in the book's composition order this is ill-typed. It has two
   well-typed readings.
   (1) g⁻¹ acts on Bf_pt by transport in z ↦ (z = F(sh_H)), as in
   def:kernel. This gives the pointing "first g, then Bf_pt", which is the
   pointing used here. The book's own proof computes with this reading:
   X((g⁻¹Bf_pt)⁻¹) = g⁻¹·X(Bf_pt⁻¹). With it, the lemma is this declaration.
   (2) "First g⁻¹, then Bf_pt" (the action of g on Mono(G)). With it, the
   statement is false (thereisaconjugate_printed_refuted, module 992: for Σ_3
   acting on {0,1,2}, H the stabilizer of 0 and g a 3-cycle, x ≔ g⁻¹·0 has
   g·x = 0 H-fixed, but x is fixed only by g⁻¹Hg ≠ gHg⁻¹).
   In reading (1), gH is the conjugate by g⁻¹ in the sense of
   rem:action-Mono(G) (conjugate_mono_action), so the name gH clashes with
   that remark. `}
def conjugate_fixed_point_iff (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) (m : GroupMonos G)
  : Product (IsSubgroupFixedPoint G X m (gset_usym_act G X g x) → IsSubgroupFixedPoint G X (conjugate_mono G g m) x)
      (IsSubgroupFixedPoint G X (conjugate_mono G g m) x → IsSubgroupFixedPoint G X m (gset_usym_act G X g x))
  ≔ let B ≔ BG G .carrier in
    let A ≔ gset_underlying G X in
    let H ≔ m .fst in let f ≔ m .snd .fst in
    let s0 ≔ shape G in
    let F0 ≔ hom_function H G f (shape H) in
    let p ≔ hom_point H G f in
    let gi ≔ inverse B s0 s0 g in
    let pi ≔ inverse B s0 F0 p in
    let gp ≔ concat B s0 s0 F0 g p in
    let key : (b : X F0 .fst) → Id A (gset_act G X F0 s0 (inverse B s0 F0 gp) b)
                                  (gset_act G X s0 s0 gi (gset_act G X F0 s0 pi b))
      ≔ b ↦ concat A (gset_act G X F0 s0 (inverse B s0 F0 gp) b) (gset_act G X F0 s0 (concat B F0 s0 s0 pi gi) b)
              (gset_act G X s0 s0 gi (gset_act G X F0 s0 pi b))
              (refl ((r ↦ gset_act G X F0 s0 r b) : Id B F0 s0 → A) (inverse_concat B s0 s0 F0 g p))
              (gset_act_concat G X F0 s0 s0 pi gi b) in
    (u ↦ (u .fst,
          let b ≔ u .fst (shape H) in
          calc
            x
            = gset_act G X s0 s0 gi (gset_act G X s0 s0 g x)
              by inverse A (gset_act G X s0 s0 gi (gset_act G X s0 s0 g x)) x (gset_act_inverse_left G X s0 s0 g x)
            = gset_act G X s0 s0 gi (gset_act G X F0 s0 pi b) by refl (gset_act G X s0 s0 gi) (u .snd)
            = gset_act G X F0 s0 (inverse B s0 F0 gp) b
              by inverse A (gset_act G X F0 s0 (inverse B s0 F0 gp) b) (gset_act G X s0 s0 gi (gset_act G X F0 s0 pi b)) (key b) ∎),
     u ↦ (u .fst,
          let b ≔ u .fst (shape H) in
          calc
            gset_act G X s0 s0 g x
            = gset_act G X s0 s0 g (gset_act G X F0 s0 (inverse B s0 F0 gp) b) by refl (gset_act G X s0 s0 g) (u .snd)
            = gset_act G X s0 s0 g (gset_act G X s0 s0 gi (gset_act G X F0 s0 pi b)) by refl (gset_act G X s0 s0 g) (key b)
            = gset_act G X F0 s0 pi b by gset_act_inverse_right G X s0 s0 g (gset_act G X F0 s0 pi b) ∎))

{` The conjugate (H, F, g p) is the image of m under the action of g⁻¹ on
   the G-set Mono(G) (rem:action-Mono(G)). `}
def conjugate_mono_action (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (GroupMonos G) (conjugate_mono G g m)
      (monos_conjugate G (shape G) (shape G) (inverse (BG G .carrier) (shape G) (shape G) g) m)
  ≔ let B ≔ BG G .carrier in
    let H ≔ m .fst in let f ≔ m .snd .fst in
    let s0 ≔ shape G in
    let F0 ≔ hom_function H G f (shape H) in
    let p ≔ hom_point H G f in
    let k ≔ conjugate_mono G g m .snd .fst in
    let k' ≔ monos_conjugate G s0 s0 (inverse B s0 s0 g) m .snd .fst in
    group_monos_path_same G H k k' (conjugate_mono G g m .snd .snd)
      (monos_conjugate G s0 s0 (inverse B s0 s0 g) m .snd .snd)
      (equiv_inverse_map (Id (GroupHom H G) k k') (PointedHomotopy (BG H) (BG G) (hom_B H G k) (hom_B H G k'))
        (group_hom_path_equiv H G k k')
        (u ↦ refl (hom_function H G f u),
         calc
           concat B s0 F0 F0 (concat B s0 s0 F0 g p) (refl F0)
           = concat B s0 s0 F0 g p by concat_p1 B s0 F0 (concat B s0 s0 F0 g p)
           = concat B s0 s0 F0 (inverse B s0 s0 (inverse B s0 s0 g)) p
             by refl ((r ↦ concat B s0 s0 F0 r p) : Id B s0 s0 → Id B s0 F0)
                  (inverse (Id B s0 s0) (inverse B s0 s0 (inverse B s0 s0 g)) g (inverse_inverse B s0 s0 g)) ∎))
