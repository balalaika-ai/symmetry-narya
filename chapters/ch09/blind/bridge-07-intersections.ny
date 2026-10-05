export "07-intersections"
export "../../../src/918-ch9-text-claims"
export "../../../src/934-epi-connected-fibers"
export "../../../src/508-stabilizer-subgroups"

{` Bridges for subgroups.tex, sec "Intersecting with normal subgroups" (blind file 07-intersections), blocks
   1804 lem:whatSylow2needs and 1825 (1801 is in bridge-07c-abstract); lem:thereisaconjugate (1840) is in bridge-07b-conjugate. The blind
   hypotheses are categorical epimorphisms; ours have connected fibers: transferred by lem:epi-surj
   (gepi_epi_connected_fibers, module 934). `}

{` The blind q_N is ours (both are the component lift of y ↦ X_y pointed by refl; module 436). `}
def bridge9w_qhom_path (G : Group) (N : NormalSubgroups G)
  : Id (GroupHom G (normal_quotient_group G N)) (blind_quotient_hom G N) (normal_quotient_hom G N)
  ≔ refl (mkhom G (normal_quotient_group G N))
      (component_lift_project (BG G) (bg_connected G) (GSet G) (N (shape G) .gset)
        (hom_B G (normal_quotient_group G N) (normal_quotient_hom G N)))

{` lem:whatSylow2needs (1), in Mono(H) and in Mono(G). `}
def bridge_whatSylow2needs_kernel : blind_whatSylow2needs_kernel
  ≔ G G' f hf m ↦
    chim_monos_path (m .fst) (blind_NcapH_to_H G G' f (m .fst) (m .snd .fst))
      (blind_ker (m .fst) G' (group_hom_compose (m .fst) G G' (m .snd .fst) f))
      (wsn_intersection_homs_path G G' (m .fst) f (m .snd .fst) (gepi_epi_connected_fibers G G' f hf))

def bridge_whatSylow2needs_kernel_in_G : blind_whatSylow2needs_kernel_in_G
  ≔ G G' f hf m ↦
    let H ≔ m .fst in let i ≔ m .snd .fst in
    let fi ≔ group_hom_compose H G G' i f in
    let K ≔ kernel_group H G' fi in let k ≔ kernel_inclusion H G' fi in
    let N ≔ kernel_group G G' f in let kf ≔ kernel_inclusion G G' f in
    let P ≔ pullback_group G N H kf i in
    let pl ≔ pullback_group_proj_left G N H kf i in let pr ≔ pullback_group_proj_right G N H kf i in
    let mj ≔ pbg_compose_mono K H G k i (kernel_inclusion_mono H G' fi) (m .snd .snd) in
    let q1 : Id (HomsInto G) (P, group_hom_compose P N G pl kf) (P, group_hom_compose P H G pr i)
      ≔ refl ((u ↦ (P, u)) : GroupHom P G → HomsInto G) (pullback_group_square G N H kf i) in
    let q2 : Id (HomsInto G) (P, group_hom_compose P H G pr i) (K, group_hom_compose K H G k i)
      ≔ refl ((w ↦ (w .fst, group_hom_compose (w .fst) H G (w .snd) i)) : HomsInto H → HomsInto G)
          (wsn_intersection_homs_path G G' H f i (gepi_epi_connected_fibers G G' f hf)) in
    (mj,
     chim_monos_path G (group_mono_intersection G (blind_ker G G' f) m) (K, (group_hom_compose K H G k i, mj))
       (concat (HomsInto G) (P, group_hom_compose P N G pl kf) (P, group_hom_compose P H G pr i)
         (K, group_hom_compose K H G k i) q1 q2))

{` lem:whatSylow2needs (2). N' = the normal subgroup ker(fi) of module 908 (underlying subgroup E(N ∩ H),
   what_sylow_needs_quotient_subgroup); k the induced monomorphism. `}
def bridge_whatSylow2needs_mono : blind_whatSylow2needs_mono
  ≔ G G' f hf m ↦
    let H ≔ m .fst in let i ≔ m .snd .fst in
    let fi ≔ group_hom_compose H G G' i f in
    let c ≔ gepi_epi_connected_fibers G G' f hf in
    let Nn ≔ kernel_normal_subgroup H G' fi in
    let Q ≔ normal_quotient_group H Nn in
    let w ≔ what_sylow_needs_induced G G' H f i in
    let N ≔ kernel_group G G' f in let kf ≔ kernel_inclusion G G' f in
    let P ≔ pullback_group G N H kf i in
    let pr ≔ pullback_group_proj_right G N H kf i in
    (Nn,
     (concat (Subgroups H) (normal_to_subgroup H Nn) (mono_to_subgroup H (wsn_intersection_as_mono G G' H f i c))
        (mono_to_subgroup H (blind_NcapH_to_H G G' f H i))
        (what_sylow_needs_quotient_subgroup G G' H f i c)
        (refl (mono_to_subgroup H)
          (group_monos_path_same H P pr pr (wsn_intersection_mono G G' H f i c)
            (pullback_group_proj_right_mono G N H kf i (blind_kermap_mono G G' f)) (refl pr))),
      (w .fst,
       (equiv_inverse_map (IsGroupMonomorphism Q G' (w .fst)) (IsGroupMono Q G' (w .fst))
          (group_monomorphism_mono_equiv Q G' (w .fst)) (w .snd .fst),
        concat (GroupHom H G') (group_hom_compose H Q G' (blind_quotient_hom H Nn) (w .fst))
          (group_hom_compose H Q G' (normal_quotient_hom H Nn) (w .fst)) fi
          (refl ((q ↦ group_hom_compose H Q G' q (w .fst)) : GroupHom H Q → GroupHom H G') (bridge9w_qhom_path H Nn))
          (w .snd .snd)))))

{` xca (subgroups.tex:1825): the Sub-form. N ∩ S as the S-orbit of pt_N in i_S^*(E(ker f)): E(ker f) is the
   transitive (f^*P_{G'}, Bf_pt) (f has connected fibers), so the orbit subgroup is that of Bf_pt in (f i_S)^*P_{G'},
   i.e. E(ker(f i_S)) (stabilizer_subgroup_path, module 508). `}
def bridge9w_sub_ncaph_kernel (G G' : Group) (f : GroupHom G G') (c : IsConnectedHom G G' f) (S : Subgroups G)
  : Id (Subgroups (subgroup_group G S)) (blind_sub_NcapH G G' f S)
      (mono_to_subgroup (subgroup_group G S)
        (kernel (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)))
  ≔ let H ≔ subgroup_group G S in let i ≔ subgroup_inclusion G S in
    let fi ≔ group_hom_compose H G G' i f in
    let SH ≔ Subgroups H in
    let KG ≔ kernel_gset G G' f in let kp ≔ hom_point G G' f in
    let KH ≔ kernel_gset H G' fi in
    let trK : IsTransitive G KG ≔ connected_action_type_transitive G KG (c (shape G')) in
    let Phi : Subgroups G → SH ≔ T ↦ orbit_subgroup H (gset_restrict H G i (T .gset)) (T .point) in
    let B' ≔ BG G' .carrier in
    let fs ≔ hom_function G G' f (shape G) in
    calc
      Phi (mono_to_subgroup G (kernel G G' f)) = Phi (KG, kp, trK)
        by refl Phi (transitive_stabilizer_subgroup_path G KG kp trK)
      = orbit_subgroup H KH (hom_point H G' fi)
        by refl ((x ↦ orbit_subgroup H KH x) : Id B' (shape G') fs → SH)
             (inverse (Id B' (shape G') fs) (concat B' (shape G') fs fs kp (refl fs)) kp (concat_p1 B' (shape G') fs kp))
      = mono_to_subgroup H (kernel H G' fi)
        by inverse SH (mono_to_subgroup H (kernel H G' fi)) (orbit_subgroup H KH (hom_point H G' fi))
             (stabilizer_subgroup_path H KH (hom_point H G' fi)) ∎

def bridge_whatSylow2needs_sub : blind_whatSylow2needs_sub
  ≔ G G' f hf S ↦
    let H ≔ subgroup_group G S in let i ≔ subgroup_inclusion G S in
    let fi ≔ group_hom_compose H G G' i f in
    let c ≔ gepi_epi_connected_fibers G G' f hf in
    let Nn ≔ kernel_normal_subgroup H G' fi in
    let Q ≔ normal_quotient_group H Nn in
    let w ≔ what_sylow_needs_induced G G' H f i in
    let pa ≔ bridge9w_sub_ncaph_kernel G G' f c S in
    (pa,
     (Nn,
      (concat (Subgroups H) (normal_to_subgroup H Nn) (mono_to_subgroup H (kernel H G' fi)) (blind_sub_NcapH G G' f S)
         (kernel_normal_subgroup_is_kernel H G' fi)
         (inverse (Subgroups H) (blind_sub_NcapH G G' f S) (mono_to_subgroup H (kernel H G' fi)) pa),
       (w .fst,
        (equiv_inverse_map (IsGroupMonomorphism Q G' (w .fst)) (IsGroupMono Q G' (w .fst))
           (group_monomorphism_mono_equiv Q G' (w .fst)) (w .snd .fst),
         concat (GroupHom H G') (group_hom_compose H Q G' (blind_quotient_hom H Nn) (w .fst))
           (group_hom_compose H Q G' (normal_quotient_hom H Nn) (w .fst)) fi
           (refl ((q ↦ group_hom_compose H Q G' q (w .fst)) : GroupHom H Q → GroupHom H G') (bridge9w_qhom_path H Nn))
           (w .snd .snd))))))
