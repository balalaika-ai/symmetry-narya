export "bridge-04a-image-core"

{` Bridges for subgroups.tex, sec:image (blind file 04-images), part 2: the statements. Statements about a
   blind image operation are stated for an arbitrary image operation (S below) and transported from ours along
   bridge9_img_op_path / bridge9_aut_op_path. `}

{` def:Im(grphom). `}
def bridge_def_Img (G H : Group) (f : GroupHom G H) : Id Group (BlindImg G H f) (image_group G H f)
  ≔ refl ((o ↦ o .fst G H f .fst) : bridge9_ImgOpM → Group) bridge9_img_op_path

def bridge_def_im_proj (G H : Group) (f : GroupHom G H)
  : Id (HomsFrom G) (BlindImg G H f, blind_im_proj G H f) (image_group G H f, image_projection G H f)
  ≔ refl ((o ↦ ((o .fst G H f .fst, o .fst G H f .snd .fst) : HomsFrom G)) : bridge9_ImgOpM → HomsFrom G) bridge9_img_op_path

def bridge_def_im_incl (G H : Group) (f : GroupHom G H)
  : Id (GroupMonos H) (BlindImg G H f, (blind_im_incl G H f, blind_im_incl_mono G H f)) (image_mono G H f)
  ≔ refl ((o ↦ ((o .fst G H f .fst, (o .fst G H f .snd .snd, o .snd G H f)) : GroupMonos H)) : bridge9_ImgOpM → GroupMonos H)
      bridge9_img_op_path

def bridge_im_unpointed_factorization : blind_im_unpointed_factorization
  ≔ G H f ↦ refl (hom_function G H f)

{` xca:p-epi-i-mono: our pointing (image_projection_point) works; epi by connected fibers (lem:epi-surj). `}
def bridge_p_epi_i_mono : blind_p_epi_i_mono
  ≔ G H f ↦
    let A ≔ BG G .carrier in let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in
    ((image_projection_point G H f,
      (map_path (GroupHom G H) (BookPointedMap (BG G) (BG H)) (hom_B G H) f
         (group_hom_compose G (image_group G H f) H (image_projection G H f) (image_inclusion G H f))
         (image_factorization_path G H f),
       gepi_connected_fibers_epi G (BlindImg G H f)
         (mkhom G (BlindImg G H f) (zero_image_factor A B Bf, image_projection_point G H f))
         (zero_image_factor_connected_fibers A B Bf))),
     equiv_inverse_map (IsGroupMonomorphism (BlindImg G H f) H (blind_im_incl G H f)) (IsGroupMono (BlindImg G H f) H (blind_im_incl G H f))
       (group_monomorphism_mono_equiv (BlindImg G H f) H (blind_im_incl G H f)) (blind_im_incl_mono G H f))

def bridge9_S_factorizes (o : bridge9_ImgOpM) : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Id (GroupHom G H) f (group_hom_compose G (o .fst G H f .fst) H (o .fst G H f .snd .fst) (o .fst G H f .snd .snd))

def bridge9_S_proj_epi (o : bridge9_ImgOpM) : Type
  ≔ (G H : Group) (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst)

def bridge_im_factorization : blind_im_factorization
  ≔ bridge9_op_transport bridge9_S_factorizes bridge9_img_op bridge9_img_op_path (G H f ↦ image_factorization_path G H f)

def bridge_im_proj_epi : blind_im_proj_epi
  ≔ bridge9_op_transport bridge9_S_proj_epi bridge9_img_op bridge9_img_op_path (G H f ↦ eqmc_image_projection_epi G H f)

{` def:Im-fact: the blind pullback (with chapter 5's monos) and ours (with categorical monos). `}
def bridge9_pullback_map (G H : Group) (t : EpiMonoFactorizations G H) : BlindEpiMonoPullback G H
  ≔ (t .fst, ((t .snd .fst .fst, (t .snd .fst .snd .fst,
      group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst) .map (t .snd .fst .snd .snd))), t .snd .snd))

def bridge9_pullback_inv (G H : Group) (t : BlindEpiMonoPullback G H) : EpiMonoFactorizations G H
  ≔ (t .fst, ((t .snd .fst .fst, (t .snd .fst .snd .fst,
      equiv_inverse_map (IsGroupMonomorphism (t .snd .fst .fst) H (t .snd .fst .snd .fst)) (IsGroupMono (t .snd .fst .fst) H (t .snd .fst .snd .fst))
        (group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst)) (t .snd .fst .snd .snd))), t .snd .snd))

def bridge_def_epi_mono_pullback (G H : Group) : Equiv (EpiMonoFactorizations G H) (BlindEpiMonoPullback G H)
  ≔ quasi_inverse_equiv (EpiMonoFactorizations G H) (BlindEpiMonoPullback G H) (bridge9_pullback_map G H) (bridge9_pullback_inv G H)
      (t ↦ refl ((m ↦ ((t .fst, ((t .snd .fst .fst, (t .snd .fst .snd .fst, m)), t .snd .snd)) : EpiMonoFactorizations G H))
                   : IsGroupMonomorphism (t .snd .fst .fst) H (t .snd .fst .snd .fst) → EpiMonoFactorizations G H)
             (is_group_monomorphism_prop (t .snd .fst .fst) H (t .snd .fst .snd .fst)
               (equiv_inverse_map (IsGroupMonomorphism (t .snd .fst .fst) H (t .snd .fst .snd .fst)) (IsGroupMono (t .snd .fst .fst) H (t .snd .fst .snd .fst))
                 (group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst))
                 (group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst) .map (t .snd .fst .snd .snd)))
               (t .snd .fst .snd .snd)))
      (t ↦ refl ((m ↦ ((t .fst, ((t .snd .fst .fst, (t .snd .fst .snd .fst, m)), t .snd .snd)) : BlindEpiMonoPullback G H))
                   : IsGroupMono (t .snd .fst .fst) H (t .snd .fst .snd .fst) → BlindEpiMonoPullback G H)
             (is_group_mono_prop (t .snd .fst .fst) H (t .snd .fst .snd .fst)
               (group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst) .map
                 (equiv_inverse_map (IsGroupMonomorphism (t .snd .fst .fst) H (t .snd .fst .snd .fst)) (IsGroupMono (t .snd .fst .fst) H (t .snd .fst .snd .fst))
                   (group_monomorphism_mono_equiv (t .snd .fst .fst) H (t .snd .fst .snd .fst)) (t .snd .fst .snd .snd)))
               (t .snd .fst .snd .snd)))

{` The image factorization map of an image operation, for any epi proofs hp. `}
def bridge9_imfact_of (o : bridge9_ImgOpM) (G H : Group)
  (hp : (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst)) (f : GroupHom G H)
  : BlindEpiMonoPullback G H
  ≔ ((o .fst G H f .fst, (o .fst G H f .snd .fst, hp f)), ((o .fst G H f .fst, (o .fst G H f .snd .snd, o .snd G H f)), refl (o .fst G H f .fst)))

def bridge_def_imfact (G H : Group) (hp : BlindImProjEpi G H) (f : GroupHom G H)
  : Id (BlindEpiMonoPullback G H) (blind_imfact G H hp f) (bridge9_imfact_of bridge9_img_op G H hp f)
  ≔ refl (blind_imfact G H hp f)

def bridge9_our_imfact_path (G H : Group)
  (hp : (f : GroupHom G H) → IsGroupEpi G (image_group G H f) (image_projection G H f)) (f : GroupHom G H)
  : Id (BlindEpiMonoPullback G H) (bridge9_pullback_map G H (image_factorization_map G H f)) (bridge9_imfact_of bridge9_our_op G H hp f)
  ≔ let I ≔ image_group G H f in let p ≔ image_projection G H f in let i ≔ image_inclusion G H f in
    refl ((ep mp ↦ (((I, (p, ep)), ((I, (i, mp)), refl I)) : BlindEpiMonoPullback G H))
            : IsGroupEpi G I p → IsGroupMono I H i → BlindEpiMonoPullback G H)
      (is_group_epi_prop G I p (eqmc_image_projection_epi G H f) (hp f))
      (is_group_mono_prop I H i (group_monomorphism_mono_equiv I H i .map (eqmc_image_inclusion_monomorphism G H f))
        (image_inclusion_mono G H f))

def bridge9_S_imfact_equiv (o : bridge9_ImgOpM) : Type
  ≔ (G H : Group) (hp : (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst))
    → BookIsEquiv (GroupHom G H) (BlindEpiMonoPullback G H) (bridge9_imfact_of o G H hp)

def bridge9_our_imfact_equiv : bridge9_S_imfact_equiv bridge9_our_op
  ≔ G H hp ↦
    book_equivalence (GroupHom G H) (BlindEpiMonoPullback G H)
      (equiv_change_map (GroupHom G H) (BlindEpiMonoPullback G H)
        (compose_equiv (GroupHom G H) (EpiMonoFactorizations G H) (BlindEpiMonoPullback G H)
          (native_equivalence (GroupHom G H) (EpiMonoFactorizations G H) (image_factorization_equiv G H))
          (bridge_def_epi_mono_pullback G H))
        (bridge9_imfact_of bridge9_our_op G H hp)
        (bridge9_our_imfact_path G H hp)) .equiv

{` lem:Im-fact-unique. `}
def bridge_im_fact_unique : blind_im_fact_unique
  ≔ bridge9_op_transport bridge9_S_imfact_equiv bridge9_img_op bridge9_img_op_path bridge9_our_imfact_equiv

{` A left inverse of an equivalence is also a right inverse. `}
def bridge9_section_of_retraction (A B : Type) (e : A → B) (he : BookIsEquiv A B e) (c : B → A)
  (s : (a : A) → Id A (c (e a)) a) (b : B) : Id B (e (c b)) b
  ≔ let a0 ≔ he b .center .fst in let q ≔ he b .center .snd in
    concat B (e (c b)) (e (c (e a0))) b
      (refl ((y ↦ e (c y)) : B → B) q)
      (concat B (e (c (e a0))) (e a0) b (refl e (s a0)) (inverse B b (e a0) q))

def bridge9_S_imfact_inverse (o : bridge9_ImgOpM) : Type
  ≔ (G H : Group) (hp : (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst))
    → Product ((f : GroupHom G H) → Id (GroupHom G H) (blind_epimono_compose G H (bridge9_imfact_of o G H hp f)) f)
        ((t : BlindEpiMonoPullback G H) → Id (BlindEpiMonoPullback G H) (bridge9_imfact_of o G H hp (blind_epimono_compose G H t)) t)

def bridge9_our_compose_imfact (G H : Group)
  (hp : (f : GroupHom G H) → IsGroupEpi G (image_group G H f) (image_projection G H f)) (f : GroupHom G H)
  : Id (GroupHom G H) (blind_epimono_compose G H (bridge9_imfact_of bridge9_our_op G H hp f)) f
  ≔ let I ≔ image_group G H f in let p ≔ image_projection G H f in let i ≔ image_inclusion G H f in
    let c ≔ group_hom_compose in
    calc
      c G I H (c G I I p (group_path_iso_equiv I I .map (refl I) .fst)) i
      = c G I H (c G I I p (group_hom_id I)) i
        by refl ((x ↦ c G I H (c G I I p x) i) : GroupHom I I → GroupHom G H) (group_path_iso_refl_hom I)
      = c G I H p i by refl ((x ↦ c G I H x i) : GroupHom G I → GroupHom G H) (group_hom_compose_id G I p)
      = f by inverse (GroupHom G H) f (c G I H p i) (image_factorization_path G H f) ∎

def bridge9_our_imfact_inverse : bridge9_S_imfact_inverse bridge9_our_op
  ≔ G H hp ↦
    (bridge9_our_compose_imfact G H hp,
     bridge9_section_of_retraction (GroupHom G H) (BlindEpiMonoPullback G H) (bridge9_imfact_of bridge9_our_op G H hp)
       (bridge9_our_imfact_equiv G H hp) (blind_epimono_compose G H) (bridge9_our_compose_imfact G H hp))

def bridge_im_fact_inverse : blind_im_fact_inverse
  ≔ bridge9_op_transport bridge9_S_imfact_inverse bridge9_img_op bridge9_img_op_path bridge9_our_imfact_inverse

{` def:image. `}
def bridge_def_image_mono (G H : Group) (f : GroupHom G H) : Id (GroupMonos H) (blind_img G H f) (image_mono G H f)
  ≔ refl ((o ↦ ((o .fst G H f .fst, (o .fst G H f .snd .snd, o .snd G H f)) : GroupMonos H)) : bridge9_ImgOpM → GroupMonos H)
      bridge9_aut_op_path

def bridge9_S_prjim (o : bridge9_ImgOpM) : Type
  ≔ (hp : (G H : Group) (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst))
    (G H : Group) (f : GroupHom G H)
    → Id (GroupEpis G) (o .fst G H f .fst, (o .fst G H f .snd .fst, hp G H f)) (image_epi_projection G H f)

def bridge_def_prjim : bridge9_S_prjim bridge9_aut_op
  ≔ bridge9_op_transport bridge9_S_prjim bridge9_aut_op bridge9_aut_op_path
      (hp G H f ↦ chim_epis_path G (image_group G H f, (image_projection G H f, hp G H f)) (image_epi_projection G H f)
         (refl ((image_group G H f, image_projection G H f) : HomsFrom G)))

def bridge_image_defs_agree : blind_image_defs_agree
  ≔ G H f ↦ concat Group (BlindImg G H f) (image_group G H f) (BlindImage G H f)
      (bridge_def_Img G H f)
      (inverse Group (BlindImage G H f) (image_group G H f)
        (refl ((o ↦ o .fst G H f .fst) : bridge9_ImgOpM → Group) bridge9_aut_op_path))

def bridge_image_prj_epi : blind_image_prj_epi
  ≔ bridge9_op_transport bridge9_S_proj_epi bridge9_aut_op bridge9_aut_op_path (G H f ↦ eqmc_image_projection_epi G H f)

def bridge_image_factorizes : blind_image_factorizes
  ≔ bridge9_op_transport bridge9_S_factorizes bridge9_aut_op bridge9_aut_op_path (G H f ↦ image_factorization_path G H f)

{` ex:charsurinj. `}
def bridge9_S_charsurinj_epi (o : bridge9_ImgOpM) : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Product (BlindIff (IsGroupEpi G G' f) (Surjective (USym G) (USym G') (usym_hom G G' f)))
        (Product (BlindIff (IsGroupEpi G G' f) (BookIsContr (gset_underlying G' (cokernel G G' f))))
                 (BlindIff (IsGroupEpi G G' f) (IsGroupIso (o .fst G G' f .fst) G' (o .fst G G' f .snd .snd))))

def bridge_charsurinj_epi : blind_charsurinj_epi
  ≔ bridge9_op_transport bridge9_S_charsurinj_epi bridge9_aut_op bridge9_aut_op_path
      (G G' f ↦
        (bridge_iff_of_equiv (IsGroupEpi G G' f) (Surjective (USym G) (USym G') (usym_hom G G' f)) (chim_epi_usym_surjective_equiv G G' f),
         (bridge_iff_of_equiv (IsGroupEpi G G' f) (BookIsContr (gset_underlying G' (cokernel G G' f)))
            (eqmc_epi_cokernel_point_contractible_equiv G G' f),
          bridge_iff_of_equiv (IsGroupEpi G G' f) (IsGroupIso (image_group G G' f) G' (image_inclusion G G' f))
            (chim_epi_image_inclusion_iso_equiv G G' f))))

def bridge9_S_charsurinj_mono (o : bridge9_ImgOpM) : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Product (BlindIff (IsGroupMonomorphism G G' f) (IsEmbedding (USym G) (USym G') (usym_hom G G' f)))
        (Product (BlindIff (IsGroupMonomorphism G G' f) (IsTrivialGroup (kernel_group G G' f)))
          (Product (BlindIff (IsGroupMonomorphism G G' f) (IsCovering (BG G .carrier) (BG G' .carrier) (hom_function G G' f)))
                   (BlindIff (IsGroupMonomorphism G G' f) (IsGroupIso G (o .fst G G' f .fst) (o .fst G G' f .snd .fst)))))

def bridge_charsurinj_mono : blind_charsurinj_mono
  ≔ bridge9_op_transport bridge9_S_charsurinj_mono bridge9_aut_op bridge9_aut_op_path
      (G G' f ↦
        (bridge_iff_of_equiv (IsGroupMonomorphism G G' f) (IsGroupMono G G' f) (chim_mono_usym_injective_equiv G G' f),
         (bridge_iff_of_equiv (IsGroupMonomorphism G G' f) (IsTrivialMono G (kernel G G' f)) (chim_mono_kernel_trivial_equiv G G' f),
          (bridge_iff_of_equiv (IsGroupMonomorphism G G' f) (IsCovering (BG G .carrier) (BG G' .carrier) (hom_function G G' f))
             (chim_mono_covering_equiv G G' f),
           bridge_iff_of_equiv (IsGroupMonomorphism G G' f) (IsGroupIso G (image_group G G' f) (image_projection G G' f))
             (chim_mono_image_projection_iso_equiv G G' f)))))

{` Lemma at line 1045. Categorical monos to chapter 5 monos. `}
def bridge9_monos_of_categorical (H : Group) (t : GroupMonomorphismsInto H) : GroupMonos H
  ≔ (t .fst, (t .snd .fst, group_monomorphism_mono_equiv (t .fst) H (t .snd .fst) .map (t .snd .snd)))

def bridge9_S_composite_mono (o : bridge9_ImgOpM) : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let O1 ≔ o .fst G0 G1 f1 in let O2 ≔ o .fst G1 G2 f2 in
      let g ≔ group_hom_compose (O1 .fst) G1 (O2 .fst) (O1 .snd .snd) (O2 .snd .fst) in
      let Og ≔ o .fst (O1 .fst) (O2 .fst) g in
      let j ≔ group_hom_compose (Og .fst) (O2 .fst) G2 (Og .snd .snd) (O2 .snd .snd) in
      let f21 ≔ group_hom_compose G0 G1 G2 f1 f2 in
      Σ (IsGroupMono (Og .fst) G2 j) (m ↦
        Id (GroupMonos G2) (o .fst G0 G2 f21 .fst, (o .fst G0 G2 f21 .snd .snd, o .snd G0 G2 f21)) (Og .fst, (j, m)))

def bridge9_our_composite_mono : bridge9_S_composite_mono bridge9_our_op
  ≔ G0 G1 G2 f1 f2 ↦
    let f21 ≔ group_hom_compose G0 G1 G2 f1 f2 in
    let t ≔ chim_composite_factorization G0 G1 G2 f1 f2 .snd .fst in
    let a ≔ image_mono_categorical G0 G2 f21 in
    (bridge9_monos_of_categorical G2 t .snd .snd,
     concat (GroupMonos G2) (image_mono G0 G2 f21) (bridge9_monos_of_categorical G2 a) (bridge9_monos_of_categorical G2 t)
       (chim_monos_path G2 (image_mono G0 G2 f21) (bridge9_monos_of_categorical G2 a)
          (refl ((image_group G0 G2 f21, image_inclusion G0 G2 f21) : HomsInto G2)))
       (refl (bridge9_monos_of_categorical G2) (chim_composite_image_mono_path G0 G1 G2 f1 f2)))

def bridge_image_composite_mono : blind_image_composite_mono
  ≔ bridge9_op_transport bridge9_S_composite_mono bridge9_aut_op bridge9_aut_op_path bridge9_our_composite_mono

def bridge9_S_composite_epi (o : bridge9_ImgOpM) : Type
  ≔ (hp : (G H : Group) (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst))
    (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let O1 ≔ o .fst G0 G1 f1 in let O2 ≔ o .fst G1 G2 f2 in
      let g ≔ group_hom_compose (O1 .fst) G1 (O2 .fst) (O1 .snd .snd) (O2 .snd .fst) in
      let Og ≔ o .fst (O1 .fst) (O2 .fst) g in
      let q ≔ group_hom_compose G0 (O1 .fst) (Og .fst) (O1 .snd .fst) (Og .snd .fst) in
      let f21 ≔ group_hom_compose G0 G1 G2 f1 f2 in
      Σ (IsGroupEpi G0 (Og .fst) q) (e ↦
        Id (GroupEpis G0) (o .fst G0 G2 f21 .fst, (o .fst G0 G2 f21 .snd .fst, hp G0 G2 f21)) (Og .fst, (q, e)))

def bridge9_our_composite_epi : bridge9_S_composite_epi bridge9_our_op
  ≔ hp G0 G1 G2 f1 f2 ↦
    let f21 ≔ group_hom_compose G0 G1 G2 f1 f2 in
    let t ≔ chim_composite_factorization G0 G1 G2 f1 f2 .fst in
    (t .snd .snd,
     concat (GroupEpis G0) (image_group G0 G2 f21, (image_projection G0 G2 f21, hp G0 G2 f21)) (image_epi_projection G0 G2 f21) t
       (chim_epis_path G0 (image_group G0 G2 f21, (image_projection G0 G2 f21, hp G0 G2 f21)) (image_epi_projection G0 G2 f21)
          (refl ((image_group G0 G2 f21, image_projection G0 G2 f21) : HomsFrom G0)))
       (chim_composite_image_epi_path G0 G1 G2 f1 f2))

def bridge_image_composite_epi : blind_image_composite_epi
  ≔ bridge9_op_transport bridge9_S_composite_epi bridge9_aut_op bridge9_aut_op_path bridge9_our_composite_epi

{` lem:kerandcoker. `}
def bridge9_S_kerandcoker (o : bridge9_ImgOpM) : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Id (GroupMonos G) (kernel G (o .fst G G' f .fst) (o .fst G G' f .snd .fst)) (kernel G G' f)

def bridge_kerandcoker : blind_kerandcoker
  ≔ bridge9_op_transport bridge9_S_kerandcoker bridge9_aut_op bridge9_aut_op_path (G G' f ↦ chim_kernel_projection_path G G' f)

{` xca at line 1160: the identifications have ua(prj) / ua(incl)⁻¹ as group components (module 990). `}
def bridge9_S_mono_own (o : bridge9_ImgOpM) : Type
  ≔ (G' : Group) (m : GroupMonos G')
    → let O ≔ o .fst (m .fst) G' (m .snd .fst) in
      Σ (IsGroupIso (m .fst) (O .fst) (O .snd .fst)) (hiso ↦
      Σ (Id (GroupMonos G') m (O .fst, (O .snd .snd, o .snd (m .fst) G' (m .snd .fst)))) (e ↦
        Id (Id Group (m .fst) (O .fst)) (e .fst) (group_path_from_iso (m .fst) (O .fst) (O .snd .fst, hiso))))

def bridge9_our_mono_own : bridge9_S_mono_own bridge9_our_op ≔ G' m ↦ mono_image_ua_path G' m

def bridge_mono_is_own_image : blind_mono_is_own_image
  ≔ bridge9_op_transport bridge9_S_mono_own bridge9_aut_op bridge9_aut_op_path bridge9_our_mono_own

def bridge9_S_epi_own (o : bridge9_ImgOpM) : Type
  ≔ (hp : (G H : Group) (f : GroupHom G H) → IsGroupEpi G (o .fst G H f .fst) (o .fst G H f .snd .fst))
    (G : Group) (e0 : GroupEpis G)
    → let O ≔ o .fst G (e0 .fst) (e0 .snd .fst) in
      Σ (IsGroupIso (O .fst) (e0 .fst) (O .snd .snd)) (hiso ↦
      Σ (Id (GroupEpis G) e0 (O .fst, (O .snd .fst, hp G (e0 .fst) (e0 .snd .fst)))) (e ↦
        Id (Id Group (e0 .fst) (O .fst)) (e .fst)
          (inverse Group (O .fst) (e0 .fst) (group_path_from_iso (O .fst) (e0 .fst) (O .snd .snd, hiso)))))

def bridge9_our_epi_own : bridge9_S_epi_own bridge9_our_op
  ≔ hp G e0 ↦
    let G' ≔ e0 .fst in let f ≔ e0 .snd .fst in
    let I ≔ image_group G G' f in let p ≔ image_projection G G' f in let i ≔ image_inclusion G G' f in
    let hiso ≔ chim_epi_image_inclusion_iso G G' f (e0 .snd .snd) in
    (hiso,
     epis_ua_path G I G' (i, hiso) p (hp G G' f) f (e0 .snd .snd)
       (inverse (GroupHom G G') f (group_hom_compose G I G' p i) (image_factorization_path G G' f)))

def bridge_epi_is_own_image : blind_epi_is_own_image
  ≔ bridge9_op_transport bridge9_S_epi_own bridge9_aut_op bridge9_aut_op_path bridge9_our_epi_own
