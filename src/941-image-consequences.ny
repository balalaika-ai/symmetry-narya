export "940-image-factorization"
export "936-epi-mono-iso"
export "905-normal-quotient-equivalence"

{` Chapter 9 (subgroups.tex), sec:image, consequences of the image
   factorization: ex:charsurinj (line 1010), the lemma on images of
   composites (line 1045), lem:kerandcoker (line 1145) and the exercise at
   line 1160 (monos and epis are identified with their image inclusion /
   projection). Notation: I = Img(f), p = prj_img(f) (image_projection),
   i = incl_img(f) (image_inclusion), f = i ∘ p (image_factorization_path). `}

{` ex:charsurinj (1): f epi ⇔ USym f surjective ⇔ cokernel contractible ⇔
   incl_img(f) an isomorphism. The first two are module 934 and module 938;
   the last uses f = i ∘ p, xca:mono1st-epi2nd (module 900) and
   lem:epimonoiso (module 936). `}
def chim_epi_image_inclusion_iso (G H : Group) (f : GroupHom G H) (e : IsGroupEpi G H f)
  : IsGroupIso (image_group G H f) H (image_inclusion G H f)
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    gepi_mono_epi_iso I H i (eqmc_image_inclusion_monomorphism G H f)
      (group_epi_cancel G I H p i
        (transport (GroupHom G H) (IsGroupEpi G H) f (group_hom_compose G I H p i) (image_factorization_path G H f) e))

def chim_image_inclusion_iso_epi (G H : Group) (f : GroupHom G H)
  (h : IsGroupIso (image_group G H f) H (image_inclusion G H f)) : IsGroupEpi G H f
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    transport (GroupHom G H) (IsGroupEpi G H) (group_hom_compose G I H p i) f
      (inverse (GroupHom G H) f (group_hom_compose G I H p i) (image_factorization_path G H f))
      (group_epi_compose G I H p i (eqmc_image_projection_epi G H f) (gepi_iso_epi I H i h))

def chim_epi_image_inclusion_iso_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupEpi G H f) (IsGroupIso (image_group G H f) H (image_inclusion G H f))
  ≔ iff_equiv (IsGroupEpi G H f) (IsGroupIso (image_group G H f) H (image_inclusion G H f))
      (is_group_epi_prop G H f) (is_group_iso_prop (image_group G H f) H (image_inclusion G H f))
      (chim_epi_image_inclusion_iso G H f) (chim_image_inclusion_iso_epi G H f)

def chim_epi_usym_surjective_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupEpi G H f) (Surjective (USym G) (USym H) (usym_hom G H f))
  ≔ gepi_epi_usym_surjective_equiv G H f

def chim_epi_cokernel_contractible_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupEpi G H f) (EqmcCokernelContractible G H f)
  ≔ eqmc_epi_cokernel_contractible_equiv G H f

{` ex:charsurinj (2): f mono ⇔ USym f injective ⇔ kernel trivial ⇔ Bf a
   covering ⇔ prj_img(f) an isomorphism. `}
def chim_mono_image_projection_iso (G H : Group) (f : GroupHom G H) (m : IsGroupMonomorphism G H f)
  : IsGroupIso G (image_group G H f) (image_projection G H f)
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    gepi_mono_epi_iso G I p
      (group_monomorphism_cancel G I H p i
        (transport (GroupHom G H) (IsGroupMonomorphism G H) f (group_hom_compose G I H p i) (image_factorization_path G H f) m))
      (eqmc_image_projection_epi G H f)

def chim_image_projection_iso_mono (G H : Group) (f : GroupHom G H)
  (h : IsGroupIso G (image_group G H f) (image_projection G H f)) : IsGroupMonomorphism G H f
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    transport (GroupHom G H) (IsGroupMonomorphism G H) (group_hom_compose G I H p i) f
      (inverse (GroupHom G H) f (group_hom_compose G I H p i) (image_factorization_path G H f))
      (group_monomorphism_compose G I H p i (gepi_iso_mono G I p h) (eqmc_image_inclusion_monomorphism G H f))

def chim_mono_image_projection_iso_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsGroupIso G (image_group G H f) (image_projection G H f))
  ≔ iff_equiv (IsGroupMonomorphism G H f) (IsGroupIso G (image_group G H f) (image_projection G H f))
      (is_group_monomorphism_prop G H f) (is_group_iso_prop G (image_group G H f) (image_projection G H f))
      (chim_mono_image_projection_iso G H f) (chim_image_projection_iso_mono G H f)

def chim_mono_usym_injective_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsGroupMono G H f)
  ≔ group_monomorphism_mono_equiv G H f

def chim_mono_kernel_trivial_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsTrivialMono G (kernel G H f))
  ≔ eqmc_mono_kernel_trivial_equiv G H f

def chim_mono_covering_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ eqmc_mono_covering_equiv G H f

{` Paths in types of monos and epis from paths of the underlying pairs. `}
def chim_monos_path (G : Group) (m m' : GroupMonos G)
  (q : Id (HomsInto G) (m .fst, m .snd .fst) (m' .fst, m' .snd .fst)) : Id (GroupMonos G) m m'
  ≔ let S ≔ Σ (HomsInto G) (w ↦ IsGroupMono (w .fst) G (w .snd)) in
    refl ((s ↦ (s .fst .fst, (s .fst .snd, s .snd))) : S → GroupMonos G)
      (subtype_equal (HomsInto G) (w ↦ IsGroupMono (w .fst) G (w .snd)) (w ↦ is_group_mono_prop (w .fst) G (w .snd))
         ((m .fst, m .snd .fst), m .snd .snd) ((m' .fst, m' .snd .fst), m' .snd .snd) q)

def chim_monomorphisms_path (G : Group) (m m' : GroupMonomorphismsInto G)
  (q : Id (HomsInto G) (m .fst, m .snd .fst) (m' .fst, m' .snd .fst)) : Id (GroupMonomorphismsInto G) m m'
  ≔ let S ≔ Σ (HomsInto G) (w ↦ IsGroupMonomorphism (w .fst) G (w .snd)) in
    refl ((s ↦ (s .fst .fst, (s .fst .snd, s .snd))) : S → GroupMonomorphismsInto G)
      (subtype_equal (HomsInto G) (w ↦ IsGroupMonomorphism (w .fst) G (w .snd))
         (w ↦ is_group_monomorphism_prop (w .fst) G (w .snd))
         ((m .fst, m .snd .fst), m .snd .snd) ((m' .fst, m' .snd .fst), m' .snd .snd) q)

def chim_epis_path (G : Group) (e e' : GroupEpis G)
  (q : Id (HomsFrom G) (e .fst, e .snd .fst) (e' .fst, e' .snd .fst)) : Id (GroupEpis G) e e'
  ≔ let S ≔ Σ (HomsFrom G) (w ↦ IsGroupEpi G (w .fst) (w .snd)) in
    refl ((s ↦ (s .fst .fst, (s .fst .snd, s .snd))) : S → GroupEpis G)
      (subtype_equal (HomsFrom G) (w ↦ IsGroupEpi G (w .fst) (w .snd)) (w ↦ is_group_epi_prop G (w .fst) (w .snd))
         ((e .fst, e .snd .fst), e .snd .snd) ((e' .fst, e' .snd .fst), e' .snd .snd) q)

{` xca (line 1160): (1) for a monomorphism f : G → G',
   f = incl_img(f) in Mono(G') (the identification of G with Img(f) is the
   one induced by the isomorphism prj_img(f), by iso induction,
   homs_into_iso_path of module 905); (2) for an epimorphism f,
   f = prj_img(f) in Epi(G). `}
def chim_mono_image_path (G H : Group) (f : GroupHom G H) (m : IsGroupMonomorphism G H f)
  : Id (GroupMonomorphismsInto H) (G, (f, m)) (image_mono_categorical G H f)
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    chim_monomorphisms_path H (G, (f, m)) (image_mono_categorical G H f)
      (concat (HomsInto H) (G, f) (G, group_hom_compose G I H p i) (I, i)
         (refl ((k ↦ (G, k)) : GroupHom G H → HomsInto H) (image_factorization_path G H f))
         (homs_into_iso_path H G I (p, chim_mono_image_projection_iso G H f m) i))

def chim_epi_image_path (G H : Group) (f : GroupHom G H) (e : IsGroupEpi G H f)
  : Id (GroupEpis G) (H, (f, e)) (image_epi_projection G H f)
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    chim_epis_path G (H, (f, e)) (image_epi_projection G H f)
      (concat (HomsFrom G) (H, f) (H, group_hom_compose G I H p i) (I, p)
         (refl ((k ↦ (H, k)) : GroupHom G H → HomsFrom G) (image_factorization_path G H f))
         (inverse (HomsFrom G) (I, p) (H, group_hom_compose G I H p i)
            (homs_from_iso_path G I H p (i, chim_epi_image_inclusion_iso G H f e))))

{` Lemma at line 1045: images of composites. For f1 : G0 → G1, f2 : G1 → G2
   let g ≔ prj_img(f2) ∘ incl_img(f1) : Img(f1) → Img(f2). Then
   img(f2 f1) = (Img g, incl_img(f2) ∘ incl_img(g), !) in Mono(G2) and
   prjim(f2 f1) = (Img g, prj_img(g) ∘ prj_img(f1), !) in Epi(G0), by
   uniqueness of the image factorization (imfact_retract). `}
def chim_composite_factorization (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : EpiMonoFactorizations G0 G2
  ≔ let I1 ≔ image_group G0 G1 f1 in
    let I2 ≔ image_group G1 G2 f2 in
    let g ≔ group_hom_compose I1 G1 I2 (image_inclusion G0 G1 f1) (image_projection G1 G2 f2) in
    let Ig ≔ image_group I1 I2 g in
    ((Ig, (group_hom_compose G0 I1 Ig (image_projection G0 G1 f1) (image_projection I1 I2 g),
           group_epi_compose G0 I1 Ig (image_projection G0 G1 f1) (image_projection I1 I2 g)
             (eqmc_image_projection_epi G0 G1 f1) (eqmc_image_projection_epi I1 I2 g))),
     ((Ig, (group_hom_compose Ig I2 G2 (image_inclusion I1 I2 g) (image_inclusion G1 G2 f2),
            group_monomorphism_compose Ig I2 G2 (image_inclusion I1 I2 g) (image_inclusion G1 G2 f2)
              (eqmc_image_inclusion_monomorphism I1 I2 g) (eqmc_image_inclusion_monomorphism G1 G2 f2))),
      refl Ig))

def chim_composite_factorization_compose (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom G0 G2) (imfact_compose G0 G2 (chim_composite_factorization G0 G1 G2 f1 f2)) (group_hom_compose G0 G1 G2 f1 f2)
  ≔ let I1 ≔ image_group G0 G1 f1 in
    let I2 ≔ image_group G1 G2 f2 in
    let p1 ≔ image_projection G0 G1 f1 in let i1 ≔ image_inclusion G0 G1 f1 in
    let p2 ≔ image_projection G1 G2 f2 in let i2 ≔ image_inclusion G1 G2 f2 in
    let g ≔ group_hom_compose I1 G1 I2 i1 p2 in
    let Ig ≔ image_group I1 I2 g in
    let pg ≔ image_projection I1 I2 g in let ig ≔ image_inclusion I1 I2 g in
    let c ≔ group_hom_compose in
    let H02 ≔ GroupHom G0 G2 in
    calc
      imfact_compose G0 G2 (chim_composite_factorization G0 G1 G2 f1 f2)
      = c G0 Ig G2 (c G0 I1 Ig p1 pg) (c Ig I2 G2 ig i2)
        by imfact_compose_refl_path G0 Ig G2 (c G0 I1 Ig p1 pg) (c Ig I2 G2 ig i2)
      = c G0 I1 G2 p1 (c I1 Ig G2 pg (c Ig I2 G2 ig i2)) by group_hom_compose_assoc G0 I1 Ig G2 p1 pg (c Ig I2 G2 ig i2)
      = c G0 I1 G2 p1 (c I1 I2 G2 (c I1 Ig I2 pg ig) i2)
        by refl (c G0 I1 G2 p1)
             (inverse (GroupHom I1 G2) (c I1 I2 G2 (c I1 Ig I2 pg ig) i2) (c I1 Ig G2 pg (c Ig I2 G2 ig i2))
                (group_hom_compose_assoc I1 Ig I2 G2 pg ig i2))
      = c G0 I1 G2 p1 (c I1 I2 G2 g i2)
        by refl ((x ↦ c G0 I1 G2 p1 (c I1 I2 G2 x i2)) : GroupHom I1 I2 → H02)
             (inverse (GroupHom I1 I2) g (c I1 Ig I2 pg ig) (image_factorization_path I1 I2 g))
      = c G0 I1 G2 p1 (c I1 G1 G2 i1 (c G1 I2 G2 p2 i2))
        by refl (c G0 I1 G2 p1) (group_hom_compose_assoc I1 G1 I2 G2 i1 p2 i2)
      = c G0 I1 G2 p1 (c I1 G1 G2 i1 f2)
        by refl ((x ↦ c G0 I1 G2 p1 (c I1 G1 G2 i1 x)) : GroupHom G1 G2 → H02)
             (inverse (GroupHom G1 G2) f2 (c G1 I2 G2 p2 i2) (image_factorization_path G1 G2 f2))
      = c G0 G1 G2 (c G0 I1 G1 p1 i1) f2
        by inverse H02 (c G0 G1 G2 (c G0 I1 G1 p1 i1) f2) (c G0 I1 G2 p1 (c I1 G1 G2 i1 f2))
             (group_hom_compose_assoc G0 I1 G1 G2 p1 i1 f2)
      = c G0 G1 G2 f1 f2
        by refl ((x ↦ c G0 G1 G2 x f2) : GroupHom G0 G1 → H02)
             (inverse (GroupHom G0 G1) f1 (c G0 I1 G1 p1 i1) (image_factorization_path G0 G1 f1)) ∎

def chim_composite_imfact_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (EpiMonoFactorizations G0 G2) (image_factorization_map G0 G2 (group_hom_compose G0 G1 G2 f1 f2))
      (chim_composite_factorization G0 G1 G2 f1 f2)
  ≔ let E ≔ EpiMonoFactorizations G0 G2 in
    let t ≔ chim_composite_factorization G0 G1 G2 f1 f2 in
    concat E (image_factorization_map G0 G2 (group_hom_compose G0 G1 G2 f1 f2))
      (image_factorization_map G0 G2 (imfact_compose G0 G2 t)) t
      (refl (image_factorization_map G0 G2)
         (inverse (GroupHom G0 G2) (imfact_compose G0 G2 t) (group_hom_compose G0 G1 G2 f1 f2)
            (chim_composite_factorization_compose G0 G1 G2 f1 f2)))
      (imfact_retract G0 G2 t)

def chim_composite_image_mono_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupMonomorphismsInto G2) (image_mono_categorical G0 G2 (group_hom_compose G0 G1 G2 f1 f2))
      (chim_composite_factorization G0 G1 G2 f1 f2 .snd .fst)
  ≔ refl ((u ↦ u .snd .fst) : EpiMonoFactorizations G0 G2 → GroupMonomorphismsInto G2)
      (chim_composite_imfact_path G0 G1 G2 f1 f2)

def chim_composite_image_epi_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupEpis G0) (image_epi_projection G0 G2 (group_hom_compose G0 G1 G2 f1 f2))
      (chim_composite_factorization G0 G1 G2 f1 f2 .fst)
  ≔ refl ((u ↦ u .fst) : EpiMonoFactorizations G0 G2 → GroupEpis G0) (chim_composite_imfact_path G0 G1 G2 f1 f2)

{` lem:kerandcoker: ker(prj_img(f)) = ker(f) in Mono(G). Deviation: the
   identification is obtained from the universal property of kernels
   (xca at line 409, module 938) and the uniqueness of mono-factorizations,
   not by writing out the map of preimages (Bp)⁻¹(sh) → (Bf)⁻¹(sh_H). `}
def chim_kernel_compose_trivial (G H : Group) (f : GroupHom G H)
  : Id (GroupHom (kernel_group G H f) H) (group_hom_compose (kernel_group G H f) G H (kernel_inclusion G H f) f)
      (EqmcTrivialHom (kernel_group G H f) H)
  ≔ let K ≔ kernel_group G H f in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    let fpt ≔ hom_point G H f in
    let sG ≔ shape G in
    ch9_hom_path K H (group_hom_compose K G H (kernel_inclusion G H f) f) (EqmcTrivialHom K H)
      ((u ↦ inverse B (shape H) (F (u .fst .fst)) (u .fst .snd)),
       calc
         concat B (shape H) (F sG) (shape H) (concat B (shape H) (F sG) (F sG) fpt (refl (F sG))) (inverse B (shape H) (F sG) fpt)
         = concat B (shape H) (F sG) (shape H) fpt (inverse B (shape H) (F sG) fpt)
           by refl ((x ↦ concat B (shape H) (F sG) (shape H) x (inverse B (shape H) (F sG) fpt)) : Id B (shape H) (F sG) → Id B (shape H) (shape H))
                (concat_p1 B (shape H) (F sG) fpt)
         = refl (shape H) by concat_inverse_right B (shape H) (F sG) fpt ∎)

def chim_trivial_postcompose (L M N : Group) (u : GroupHom M N)
  : Id (GroupHom L N) (group_hom_compose L M N (EqmcTrivialHom L M) u) (EqmcTrivialHom L N)
  ≔ let B ≔ BG N .carrier in
    let U ≔ hom_function M N u in
    let upt ≔ hom_point M N u in
    ch9_hom_path L N (group_hom_compose L M N (EqmcTrivialHom L M) u) (EqmcTrivialHom L N)
      ((_ ↦ inverse B (shape N) (U (shape M)) upt),
       calc
         concat B (shape N) (U (shape M)) (shape N) (concat B (shape N) (U (shape M)) (U (shape M)) upt (refl (U (shape M))))
           (inverse B (shape N) (U (shape M)) upt)
         = concat B (shape N) (U (shape M)) (shape N) upt (inverse B (shape N) (U (shape M)) upt)
           by refl ((x ↦ concat B (shape N) (U (shape M)) (shape N) x (inverse B (shape N) (U (shape M)) upt))
                    : Id B (shape N) (U (shape M)) → Id B (shape N) (shape N))
                (concat_p1 B (shape N) (U (shape M)) upt)
         = refl (shape N) by concat_inverse_right B (shape N) (U (shape M)) upt ∎)

def chim_mono_cancel (A B C : Group) (m : GroupHom B C) (hm : IsGroupMonomorphism B C m) (x y : GroupHom A B)
  (r : Id (GroupHom A C) (group_hom_compose A B C x m) (group_hom_compose A B C y m)) : Id (GroupHom A B) x y
  ≔ embedding_reflects_paths (GroupHom A B) (GroupHom A C) (k ↦ group_hom_compose A B C k m) (hm A) x y r

{` Two homomorphisms that are mutually inverse give an isomorphism. `}
def chim_inverse_homs_iso (A B : Group) (a : GroupHom A B) (b : GroupHom B A)
  (ab : Id (GroupHom A A) (group_hom_compose A B A a b) (group_hom_id A))
  (ba : Id (GroupHom B B) (group_hom_compose B A B b a) (group_hom_id B))
  : IsGroupIso A B a
  ≔ book_equivalence (BG A .carrier) (BG B .carrier)
      (quasi_inverse_equiv (BG A .carrier) (BG B .carrier) (hom_function A B a) (hom_function B A b)
        (group_hom_path_equiv A A (group_hom_compose A B A a b) (group_hom_id A) .map ab .fst)
        (group_hom_path_equiv B B (group_hom_compose B A B b a) (group_hom_id B) .map ba .fst)) .equiv

def chim_kernel_projection_path (G H : Group) (f : GroupHom G H)
  : Id (GroupMonos G) (kernel G (image_group G H f) (image_projection G H f)) (kernel G H f)
  ≔ let I ≔ image_group G H f in
    let p ≔ image_projection G H f in
    let i ≔ image_inclusion G H f in
    let Kp ≔ kernel_group G I p in
    let Kf ≔ kernel_group G H f in
    let ιp ≔ kernel_inclusion G I p in
    let ιf ≔ kernel_inclusion G H f in
    let c ≔ group_hom_compose in
    let mi ≔ eqmc_image_inclusion_monomorphism G H f in
    let mιp ≔ usym_injective_group_mono Kp G ιp (kernel_inclusion_mono G I p) in
    let mιf ≔ usym_injective_group_mono Kf G ιf (kernel_inclusion_mono G H f) in
    let r1 : Id (GroupHom Kp H) (c Kp G H ιp f) (EqmcTrivialHom Kp H)
      ≔ calc
          c Kp G H ιp f
          = c Kp G H ιp (c G I H p i) by refl (c Kp G H ιp) (image_factorization_path G H f)
          = c Kp I H (c Kp G I ιp p) i
            by inverse (GroupHom Kp H) (c Kp I H (c Kp G I ιp p) i) (c Kp G H ιp (c G I H p i))
                 (group_hom_compose_assoc Kp G I H ιp p i)
          = c Kp I H (EqmcTrivialHom Kp I) i
            by refl ((x ↦ c Kp I H x i) : GroupHom Kp I → GroupHom Kp H) (chim_kernel_compose_trivial G I p)
          = EqmcTrivialHom Kp H by chim_trivial_postcompose Kp I H i ∎ in
    let r2 : Id (GroupHom Kf I) (c Kf G I ιf p) (EqmcTrivialHom Kf I)
      ≔ chim_mono_cancel Kf I H i mi (c Kf G I ιf p) (EqmcTrivialHom Kf I)
          (calc
             c Kf I H (c Kf G I ιf p) i
             = c Kf G H ιf (c G I H p i) by group_hom_compose_assoc Kf G I H ιf p i
             = c Kf G H ιf f
               by refl (c Kf G H ιf) (inverse (GroupHom G H) f (c G I H p i) (image_factorization_path G H f))
             = EqmcTrivialHom Kf H by chim_kernel_compose_trivial G H f
             = c Kf I H (EqmcTrivialHom Kf I) i
               by inverse (GroupHom Kf H) (c Kf I H (EqmcTrivialHom Kf I) i) (EqmcTrivialHom Kf H)
                    (chim_trivial_postcompose Kf I H i) ∎) in
    let la ≔ eqmc_kernel_lift G H f Kp ιp r1 in
    let lb ≔ eqmc_kernel_lift G I p Kf ιf r2 in
    let a ≔ la .fst in
    let b ≔ lb .fst in
    let ab : Id (GroupHom Kp Kp) (c Kp Kf Kp a b) (group_hom_id Kp)
      ≔ chim_mono_cancel Kp Kp G ιp mιp (c Kp Kf Kp a b) (group_hom_id Kp)
          (calc
             c Kp Kp G (c Kp Kf Kp a b) ιp
             = c Kp Kf G a (c Kf Kp G b ιp) by group_hom_compose_assoc Kp Kf Kp G a b ιp
             = c Kp Kf G a ιf by refl (c Kp Kf G a) (inverse (GroupHom Kf G) ιf (c Kf Kp G b ιp) (lb .snd))
             = ιp by inverse (GroupHom Kp G) ιp (c Kp Kf G a ιf) (la .snd)
             = c Kp Kp G (group_hom_id Kp) ιp
               by inverse (GroupHom Kp G) (c Kp Kp G (group_hom_id Kp) ιp) ιp (group_hom_id_compose Kp G ιp) ∎) in
    let ba : Id (GroupHom Kf Kf) (c Kf Kp Kf b a) (group_hom_id Kf)
      ≔ chim_mono_cancel Kf Kf G ιf mιf (c Kf Kp Kf b a) (group_hom_id Kf)
          (calc
             c Kf Kf G (c Kf Kp Kf b a) ιf
             = c Kf Kp G b (c Kp Kf G a ιf) by group_hom_compose_assoc Kf Kp Kf G b a ιf
             = c Kf Kp G b ιp by refl (c Kf Kp G b) (inverse (GroupHom Kp G) ιp (c Kp Kf G a ιf) (la .snd))
             = ιf by inverse (GroupHom Kf G) ιf (c Kf Kp G b ιp) (lb .snd)
             = c Kf Kf G (group_hom_id Kf) ιf
               by inverse (GroupHom Kf G) (c Kf Kf G (group_hom_id Kf) ιf) ιf (group_hom_id_compose Kf G ιf) ∎) in
    chim_monos_path G (kernel G I p) (kernel G H f)
      (concat (HomsInto G) (Kp, ιp) (Kp, c Kp Kf G a ιf) (Kf, ιf)
         (refl ((k ↦ (Kp, k)) : GroupHom Kp G → HomsInto G) (la .snd))
         (homs_into_iso_path G Kp Kf (a, chim_inverse_homs_iso Kp Kf a b ab ba) ιf))
