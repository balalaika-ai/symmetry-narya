export "941-image-consequences"
export "955-inner-automorphisms-kernel"

{` Chapter 9 (subgroups.tex), xca at line 1160: the book asks for
   the specific identifications ua(prj_img(f)) : (G, f, !) = img(f) in Mono(G') and ua(incl_img(f)) in Epi(G);
   module 941 (chim_mono_image_path, chim_epi_image_path) gives some identification. Here the group component is
   pinned down. Needs ptoe(refl) = id for the univalence map of groups (group_path_iso_refl_hom, from module 955's
   computation of pointed univalence at reflexivity). `}

{` ptoe(refl_Z) = id_Z. `}
def group_path_iso_refl_hom (Z : Group)
  : Id (GroupHom Z Z) (group_path_iso_equiv Z Z .map (refl Z) .fst) (group_hom_id Z)
  ≔ let X ≔ BG Z .carrier in let x ≔ shape Z in
    concat (GroupHom Z Z) (group_path_iso_equiv Z Z .map (refl Z) .fst) (conj_hom Z x (refl x)) (group_hom_id Z)
      (inn_ap_iso_hom Z x (refl x))
      (ch9_hom_path Z Z (conj_hom Z x (refl x)) (group_hom_id Z)
        ((z ↦ refl z),
         concat (Id X x x) (concat X x x x (inverse X x x (refl x)) (refl x)) (inverse X x x (refl x)) (refl x)
           (concat_p1 X x x (inverse X x x (refl x))) (inverse_refl X x)))

def monos_ua_motive (G' Z : Group) (i : GroupHom Z G') (m : IsGroupMono Z G' i) (Z' : Group) (α : Id Group Z Z') : Type
  ≔ (i' : GroupHom Z' G') (m' : IsGroupMono Z' G' i')
    → Id (GroupHom Z G') (group_hom_compose Z Z' G' (group_path_iso_equiv Z Z' .map α .fst) i') i
    → Σ (Id (GroupMonos G') (Z, (i, m)) (Z', (i', m'))) (e ↦ Id (Id Group Z Z') (e .fst) α)

{` If i = i' ∘ Q for an isomorphism Q : Z ≅ Z', then (Z, i, !) = (Z', i', !) in Mono(G') with group component
   ua(Q). `}
def monos_ua_path (G' Z Z' : Group) (Q : GroupIso Z Z') (i : GroupHom Z G') (m : IsGroupMono Z G' i)
  (i' : GroupHom Z' G') (m' : IsGroupMono Z' G' i')
  (c : Id (GroupHom Z G') (group_hom_compose Z Z' G' (Q .fst) i') i)
  : Σ (Id (GroupMonos G') (Z, (i, m)) (Z', (i', m'))) (e ↦ Id (Id Group Z Z') (e .fst) (group_path_from_iso Z Z' Q))
  ≔ let α ≔ group_path_from_iso Z Z' Q in
    let E ≔ group_path_iso_equiv Z Z' in
    J Group Z (monos_ua_motive G' Z i m)
      (i0 m0 c0 ↦
        let r : Id (GroupHom Z G') i i0
          ≔ calc
              i = group_hom_compose Z Z G' (group_path_iso_equiv Z Z .map (refl Z) .fst) i0
                by inverse (GroupHom Z G') (group_hom_compose Z Z G' (group_path_iso_equiv Z Z .map (refl Z) .fst) i0) i c0
              = group_hom_compose Z Z G' (group_hom_id Z) i0
                by refl ((x ↦ group_hom_compose Z Z G' x i0) : GroupHom Z Z → GroupHom Z G') (group_path_iso_refl_hom Z)
              = i0 by group_hom_id_compose Z G' i0 ∎ in
        ((refl Z, subtype_equal (GroupHom Z G') (IsGroupMono Z G') (is_group_mono_prop Z G') (i, m) (i0, m0) r),
         refl (refl Z)))
      Z' α i' m'
      (transport (GroupIso Z Z') (R ↦ Id (GroupHom Z G') (group_hom_compose Z Z' G' (R .fst) i') i)
         Q (E .map α) (inverse (GroupIso Z Z') (E .map α) Q (equiv_counit (Id Group Z Z') (GroupIso Z Z') E Q)) c)

def epis_ua_motive (G Z : Group) (p : GroupHom G Z) (e : IsGroupEpi G Z p) (Z' : Group) (α : Id Group Z Z') : Type
  ≔ (p' : GroupHom G Z') (e' : IsGroupEpi G Z' p')
    → Id (GroupHom G Z') (group_hom_compose G Z Z' p (group_path_iso_equiv Z Z' .map α .fst)) p'
    → Σ (Id (GroupEpis G) (Z', (p', e')) (Z, (p, e))) (ε ↦ Id (Id Group Z' Z) (ε .fst) (inverse Group Z Z' α))

{` If p' = Q ∘ p for an isomorphism Q : Z ≅ Z', then (Z', p', !) = (Z, p, !) in Epi(G) with group component
   ua(Q)⁻¹. `}
def epis_ua_path (G Z Z' : Group) (Q : GroupIso Z Z') (p : GroupHom G Z) (e : IsGroupEpi G Z p)
  (p' : GroupHom G Z') (e' : IsGroupEpi G Z' p')
  (c : Id (GroupHom G Z') (group_hom_compose G Z Z' p (Q .fst)) p')
  : Σ (Id (GroupEpis G) (Z', (p', e')) (Z, (p, e))) (ε ↦ Id (Id Group Z' Z) (ε .fst) (inverse Group Z Z' (group_path_from_iso Z Z' Q)))
  ≔ let α ≔ group_path_from_iso Z Z' Q in
    let E ≔ group_path_iso_equiv Z Z' in
    J Group Z (epis_ua_motive G Z p e)
      (p0 e0 c0 ↦
        let r : Id (GroupHom G Z) p0 p
          ≔ calc
              p0 = group_hom_compose G Z Z p (group_path_iso_equiv Z Z .map (refl Z) .fst)
                by inverse (GroupHom G Z) (group_hom_compose G Z Z p (group_path_iso_equiv Z Z .map (refl Z) .fst)) p0 c0
              = group_hom_compose G Z Z p (group_hom_id Z)
                by refl (group_hom_compose G Z Z p) (group_path_iso_refl_hom Z)
              = p by group_hom_compose_id G Z p ∎ in
        ((refl Z, subtype_equal (GroupHom G Z) (IsGroupEpi G Z) (is_group_epi_prop G Z) (p0, e0) (p, e) r),
         inverse (Id Group Z Z) (inverse Group Z Z (refl Z)) (refl Z) (inverse_refl Group Z)))
      Z' α p' e'
      (transport (GroupIso Z Z') (R ↦ Id (GroupHom G Z') (group_hom_compose G Z Z' p (R .fst)) p')
         Q (E .map α) (inverse (GroupIso Z Z') (E .map α) Q (equiv_counit (Id Group Z Z') (GroupIso Z Z') E Q)) c)

{` xca at line 1160 (1): for a monomorphism (G, f, !) : Mono(G'), ua(prj_img(f)) : (G, f, !) = img(f). `}
def mono_image_ua_path (G' : Group) (m : GroupMonos G')
  : Σ (IsGroupIso (m .fst) (image_group (m .fst) G' (m .snd .fst)) (image_projection (m .fst) G' (m .snd .fst))) (hiso ↦
    Σ (Id (GroupMonos G') m (image_mono (m .fst) G' (m .snd .fst))) (e ↦
      Id (Id Group (m .fst) (image_group (m .fst) G' (m .snd .fst))) (e .fst)
        (group_path_from_iso (m .fst) (image_group (m .fst) G' (m .snd .fst)) (image_projection (m .fst) G' (m .snd .fst), hiso))))
  ≔ let G ≔ m .fst in let f ≔ m .snd .fst in
    let I ≔ image_group G G' f in let p ≔ image_projection G G' f in let i ≔ image_inclusion G G' f in
    let hiso ≔ chim_mono_image_projection_iso G G' f (usym_injective_group_mono G G' f (m .snd .snd)) in
    (hiso,
     monos_ua_path G' G I (p, hiso) f (m .snd .snd) i (image_inclusion_mono G G' f)
       (inverse (GroupHom G G') f (group_hom_compose G I G' p i) (image_factorization_path G G' f)))

{` xca at line 1160 (2): for an epimorphism (G', f, !) : Epi(G), ua(incl_img(f))⁻¹ : (G', f, !) = prjim(f). `}
def epi_image_ua_path (G : Group) (e0 : GroupEpis G)
  : Σ (IsGroupIso (image_group G (e0 .fst) (e0 .snd .fst)) (e0 .fst) (image_inclusion G (e0 .fst) (e0 .snd .fst))) (hiso ↦
    Σ (Id (GroupEpis G) e0 (image_epi_projection G (e0 .fst) (e0 .snd .fst))) (e ↦
      Id (Id Group (e0 .fst) (image_group G (e0 .fst) (e0 .snd .fst))) (e .fst)
        (inverse Group (image_group G (e0 .fst) (e0 .snd .fst)) (e0 .fst)
          (group_path_from_iso (image_group G (e0 .fst) (e0 .snd .fst)) (e0 .fst) (image_inclusion G (e0 .fst) (e0 .snd .fst), hiso)))))
  ≔ let G' ≔ e0 .fst in let f ≔ e0 .snd .fst in
    let I ≔ image_group G G' f in let p ≔ image_projection G G' f in let i ≔ image_inclusion G G' f in
    let hiso ≔ chim_epi_image_inclusion_iso G G' f (e0 .snd .snd) in
    (hiso,
     epis_ua_path G I G' (i, hiso) p (eqmc_image_projection_epi G G' f) f (e0 .snd .snd)
       (inverse (GroupHom G G') f (group_hom_compose G I G' p i) (image_factorization_path G G' f)))
