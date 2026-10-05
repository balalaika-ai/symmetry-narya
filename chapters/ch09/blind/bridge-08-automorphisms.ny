export "bridge-00-core"
export "08-automorphisms"
export "../../../src/957-outer-automorphisms-simple"
export "../../../src/992-conjugate-counterexamples"

{` Bridges for subgroups.tex, sec:aut-group (blind file 08-automorphisms). `}

{` Remark (subgroups.tex:1887): the blind iso is ours (automorphism_group_usym_equiv .map is the first projection). `}
def bridge_def_inn_iso (G : Group) (g : USym G) : Id (GroupIso G G) (blind_inn_iso G g) (inn_symmetry_iso G g)
  ≔ refl (inn_symmetry_iso G g)

{` The printed formula h ↦ g⁻¹hg is FALSE for our (= the blind) inn: USym(USym inn(g)) is h ↦ g h g⁻¹
   (inn_usym_usym). Refuted in src (module 992, inn_usym_printed is blind_usym_inn by definition): Σ_3, g = (0 1 2),
   h = (0 1). `}
def bridge_usym_inn_refuted : Not blind_usym_inn ≔ inn_usym_printed_refuted

{` The corrected statement (ours): USym(USym inn(g)) is h ↦ g h g⁻¹. `}
def bridge_usym_inn_corrected (G : Group) (g h : USym G)
  : Id (USym G) (usym_hom G G (blind_inn_iso G g .fst) h) (usym_mul G (usym_mul G g h) (usym_inv G g))
  ≔ inn_usym_usym G g h

{` Definition (subgroups.tex:1938) and lemma:coker-out-action. `}
def bridge_def_out (G : Group) : Id (GSet (group_aut G)) (blind_out G) (outer_gset G) ≔ refl (outer_gset G)

def bridge_def_out_family (G : Group) : Id (GSet (group_aut G)) (blind_out_family G) (outer_paths_gset G)
  ≔ refl (outer_paths_gset G)

def bridge_coker_out_action : blind_coker_out_action ≔ G ↦ outer_gset_path G

{` Definition (subgroups.tex:1956): the blind Inn(G) is def:image's form, ours def:Im(grphom)'s. `}
def bridge_def_inn (G : Group) : Id Group (BlindInn G) (inner_aut_group G) ≔ image_group_aut_path G (group_aut G) (inn G)

def bridge_Inn_classifying : blind_Inn_classifying
  ≔ G ↦
    let X ≔ ActionType (group_aut G) (cokernel G (group_aut G) (inn G)) in
    let x : X ≔ (shape (group_aut G), cokernel_point G (group_aut G) (inn G)) in
    let T ≔ Σ Group (H ↦ SetTrunc (Id Type (BG H .carrier) (BG G .carrier))) in
    book_equivalence (NativeComponent X x) T
      (compose_equiv (NativeComponent X x) X T
        (ch9_component_equiv X x (cokernel_action_type_connected G (group_aut G) (inn G)))
        (inner_aut_classifying_equiv_group G))

{` The blind img(f) (def:image form) and our image_mono agree in Mono(H). `}
def bridge9w_image_iso (G H : Group) (f : GroupHom G H) : GroupIso (BlindImage G H f) (image_group G H f)
  ≔ let X ≔ ActionType H (cokernel G H f) in let x : X ≔ (shape H, cokernel_point G H f) in
    (mkhom (BlindImage G H f) (image_group G H f) ((u ↦ u .fst), refl x),
     book_equivalence (NativeComponent X x) X (ch9_component_equiv X x (cokernel_action_type_connected G H f)) .equiv)

def bridge9w_img_path (G H : Group) (f : GroupHom G H) : Id (GroupMonos H) (blind_img G H f) (image_mono G H f)
  ≔ ch9w2_monos_path_from_iso H (BlindImage G H f) (image_group G H f) (bridge9w_image_iso G H f)
      (blind_image_incl G H f) (blind_image_incl_mono G H f) (image_inclusion G H f) (image_inclusion_mono G H f)
      (refl (mkhom (BlindImage G H f) H)
        ((refl ((u ↦ u .fst .fst) : BG (BlindImage G H f) .carrier → BG H .carrier),
          concat_1p (BG H .carrier) (shape H) (shape H) (refl (shape H)))
         : Id (BookPointedMap (BG (BlindImage G H f)) (BG H))
             (book_pointed_compose (BG (BlindImage G H f)) (BG (image_group G H f)) (BG H)
               (hom_B (BlindImage G H f) (image_group G H f) (bridge9w_image_iso G H f .fst))
               (hom_B (image_group G H f) H (image_inclusion G H f)))
             (hom_B (BlindImage G H f) H (blind_image_incl G H f))))

def bridge9w_inner_normal_blind_path (G : Group)
  : Id (Subgroups (group_aut G)) (normal_to_subgroup (group_aut G) (inner_normal G))
      (mono_to_subgroup (group_aut G) (blind_img G (group_aut G) (inn G)))
  ≔ let A ≔ group_aut G in
    concat (Subgroups A) (normal_to_subgroup A (inner_normal G)) (mono_to_subgroup A (image_mono G A (inn G)))
      (mono_to_subgroup A (blind_img G A (inn G)))
      (inner_normal_path G)
      (refl (mono_to_subgroup A)
        (inverse (GroupMonos A) (blind_img G A (inn G)) (image_mono G A (inn G)) (bridge9w_img_path G A (inn G))))

{` Lemma (subgroups.tex:1967). `}
def bridge_Inn_normal : blind_Inn_normal ≔ G ↦ (inner_normal G, bridge9w_inner_normal_blind_path G)

{` Definition (subgroups.tex:2001): both forms of Out(G). `}
def bridge_def_out_group (G : Group) : Id Group (BlindOut G) (outer_aut_group G) ≔ refl (outer_aut_group G)

def bridge_Out_is_quotient : blind_Out_is_quotient
  ≔ G N e ↦
    let A ≔ group_aut G in
    let pN : Id (NormalSubgroups A) N (inner_normal G)
      ≔ invariant_maps_eq_at_shape A (subgroups_gset A) N (inner_normal G)
          (concat (Subgroups A) (normal_to_subgroup A N) (mono_to_subgroup A (blind_img G A (inn G)))
            (normal_to_subgroup A (inner_normal G)) e
            (inverse (Subgroups A) (normal_to_subgroup A (inner_normal G)) (mono_to_subgroup A (blind_img G A (inn G)))
              (bridge9w_inner_normal_blind_path G))) in
    concat Group (normal_quotient_group A N) (normal_quotient_group A (inner_normal G)) (outer_aut_group G)
      (refl (normal_quotient_group A) pN) (outer_aut_group_quotient_path G)

{` cons:simpler-version-Out. `}
def bridge_def_aut_one_trunc (G : Group) : Id Group (BlindAutOneTrunc G) (outer_simple_group G) ≔ refl (outer_simple_group G)

def bridge_simpler_version_Out : blind_simpler_version_Out ≔ G ↦ outer_simple_path G

{` ‖a = b‖₀ ≃ (|a|₁ = |b|₁) for any type (module 957's universe_one_trunc_paths with A in place of U). `}
def bridge9w_one_trunc_paths (A : Type) (a b : A)
  : Equiv (SetTrunc (Id A a b)) (Id (Trunc (suc. (suc. zero.)) A) (trunc_unit (suc. (suc. zero.)) A a) (trunc_unit (suc. (suc. zero.)) A b))
  ≔ compose_equiv (SetTrunc (Id A a b)) (Trunc (suc. zero.) (Id A a b))
      (Id (Trunc (suc. (suc. zero.)) A) (trunc_unit (suc. (suc. zero.)) A a) (trunc_unit (suc. (suc. zero.)) A b))
      (canonical_inverse_equiv (Trunc (suc. zero.) (Id A a b)) (SetTrunc (Id A a b)) (trunc_one_set_trunc_equiv (Id A a b)))
      (trunc_path_equiv (suc. zero.) A a b)

def bridge_one_trunc_paths : blind_one_trunc_paths
  ≔ A a b ↦ book_equivalence (SetTrunc (Id A a b))
      (Id (Trunc (suc. (suc. zero.)) A) (trunc_unit (suc. (suc. zero.)) A a) (trunc_unit (suc. (suc. zero.)) A b))
      (bridge9w_one_trunc_paths A a b)

def bridge_one_trunc_components : blind_one_trunc_components
  ≔ X Y ↦
    let T ≔ Id (Trunc (suc. (suc. zero.)) Type) (trunc_unit (suc. (suc. zero.)) Type X) (trunc_unit (suc. (suc. zero.)) Type Y) in
    let P ≔ Id Type X Y in
    let e ≔ bridge9w_one_trunc_paths Type X Y in
    (mere_rec T (Mere P) (mere_isprop P)
       (t ↦ set_trunc_rec P (Mere P) (prop_is_set (Mere P) (mere_isprop P)) (mere P) (equiv_inverse_map (SetTrunc P) T e t)),
     mere_rec P (Mere T) (mere_isprop T) (p ↦ mere T (e .map (set_trunc P p))))
