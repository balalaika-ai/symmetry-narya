export "802-semidirect-symmetries"
export "503-orbits-and-stabilizers"

{` Chapter 8 (congp.tex), the unlabeled lemma at line 291: the
   homomorphism j : H(sh_G) → G ⋉ H is a monomorphism and gives the same
   subgroup of G ⋉ H as the kernel of p : G ⋉ H → G.

   Monomorphisms are those of def:typeofmono (IsGroupMono, module 502:
   USym i is an injection; module 687 shows that these are the
   monomorphisms of the category of groups), and "the same subgroup" is an
   identification in the type GroupMonos(G ⋉ H) of monomorphisms into
   G ⋉ H. The kernel is chapter 9's def:kernel (subgroups.tex:289), which
   has no module yet; it is defined here locally (fiber_kernel_*) and may
   be superseded by chapter 9. The parenthetical "(normal)" (normality of
   kernels, def:normalsubgroup) is a chapter-9 notion and is not
   formalized here. `}

{` def:kernel (subgroups.tex:289). For f : Hom(G, G'), the preimage
   (Bf)⁻¹(sh_{G'}) ≔ Σ_{z:BG} (sh_{G'} = Bf(z)) (BookFiber), a groupoid,
   pointed at (sh_G, Bf_pt); Ker(f) ≔ Aut_{(Bf)⁻¹(sh_{G'})}(sh_G, Bf_pt),
   with ker(f) the first projection BKer(f) → BG (a covering, hence a
   monomorphism). `}
def fiber_kernel_fiber (G G' : Group) (f : GroupHom G G') : Type
  ≔ BookFiber (BG G .carrier) (BG G' .carrier) (hom_function G G' f) (shape G')

def fiber_kernel_fiber_groupoid (G G' : Group) (f : GroupHom G G') : isGroupoid (fiber_kernel_fiber G G' f)
  ≔ hlevel_to_groupoid (fiber_kernel_fiber G G' f)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (BG G .carrier)
        (z ↦ Id (BG G' .carrier) (shape G') (hom_function G G' f z))
        (groupoid_to_hlevel (BG G .carrier) (bg_groupoid G))
        (z ↦ groupoid_to_hlevel (Id (BG G' .carrier) (shape G') (hom_function G G' f z))
          (set_is_groupoid (Id (BG G' .carrier) (shape G') (hom_function G G' f z))
            (bg_groupoid G' (shape G') (hom_function G G' f z)))))

def fiber_kernel_point (G G' : Group) (f : GroupHom G G') : fiber_kernel_fiber G G' f
  ≔ (shape G, hom_point G G' f)

def fiber_kernel_group (G G' : Group) (f : GroupHom G G') : Group
  ≔ automorphism_group (fiber_kernel_fiber G G' f) (fiber_kernel_fiber_groupoid G G' f) (fiber_kernel_point G G' f)

def fiber_kernel_inclusion (G G' : Group) (f : GroupHom G G') : GroupHom (fiber_kernel_group G G' f) G
  ≔ mkhom (fiber_kernel_group G G' f) G (v ↦ v .fst .fst, refl (shape G))

def fiber_kernel_inclusion_covering (G G' : Group) (f : GroupHom G G')
  : IsCovering (BG (fiber_kernel_group G G' f) .carrier) (BG G .carrier)
      (hom_function (fiber_kernel_group G G' f) G (fiber_kernel_inclusion G G' f))
  ≔ coverings_compose (NativeComponent (fiber_kernel_fiber G G' f) (fiber_kernel_point G G' f))
      (fiber_kernel_fiber G G' f) (BG G .carrier) (c ↦ c .fst) (u ↦ u .fst)
      (stabilizer_component_covering (fiber_kernel_fiber G G' f) (fiber_kernel_point G G' f))
      (setfamily_to_covering (BG G .carrier)
        (z ↦ (Id (BG G' .carrier) (shape G') (hom_function G G' f z),
              bg_groupoid G' (shape G') (hom_function G G' f z))) .snd)

def fiber_kernel_inclusion_mono (G G' : Group) (f : GroupHom G G')
  : IsGroupMono (fiber_kernel_group G G' f) G (fiber_kernel_inclusion G G' f)
  ≔ covering_group_mono (fiber_kernel_group G G' f) G (fiber_kernel_inclusion G G' f)
      (fiber_kernel_inclusion_covering G G' f)

{` ker(f) ≔ (Ker(f), the inclusion, !) : Mono(G). `}
def fiber_kernel (G G' : Group) (f : GroupHom G G') : GroupMonos G
  ≔ (fiber_kernel_group G G' f, (fiber_kernel_inclusion G G' f, fiber_kernel_inclusion_mono G G' f))

{` Identifications in Mono(L) from isomorphisms (the footnote of
   def:typeofmono: triples are identified when the homomorphisms differ by
   an identification of the underlying groups). The type of groups with
   an isomorphism from K is contractible (remark:groupsasunivalenttype). `}
def sdp_group_iso_total_contractible (K : Group) : isContr (Σ Group (K' ↦ GroupIso K K'))
  ≔ contractible_retract (Σ Group (K' ↦ Id Group K K')) (Σ Group (K' ↦ GroupIso K K'))
      (iscontr_idfrom Group K)
      (family_equiv Group (K' ↦ Id Group K K') (K' ↦ GroupIso K K') (K' ↦ group_path_iso_equiv K K') .map)
      (equiv_inverse_map (Σ Group (K' ↦ Id Group K K')) (Σ Group (K' ↦ GroupIso K K'))
        (family_equiv Group (K' ↦ Id Group K K') (K' ↦ GroupIso K K') (K' ↦ group_path_iso_equiv K K')))
      (equiv_counit (Σ Group (K' ↦ Id Group K K')) (Σ Group (K' ↦ GroupIso K K'))
        (family_equiv Group (K' ↦ Id Group K K') (K' ↦ GroupIso K K') (K' ↦ group_path_iso_equiv K K')))

def sdp_group_monos_path_base (L K : Group) (i : GroupHom K L) (m : IsGroupMono K L i)
  (i' : GroupHom K L) (m' : IsGroupMono K L i')
  (c : Id (GroupHom K L) (group_hom_compose K K L (group_hom_id K) i') i)
  : Id (GroupMonos L) (K, (i, m)) (K, (i', m'))
  ≔ (refl K,
     subtype_equal (GroupHom K L) (IsGroupMono K L) (is_group_mono_prop K L) (i, m) (i', m')
       (concat (GroupHom K L) i (group_hom_compose K K L (group_hom_id K) i') i'
         (inverse (GroupHom K L) (group_hom_compose K K L (group_hom_id K) i') i c)
         (group_hom_id_compose K L i')))

def sdp_group_monos_path_motive (L K : Group) (i : GroupHom K L) (m : IsGroupMono K L i)
  (u : Σ Group (K' ↦ GroupIso K K')) : Type
  ≔ (i' : GroupHom (u .fst) L) (m' : IsGroupMono (u .fst) L i')
      → Id (GroupHom K L) (group_hom_compose K (u .fst) L (u .snd .fst) i') i
      → Id (GroupMonos L) (K, (i, m)) (u .fst, (i', m'))

def sdp_group_monos_path_from_iso (L K K' : Group) (e : GroupIso K K') (i : GroupHom K L) (m : IsGroupMono K L i)
  (i' : GroupHom K' L) (m' : IsGroupMono K' L i')
  (c : Id (GroupHom K L) (group_hom_compose K K' L (e .fst) i') i)
  : Id (GroupMonos L) (K, (i, m)) (K', (i', m'))
  ≔ transport (Σ Group (K' ↦ GroupIso K K')) (sdp_group_monos_path_motive L K i m) (K, group_iso_id K) (K', e)
      (contractible_prop (Σ Group (K' ↦ GroupIso K K')) (sdp_group_iso_total_contractible K)
        (K, group_iso_id K) (K', e))
      (i' m' c ↦ sdp_group_monos_path_base L K i m i' m' c) i' m' c

{` The lemma, first part: j is a monomorphism. USym j(q) = (refl, q) up to
   conjugation by refl, and the second component of the bijection of
   lem:pathpairsection is a retraction of USym j. `}
def semidirect_inclusion_retraction (G : Group) (H : BG G .carrier → Group) (q : USym (H (shape G)))
  : Id (USym (H (shape G)))
      (semidirect_usym_pair G H (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q) .snd) q
  ≔ refl ((a ↦ a .snd) : Product (USym G) (USym (H (shape G))) → USym (H (shape G)))
      (semidirect_usym_pair_inclusion G H q)

def semidirect_inclusion_mono (G : Group) (H : BG G .carrier → Group)
  : IsGroupMono (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H)
  ≔ let K ≔ H (shape G) in
    let GH ≔ semidirect_product G H in
    let j ≔ semidirect_inclusion G H in
    path_reflecting_set_embedding (USym K) (USym GH) (usym_set GH) (usym_hom K GH j)
      (l l' s ↦ calc
        l = semidirect_usym_pair G H (usym_hom K GH j l) .snd
          by inverse (USym K) (semidirect_usym_pair G H (usym_hom K GH j l) .snd) l
               (semidirect_inclusion_retraction G H l)
        = semidirect_usym_pair G H (usym_hom K GH j l') .snd
          by refl ((e ↦ semidirect_usym_pair G H e .snd) : USym GH → USym K) s
        = l' by semidirect_inclusion_retraction G H l' ∎)

{` The proof of the lemma. By lem:fst-fiber(a)=B(a) the map
   BH(sh_G) → (Bp)⁻¹(sh_G), u ↦ ((sh_G, u), refl sh_G), is an equivalence;
   so the fiber is connected and serves as the classifying type of ker p. `}
def semidirect_kernel_fiber_equiv (G : Group) (H : BG G .carrier → Group)
  : BookEquiv (BG (H (shape G)) .carrier)
      (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
  ≔ book_projection_inclusion_equiv (BG G .carrier) (t ↦ BG (H t) .carrier) (shape G)

def semidirect_kernel_fiber_connected (G : Group) (H : BG G .carrier → Group)
  : Connected (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
  ≔ connected_equiv (BG (H (shape G)) .carrier) (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
      (native_equivalence (BG (H (shape G)) .carrier)
        (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
        (semidirect_kernel_fiber_equiv G H))
      .map (bg_connected (H (shape G)))

{` The isomorphism H(sh_G) ≅ Ker p: u ↦ ((sh_G, u), refl sh_G) in the
   component of the fiber (the truncated part from connectedness of BH). `}
def semidirect_kernel_iso_map (G : Group) (H : BG G .carrier → Group) (u : BG (H (shape G)) .carrier)
  : BG (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H)) .carrier
  ≔ let F ≔ fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H) in
    let b ≔ fiber_kernel_point (semidirect_product G H) G (semidirect_projection G H) in
    let K ≔ H (shape G) in
    (semidirect_kernel_fiber_equiv G H .map u,
     mere_rec (Id (BG K .carrier) (shape K) u) (Mere (Id F b (semidirect_kernel_fiber_equiv G H .map u)))
       (mere_isprop (Id F b (semidirect_kernel_fiber_equiv G H .map u)))
       (r ↦ mere (Id F b (semidirect_kernel_fiber_equiv G H .map u)) (refl (semidirect_kernel_fiber_equiv G H .map) r))
       (bg_connected K .snd (shape K) u))

def semidirect_kernel_iso_inverse (G : Group) (H : BG G .carrier → Group)
  (v : BG (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H)) .carrier)
  : BG (H (shape G)) .carrier
  ≔ equiv_inverse_map (BG (H (shape G)) .carrier) (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
      (native_equivalence (BG (H (shape G)) .carrier)
        (fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H))
        (semidirect_kernel_fiber_equiv G H))
      (v .fst)

def semidirect_kernel_iso_equiv (G : Group) (H : BG G .carrier → Group)
  : Equiv (BG (H (shape G)) .carrier)
      (BG (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H)) .carrier)
  ≔ let F ≔ fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H) in
    let b ≔ fiber_kernel_point (semidirect_product G H) G (semidirect_projection G H) in
    let BK ≔ BG (H (shape G)) .carrier in
    let e ≔ native_equivalence BK F (semidirect_kernel_fiber_equiv G H) in
    quasi_inverse_equiv BK (NativeComponent F b) (semidirect_kernel_iso_map G H) (semidirect_kernel_iso_inverse G H)
      (u ↦ equiv_retraction BK F e u)
      (v ↦ component_path F b (semidirect_kernel_iso_map G H (semidirect_kernel_iso_inverse G H v)) v
        (equiv_counit BK F e (v .fst)))

def semidirect_kernel_iso_hom (G : Group) (H : BG G .carrier → Group)
  : GroupHom (H (shape G)) (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
  ≔ let F ≔ fiber_kernel_fiber (semidirect_product G H) G (semidirect_projection G H) in
    let b ≔ fiber_kernel_point (semidirect_product G H) G (semidirect_projection G H) in
    mkhom (H (shape G)) (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
      (semidirect_kernel_iso_map G H,
       component_path F b (component_point F b) (semidirect_kernel_iso_map G H (shape (H (shape G)))) (refl b))

def semidirect_kernel_iso (G : Group) (H : BG G .carrier → Group)
  : GroupIso (H (shape G)) (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
  ≔ (semidirect_kernel_iso_hom G H,
     book_equivalence (BG (H (shape G)) .carrier)
       (BG (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H)) .carrier)
       (semidirect_kernel_iso_equiv G H) .equiv)

{` "The composite map H ≅ ker p → G ⋉ H is j": the underlying functions
   agree judgmentally, the pointing paths are concat refl refl and refl. `}
def semidirect_kernel_iso_inclusion (G : Group) (H : BG G .carrier → Group)
  : Id (GroupHom (H (shape G)) (semidirect_product G H))
      (group_hom_compose (H (shape G)) (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
        (semidirect_product G H) (semidirect_kernel_iso_hom G H)
        (fiber_kernel_inclusion (semidirect_product G H) G (semidirect_projection G H)))
      (semidirect_inclusion G H)
  ≔ (classifying_map ≔
      (refl ((u ↦ (shape G, u)) : BG (H (shape G)) .carrier → semidirect_classifying_type G H),
       concat_p1 (semidirect_classifying_type G H) (semidirect_shape G H) (semidirect_shape G H)
         (refl (semidirect_shape G H))))

{` The lemma at line 291: j is a monomorphism, and (H(sh_G), j) is the same
   monomorphism into G ⋉ H (the same subgroup) as ker p. `}
def semidirect_inclusion_kernel (G : Group) (H : BG G .carrier → Group)
  : Id (GroupMonos (semidirect_product G H))
      (H (shape G), (semidirect_inclusion G H, semidirect_inclusion_mono G H))
      (fiber_kernel (semidirect_product G H) G (semidirect_projection G H))
  ≔ sdp_group_monos_path_from_iso (semidirect_product G H) (H (shape G))
      (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
      (semidirect_kernel_iso G H) (semidirect_inclusion G H) (semidirect_inclusion_mono G H)
      (fiber_kernel_inclusion (semidirect_product G H) G (semidirect_projection G H))
      (fiber_kernel_inclusion_mono (semidirect_product G H) G (semidirect_projection G H))
      (semidirect_kernel_iso_inclusion G H)

def semidirect_inclusion_kernel_lemma (G : Group) (H : BG G .carrier → Group)
  : Σ (IsGroupMono (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H))
      (m ↦ Id (GroupMonos (semidirect_product G H)) (H (shape G), (semidirect_inclusion G H, m))
        (fiber_kernel (semidirect_product G H) G (semidirect_projection G H)))
  ≔ (semidirect_inclusion_mono G H, semidirect_inclusion_kernel G H)
