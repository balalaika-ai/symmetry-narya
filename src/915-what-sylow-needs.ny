export "914-intersections"

{` Chapter 9 (subgroups.tex), lem:whatSylow2needs, assembled. Let
   f : Hom(G, G') have connected fibers (an epimorphism, lem:epi-surj),
   N ≔ ker f and (H, i) a monomorphism into G.
   (1) N ∩ H (the pullback of the kernel inclusion and i) is the kernel of
       fi : Hom(H, G') as a subgroup of H (an identification in Mono(H)).
   (2) The induced homomorphism H/(N ∩ H) → G' (with H/(N ∩ H) the quotient
       of thm:fund-thm-homs for fi, i.e. "another name for Img(fi)") is a
       monomorphism, and composed with the quotient map it is fi. `}

def wsn_intersection_homs_path (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Id (HomsInto H)
      (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i,
       pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
      (kernel_group H G' (group_hom_compose H G G' i f), kernel_inclusion H G' (group_hom_compose H G G' i f))
  ≔ let I ≔ pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    let K ≔ kernel_group H G' (group_hom_compose H G G' i f) in
    let k ≔ kernel_inclusion H G' (group_hom_compose H G G' i f) in
    let pr ≔ pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    concat (HomsInto H) (I, pr) (I, group_hom_compose I K H (wsn_iso_hom G G' H f i c) k) (K, k)
      (map_path (GroupHom I H) (HomsInto H) (k' ↦ (I, k')) pr (group_hom_compose I K H (wsn_iso_hom G G' H f i c) k)
        (inverse (GroupHom I H) (group_hom_compose I K H (wsn_iso_hom G G' H f i c) k) pr (wsn_iso_compose G G' H f i c)))
      (homs_into_iso_path H I K (wsn_iso_hom G G' H f i c, wsn_iso G G' H f i c) k)

def wsn_intersection_mono (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : IsGroupMono (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i) H
      (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
  ≔ let K ≔ kernel_group H G' (group_hom_compose H G G' i f) in
    let k ≔ kernel_inclusion H G' (group_hom_compose H G G' i f) in
    transport (HomsInto H) (u ↦ IsGroupMono (u .fst) H (u .snd)) (K, k)
      (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i,
       pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
      (inverse (HomsInto H)
        (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i,
         pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i) (K, k)
        (wsn_intersection_homs_path G G' H f i c))
      (kernel_inclusion_mono H G' (group_hom_compose H G G' i f))

def wsn_intersection_as_mono (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : GroupMonos H
  ≔ (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i,
     (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i, wsn_intersection_mono G G' H f i c))

def wsn_monos_reassoc (K : Group) (u : Σ (HomsInto K) (v ↦ IsGroupMono (v .fst) K (v .snd))) : GroupMonos K
  ≔ (u .fst .fst, (u .fst .snd, u .snd))

{` lem:whatSylow2needs (1): N ∩ H = ker(fi) in Mono(H). `}
def what_sylow_needs_kernel (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Id (GroupMonos H) (wsn_intersection_as_mono G G' H f i c) (kernel H G' (group_hom_compose H G G' i f))
  ≔ let K ≔ kernel_group H G' (group_hom_compose H G G' i f) in
    let k ≔ kernel_inclusion H G' (group_hom_compose H G G' i f) in
    let I ≔ pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    let pr ≔ pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    map_path (Σ (HomsInto H) (v ↦ IsGroupMono (v .fst) H (v .snd))) (GroupMonos H) (wsn_monos_reassoc H)
      ((I, pr), wsn_intersection_mono G G' H f i c) ((K, k), kernel_inclusion_mono H G' (group_hom_compose H G G' i f))
      (subtype_equal (HomsInto H) (v ↦ IsGroupMono (v .fst) H (v .snd)) (v ↦ is_group_mono_prop (v .fst) H (v .snd))
        ((I, pr), wsn_intersection_mono G G' H f i c) ((K, k), kernel_inclusion_mono H G' (group_hom_compose H G G' i f))
        (wsn_intersection_homs_path G G' H f i c))

{` (2) An isomorphism out of Img(fi) followed by a monomorphism: by iso
   induction, for every Q : Img(fi) ≅ L there is a monomorphism k : L → G'
   with k ∘ (Q ∘ p(fi)) = i(fi) ∘ p(fi). `}
def WsnInduced (H G' : Group) (e : GroupHom H G') (w : Σ Group (L ↦ GroupIso (image_group H G' e) L)) : Type
  ≔ Σ (GroupHom (w .fst) G') (k ↦ Product (IsGroupMono (w .fst) G' k)
      (Id (GroupHom H G')
        (group_hom_compose H (w .fst) G'
          (group_hom_compose H (image_group H G' e) (w .fst) (image_projection H G' e) (w .snd .fst)) k)
        (group_hom_compose H (image_group H G' e) G' (image_projection H G' e) (image_inclusion H G' e))))

def wsn_induced_base (H G' : Group) (e : GroupHom H G')
  : WsnInduced H G' e (image_group H G' e, group_iso_id (image_group H G' e))
  ≔ let Im ≔ image_group H G' e in
    (image_inclusion H G' e,
     (image_inclusion_mono H G' e,
      refl ((k ↦ group_hom_compose H Im G' k (image_inclusion H G' e)) : GroupHom H Im → GroupHom H G')
        (group_hom_compose_id H Im (image_projection H G' e))))

def wsn_induced (H G' : Group) (e : GroupHom H G') (w : Σ Group (L ↦ GroupIso (image_group H G' e) L))
  : WsnInduced H G' e w
  ≔ let T ≔ Σ Group (L ↦ GroupIso (image_group H G' e) L) in
    let ctr ≔ group_iso_total_contractible (image_group H G' e) in
    let i0 : T ≔ (image_group H G' e, group_iso_id (image_group H G' e)) in
    transport T (WsnInduced H G' e) i0 w
      (concat T i0 (ctr .center) w (ctr .contract i0) (inverse T w (ctr .center) (ctr .contract w)))
      (wsn_induced_base H G' e)

{` lem:whatSylow2needs (2): the induced homomorphism
   H/(N ∩ H) ≡ kernel_quotient_group H G' (fi) → G' is a monomorphism and
   k ∘ q = fi. (The underlying subgroup of the normal subgroup of the
   quotient is E(ker p(fi)) = E(ker fi) = E(N ∩ H), by
   kernel_normal_subgroup_underlying, lem:kerandcoker and (1).) `}
def what_sylow_needs_induced (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G)
  : Σ (GroupHom (kernel_quotient_group H G' (group_hom_compose H G G' i f)) G')
      (k ↦ Product (IsGroupMono (kernel_quotient_group H G' (group_hom_compose H G G' i f)) G' k)
        (Id (GroupHom H G')
          (group_hom_compose H (kernel_quotient_group H G' (group_hom_compose H G G' i f)) G'
            (normal_quotient_hom H (kernel_normal_subgroup H G' (group_hom_compose H G G' i f))) k)
          (group_hom_compose H G G' i f)))
  ≔ let e ≔ group_hom_compose H G G' i f in
    let Q ≔ kernel_quotient_group H G' e in
    let w ≔ wsn_induced H G' e (Q, fundamental_theorem_homs H G' e) in
    (w .fst,
     (w .snd .fst,
      calc
        group_hom_compose H Q G' (normal_quotient_hom H (kernel_normal_subgroup H G' e)) (w .fst)
        = group_hom_compose H Q G'
            (group_hom_compose H (image_group H G' e) Q (image_projection H G' e) (fundamental_theorem_homs H G' e .fst)) (w .fst)
          by refl ((k ↦ group_hom_compose H Q G' k (w .fst)) : GroupHom H Q → GroupHom H G')
               (inverse (GroupHom H Q)
                 (group_hom_compose H (image_group H G' e) Q (image_projection H G' e) (fundamental_theorem_homs H G' e .fst))
                 (normal_quotient_hom H (kernel_normal_subgroup H G' e))
                 (fundamental_theorem_homs_compat H G' e))
        = group_hom_compose H (image_group H G' e) G' (image_projection H G' e) (image_inclusion H G' e)
          by w .snd .snd
        = e by inverse (GroupHom H G') e
                 (group_hom_compose H (image_group H G' e) G' (image_projection H G' e) (image_inclusion H G' e))
                 (image_factorization_path H G' e) ∎))
