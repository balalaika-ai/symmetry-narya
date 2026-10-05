export "941-image-consequences"
export "910-weyl-normalizer"
export "915-what-sylow-needs"

{` Chapter 9 (subgroups.tex), running-text claims not attached to a block. `}

{` Footnote of def:cokernel: coker(f) is the induced G'-set f_!(triv_G 1)
   (def:restrictandinduce: f_!X(w) = ‖Σ_z (Bf z = w) × X(z)‖₀). `}
def coker_induced_fiber_equiv (G H : Group) (f : GroupHom G H) (w : BG H .carrier)
  : Equiv (HomFiber G H f w) (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in
    quasi_inverse_equiv (HomFiber G H f w) (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w)
      (u ↦ (u .fst, (inverse B w (hom_function G H f (u .fst)) (u .snd), star.)))
      (v ↦ (v .fst, inverse B (hom_function G H f (v .fst)) w (v .snd .fst)))
      (u ↦ map_path (Id B w (hom_function G H f (u .fst))) (HomFiber G H f w) (q ↦ (u .fst, q))
        (inverse B (hom_function G H f (u .fst)) w (inverse B w (hom_function G H f (u .fst)) (u .snd))) (u .snd)
        (inverse_inverse B w (hom_function G H f (u .fst)) (u .snd)))
      (v ↦ map_path (Product (Id B (hom_function G H f (v .fst)) w) Unit) (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w)
        (t ↦ (v .fst, t))
        (inverse B w (hom_function G H f (v .fst)) (inverse B (hom_function G H f (v .fst)) w (v .snd .fst)), star.) (v .snd)
        ((inverse_inverse B (hom_function G H f (v .fst)) w (v .snd .fst), unit_prop star. (v .snd .snd))
          : Id (Product (Id B (hom_function G H f (v .fst)) w) Unit)
              (inverse B w (hom_function G H f (v .fst)) (inverse B (hom_function G H f (v .fst)) w (v .snd .fst)), star.)
              (v .snd)))

def cokernel_induced_path (G H : Group) (f : GroupHom G H)
  : Id (GSet H) (cokernel G H f) (gset_induce G H f (gset_trivial G (Unit, unit_set)))
  ≔ gset_path_from_equivs H (cokernel G H f) (gset_induce G H f (gset_trivial G (Unit, unit_set)))
      (w ↦ id_to_equiv (SetTrunc (HomFiber G H f w)) (SetTrunc (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w))
        (map_path Type Type SetTrunc (HomFiber G H f w) (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w)
          (ua (HomFiber G H f w) (GSetInducedSum G H f (gset_trivial G (Unit, unit_set)) w) (coker_induced_fiber_equiv G H f w))))

{` sec:assker: Ker q(N) ≔ Aut_{Σ_{x:BG} (X_x = X_{sh_G})}(sh_G, refl): the
   fiber of Bq_N at the shape is Σ_x (X_x = X_{sh_G}) (paths in the
   component are paths of G-sets; the book's orientation X_x = X_sh is the
   inverse of sh = Bq(x)). `}
def quotient_kernel_fiber_equiv (G : Group) (N : NormalSubgroups G)
  : Equiv (HomFiber G (normal_quotient_group G N) (normal_quotient_hom G N) (shape (normal_quotient_group G N)))
      (Σ (BG G .carrier) (x ↦ Id (GSet G) (normal_family G N x) (normal_family G N (shape G))))
  ≔ let Q ≔ normal_quotient_group G N in
    let C ≔ BG Q .carrier in
    let X ≔ normal_family G N in
    family_equiv (BG G .carrier) (x ↦ Id C (shape Q) (normal_quotient_map G N x))
      (x ↦ Id (GSet G) (X x) (X (shape G)))
      (x ↦ compose_equiv (Id C (shape Q) (normal_quotient_map G N x)) (Id (GSet G) (X (shape G)) (X x))
             (Id (GSet G) (X x) (X (shape G)))
             (component_path_equiv (GSet G) (X (shape G)) (shape Q) (normal_quotient_map G N x))
             (inverse_path_equiv (GSet G) (X (shape G)) (X x)))

{` sec:Weyl: "def:normalquotient never used that the subgroup was normal":
   G/N is literally the Weyl group of the subgroup N(sh_G). `}
def normal_quotient_is_weyl (G : Group) (N : NormalSubgroups G)
  : Id Group (normal_quotient_group G N) (weyl_group G (normal_to_subgroup G N))
  ≔ refl (normal_quotient_group G N)

{` sec:Weyl: the subgroup corresponding to a monomorphism i_H is
   G/H ≔ coker(i_H) pointed at |(sh_H, p_{i_H})|₀ (image_subgroup), i.e.
   E(H, i_H) = (coker i_H, |sh_H, p|₀, !) in Sub(G). `}
def monos_path_from_homs (K : Group) (u v : Σ (HomsInto K) (w ↦ IsGroupMono (w .fst) K (w .snd)))
  (p : Id (HomsInto K) (u .fst) (v .fst))
  : Id (GroupMonos K) (u .fst .fst, (u .fst .snd, u .snd)) (v .fst .fst, (v .fst .snd, v .snd))
  ≔ map_path (Σ (HomsInto K) (w ↦ IsGroupMono (w .fst) K (w .snd))) (GroupMonos K)
      (t ↦ (t .fst .fst, (t .fst .snd, t .snd))) u v
      (subtype_equal (HomsInto K) (w ↦ IsGroupMono (w .fst) K (w .snd)) (w ↦ is_group_mono_prop (w .fst) K (w .snd)) u v p)

def mono_subgroup_cokernel_path (G H : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  : Id (Subgroups G) (mono_to_subgroup G (H, (i, m))) (image_subgroup H G i)
  ≔ let cm ≔ equiv_inverse_map (IsGroupMonomorphism H G i) (IsGroupMono H G i) (group_monomorphism_mono_equiv H G i) m in
    let S ≔ image_subgroup H G i in
    let hp : Id (HomsInto G) (H, i) (image_group H G i, image_inclusion H G i)
      ≔ map_path (GroupMonomorphismsInto G) (HomsInto G) (t ↦ (t .fst, t .snd .fst)) (H, (i, cm))
          (image_mono_categorical H G i) (chim_mono_image_path H G i cm) in
    let mp : Id (GroupMonos G) (H, (i, m)) (subgroup_to_mono G S)
      ≔ monos_path_from_homs G ((H, i), m) ((image_group H G i, image_inclusion H G i), subgroup_inclusion_mono G S) hp in
    concat (Subgroups G) (mono_to_subgroup G (H, (i, m))) (mono_to_subgroup G (subgroup_to_mono G S)) S
      (map_path (GroupMonos G) (Subgroups G) (mono_to_subgroup G) (H, (i, m)) (subgroup_to_mono G S) mp)
      (subgroup_mono_roundtrip G S)

{` thm:fund-thm-homs / lem:kerandcoker: the normal subgroup "ker f" of
   module 908 has E(ker f) as underlying subgroup. `}
def kernel_normal_subgroup_is_kernel (G H : Group) (f : GroupHom G H)
  : Id (Subgroups G) (normal_to_subgroup G (kernel_normal_subgroup G H f)) (mono_to_subgroup G (kernel G H f))
  ≔ concat (Subgroups G) (normal_to_subgroup G (kernel_normal_subgroup G H f))
      (mono_to_subgroup G (kernel G (image_group G H f) (image_projection G H f))) (mono_to_subgroup G (kernel G H f))
      (kernel_normal_subgroup_underlying G H f)
      (map_path (GroupMonos G) (Subgroups G) (mono_to_subgroup G) (kernel G (image_group G H f) (image_projection G H f))
        (kernel G H f) (chim_kernel_projection_path G H f))

{` lem:whatSylow2needs: the quotient H/(N ∩ H) of what_sylow_needs_induced is
   by the normal subgroup whose underlying subgroup is E(N ∩ H). `}
def what_sylow_needs_quotient_subgroup (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Id (Subgroups H) (normal_to_subgroup H (kernel_normal_subgroup H G' (group_hom_compose H G G' i f)))
      (mono_to_subgroup H (wsn_intersection_as_mono G G' H f i c))
  ≔ concat (Subgroups H) (normal_to_subgroup H (kernel_normal_subgroup H G' (group_hom_compose H G G' i f)))
      (mono_to_subgroup H (kernel H G' (group_hom_compose H G G' i f))) (mono_to_subgroup H (wsn_intersection_as_mono G G' H f i c))
      (kernel_normal_subgroup_is_kernel H G' (group_hom_compose H G G' i f))
      (map_path (GroupMonos H) (Subgroups H) (mono_to_subgroup H) (kernel H G' (group_hom_compose H G G' i f))
        (wsn_intersection_as_mono G G' H f i c)
        (inverse (GroupMonos H) (wsn_intersection_as_mono G G' H f i c) (kernel H G' (group_hom_compose H G G' i f))
          (what_sylow_needs_kernel G G' H f i c)))
