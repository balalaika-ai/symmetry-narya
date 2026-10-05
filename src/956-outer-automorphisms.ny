export "903-normal-subgroups"
export "1202-group-center"
export "952-cokernels-of-composites"
export "955-inner-automorphisms-kernel"

{` Chapter 9 (subgroups.tex 1934-2004): the Aut(G)-set out(G), its
   description lemma:coker-out-action, Inn(G) and its classifying type,
   the normality of Inn(G) in Aut(G), and Out(G).

   Out(G) is defined directly as Aut_{GSet(Aut(G))}(out(G)) (the book's
   right-hand side); the normal quotient Aut(G)/Inn(G) in the form
   Aut_{GSet}(N(sh).gset) (module 904, not available when this was
   written) is identified with it in outer_aut_group_quotient_path. `}

{` The Aut(G)-set out(G) ≔ coker(inn). `}
def outer_gset (G : Group) : GSet (group_aut G) ≔ cokernel G (group_aut G) (inn G)

{` The Aut(G)-set G' ↦ ‖BG'÷ = BG÷‖₀. `}
def outer_paths_gset (G : Group) : GSet (group_aut G)
  ≔ G' ↦ (SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier)),
          set_trunc_set (Id Type (BG (G' .fst) .carrier) (BG G .carrier)))

{` lemma:coker-out-action: out(G)(G') ≡ ‖Binn⁻¹(G')‖₀ ≃ ‖BG'÷ = BG÷‖₀
   (the set truncation of inn_fiber_equiv), hence out(G) = outer_paths_gset. `}
def outer_gset_equiv (G : Group) (G' : BG (group_aut G) .carrier)
  : Equiv (outer_gset G G' .fst) (outer_paths_gset G G' .fst)
  ≔ ch9w2_set_trunc_equiv (HomFiber G (group_aut G) (inn G) G') (Id Type (BG (G' .fst) .carrier) (BG G .carrier))
      (inn_fiber_equiv G G')

def outer_gset_path (G : Group) : Id (GSet (group_aut G)) (outer_gset G) (outer_paths_gset G)
  ≔ gset_path_from_equivs (group_aut G) (outer_gset G) (outer_paths_gset G) (outer_gset_equiv G)

{` The chosen point |(sh_G, Binn_pt)|₀ of out(G)(G) goes to |refl_{BG÷}|₀. `}
def outer_gset_equiv_point (G : Group)
  : Id (SetTrunc (Id Type (BG G .carrier) (BG G .carrier)))
      (outer_gset_equiv G (shape (group_aut G)) .map (cokernel_point G (group_aut G) (inn G)))
      (set_trunc (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)))
  ≔ refl (set_trunc (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)))

{` The group Inn(G) of inner automorphisms ≔ Img(inn). `}
def inner_aut_group (G : Group) : Group ≔ image_group G (group_aut G) (inn G)

{` BInn(G) ≡ Σ_{G':BAut(G)} out(G)(G') ≃ Σ_{G':BAut(G)} ‖BG'÷ = BG÷‖₀. `}
def inner_aut_classifying_equiv (G : Group)
  : Equiv (BG (inner_aut_group G) .carrier)
      (Σ (BG (group_aut G) .carrier) (G' ↦ SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier))))
  ≔ family_equiv (BG (group_aut G) .carrier) (G' ↦ outer_gset G G' .fst) (G' ↦ outer_paths_gset G G' .fst)
      (outer_gset_equiv G)

{` The book writes the sum over all G' : Group; an element of
   ‖BG'÷ = BG÷‖₀ forces G' into the component of G (G' = mkgroup(BG÷, q.trr sh)
   for q : BG'÷ = BG÷, and BG is connected), so both sums agree. `}
def ch9w2_group_path_sigma_equiv (H K : Group)
  : Equiv (Id Group H K) (Σ (Id Type (BG H .carrier) (BG K .carrier)) (q ↦ Id (T ↦ T) q (shape H) (shape K)))
  ≔ compose_equiv (Id Group H K) (Id PointedConnectedGroupoid (group_B H) (group_B K))
      (Σ (Id Type (BG H .carrier) (BG K .carrier)) (q ↦ Id (T ↦ T) q (shape H) (shape K)))
      (group_path_classifying_equiv H K)
      (compose_equiv (Id PointedConnectedGroupoid (group_B H) (group_B K)) (Id Pointed (BG H) (BG K))
        (Σ (Id Type (BG H .carrier) (BG K .carrier)) (q ↦ Id (T ↦ T) q (shape H) (shape K)))
        (pcg_path_pointed_equiv (group_B H) (group_B K))
        (ch9w2_pointed_path_sigma_equiv (BG H) (BG K)))

def outer_paths_component (G H : Group) (t : SetTrunc (Id Type (BG H .carrier) (BG G .carrier))) : Mere (Id Group G H)
  ≔ set_trunc_rec (Id Type (BG H .carrier) (BG G .carrier)) (Mere (Id Group G H))
      (prop_is_set (Mere (Id Group G H)) (mere_isprop (Id Group G H)))
      (q ↦
        let y ≔ q .trr (shape H) in
        let e : Id Group H (group_at G y)
          ≔ equiv_inverse_map (Id Group H (group_at G y))
              (Σ (Id Type (BG H .carrier) (BG G .carrier)) (r ↦ Id (T ↦ T) r (shape H) y))
              (ch9w2_group_path_sigma_equiv H (group_at G y)) (q, q .liftr (shape H)) in
        mere_rec (Id Group G (group_at G y)) (Mere (Id Group G H)) (mere_isprop (Id Group G H))
          (d ↦ mere (Id Group G H) (concat Group G (group_at G y) H d (inverse Group H (group_at G y) e)))
          (inn_component_witness G y))
      t

def inner_aut_classifying_group_equiv (G : Group)
  : Equiv (Σ (BG (group_aut G) .carrier) (G' ↦ SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier))))
      (Σ Group (H ↦ SetTrunc (Id Type (BG H .carrier) (BG G .carrier))))
  ≔ let S ≔ Σ (BG (group_aut G) .carrier) (G' ↦ SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier))) in
    let T ≔ Σ Group (H ↦ SetTrunc (Id Type (BG H .carrier) (BG G .carrier))) in
    quasi_inverse_equiv S T (u ↦ (u .fst .fst, u .snd)) (v ↦ ((v .fst, outer_paths_component G (v .fst) (v .snd)), v .snd))
      (u ↦ (component_path Group G ((u .fst .fst, outer_paths_component G (u .fst .fst) (u .snd))) (u .fst) (refl (u .fst .fst)),
            refl (u .snd)))
      (v ↦ refl v)

def inner_aut_classifying_equiv_group (G : Group)
  : Equiv (BG (inner_aut_group G) .carrier) (Σ Group (H ↦ SetTrunc (Id Type (BG H .carrier) (BG G .carrier))))
  ≔ compose_equiv (BG (inner_aut_group G) .carrier)
      (Σ (BG (group_aut G) .carrier) (G' ↦ SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier))))
      (Σ Group (H ↦ SetTrunc (Id Type (BG H .carrier) (BG G .carrier))))
      (inner_aut_classifying_equiv G) (inner_aut_classifying_group_equiv G)

{` The lemma "Inn(G) is normal in Aut(G)": N(G') ≔ (H ↦ ‖BG'÷ = BH÷‖₀,
   |refl_{BG'÷}|₀, !) : Sub_{Aut(G)}(G') and N(sh) = E(img(inn)). `}
def inner_normal_gset (G : Group) (G' : BG (group_aut G) .carrier) : GSet (group_at (group_aut G) G')
  ≔ H ↦ (SetTrunc (Id Type (BG (G' .fst) .carrier) (BG (H .fst) .carrier)),
         set_trunc_set (Id Type (BG (G' .fst) .carrier) (BG (H .fst) .carrier)))

def inner_normal_point (G : Group) (G' : BG (group_aut G) .carrier)
  : gset_underlying (group_at (group_aut G) G') (inner_normal_gset G G')
  ≔ set_trunc (Id Type (BG (G' .fst) .carrier) (BG (G' .fst) .carrier)) (refl (BG (G' .fst) .carrier))

{` At G' ≡ G, N(G) and out(G) are identified (inverting paths). `}
def inner_normal_outer_equiv (G : Group) (H : BG (group_aut G) .carrier)
  : Equiv (inner_normal_gset G (shape (group_aut G)) H .fst) (outer_gset G H .fst)
  ≔ let X ≔ BG G .carrier in let Y ≔ BG (H .fst) .carrier in
    compose_equiv (SetTrunc (Id Type X Y)) (SetTrunc (Id Type Y X)) (outer_gset G H .fst)
      (ch9w2_set_trunc_equiv (Id Type X Y) (Id Type Y X) (inverse_path_equiv Type X Y))
      (canonical_inverse_equiv (outer_gset G H .fst) (SetTrunc (Id Type Y X)) (outer_gset_equiv G H))

def inner_normal_outer_path (G : Group)
  : Id (GSet (group_aut G)) (inner_normal_gset G (shape (group_aut G))) (outer_gset G)
  ≔ gset_path_from_equivs (group_aut G) (inner_normal_gset G (shape (group_aut G))) (outer_gset G)
      (inner_normal_outer_equiv G)

def inner_normal_transitive_shape (G : Group)
  : IsTransitive (group_aut G) (inner_normal_gset G (shape (group_aut G)))
  ≔ transport (GSet (group_aut G)) (IsTransitive (group_aut G)) (outer_gset G) (inner_normal_gset G (shape (group_aut G)))
      (inverse (GSet (group_aut G)) (inner_normal_gset G (shape (group_aut G))) (outer_gset G) (inner_normal_outer_path G))
      (cokernel_transitive G (group_aut G) (inn G))

def inner_normal_transitive (G : Group) (G' : BG (group_aut G) .carrier)
  : IsTransitive (group_at (group_aut G) G') (inner_normal_gset G G')
  ≔ let A ≔ group_aut G in
    mere_rec (Id (BG A .carrier) (shape A) G') (IsTransitive (group_at A G') (inner_normal_gset G G'))
      (is_transitive_prop (group_at A G') (inner_normal_gset G G'))
      (q ↦ transport (BG A .carrier) (z ↦ IsTransitive (group_at A z) (inner_normal_gset G z)) (shape A) G' q
        (inner_normal_transitive_shape G))
      (bg_connected A .snd (shape A) G')

def inner_normal (G : Group) : NormalSubgroups (group_aut G)
  ≔ G' ↦ (inner_normal_gset G G', inner_normal_point G G', inner_normal_transitive G G')

{` N(sh) = (out(G), |(sh_G, Binn_pt)|₀) = img(inn) as subgroups. `}
def inner_normal_image_subgroup (G : Group)
  : Id (Subgroups (group_aut G)) (normal_to_subgroup (group_aut G) (inner_normal G)) (image_subgroup G (group_aut G) (inn G))
  ≔ let A ≔ group_aut G in let X ≔ BG G .carrier in
    let F ≔ HomFiber G A (inn G) (shape A) in
    let e ≔ inn_fiber_equiv G (shape A) in
    let ks ≔ kernel_shape G A (inn G) in
    subgroup_path A (normal_to_subgroup A (inner_normal G)) (image_subgroup G A (inn G))
      (pointed_gset_path A (inner_normal_gset G (shape A)) (outer_gset G) (inner_normal_point G (shape A))
        (cokernel_point G A (inn G)) (inner_normal_outer_equiv G)
        (refl (set_trunc F)
          (concat F (equiv_inverse_map F (Id Type X X) e (inverse Type X X (refl X)))
            (equiv_inverse_map F (Id Type X X) e (e .map ks)) ks
            (refl (equiv_inverse_map F (Id Type X X) e) (inverse_refl Type X))
            (equiv_retraction F (Id Type X X) e ks))))

def inner_normal_path (G : Group)
  : Id (Subgroups (group_aut G)) (normal_to_subgroup (group_aut G) (inner_normal G))
      (mono_to_subgroup (group_aut G) (image_mono G (group_aut G) (inn G)))
  ≔ concat (Subgroups (group_aut G)) (normal_to_subgroup (group_aut G) (inner_normal G))
      (image_subgroup G (group_aut G) (inn G)) (mono_to_subgroup (group_aut G) (image_mono G (group_aut G) (inn G)))
      (inner_normal_image_subgroup G)
      (inverse (Subgroups (group_aut G)) (mono_to_subgroup (group_aut G) (image_mono G (group_aut G) (inn G)))
        (image_subgroup G (group_aut G) (inn G))
        (subgroup_mono_roundtrip (group_aut G) (image_subgroup G (group_aut G) (inn G))))

{` The lemma, in the form of def:normalsubgroup: E(img(inn)) is normal. `}
def inner_aut_normal (G : Group)
  : IsNormalSubgroup (group_aut G) (mono_to_subgroup (group_aut G) (image_mono G (group_aut G) (inn G)))
  ≔ (inner_normal G,
     inverse (Subgroups (group_aut G)) (normal_to_subgroup (group_aut G) (inner_normal G))
       (mono_to_subgroup (group_aut G) (image_mono G (group_aut G) (inn G))) (inner_normal_path G))

{` def (subgroups.tex 2001): Out(G) ≔ Aut(G)/Inn(G) ≡ Aut_{GSet(Aut(G))}(out(G)). `}
def outer_aut_group (G : Group) : Group
  ≔ automorphism_group (GSet (group_aut G)) (gset_groupoid (group_aut G)) (outer_gset G)

{` The normal quotient by Inn(G) in the form Aut_{GSet}(N(sh).gset) is Out(G). `}
def outer_aut_group_quotient_path (G : Group)
  : Id Group (automorphism_group (GSet (group_aut G)) (gset_groupoid (group_aut G))
        (inner_normal G (shape (group_aut G)) .gset))
      (outer_aut_group G)
  ≔ refl ((X ↦ automorphism_group (GSet (group_aut G)) (gset_groupoid (group_aut G)) X) : GSet (group_aut G) → Group)
      (inner_normal_outer_path G)
