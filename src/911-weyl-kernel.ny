export "910-weyl-normalizer"
export "908-fundamental-theorem-homs"

{` Chapter 9 (subgroups.tex), sec:Weyl, lemma at line 2141 (rest): j_H
   defines H as a normal subgroup of the normalizer, ker p_G^H = (H, j_H) in
   Mono(N_GH); and symmetry.tex lem:aut-orbit: Aut_{G-Set}(G/H) = W_GH is
   isomorphic to N_G(H)/H. The fiber of Bp over Y0 : BW_GH is identified with
   Σ_{y:BG} Y0(y) (for Y0 ≡ sh_W this is BH). `}

{` The fiber of Bp at Y0 and its identification with Σ_{y:BG} Y0(y). `}
def WeylFiber (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier) : Type
  ≔ BookFiber (BG (normalizer_group G S) .carrier) (BG (weyl_group G S) .carrier) (weyl_projection_map G S) Y0

def weyl_fiber_from (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier) (w : ActionType G (Y0 .fst))
  : WeylFiber G S Y0
  ≔ (sigma_to_normalizer G S (Y0, w),
     component_path (GSet G) (S .gset) Y0 (weyl_projection_map G S (sigma_to_normalizer G S (Y0, w))) (refl (Y0 .fst)))

def weyl_fiber_to (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier) (u : WeylFiber G S Y0)
  : ActionType G (Y0 .fst)
  ≔ let Y ≔ u .fst .fst .snd .gset in
    let y ≔ u .fst .fst .fst in
    (y, equiv_inverse_map (Y0 .fst y .fst) (Y y .fst) (gset_path_equiv G (Y0 .fst) Y .map (u .snd .fst) y)
          (u .fst .fst .snd .point))

def weyl_transport_inverse_refl (G : Group) (Y : GSet G) (z : BG G .carrier) (a : Y z .fst)
  : Id (Y z .fst) (equiv_inverse_map (Y z .fst) (Y z .fst) (gset_path_equiv G Y Y .map (refl Y) z) a) a
  ≔ let e ≔ gset_path_equiv G Y Y .map (refl Y) z in
    concat (Y z .fst) (equiv_inverse_map (Y z .fst) (Y z .fst) e a) (equiv_inverse_map (Y z .fst) (Y z .fst) e (e .map a)) a
      (refl (equiv_inverse_map (Y z .fst) (Y z .fst) e)
        (inverse (Y z .fst) (e .map a) a (transport_refl (GSet G) (W ↦ W z .fst) Y a)))
      (equiv_retraction (Y z .fst) (Y z .fst) e a)

def weyl_fiber_to_from (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier) (w : ActionType G (Y0 .fst))
  : Id (ActionType G (Y0 .fst)) (weyl_fiber_to G S Y0 (weyl_fiber_from G S Y0 w)) w
  ≔ map_path (Y0 .fst (w .fst) .fst) (ActionType G (Y0 .fst)) (a ↦ (w .fst, a))
      (equiv_inverse_map (Y0 .fst (w .fst) .fst) (Y0 .fst (w .fst) .fst)
        (gset_path_equiv G (Y0 .fst) (Y0 .fst) .map (refl (Y0 .fst)) (w .fst)) (w .snd))
      (w .snd) (weyl_transport_inverse_refl G (Y0 .fst) (w .fst) (w .snd))

{` Transport in the family u ↦ (c = f(u)) is post-concatenation with ap_f. `}
def weyl_transport_right (A C : Type) (f : A → C) (c : C) (a b : A) (r : Id A a b) (q : Id C c (f a))
  : Id (Id C c (f b)) (transport A (u ↦ Id C c (f u)) a b r q) (concat C c (f a) (f b) q (map_path A C f a b r))
  ≔ J A a (b r ↦ Id (Id C c (f b)) (transport A (u ↦ Id C c (f u)) a b r q) (concat C c (f a) (f b) q (map_path A C f a b r)))
      (concat (Id C c (f a)) (transport A (u ↦ Id C c (f u)) a a (refl a) q) q (concat C c (f a) (f a) q (refl (f a)))
        (transport_refl A (u ↦ Id C c (f u)) a q)
        (inverse (Id C c (f a)) (concat C c (f a) (f a) q (refl (f a))) q (concat_p1 C c (f a) q)))
      b r

{` from ∘ to = id, at the base case Y0 ≡ Bp(u), q ≡ refl. `}
def weyl_fiber_from_to_base (G : Group) (S : Subgroups G) (u : BG (normalizer_group G S) .carrier)
  : Id (WeylFiber G S (weyl_projection_map G S u))
      (weyl_fiber_from G S (weyl_projection_map G S u)
        (weyl_fiber_to G S (weyl_projection_map G S u) (u, refl (weyl_projection_map G S u))))
      (u, refl (weyl_projection_map G S u))
  ≔ let A ≔ ActionType G (subgroups_gset G) in
    let BN ≔ BG (normalizer_group G S) .carrier in
    let BW ≔ BG (weyl_group G S) .carrier in
    let Bp ≔ weyl_projection_map G S in
    let Y0 ≔ Bp u in
    let y ≔ u .fst .fst in
    let T ≔ u .fst .snd in
    let Y ≔ T .gset in
    let Gy ≔ group_at G y in
    let v' ≔ weyl_fiber_to G S Y0 (u, refl Y0) .snd in
    let tr ≔ weyl_component_transitive G S Y (Y0 .snd) y in
    let vv : Id (Y y .fst) v' (T .point) ≔ weyl_transport_inverse_refl G Y y (T .point) in
    let sub_eq : Id (Subgroups Gy) (Y, v', tr) T
      ≔ concat (Subgroups Gy) (Y, v', tr) (Y, T .point, tr) T
          (map_path (Y y .fst) (Subgroups Gy) (a ↦ (Y, a, tr)) v' (T .point) vv)
          (map_path (IsTransitive Gy Y) (Subgroups Gy) (t ↦ (Y, T .point, t)) tr (T .transitive)
            (is_transitive_prop Gy Y tr (T .transitive))) in
    let first : Id A (y, (Y, v', tr)) (u .fst)
      ≔ map_path (Subgroups Gy) A (T' ↦ (y, T')) (Y, v', tr) T sub_eq in
    let s0 ≔ sigma_to_normalizer G S (Y0, (y, v')) in
    let r : Id BN s0 u ≔ component_path A (shape G, S) s0 u first in
    let cp ≔ weyl_fiber_from G S Y0 (y, v') .snd in
    let cpe ≔ component_path_equiv (GSet G) (S .gset) Y0 Y0 in
    let snd_eq : Id (Id BW Y0 Y0) (concat BW Y0 (Bp s0) Y0 cp (map_path BN BW Bp s0 u r)) (refl Y0)
      ≔ equivalence_injective (Id BW Y0 Y0) (Id (GSet G) Y Y) cpe
          (concat BW Y0 (Bp s0) Y0 cp (map_path BN BW Bp s0 u r)) (refl Y0)
          (calc
             cpe .map (concat BW Y0 (Bp s0) Y0 cp (map_path BN BW Bp s0 u r))
             = concat (GSet G) Y Y Y (refl Y) (map_path A (GSet G) (w ↦ w .snd .gset) (s0 .fst) (u .fst) first)
               by map_path_concat BW (GSet G) (w ↦ w .fst) Y0 (Bp s0) Y0 cp (map_path BN BW Bp s0 u r)
             = map_path A (GSet G) (w ↦ w .snd .gset) (s0 .fst) (u .fst) first
               by concat_1p (GSet G) Y Y (map_path A (GSet G) (w ↦ w .snd .gset) (s0 .fst) (u .fst) first)
             = refl Y
               by calc
                    map_path A (GSet G) (w ↦ w .snd .gset) (s0 .fst) (u .fst) first
                    = concat (GSet G) Y Y Y (refl Y) (refl Y)
                      by map_path_concat (Subgroups Gy) (GSet G) (T' ↦ T' .gset) (Y, v', tr) (Y, T .point, tr) T
                           (map_path (Y y .fst) (Subgroups Gy) (a ↦ (Y, a, tr)) v' (T .point) vv)
                           (map_path (IsTransitive Gy Y) (Subgroups Gy) (t ↦ (Y, T .point, t)) tr (T .transitive)
                             (is_transitive_prop Gy Y tr (T .transitive)))
                    = refl Y by concat_p1 (GSet G) Y Y (refl Y) ∎
             = cpe .map (refl Y0) by refl (refl Y) ∎) in
    (r, pathover_of_eq BN (w ↦ Id BW Y0 (Bp w)) s0 u r cp (refl Y0)
          (concat (Id BW Y0 (Bp u)) (transport BN (w ↦ Id BW Y0 (Bp w)) s0 u r cp)
            (concat BW Y0 (Bp s0) Y0 cp (map_path BN BW Bp s0 u r)) (refl Y0)
            (weyl_transport_right BN BW Bp Y0 s0 u r cp) snd_eq))

def weyl_fiber_from_to (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier) (u : WeylFiber G S Y0)
  : Id (WeylFiber G S Y0) (weyl_fiber_from G S Y0 (weyl_fiber_to G S Y0 u)) u
  ≔ let BW ≔ BG (weyl_group G S) .carrier in
    let Bp ≔ weyl_projection_map G S in
    let b ≔ Bp (u .fst) in
    let T ≔ Σ BW (Y ↦ Id BW Y b) in
    let c ≔ path_to_contractible BW b in
    let P : T → Type
      ≔ t ↦ Id (WeylFiber G S (t .fst)) (weyl_fiber_from G S (t .fst) (weyl_fiber_to G S (t .fst) (u .fst, t .snd)))
              (u .fst, t .snd) in
    transport T P (b, refl b) (Y0, u .snd)
      (concat T (b, refl b) (c .center) (Y0, u .snd) (c .contract (b, refl b))
        (inverse T (Y0, u .snd) (c .center) (c .contract (Y0, u .snd))))
      (weyl_fiber_from_to_base G S (u .fst))

def weyl_fiber_equiv (G : Group) (S : Subgroups G) (Y0 : BG (weyl_group G S) .carrier)
  : Equiv (ActionType G (Y0 .fst)) (WeylFiber G S Y0)
  ≔ quasi_inverse_equiv (ActionType G (Y0 .fst)) (WeylFiber G S Y0) (weyl_fiber_from G S Y0) (weyl_fiber_to G S Y0)
      (weyl_fiber_to_from G S Y0) (weyl_fiber_from_to G S Y0)

{` H ≅ Ker(p_G^H), compatible with j_H and the kernel inclusion. `}
def weyl_kernel_map (G : Group) (S : Subgroups G)
  : BG (subgroup_group G S) .carrier
    → BG (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S)) .carrier
  ≔ let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    let F ≔ WeylFiber G S (shape W) in
    let hF : Connected F ≔ weyl_projection_connected G S (shape W) in
    w ↦ (weyl_fiber_from G S (shape W) w, hF .snd (kernel_shape N W (weyl_projection G S)) (weyl_fiber_from G S (shape W) w))

def weyl_kernel_point (G : Group) (S : Subgroups G)
  : Id (BG (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S)) .carrier)
      (shape (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S)))
      (weyl_kernel_map G S (shape (subgroup_group G S)))
  ≔ let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    let BN ≔ BG N .carrier in let BW ≔ BG W .carrier in
    let Bp ≔ weyl_projection_map G S in
    let F ≔ WeylFiber G S (shape W) in
    let x0 ≔ kernel_shape N W (weyl_projection G S) in
    let jpt ≔ normalizer_subgroup_point_path G S in
    let u1 ≔ normalizer_subgroup_map G S (shape (subgroup_group G S)) in
    let ppt ≔ weyl_projection_point G S in
    let cp ≔ weyl_fiber_from G S (shape W) (shape (subgroup_group G S)) .snd in
    let X ≔ S .gset in
    let cpe ≔ component_path_equiv (GSet G) X (shape W) (Bp u1) in
    let snd_eq : Id (Id BW (shape W) (Bp u1)) (concat BW (shape W) (Bp (shape N)) (Bp u1) ppt (map_path BN BW Bp (shape N) u1 jpt)) cp
      ≔ equivalence_injective (Id BW (shape W) (Bp u1)) (Id (GSet G) X X) cpe
          (concat BW (shape W) (Bp (shape N)) (Bp u1) ppt (map_path BN BW Bp (shape N) u1 jpt)) cp
          (calc
             cpe .map (concat BW (shape W) (Bp (shape N)) (Bp u1) ppt (map_path BN BW Bp (shape N) u1 jpt))
             = concat (GSet G) X X X (refl X) (refl X)
               by map_path_concat BW (GSet G) (w ↦ w .fst) (shape W) (Bp (shape N)) (Bp u1) ppt
                    (map_path BN BW Bp (shape N) u1 jpt)
             = refl X by concat_p1 (GSet G) X X (refl X)
             = cpe .map cp by refl (refl X) ∎) in
    let pf : Id F x0 (weyl_fiber_from G S (shape W) (shape (subgroup_group G S)))
      ≔ (jpt, pathover_of_eq BN (w ↦ Id BW (shape W) (Bp w)) (shape N) u1 jpt ppt cp
            (concat (Id BW (shape W) (Bp u1)) (transport BN (w ↦ Id BW (shape W) (Bp w)) (shape N) u1 jpt ppt)
              (concat BW (shape W) (Bp (shape N)) (Bp u1) ppt (map_path BN BW Bp (shape N) u1 jpt)) cp
              (weyl_transport_right BN BW Bp (shape W) (shape N) u1 jpt ppt) snd_eq)) in
    component_path F x0 (shape (kernel_group N W (weyl_projection G S))) (weyl_kernel_map G S (shape (subgroup_group G S))) pf

def weyl_kernel_hom (G : Group) (S : Subgroups G)
  : GroupHom (subgroup_group G S) (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
  ≔ mkhom (subgroup_group G S) (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
      (weyl_kernel_map G S, weyl_kernel_point G S)

def weyl_kernel_iso (G : Group) (S : Subgroups G)
  : IsGroupIso (subgroup_group G S) (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
      (weyl_kernel_hom G S)
  ≔ let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    let BH ≔ BG (subgroup_group G S) .carrier in
    let F ≔ WeylFiber G S (shape W) in
    let K ≔ BG (kernel_group N W (weyl_projection G S)) .carrier in
    let x0 ≔ kernel_shape N W (weyl_projection G S) in
    let hF : Connected F ≔ weyl_projection_connected G S (shape W) in
    book_equivalence BH K
      (equiv_change_map BH K
        (compose_equiv BH F K (weyl_fiber_equiv G S (shape W))
          (canonical_inverse_equiv K F (ch9_component_equiv F x0 hF)))
        (weyl_kernel_map G S) (w ↦ refl (weyl_kernel_map G S w)))
    .equiv

def weyl_kernel_compose (G : Group) (S : Subgroups G)
  : Id (GroupHom (subgroup_group G S) (normalizer_group G S))
      (group_hom_compose (subgroup_group G S) (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
        (normalizer_group G S) (weyl_kernel_hom G S)
        (kernel_inclusion (normalizer_group G S) (weyl_group G S) (weyl_projection G S)))
      (normalizer_subgroup_hom G S)
  ≔ let H ≔ subgroup_group G S in
    let N ≔ normalizer_group G S in
    let BN ≔ BG N .carrier in
    let comp ≔ group_hom_compose H (kernel_group N (weyl_group G S) (weyl_projection G S)) N (weyl_kernel_hom G S)
      (kernel_inclusion N (weyl_group G S) (weyl_projection G S)) in
    let jpt ≔ normalizer_subgroup_point_path G S in
    let u1 ≔ normalizer_subgroup_map G S (shape H) in
    equiv_inverse_map (Id (GroupHom H N) comp (normalizer_subgroup_hom G S))
      (PointedHomotopy (BG H) (BG N) (hom_B H N comp) (hom_B H N (normalizer_subgroup_hom G S)))
      (group_hom_path_equiv H N comp (normalizer_subgroup_hom G S))
      (w ↦ refl (normalizer_subgroup_map G S w),
       calc
         concat BN (shape N) u1 u1 (hom_point H N comp) (refl u1)
         = hom_point H N comp by concat_p1 BN (shape N) u1 (hom_point H N comp)
         = jpt by concat_1p BN (shape N) u1 jpt ∎)

{` Lemma at line 2141: ker p_G^H = (H, j_H) as homomorphisms into N_GH;
   hence j_H is a monomorphism, and (H, j_H) = ker p_G^H in Mono(N_GH). `}
def weyl_kernel_homs_path (G : Group) (S : Subgroups G)
  : Id (HomsInto (normalizer_group G S)) (subgroup_group G S, normalizer_subgroup_hom G S)
      (kernel_group (normalizer_group G S) (weyl_group G S) (weyl_projection G S),
       kernel_inclusion (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
  ≔ let H ≔ subgroup_group G S in
    let N ≔ normalizer_group G S in
    let K ≔ kernel_group N (weyl_group G S) (weyl_projection G S) in
    let k ≔ kernel_inclusion N (weyl_group G S) (weyl_projection G S) in
    concat (HomsInto N) (H, normalizer_subgroup_hom G S) (H, group_hom_compose H K N (weyl_kernel_hom G S) k) (K, k)
      (map_path (GroupHom H N) (HomsInto N) (k' ↦ (H, k')) (normalizer_subgroup_hom G S)
        (group_hom_compose H K N (weyl_kernel_hom G S) k)
        (inverse (GroupHom H N) (group_hom_compose H K N (weyl_kernel_hom G S) k) (normalizer_subgroup_hom G S)
          (weyl_kernel_compose G S)))
      (homs_into_iso_path N H K (weyl_kernel_hom G S, weyl_kernel_iso G S) k)

def normalizer_subgroup_mono (G : Group) (S : Subgroups G)
  : IsGroupMono (subgroup_group G S) (normalizer_group G S) (normalizer_subgroup_hom G S)
  ≔ let N ≔ normalizer_group G S in
    transport (HomsInto N) (u ↦ IsGroupMono (u .fst) N (u .snd))
      (kernel_group N (weyl_group G S) (weyl_projection G S), kernel_inclusion N (weyl_group G S) (weyl_projection G S))
      (subgroup_group G S, normalizer_subgroup_hom G S)
      (inverse (HomsInto N) (subgroup_group G S, normalizer_subgroup_hom G S)
        (kernel_group N (weyl_group G S) (weyl_projection G S), kernel_inclusion N (weyl_group G S) (weyl_projection G S))
        (weyl_kernel_homs_path G S))
      (kernel_inclusion_mono N (weyl_group G S) (weyl_projection G S))

def normalizer_subgroup_as_mono (G : Group) (S : Subgroups G) : GroupMonos (normalizer_group G S)
  ≔ (subgroup_group G S, (normalizer_subgroup_hom G S, normalizer_subgroup_mono G S))

def weyl_monos_reassoc (K : Group) (u : Σ (HomsInto K) (v ↦ IsGroupMono (v .fst) K (v .snd))) : GroupMonos K
  ≔ (u .fst .fst, (u .fst .snd, u .snd))

def weyl_kernel_mono_path (G : Group) (S : Subgroups G)
  : Id (GroupMonos (normalizer_group G S)) (normalizer_subgroup_as_mono G S)
      (kernel (normalizer_group G S) (weyl_group G S) (weyl_projection G S))
  ≔ let N ≔ normalizer_group G S in
    let K ≔ kernel_group N (weyl_group G S) (weyl_projection G S) in
    let k ≔ kernel_inclusion N (weyl_group G S) (weyl_projection G S) in
    map_path (Σ (HomsInto N) (v ↦ IsGroupMono (v .fst) N (v .snd))) (GroupMonos N) (weyl_monos_reassoc N)
      ((subgroup_group G S, normalizer_subgroup_hom G S), normalizer_subgroup_mono G S)
      ((K, k), kernel_inclusion_mono N (weyl_group G S) (weyl_projection G S))
      (subtype_equal (HomsInto N) (v ↦ IsGroupMono (v .fst) N (v .snd)) (v ↦ is_group_mono_prop (v .fst) N (v .snd))
        ((subgroup_group G S, normalizer_subgroup_hom G S), normalizer_subgroup_mono G S)
        ((K, k), kernel_inclusion_mono N (weyl_group G S) (weyl_projection G S))
        (weyl_kernel_homs_path G S))

{` "j_H defines H as a normal subgroup of the normalizer". `}
def normalizer_subgroup_normal (G : Group) (S : Subgroups G)
  : IsNormalSubgroup (normalizer_group G S) (mono_to_subgroup (normalizer_group G S) (normalizer_subgroup_as_mono G S))
  ≔ let N ≔ normalizer_group G S in
    transport (GroupMonos N) (m ↦ IsNormalSubgroup N (mono_to_subgroup N m))
      (kernel N (weyl_group G S) (weyl_projection G S)) (normalizer_subgroup_as_mono G S)
      (inverse (GroupMonos N) (normalizer_subgroup_as_mono G S) (kernel N (weyl_group G S) (weyl_projection G S))
        (weyl_kernel_mono_path G S))
      (kernel_normal N (weyl_group G S) (weyl_projection G S) (weyl_projection_connected G S))

{` H as an element of Nor(N_GH), with quotient N_G(H)/H. `}
def normalizer_subgroup_normal_element (G : Group) (S : Subgroups G) : NormalSubgroups (normalizer_group G S)
  ≔ nor_conn (normalizer_group G S) (weyl_group G S, (weyl_projection G S, weyl_projection_connected G S))

def normalizer_subgroup_normal_element_underlying (G : Group) (S : Subgroups G)
  : Id (Subgroups (normalizer_group G S)) (normal_to_subgroup (normalizer_group G S) (normalizer_subgroup_normal_element G S))
      (mono_to_subgroup (normalizer_group G S) (normalizer_subgroup_as_mono G S))
  ≔ let N ≔ normalizer_group G S in
    concat (Subgroups N) (normal_to_subgroup N (normalizer_subgroup_normal_element G S))
      (mono_to_subgroup N (kernel N (weyl_group G S) (weyl_projection G S)))
      (mono_to_subgroup N (normalizer_subgroup_as_mono G S))
      (diag_for_normal N (weyl_group G S) (weyl_projection G S) (weyl_projection_connected G S))
      (map_path (GroupMonos N) (Subgroups N) (mono_to_subgroup N) (kernel N (weyl_group G S) (weyl_projection G S))
        (normalizer_subgroup_as_mono G S)
        (inverse (GroupMonos N) (normalizer_subgroup_as_mono G S) (kernel N (weyl_group G S) (weyl_projection G S))
          (weyl_kernel_mono_path G S)))

{` lem:aut-orbit: Aut_{G-Set}(G/H) ≡ W_GH ≅ N_G(H)/H, compatibly with the
   projections (Q ∘ p_G^H = q_H). `}
def aut_orbit_iso (G : Group) (S : Subgroups G)
  : GroupIso (weyl_group G S)
      (normal_quotient_group (normalizer_group G S) (normalizer_subgroup_normal_element G S))
  ≔ (qeq_Q (normalizer_group G S) (weyl_group G S) (weyl_projection G S) (weyl_projection_connected G S),
     qeq_Q_iso (normalizer_group G S) (weyl_group G S) (weyl_projection G S) (weyl_projection_connected G S))

def aut_orbit_compat (G : Group) (S : Subgroups G)
  : Id (GroupHom (normalizer_group G S)
        (normal_quotient_group (normalizer_group G S) (normalizer_subgroup_normal_element G S)))
      (group_hom_compose (normalizer_group G S) (weyl_group G S)
        (normal_quotient_group (normalizer_group G S) (normalizer_subgroup_normal_element G S))
        (weyl_projection G S) (aut_orbit_iso G S .fst))
      (normal_quotient_hom (normalizer_group G S) (normalizer_subgroup_normal_element G S))
  ≔ qeq_Q_compose_path (normalizer_group G S) (weyl_group G S) (weyl_projection G S) (weyl_projection_connected G S)
