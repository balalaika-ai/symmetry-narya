export "507-subgroups-monos-equiv"

{` Chapter 5, sec:torsors: torsors are the free transitive G-sets
   (xca:torsor=free+transitive), Torsor_G as a component of the type of G-sets
   and of coverings over BG, the group classified by (Torsor_G, P_G)
   (remark after xca:torsor=free+transitive), and the variants of P_- on paths
   (rem:pathsptransport). `}

{` xca:torsor=free+transitive (⇒). `}
def torsor_transitive (G : Group) (X : GSet G) (t : Mere (Id (GSet G) (principal_gset G) X)) : IsTransitive G X
  ≔ mere_rec (Id (GSet G) (principal_gset G) X) (IsTransitive G X) (is_transitive_prop G X)
      (p ↦ transport (GSet G) (IsTransitive G) (principal_gset G) X p (principal_gset_transitive G)) t

def torsor_free (G : Group) (X : GSet G) (t : Mere (Id (GSet G) (principal_gset G) X)) : IsFreeGSet G X
  ≔ mere_rec (Id (GSet G) (principal_gset G) X) (IsFreeGSet G X) (is_free_gset_prop G X)
      (p ↦ transport (GSet G) (IsFreeGSet G) (principal_gset G) X p (principal_gset_free G)) t

{` A connected type is equivalent to each of its components. `}
def connected_component_equiv (A : Type) (c : Connected A) (a : A) : Equiv A (NativeComponent A a)
  ≔ quasi_inverse_equiv A (NativeComponent A a) (v ↦ (v, c .snd a v)) (w ↦ w .fst)
      (v ↦ refl v)
      (w ↦ subtype_equal A (v ↦ Mere (Id A a v)) (v ↦ mere_isprop (Id A a v)) (w .fst, c .snd a (w .fst)) w
        (refl (w .fst)))

{` A free transitive G-set has a contractible action type. `}
def free_transitive_action_type_contractible (G : Group) (X : GSet G) (hf : IsFreeGSet G X) (ht : IsTransitive G X)
  (x0 : gset_underlying G X) : BookIsContr (ActionType G X)
  ≔ let T ≔ ActionType G X in
    book_contractibility_equiv (NativeComponent T (shape G, x0)) T
      (canonical_inverse_equiv T (NativeComponent T (shape G, x0))
        (connected_component_equiv T (transitive_action_type_connected G X ht) (shape G, x0)))
      .map (hf x0)

{` A G-set with contractible action type and a point x0 : X(sh) is
   identified with P_G by p ↦ p · x0. `}
def contractible_action_type_principal_path (G : Group) (X : GSet G) (x0 : gset_underlying G X)
  (h : BookIsContr (ActionType G X)) : Id (GSet G) (principal_gset G) X
  ≔ let B ≔ BG G .carrier in
    let P ≔ principal_gset G in
    let f : (z : B) → P z .fst → X z .fst ≔ z p ↦ gset_act G X (shape G) z p x0 in
    gset_path_from_equivs G P X
      (z ↦ (f z, fiberwise_from_total B (w ↦ P w .fst) (w ↦ X w .fst) f
        (contractible_map_equiv (ActionType G P) (ActionType G X) (totalize B (w ↦ P w .fst) (w ↦ X w .fst) f)
          (gset_paths_action_type_contractible G (shape G)) h) z))

{` xca:torsor=free+transitive (⇐). `}
def free_transitive_torsor (G : Group) (X : GSet G) (hf : IsFreeGSet G X) (ht : IsTransitive G X)
  : Mere (Id (GSet G) (principal_gset G) X)
  ≔ let S ≔ gset_underlying G X in
    mere_rec (Σ S (x ↦ (y : S) → Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))))
      (Mere (Id (GSet G) (principal_gset G) X)) (mere_isprop (Id (GSet G) (principal_gset G) X))
      (xh ↦ mere (Id (GSet G) (principal_gset G) X)
        (contractible_action_type_principal_path G X (xh .fst)
          (free_transitive_action_type_contractible G X hf ht (xh .fst))))
      ht

def torsor_iff_free_transitive (G : Group) (X : GSet G)
  : Product (Mere (Id (GSet G) (principal_gset G) X) → Product (IsFreeGSet G X) (IsTransitive G X))
      (Product (IsFreeGSet G X) (IsTransitive G X) → Mere (Id (GSet G) (principal_gset G) X))
  ≔ (t ↦ (torsor_free G X t, torsor_transitive G X t), h ↦ free_transitive_torsor G X (h .fst) (h .snd))

{` Remark after xca:torsor=free+transitive: Torsor_G is (by definition) the
   component of the type of G-sets at P_G. `}
def torsors_component (G : Group) : Id Type (Torsors G) (NativeComponent (GSet G) (principal_gset G))
  ≔ refl (Torsors G)

{` ... and corresponds to the component of the type of coverings over BG
   containing the universal covering (Tot(P_G), fst) (whose domain
   Σ_z (sh_G = z) is contractible). `}
def universal_covering_over (G : Group) : Coverings (BG G .carrier)
  ≔ (ActionType G (principal_gset G), (u ↦ u .fst, action_type_projection_covering G (principal_gset G)))

def universal_covering_domain_contractible (G : Group) : BookIsContr (universal_covering_over G .fst)
  ≔ gset_paths_action_type_contractible G (shape G)

def universal_covering_fibers_path (G : Group)
  : Id (GSet G) (principal_gset G) (coverings_setfamilies_equiv (BG G .carrier) .map (universal_covering_over G))
  ≔ inverse (GSet G) (coverings_setfamilies_equiv (BG G .carrier) .map (universal_covering_over G)) (principal_gset G)
      (gset_path_from_equivs G (coverings_setfamilies_equiv (BG G .carrier) .map (universal_covering_over G))
        (principal_gset G) (z ↦ action_type_fiber_equiv G (principal_gset G) z))

def torsors_coverings_component_equiv (G : Group)
  : Equiv (NativeComponent (Coverings (BG G .carrier)) (universal_covering_over G)) (Torsors G)
  ≔ let C ≔ Coverings (BG G .carrier) in
    let e ≔ coverings_setfamilies_equiv (BG G .carrier) in
    let u ≔ universal_covering_over G in
    let q ≔ universal_covering_fibers_path G in
    sigma_equivalences C (GSet G) (c ↦ Mere (Id C u c)) (X ↦ Mere (Id (GSet G) (principal_gset G) X)) e
      (c ↦ iff_equiv (Mere (Id C u c)) (Mere (Id (GSet G) (principal_gset G) (e .map c)))
        (mere_isprop (Id C u c)) (mere_isprop (Id (GSet G) (principal_gset G) (e .map c)))
        (mere_rec (Id C u c) (Mere (Id (GSet G) (principal_gset G) (e .map c)))
          (mere_isprop (Id (GSet G) (principal_gset G) (e .map c)))
          (r ↦ mere (Id (GSet G) (principal_gset G) (e .map c))
            (concat (GSet G) (principal_gset G) (e .map u) (e .map c) q (map_path C (GSet G) (e .map) u c r))))
        (mere_rec (Id (GSet G) (principal_gset G) (e .map c)) (Mere (Id C u c)) (mere_isprop (Id C u c))
          (s ↦ mere (Id C u c)
            (equivalence_injective C (GSet G) e u c
              (concat (GSet G) (e .map u) (principal_gset G) (e .map c) (inverse (GSet G) (principal_gset G) (e .map u) q) s)))))

{` "It classifies a group. Guess which one!": the group (Torsor_G, P_G) is G,
   by lem:BGbytorsor. `}
def torsor_group (G : Group) : Group
  ≔ mkgroup (Torsors G, principal_torsor G, torsors_connected G, torsors_groupoid G)

def torsor_group_path (G : Group) : Id Group G (torsor_group G)
  ≔ group_path_from_pointed_equiv G (torsor_group G) (bg_to_torsors_pointed G, bg_to_torsors_is_equiv G)

{` rem:pathsptransport. For q : y = z: the action on paths of P_- (map_path,
   core 504), its pointwise form Π_x (P_y(x) = P_z(x)) (function
   extensionality), and the pointwise equivalence = transport in the family
   P_-(x), which sends p : y = x to p q⁻¹ = concat q⁻¹ p. `}
def gset_paths_pointwise (G : Group) (y z : BG G .carrier) (q : Id (BG G .carrier) y z) (x : BG G .carrier)
  : Id SetTypes (gset_paths G y x) (gset_paths G z x)
  ≔ happly (BG G .carrier) (_ ↦ SetTypes) (gset_paths G y) (gset_paths G z)
      (map_path (BG G .carrier) (GSet G) (gset_paths G) y z q) x

def gset_paths_family_transport (G : Group) (y z x : BG G .carrier) (q : Id (BG G .carrier) y z)
  (p : Id (BG G .carrier) y x)
  : Id (Id (BG G .carrier) z x) (transport (BG G .carrier) (w ↦ Id (BG G .carrier) w x) y z q p)
      (concat (BG G .carrier) z y x (inverse (BG G .carrier) y z q) p)
  ≔ let B ≔ BG G .carrier in
    J B y (z q ↦ Id (Id B z x) (transport B (w ↦ Id B w x) y z q p) (concat B z y x (inverse B y z q) p))
      (concat (Id B y x) (transport B (w ↦ Id B w x) y y (refl y) p) p (concat B y y x (inverse B y y (refl y)) p)
        (transport_refl B (w ↦ Id B w x) y p)
        (inverse (Id B y x) (concat B y y x (inverse B y y (refl y)) p) p (inverse_refl_concat B y x p)))
      z q
