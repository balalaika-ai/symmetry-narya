export "501-transitive-gsets"

{` Chapter 5, sec:subgroups: subgroups as pointed transitive G-sets
   (def:set-of-subgroups), their underlying groups, Sub(G) is a set
   (lem:SubGisset), monomorphisms (def:typeofmono) and the maps F and E of
   lem:SubG=MonoG. `}

{` def:set-of-subgroups. Sub(G) ≔ Σ_{X:BG→Set} X(sh_G) × istrans(X), as a
   record with the three components in the printed order
   (subgroups_sigma_equiv is the literal Σ-type). `}
def Subgroups (G : Group) : Type
  ≔ sig (gset : GSet G, point : gset_underlying G gset, transitive : IsTransitive G gset)

def SubgroupsSigma (G : Group) : Type
  ≔ Σ (GSet G) (X ↦ Product (gset_underlying G X) (IsTransitive G X))

def subgroups_sigma_equiv (G : Group) : Equiv (Subgroups G) (SubgroupsSigma G)
  ≔ quasi_inverse_equiv (Subgroups G) (SubgroupsSigma G)
      (S ↦ (S .gset, (S .point, S .transitive))) (u ↦ (u .fst, u .snd .fst, u .snd .snd))
      (S ↦ refl S) (u ↦ refl u)

{` xca:group-Xx!. For a transitive G-set X, Σ_{z:BG} X(z) is a connected
   groupoid. `}
def transitive_action_type_pcg (G : Group) (X : GSet G) (x : gset_underlying G X) (t : IsTransitive G X)
  : PointedConnectedGroupoid
  ≔ (ActionType G X, (shape G, x), transitive_action_type_connected G X t, action_type_groupoid G X)

{` def:underlying-group-of-subgroup. mkgroup(Tot(X), (sh_G, pt)). `}
def subgroup_group (G : Group) (S : Subgroups G) : Group
  ≔ mkgroup (transitive_action_type_pcg G (S .gset) (S .point) (S .transitive))

def subgroup_group_classifying (G : Group) (S : Subgroups G)
  : Id Pointed (BG (subgroup_group G S)) (ActionType G (S .gset), (shape G, S .point))
  ≔ refl (BG (subgroup_group G S))

{` lem:SubGisset. Pointed G-sets (X, x) and their identity types:
   ((X, x) = (X', x')) ≃ Σ_{e : X = X'} (ev_x(e) = x'), the fiber of ev_x
   at x', a proposition when X is transitive. `}
def PointedGSet (G : Group) : Type ≔ Σ (GSet G) (X ↦ gset_underlying G X)

def pointed_gset_path_fiber_equiv (G : Group) (u v : PointedGSet G)
  : Equiv (Id (PointedGSet G) u v)
      (Fiber (Id (GSet G) (u .fst) (v .fst)) (gset_underlying G (v .fst))
        (gset_path_eval G (u .fst) (v .fst) (shape G) (u .snd)) (v .snd))
  ≔ let F : GSet G → Type ≔ W ↦ W (shape G) .fst in
    compose_equiv (Id (PointedGSet G) u v) (SigmaPath (GSet G) F u v)
      (Fiber (Id (GSet G) (u .fst) (v .fst)) (gset_underlying G (v .fst))
        (gset_path_eval G (u .fst) (v .fst) (shape G) (u .snd)) (v .snd))
      (canonical_inverse_equiv (SigmaPath (GSet G) F u v) (Id (PointedGSet G) u v) (sigma_path_equiv (GSet G) F u v))
      (family_equiv (Id (GSet G) (u .fst) (v .fst)) (e ↦ Id F e (u .snd) (v .snd))
        (e ↦ Id (gset_underlying G (v .fst)) (gset_path_eval G (u .fst) (v .fst) (shape G) (u .snd) e) (v .snd))
        (e ↦ pathover_transport_equiv (GSet G) F (u .fst) (v .fst) e (u .snd) (v .snd)))

def pointed_gset_paths_prop (G : Group) (u v : PointedGSet G) (hX : IsTransitive G (u .fst))
  : isProp (Id (PointedGSet G) u v)
  ≔ let f ≔ gset_path_eval G (u .fst) (v .fst) (shape G) (u .snd) in
    let A ≔ Id (GSet G) (u .fst) (v .fst) in
    let S ≔ gset_underlying G (v .fst) in
    let e ≔ pointed_gset_path_fiber_equiv G u v in
    let fiber_prop : isProp (Fiber A S f (v .snd))
      ≔ retract_prop (BookFiber A S f (v .snd)) (Fiber A S f (v .snd))
          (gset_path_eval_injective G (u .fst) (v .fst) (shape G) (u .snd) hX (v .snd))
          (fiber_from_book A S f (v .snd)) (fiber_to_book A S f (v .snd))
          (t ↦ (refl (t .fst), inverse_inverse S (f (t .fst)) (v .snd) (t .snd))) in
    retract_prop (Fiber A S f (v .snd)) (Id (PointedGSet G) u v) fiber_prop
      (equiv_inverse_map (Id (PointedGSet G) u v) (Fiber A S f (v .snd)) e) (e .map)
      (equiv_retraction (Id (PointedGSet G) u v) (Fiber A S f (v .snd)) e)

def SubgroupsPairs (G : Group) : Type ≔ Σ (PointedGSet G) (u ↦ IsTransitive G (u .fst))

def subgroups_pairs_equiv (G : Group) : Equiv (Subgroups G) (SubgroupsPairs G)
  ≔ quasi_inverse_equiv (Subgroups G) (SubgroupsPairs G)
      (S ↦ ((S .gset, S .point), S .transitive)) (u ↦ (u .fst .fst, u .fst .snd, u .snd))
      (S ↦ refl S) (u ↦ refl u)

def subgroups_pairs_set (G : Group) : isSet (SubgroupsPairs G)
  ≔ u v ↦
    let e ≔ subtype_path_equiv (PointedGSet G) (w ↦ IsTransitive G (w .fst)) (w ↦ is_transitive_prop G (w .fst)) u v in
    retract_prop (Id (PointedGSet G) (u .fst) (v .fst)) (Id (SubgroupsPairs G) u v)
      (pointed_gset_paths_prop G (u .fst) (v .fst) (u .snd))
      (equiv_inverse_map (Id (SubgroupsPairs G) u v) (Id (PointedGSet G) (u .fst) (v .fst)) e) (e .map)
      (equiv_retraction (Id (SubgroupsPairs G) u v) (Id (PointedGSet G) (u .fst) (v .fst)) e)

def subgroups_set (G : Group) : isSet (Subgroups G)
  ≔ hlevel_two_to_set (Subgroups G)
      (hlevel_equiv (suc. (suc. zero.)) (SubgroupsPairs G) (Subgroups G)
        (canonical_inverse_equiv (Subgroups G) (SubgroupsPairs G) (subgroups_pairs_equiv G))
        (set_to_hlevel_two (SubgroupsPairs G) (subgroups_pairs_set G)))

{` def:decidable-subgroup. `}
def IsDecidableSubgroup (G : Group) (S : Subgroups G) : Type
  ≔ DecidableEquality (gset_underlying G (S .gset))

{` def:typeofmono. i : Hom(H, G) is a monomorphism if USym i is an
   injection (all its preimages are propositions). `}
def IsGroupMono (H G : Group) (i : GroupHom H G) : Type
  ≔ IsEmbedding (USym H) (USym G) (usym_hom H G i)

def is_group_mono_prop (H G : Group) (i : GroupHom H G) : isProp (IsGroupMono H G i)
  ≔ pi_prop (USym G) (g ↦ isProp (BookFiber (USym H) (USym G) (usym_hom H G i) g))
      (g ↦ isprop_isprop (BookFiber (USym H) (USym G) (usym_hom H G i) g))

{` Mono(G) ≔ Σ_{H:Group} Σ_{i:Hom(H,G)} ismono(i). `}
def GroupMonos (G : Group) : Type
  ≔ Σ Group (H ↦ Σ (GroupHom H G) (i ↦ IsGroupMono H G i))

{` A group H is trivial if its classifying type BH is contractible (the
   formulation used in def:triv-proper-Mono: "the underlying group is
   trivial, i.e. Tot(X) is contractible"); equivalently USym H is
   contractible, equivalently H = TG (module 506). `}
def IsTrivialGroup (H : Group) : Type ≔ BookIsContr (BG H .carrier)

def is_trivial_group_prop (H : Group) : isProp (IsTrivialGroup H) ≔ book_iscontr_isprop (BG H .carrier)

{` def:typeofmono (1)-(2): a monomorphism (H, i) is trivial if H is the
   trivial group, proper if i is not an isomorphism. `}
def IsTrivialMono (G : Group) (m : GroupMonos G) : Type ≔ IsTrivialGroup (m .fst)

def IsProperMono (G : Group) (m : GroupMonos G) : Type ≔ IsGroupIso (m .fst) G (m .snd .fst) → Empty

{` def:triv-proper-Mono: a subgroup (X, pt) is trivial if Tot(X) is
   contractible, proper if X(sh_G) is not contractible. `}
def IsTrivialSubgroup (G : Group) (S : Subgroups G) : Type ≔ BookIsContr (ActionType G (S .gset))

def IsProperSubgroup (G : Group) (S : Subgroups G) : Type
  ≔ BookIsContr (gset_underlying G (S .gset)) → Empty

{` Conjugation of loops by a path is injective. `}
def mono_loop_conjugate_injective (A : Type) (a x : A) (p : Id A a x) (l l' : Id A x x)
  (e : Id (Id A a a) (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p l'))
  : Id (Id A x x) l l'
  ≔ concat_cancel_right A x x a l l' (inverse A a x p)
      (concat_cancel_left A a x a p (concat A x x a l (inverse A a x p)) (concat A x x a l' (inverse A a x p)) e)

{` cor:fib-vs-path (set-fib-vs-path-point), as used in sec:subgroups-mono:
   USym i is injective iff Bi is a covering (BH connected). `}
def group_mono_ap_reflects (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  : PathReflecting (USym H) (Id (BG G .carrier) (hom_function H G i (shape H)) (hom_function H G i (shape H)))
      (map_path (BG H .carrier) (BG G .carrier) (hom_function H G i) (shape H) (shape H))
  ≔ let B ≔ BG G .carrier in
    let b ≔ hom_function H G i (shape H) in
    l l' e ↦ embedding_reflects_paths (USym H) (USym G) (usym_hom H G i) m l l'
      (map_path (Id B b b) (USym G) (pointed_loop_conjugate B (shape G) b (hom_point H G i))
        (map_path (BG H .carrier) B (hom_function H G i) (shape H) (shape H) l)
        (map_path (BG H .carrier) B (hom_function H G i) (shape H) (shape H) l') e)

def group_mono_covering (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  : IsCovering (BG H .carrier) (BG G .carrier) (hom_function H G i)
  ≔ let A ≔ BG H .carrier in
    let B ≔ BG G .carrier in
    let f ≔ hom_function H G i in
    let a ≔ shape H in
    y ↦ hlevel_two_to_set (BookFiber A B f y)
      (loop_fibers_to_fibers native_truncation (suc. zero.) A B f (bg_connected H) a
        (p ↦ prop_to_hlevel_one (BookFiber (Id A a a) (Id B (f a) (f a)) (map_path A B f a a) p)
          (path_reflecting_set_embedding (Id A a a) (Id B (f a) (f a)) (bg_groupoid G (f a) (f a))
            (map_path A B f a a) (group_mono_ap_reflects H G i m) p))
        y)

def covering_group_mono (H G : Group) (i : GroupHom H G)
  (c : IsCovering (BG H .carrier) (BG G .carrier) (hom_function H G i)) : IsGroupMono H G i
  ≔ let A ≔ BG H .carrier in
    let B ≔ BG G .carrier in
    let f ≔ hom_function H G i in
    let a ≔ shape H in
    path_reflecting_set_embedding (USym H) (USym G) (usym_set G) (usym_hom H G i)
      (l l' e ↦ embedding_reflects_paths (Id A a a) (Id B (f a) (f a)) (map_path A B f a a)
        (p ↦ hlevel_one_to_prop (BookFiber (Id A a a) (Id B (f a) (f a)) (map_path A B f a a) p)
          (fibers_hlevel_to_ap (suc. zero.) A B f (y ↦ set_to_hlevel_two (BookFiber A B f y) (c y)) a a p))
        l l'
        (mono_loop_conjugate_injective B (shape G) (f a) (hom_point H G i)
          (map_path A B f a a l) (map_path A B f a a l') e))

{` rem:G-set-vs-set-bundle: the first projection Tot(X) → BG is a covering. `}
def action_type_projection_covering (G : Group) (X : GSet G)
  : IsCovering (ActionType G X) (BG G .carrier) (u ↦ u .fst)
  ≔ setfamily_to_covering (BG G .carrier) X .snd

{` lem:SubG=MonoG, the map F: (X, pt) ↦ (mkgroup(Tot(X), (sh_G, pt)), mkgroup(fst)),
   fst pointed by reflexivity. `}
def subgroup_inclusion (G : Group) (S : Subgroups G) : GroupHom (subgroup_group G S) G
  ≔ mkhom (subgroup_group G S) G (u ↦ u .fst, refl (shape G))

def subgroup_inclusion_mono (G : Group) (S : Subgroups G)
  : IsGroupMono (subgroup_group G S) G (subgroup_inclusion G S)
  ≔ covering_group_mono (subgroup_group G S) G (subgroup_inclusion G S)
      (action_type_projection_covering G (S .gset))

def subgroup_to_mono (G : Group) (S : Subgroups G) : GroupMonos G
  ≔ (subgroup_group G S, (subgroup_inclusion G S, subgroup_inclusion_mono G S))

{` lem:SubG=MonoG, the map E: (H, i) ↦ (Bi÷⁻¹, (sh_H, Bi_pt)). The preimage
   family z ↦ Σ_{x:BH} (z = Bi(x)) is a transitive G-set because Bi is a
   covering with connected domain. `}
def mono_gset (G : Group) (m : GroupMonos G) : GSet G
  ≔ z ↦ (BookFiber (BG (m .fst) .carrier) (BG G .carrier) (hom_function (m .fst) G (m .snd .fst)) z,
      group_mono_covering (m .fst) G (m .snd .fst) (m .snd .snd) z)

def mono_gset_transitive (G : Group) (m : GroupMonos G) : IsTransitive G (mono_gset G m)
  ≔ let A ≔ BG (m .fst) .carrier in
    let f ≔ hom_function (m .fst) G (m .snd .fst) in
    connected_action_type_transitive G (mono_gset G m)
      (connected_equiv A (ActionType G (mono_gset G m))
        (canonical_inverse_equiv (ActionType G (mono_gset G m)) A (sum_of_fibers_equiv A (BG G .carrier) f))
        .map (bg_connected (m .fst)))

def mono_to_subgroup (G : Group) (m : GroupMonos G) : Subgroups G
  ≔ (mono_gset G m, (shape (m .fst), hom_point (m .fst) G (m .snd .fst)), mono_gset_transitive G m)
