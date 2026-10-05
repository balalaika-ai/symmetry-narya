export "506-trivial-groups"

{` Chapter 5, sec:subgroups-mono: lem:SubG=MonoG and xca:SubG=MonoG (the map
   F : Sub(G) → Mono(G) is an equivalence with inverse E),
   lem:setofsubgroups (Mono(G) is a set) and lem:E-preserves-symms. `}

{` The fiber of fst : Tot(X) → BG at z is X(z): ((z', x'), q : z = z') ↦ q⁻¹ · x',
   with inverse x ↦ ((z, x), refl z). `}
def action_type_fiber_map (G : Group) (X : GSet G) (z : BG G .carrier)
  (u : BookFiber (ActionType G X) (BG G .carrier) (v ↦ v .fst) z) : X z .fst
  ≔ gset_act G X (u .fst .fst) z (inverse (BG G .carrier) z (u .fst .fst) (u .snd)) (u .fst .snd)

def action_type_fiber_section (G : Group) (X : GSet G) (z : BG G .carrier) (x : X z .fst)
  : Id (X z .fst) (action_type_fiber_map G X z ((z, x), refl z)) x
  ≔ concat (X z .fst) (gset_act G X z z (inverse (BG G .carrier) z z (refl z)) x) (gset_act G X z z (refl z) x) x
      (map_path (Id (BG G .carrier) z z) (X z .fst) (r ↦ gset_act G X z z r x)
        (inverse (BG G .carrier) z z (refl z)) (refl z) (inverse_refl (BG G .carrier) z))
      (gset_act_refl G X z x)

def action_type_fiber_retraction (G : Group) (X : GSet G) (z : BG G .carrier)
  (u : BookFiber (ActionType G X) (BG G .carrier) (v ↦ v .fst) z)
  : Id (BookFiber (ActionType G X) (BG G .carrier) (v ↦ v .fst) z)
      ((z, action_type_fiber_map G X z u), refl z) u
  ≔ let B ≔ BG G .carrier in
    let F ≔ BookFiber (ActionType G X) B (v ↦ v .fst) z in
    J B z
      (z' q ↦ (x' : X z' .fst) →
        Id F ((z, action_type_fiber_map G X z ((z', x'), q)), refl z) ((z', x'), q))
      (x' ↦ map_path (X z .fst) F (y ↦ ((z, y), refl z))
        (action_type_fiber_map G X z ((z, x'), refl z)) x' (action_type_fiber_section G X z x'))
      (u .fst .fst) (u .snd) (u .fst .snd)

def action_type_fiber_equiv (G : Group) (X : GSet G) (z : BG G .carrier)
  : Equiv (BookFiber (ActionType G X) (BG G .carrier) (v ↦ v .fst) z) (X z .fst)
  ≔ quasi_inverse_equiv (BookFiber (ActionType G X) (BG G .carrier) (v ↦ v .fst) z) (X z .fst)
      (action_type_fiber_map G X z) (x ↦ ((z, x), refl z))
      (action_type_fiber_retraction G X z) (action_type_fiber_section G X z)

{` xca:SubG=MonoG, first round trip: E(F(X, pt)) = (X, pt). `}
def subgroup_mono_roundtrip (G : Group) (S : Subgroups G)
  : Id (Subgroups G) (mono_to_subgroup G (subgroup_to_mono G S)) S
  ≔ subgroup_path G (mono_to_subgroup G (subgroup_to_mono G S)) S
      (pointed_gset_path G (mono_gset G (subgroup_to_mono G S)) (S .gset)
        ((shape G, S .point), refl (shape G)) (S .point)
        (z ↦ action_type_fiber_equiv G (S .gset) z)
        (action_type_fiber_section G (S .gset) (shape G) (S .point)))

{` Identifications of pointed maps over a pointed type B from a pointed
   equivalence e : X ≃* Y and a pointed homotopy f ∘ e ~ g (pointed
   equivalence induction via the contractibility of Σ_Y (X ≃* Y)). `}
def PointedMapsOver (B : Pointed) : Type ≔ Σ Pointed (Z ↦ BookPointedMap Z B)

def pointed_identity_equiv (X : Pointed) : BookPointedEquiv X X
  ≔ (book_pointed_identity X, book_equivalence (X .carrier) (X .carrier) (identity_equiv (X .carrier)) .equiv)

def pointed_compose_identity_homotopy (X B : Pointed) (f : BookPointedMap X B)
  : PointedHomotopy X B (book_pointed_compose X X B (book_pointed_identity X) f) f
  ≔ let b ≔ f .fst (X .point) in
    (x ↦ refl (f .fst x),
     concat (Id (B .carrier) (B .point) b)
       (concat (B .carrier) (B .point) b b (concat (B .carrier) (B .point) b b (f .snd) (refl b)) (refl b))
       (concat (B .carrier) (B .point) b b (f .snd) (refl b)) (f .snd)
       (concat_p1 (B .carrier) (B .point) b (concat (B .carrier) (B .point) b b (f .snd) (refl b)))
       (concat_p1 (B .carrier) (B .point) b (f .snd)))

def pointed_over_family (B X : Pointed) (g : BookPointedMap X B) (w : Σ Pointed (Y ↦ BookPointedEquiv X Y)) : Type
  ≔ (f : BookPointedMap (w .fst) B) → PointedHomotopy X B (book_pointed_compose X (w .fst) B (w .snd .fst) f) g
      → Id (PointedMapsOver B) (X, g) (w .fst, f)

def pointed_over_base (B X : Pointed) (g : BookPointedMap X B)
  : pointed_over_family B X g (X, pointed_identity_equiv X)
  ≔ f h ↦
    let M ≔ BookPointedMap X B in
    let c ≔ book_pointed_compose X X B (book_pointed_identity X) f in
    let p1 : Id M c g ≔ equiv_inverse_map (Id M c g) (PointedHomotopy X B c g) (pointed_map_path_equiv X B c g) h in
    let p2 : Id M c f ≔ equiv_inverse_map (Id M c f) (PointedHomotopy X B c f) (pointed_map_path_equiv X B c f)
      (pointed_compose_identity_homotopy X B f) in
    map_path M (PointedMapsOver B) (k ↦ (X, k)) g f (concat M g c f (inverse M c g p1) p2)

def pointed_over_path (B X Y : Pointed) (g : BookPointedMap X B) (f : BookPointedMap Y B)
  (e : BookPointedEquiv X Y) (h : PointedHomotopy X B (book_pointed_compose X Y B (e .fst) f) g)
  : Id (PointedMapsOver B) (X, g) (Y, f)
  ≔ let T ≔ Σ Pointed (Z ↦ BookPointedEquiv X Z) in
    let c ≔ pointed_equivalences_total_contractible X in
    let i : T ≔ (X, pointed_identity_equiv X) in
    transport T (pointed_over_family B X g) i (Y, e)
      (concat T i (c .center) (Y, e) (inverse T (c .center) i (c .contract i)) (c .contract (Y, e)))
      (pointed_over_base B X g) f h

{` Monomorphisms as pointed maps over BG with the remaining (propositional)
   data; repackaging is definitional. `}
def MonoData (G : Group) : Type
  ≔ Σ (PointedMapsOver (BG G)) (w ↦ Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
      (IsEmbedding (Loop (w .fst)) (USym G) (loops_map (w .fst) (BG G) (w .snd))))

def mono_data_prop (G : Group) (w : PointedMapsOver (BG G))
  : isProp (Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
      (IsEmbedding (Loop (w .fst)) (USym G) (loops_map (w .fst) (BG G) (w .snd))))
  ≔ product_prop (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
      (IsEmbedding (Loop (w .fst)) (USym G) (loops_map (w .fst) (BG G) (w .snd)))
      (product_prop (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier))
        (connected_isprop (w .fst .carrier)) (isgroupoid_isprop (w .fst .carrier)))
      (pi_prop (USym G) (b ↦ isProp (BookFiber (Loop (w .fst)) (USym G) (loops_map (w .fst) (BG G) (w .snd)) b))
        (b ↦ isprop_isprop (BookFiber (Loop (w .fst)) (USym G) (loops_map (w .fst) (BG G) (w .snd)) b)))

def mono_data_to_mono (G : Group) (d : MonoData G) : GroupMonos G
  ≔ (mkgroup (d .fst .fst .carrier, d .fst .fst .point, d .snd .fst .fst, d .snd .fst .snd),
     (mkhom (mkgroup (d .fst .fst .carrier, d .fst .fst .point, d .snd .fst .fst, d .snd .fst .snd)) G (d .fst .snd),
      d .snd .snd))

def mono_to_mono_data (G : Group) (m : GroupMonos G) : MonoData G
  ≔ ((BG (m .fst), hom_B (m .fst) G (m .snd .fst)),
     ((bg_connected (m .fst), bg_groupoid (m .fst)), m .snd .snd))

{` xca:SubG=MonoG, second round trip: F(E(H, i)) = (H, i). The sum of the
   fibers of Bi is identified with BH (lem:sum-of-fibers), pointed by
   reflexivity, and Bi ∘ (that equivalence) is fst up to the fiber paths. `}
def mono_roundtrip_equiv (G : Group) (m : GroupMonos G)
  : BookPointedEquiv (BG (subgroup_group G (mono_to_subgroup G m))) (BG (m .fst))
  ≔ ((s ↦ s .snd .fst, refl (shape (m .fst))),
     book_sum_of_fibers_equiv (BG (m .fst) .carrier) (BG G .carrier) (hom_function (m .fst) G (m .snd .fst)) .equiv)

def mono_roundtrip_homotopy (G : Group) (m : GroupMonos G)
  : PointedHomotopy (BG (subgroup_group G (mono_to_subgroup G m))) (BG G)
      (book_pointed_compose (BG (subgroup_group G (mono_to_subgroup G m))) (BG (m .fst)) (BG G)
        (mono_roundtrip_equiv G m .fst) (hom_B (m .fst) G (m .snd .fst)))
      (hom_B (subgroup_group G (mono_to_subgroup G m)) G (subgroup_inclusion G (mono_to_subgroup G m)))
  ≔ let B ≔ BG G .carrier in
    let b ≔ hom_function (m .fst) G (m .snd .fst) (shape (m .fst)) in
    let p ≔ hom_point (m .fst) G (m .snd .fst) in
    (s ↦ inverse B (s .fst) (hom_function (m .fst) G (m .snd .fst) (s .snd .fst)) (s .snd .snd),
     concat (Id B (shape G) (shape G))
       (concat B (shape G) b (shape G) (concat B (shape G) b b p (refl b)) (inverse B (shape G) b p))
       (concat B (shape G) b (shape G) p (inverse B (shape G) b p)) (refl (shape G))
       (map_path (Id B (shape G) b) (Id B (shape G) (shape G)) (t ↦ concat B (shape G) b (shape G) t (inverse B (shape G) b p))
         (concat B (shape G) b b p (refl b)) p (concat_p1 B (shape G) b p))
       (concat_inverse_right B (shape G) b p))

def mono_subgroup_roundtrip (G : Group) (m : GroupMonos G)
  : Id (GroupMonos G) (subgroup_to_mono G (mono_to_subgroup G m)) m
  ≔ let S ≔ mono_to_subgroup G m in
    let H' ≔ subgroup_group G S in
    let B ≔ BG G in
    map_path (MonoData G) (GroupMonos G) (mono_data_to_mono G)
      (mono_to_mono_data G (subgroup_to_mono G S)) (mono_to_mono_data G m)
      (subtype_equal (PointedMapsOver B)
        (w ↦ Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
          (IsEmbedding (Loop (w .fst)) (USym G) (loops_map (w .fst) B (w .snd))))
        (mono_data_prop G)
        (mono_to_mono_data G (subgroup_to_mono G S)) (mono_to_mono_data G m)
        (pointed_over_path B (BG H') (BG (m .fst)) (hom_B H' G (subgroup_inclusion G S))
          (hom_B (m .fst) G (m .snd .fst)) (mono_roundtrip_equiv G m) (mono_roundtrip_homotopy G m)))

{` lem:SubG=MonoG. F : Sub(G) → Mono(G) is an equivalence, with inverse E. `}
def subgroups_monos_equiv (G : Group) : BookEquiv (Subgroups G) (GroupMonos G)
  ≔ book_quasi_inverse_equiv (Subgroups G) (GroupMonos G) (subgroup_to_mono G) (mono_to_subgroup G)
      (subgroup_mono_roundtrip G) (mono_subgroup_roundtrip G)

def subgroups_monos_is_equiv (G : Group) : BookIsEquiv (Subgroups G) (GroupMonos G) (subgroup_to_mono G)
  ≔ subgroups_monos_equiv G .equiv

{` lem:setofsubgroups. Mono(G) is a set. `}
def group_monos_set (G : Group) : isSet (GroupMonos G)
  ≔ hlevel_two_to_set (GroupMonos G)
      (hlevel_equiv (suc. (suc. zero.)) (Subgroups G) (GroupMonos G)
        (native_equivalence (Subgroups G) (GroupMonos G) (subgroups_monos_equiv G))
        (set_to_hlevel_two (Subgroups G) (subgroups_set G)))

{` lem:E-preserves-symms. For (H, i) = F(X, pt) and g : USym G:
   g ·_X pt = pt iff g is in the image of USym i. `}
def SymmetryPickedOut (G : Group) (m : GroupMonos G) (g : USym G) : Type
  ≔ Mere (Σ (USym (m .fst)) (h ↦ Id (USym G) g (usym_hom (m .fst) G (m .snd .fst) h)))

def subgroup_inclusion_usym (G : Group) (S : Subgroups G) (h : USym (subgroup_group G S))
  : Id (USym G) (usym_hom (subgroup_group G S) G (subgroup_inclusion G S) h) (h .fst)
  ≔ loop_conjugate_at_refl (BG G .carrier) (shape G) (h .fst)

def subgroup_fixes_picked_out (G : Group) (S : Subgroups G) (g : USym G)
  (e : Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point))
  : SymmetryPickedOut G (subgroup_to_mono G S) g
  ≔ let h ≔ action_type_path G (S .gset) (shape G) (shape G) (S .point) (S .point) g e in
    mere (Σ (USym (subgroup_group G S)) (k ↦ Id (USym G) g (usym_hom (subgroup_group G S) G (subgroup_inclusion G S) k)))
      (h, inverse (USym G) (usym_hom (subgroup_group G S) G (subgroup_inclusion G S) h) g
            (subgroup_inclusion_usym G S h))

def subgroup_picked_out_fixes (G : Group) (S : Subgroups G) (g : USym G)
  (t : SymmetryPickedOut G (subgroup_to_mono G S) g)
  : Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)
  ≔ let X ≔ S .gset in
    let pt ≔ S .point in
    let Y ≔ gset_underlying G X in
    let H ≔ subgroup_group G S in
    mere_rec (Σ (USym H) (k ↦ Id (USym G) g (usym_hom H G (subgroup_inclusion G S) k)))
      (Id Y (gset_usym_act G X g pt) pt) (gset_underlying_set G X (gset_usym_act G X g pt) pt)
      (kq ↦
        let r ≔ action_type_path_equiv G X (shape G, pt) (shape G, pt) .map (kq .fst) in
        transport (USym G) (l ↦ Id Y (gset_usym_act G X l pt) pt) (kq .fst .fst) g
          (inverse (USym G) g (kq .fst .fst)
            (concat (USym G) g (usym_hom H G (subgroup_inclusion G S) (kq .fst)) (kq .fst .fst)
              (kq .snd) (subgroup_inclusion_usym G S (kq .fst))))
          (r .snd))
      t

def mono_preserves_symmetries (G : Group) (S : Subgroups G) (m : GroupMonos G)
  (p : Id (GroupMonos G) m (subgroup_to_mono G S)) (g : USym G)
  : Product (Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point) → SymmetryPickedOut G m g)
      (SymmetryPickedOut G m g → Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point))
  ≔ let P ≔ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point) in
    transport (GroupMonos G) (n ↦ Product (P → SymmetryPickedOut G n g) (SymmetryPickedOut G n g → P))
      (subgroup_to_mono G S) m (inverse (GroupMonos G) m (subgroup_to_mono G S) p)
      (subgroup_fixes_picked_out G S g, subgroup_picked_out_fixes G S g)
