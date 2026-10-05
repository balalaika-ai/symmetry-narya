export "505-gset-core-litmus"

{` Chapter 5 helpers: trivial groups (xca:connected-trivia as used in
   lem:free-pt-char and def:triv-proper-Mono) and transport along
   identifications of G-sets built from equivalences. `}

{` IsTrivialGroup H (BH contractible) ⇔ USym H contractible
   (xca:connected-trivia for the pointed connected groupoid BH). `}
def is_trivial_group_usym_contractible (H : Group) (h : IsTrivialGroup H) : BookIsContr (USym H)
  ≔ let B ≔ BG H .carrier in
    let hp : isProp B ≔ contractible_prop B (native_contraction B h) in
    (refl (shape H), q ↦ prop_is_set B hp (shape H) (shape H) (refl (shape H)) q)

def usym_contractible_trivial_group (H : Group) (h : BookIsContr (USym H)) : IsTrivialGroup H
  ≔ let B ≔ BG H .carrier in
    connected_loops_prop_contractible native_truncation B (bg_connected H)
      (connected_based_elim native_truncation B (bg_connected H) (shape H)
        (a ↦ isProp (Id B a a)) (a ↦ isprop_isprop (Id B a a))
        (contractible_prop (USym H) (native_contraction (USym H) h)))

def trivial_group_iff_usym_contractible (H : Group) : Equiv (IsTrivialGroup H) (BookIsContr (USym H))
  ≔ iff_equiv (IsTrivialGroup H) (BookIsContr (USym H)) (is_trivial_group_prop H) (book_iscontr_isprop (USym H))
      (is_trivial_group_usym_contractible H) (usym_contractible_trivial_group H)

{` The book's trivial group TG = Aut_Prop(true) is trivial. `}
def trivial_group_is_trivial : IsTrivialGroup trivial_group
  ≔ usym_contractible_trivial_group trivial_group trivial_group_usym_contractible

{` IsTrivialGroup H ⇔ H = TG ("H is the trivial group"). A pointed map into
   a contractible pointed type between contractible types is a pointed
   equivalence, hence an identification of groups. `}
def contractible_types_map_book_equiv (A B : Type) (f : A → B) (hA : BookIsContr A) (hB : BookIsContr B)
  : BookIsEquiv A B f
  ≔ book_equivalence A B (f, contractible_map_equiv A B f hA hB) .equiv

def trivial_group_path (H : Group) (h : IsTrivialGroup H) : Id Group H trivial_group
  ≔ let T ≔ BG trivial_group in
    let hT ≔ trivial_group_is_trivial in
    group_path_from_pointed_equiv H trivial_group
      ((_ ↦ T .point, refl (T .point)),
       contractible_types_map_book_equiv (BG H .carrier) (T .carrier) (_ ↦ T .point) h hT)

def path_trivial_group (H : Group) (p : Id Group H trivial_group) : IsTrivialGroup H
  ≔ transport Group IsTrivialGroup trivial_group H (inverse Group H trivial_group p) trivial_group_is_trivial

def trivial_group_iff_path (H : Group)
  : Product (IsTrivialGroup H → Id Group H trivial_group) (Id Group H trivial_group → IsTrivialGroup H)
  ≔ (trivial_group_path H, path_trivial_group H)

{` Transport along the identification of G-sets built from a family of
   equivalences is the family of maps (from the counit of gset_path_equiv). `}
def gset_path_from_equivs_transport (G : Group) (X Y : GSet G)
  (e : (z : BG G .carrier) → Equiv (X z .fst) (Y z .fst)) (z : BG G .carrier) (x : X z .fst)
  : Id (Y z .fst) (gset_path_transport G X Y (gset_path_from_equivs G X Y e) z x) (e z .map x)
  ≔ refl ((k ↦ k z .map x) : ((w : BG G .carrier) → Equiv (X w .fst) (Y w .fst)) → Y z .fst)
      (equiv_counit (Id (GSet G) X Y) ((w : BG G .carrier) → Equiv (X w .fst) (Y w .fst))
        (gset_path_equiv G X Y) e)

{` Identifications of pointed G-sets from a family of equivalences sending
   the point to the point. `}
def pointed_gset_path (G : Group) (X Y : GSet G) (x : gset_underlying G X) (y : gset_underlying G Y)
  (e : (z : BG G .carrier) → Equiv (X z .fst) (Y z .fst)) (ex : Id (gset_underlying G Y) (e (shape G) .map x) y)
  : Id (PointedGSet G) (X, x) (Y, y)
  ≔ equiv_inverse_map (Id (PointedGSet G) (X, x) (Y, y))
      (Fiber (Id (GSet G) X Y) (gset_underlying G Y) (gset_path_eval G X Y (shape G) x) y)
      (pointed_gset_path_fiber_equiv G (X, x) (Y, y))
      (gset_path_from_equivs G X Y e,
       concat (gset_underlying G Y) (gset_path_transport G X Y (gset_path_from_equivs G X Y e) (shape G) x)
         (e (shape G) .map x) y
         (gset_path_from_equivs_transport G X Y e (shape G) x) ex)

{` Identifications of subgroups from identifications of pointed G-sets. `}
def subgroups_pairs_to_subgroup (G : Group) (u : SubgroupsPairs G) : Subgroups G
  ≔ (u .fst .fst, u .fst .snd, u .snd)

def subgroup_path (G : Group) (S T : Subgroups G)
  (p : Id (PointedGSet G) (S .gset, S .point) (T .gset, T .point)) : Id (Subgroups G) S T
  ≔ map_path (SubgroupsPairs G) (Subgroups G) (subgroups_pairs_to_subgroup G)
      ((S .gset, S .point), S .transitive) ((T .gset, T .point), T .transitive)
      (subtype_equal (PointedGSet G) (w ↦ IsTransitive G (w .fst)) (w ↦ is_transitive_prop G (w .fst))
        ((S .gset, S .point), S .transitive) ((T .gset, T .point), T .transitive) p)
