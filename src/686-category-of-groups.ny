export "603-adjunctions-and-equivalences"
export "406-symmetric-group-three"
export "606-category-sizes"

{` Chapter 6 examples involving groups (chapter 4): the category of groups
   (bullet after def:category), its univalence, and the functor
   USym : Group → Set (ex:USym-functor). `}

{` The category of groups: objects Group, arrows GroupHom G H, identities
   group_hom_id and composition group_hom_compose (which takes the first
   arrow first: comp G H K g f = group_hom_compose G H K f g = g ∘ f). `}
def GroupWild : WildPrecat
  ≔ (ob ≔ Group,
     hom ≔ GroupHom,
     idn ≔ group_hom_id,
     comp ≔ G H K g f ↦ group_hom_compose G H K f g,
     lu ≔ G H f ↦ group_hom_compose_id G H f,
     ru ≔ G H f ↦ group_hom_id_compose G H f,
     assoc ≔ G H K L f g h ↦ group_hom_compose_assoc G H K L f g h)

def group_wild_homset : HasHomSets GroupWild ≔ group_hom_set

{` A categorical isomorphism of groups has an underlying equivalence of
   classifying types (the book's def:groupisomorphism). The projection to
   underlying functions is taken in a separate definition, abstracting
   over the identification (cf. the E0500 note in docs/narya-notes.md). `}
def group_hom_function_path (G H : Group) (f f' : GroupHom G H) (r : Id (GroupHom G H) f f')
  : Id (BG G .carrier → BG H .carrier) (hom_function G H f) (hom_function G H f')
  ≔ refl ((u ↦ hom_function G H u) : GroupHom G H → BG G .carrier → BG H .carrier) r

def group_cat_is_iso_to_group_iso (G H : Group) (f : GroupHom G H) (i : CatIsIso GroupWild G H f)
  : IsGroupIso G H f
  ≔ let s ≔ group_hom_function_path H H (group_hom_compose H G H (i .fst .fst) f) (group_hom_id H) (i .fst .snd) in
    let r ≔ group_hom_function_path G G (group_hom_compose G H G f (i .snd .fst)) (group_hom_id G) (i .snd .snd) in
    book_equivalence (BG G .carrier) (BG H .carrier)
      (biinvertible_equiv (BG G .carrier) (BG H .carrier) (hom_function G H f)
        (hom_function H G (i .fst .fst)) (y ↦ s (refl y))
        (hom_function H G (i .snd .fst)) (x ↦ r (refl x))) .equiv

{` Conversely, every group isomorphism is a categorical isomorphism: the
   type Σ H, GroupIso G H is contractible (Id Group G H ≃ GroupIso G H,
   module 402), so it suffices to treat the identity, which is invertible. `}
def group_iso_total_contractible (G : Group) : isContr (Σ Group (H ↦ GroupIso G H))
  ≔ hlevel_equiv zero. (Σ Group (H ↦ Id Group G H)) (Σ Group (H ↦ GroupIso G H))
      (family_equiv Group (H ↦ Id Group G H) (H ↦ GroupIso G H) (group_path_iso_equiv G))
      (iscontr_idfrom Group G)

def group_iso_to_cat_is_iso (G H : Group) (f : GroupHom G H) (i : IsGroupIso G H f)
  : CatIsIso GroupWild G H f
  ≔ let T ≔ Σ Group (K ↦ GroupIso G K) in
    let P : T → Type ≔ u ↦ CatIsIso GroupWild G (u .fst) (u .snd .fst) in
    transport T P (G, group_iso_id G) (H, (f, i))
      (contractible_prop T (group_iso_total_contractible G) (G, group_iso_id G) (H, (f, i)))
      (cat_identity_is_iso GroupWild G)

def group_iso_cat_iso_equiv (G H : Group) : Equiv (GroupIso G H) (CatIso GroupWild G H)
  ≔ family_equiv (GroupHom G H) (IsGroupIso G H) (CatIsIso GroupWild G H)
      (f ↦ iff_equiv (IsGroupIso G H f) (CatIsIso GroupWild G H f)
        (is_group_iso_prop G H f) (cat_is_iso_prop GroupWild G H f)
        (group_iso_to_cat_is_iso G H f) (group_cat_is_iso_to_group_iso G H f))

{` The category of groups is univalent: (G = H) ≃ GroupIso G H ≃ (G ≅ H). `}
def group_wild_univalent : IsUnivalentCat GroupWild
  ≔ cat_univalent_from_equivalences GroupWild (G H ↦
      compose_equiv (Id Group G H) (GroupIso G H) (CatIso GroupWild G H)
        (group_path_iso_equiv G H) (group_iso_cat_iso_equiv G H))

def GroupCat : Category ≔ (GroupWild, group_wild_homset, group_wild_univalent)

{` ex:USym-functor: USym : Group → Set, with USym(id_G) = id (usym_hom_id)
   and preservation of composition (cor:USym-compose, usym_hom_compose). `}
def usym_set_object (G : Group) : SetCat .wild .ob ≔ (USym G, usym_set G)

def usym_functor : WildFunctor GroupWild SetWild
  ≔ (obj ≔ usym_set_object,
     mor ≔ G H f ↦ usym_hom G H f,
     map_id ≔ G ↦ funext (USym G) (_ ↦ USym G) (usym_hom G G (group_hom_id G)) (x ↦ x) (usym_hom_id G),
     map_comp ≔ G H K f g ↦ usym_hom_compose G H K f g)

{` Litmus: the functor USym sends the identity of the symmetric group Σ_3
   to a map fixing the transposition τ, and GroupCat's composition is the
   chapter-4 composition. `}
def usym_functor_identity_check
  : Id (USym (symmetric_group three)) (usym_functor .mor (symmetric_group three) (symmetric_group three)
      (GroupWild .idn (symmetric_group three)) sigma3_tau) sigma3_tau
  ≔ usym_hom_id (symmetric_group three) sigma3_tau

def group_cat_compose_check (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
  : Id (GroupHom G K) (GroupCat .wild .comp G H K g f) (group_hom_compose G H K f g)
  ≔ refl (group_hom_compose G H K f g)

{` rem:cat-sizes, groups: the category of groups whose classifying types
   lie in a universe U (smallness predicates of module 190) is locally
   U-small, since GroupHom G H ≃ BookPointedMap (BG G) (BG H). `}
def SmallGroupPredicate (U : Universe) : Subtypes Group
  ≔ G ↦ (U .small (BG G .carrier), U .small_prop (BG G .carrier))

def GroupWildIn (U : Universe) : WildPrecat ≔ FullSubcat GroupWild (SmallGroupPredicate U)

def group_wild_in_locally_small (U : Universe) : IsLocallySmallWildPrecat U (GroupWildIn U)
  ≔ G H ↦ small_equiv U (BookPointedMap (BG (G .fst)) (BG (H .fst))) (GroupHom (G .fst) (H .fst))
      (canonical_inverse_equiv (GroupHom (G .fst) (H .fst)) (BookPointedMap (BG (G .fst)) (BG (H .fst)))
        (group_hom_classifying_equiv (G .fst) (H .fst)))
      (pointed_wild_in_hom_small U (BG (G .fst)) (BG (H .fst)) (G .snd) (H .snd))
