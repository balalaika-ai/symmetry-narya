export "709-groups-are-abstract-groups"
export "674-rezk-universal-property"
export "626-path-functor-categories"

{` Chapter 7 (absgroup.tex), the (wip) section sec:Rezk-delooping,
   "Delooping groups and homomorphisms via the Rezk completion". The
   section has no text in the pinned book; we formalize its title claim for
   groups: an abstract group G is a one-object precategory BG_pre (arrows S,
   composition μ); the objects of its Rezk completion (module 673) form a
   pointed connected groupoid whose group of symmetries is isomorphic to G
   as an abstract group. By thm:Groupsareidentitytypes this group is concr(G),
   which cross-checks the torsor construction of def:concr against the Rezk
   completion of chapter 6. `}

{` The one-object precategory of an abstract group (g ∘ f ≔ g · f). `}
def abstract_group_one_object_wild (G : AbstractGroup) : WildPrecat
  ≔ (ob ≔ Unit,
     hom ≔ _ _ ↦ G .carrier,
     idn ≔ _ ↦ G .unit,
     comp ≔ _ _ _ g f ↦ G .mul g f,
     lu ≔ _ _ f ↦ G .laws .unit_left f,
     ru ≔ _ _ f ↦ G .laws .unit_right f,
     assoc ≔ _ _ _ _ f g h ↦ G .laws .assoc h g f)

def abstract_group_one_object_precat (G : AbstractGroup) : Precat
  ≔ (abstract_group_one_object_wild G, _ _ ↦ abstract_group_set G)

def rezk_delooping_category (G : AbstractGroup) : Category ≔ RezkCompletion (abstract_group_one_object_precat G)

def rezk_delooping_unit (G : AbstractGroup)
  : WildFunctor (abstract_group_one_object_wild G) (rezk_delooping_category G .wild)
  ≔ rezk_unit (abstract_group_one_object_precat G)

def rezk_delooping_point (G : AbstractGroup) : rezk_delooping_category G .wild .ob
  ≔ rezk_delooping_unit G .obj star.

def rezk_delooping_unit_point_path (G : AbstractGroup) (u : Unit)
  : Id (rezk_delooping_category G .wild .ob) (rezk_delooping_point G) (rezk_delooping_unit G .obj u)
  ≔ match u [ star. ↦ refl (rezk_delooping_point G) ]

{` The objects of the Rezk completion form a connected groupoid
   (η is surjective on objects; lem:obj-gpd). `}
def rezk_delooping_connected (G : AbstractGroup) : Connected (rezk_delooping_category G .wild .ob)
  ≔ let R ≔ rezk_delooping_category G .wild .ob in
    let pt ≔ rezk_delooping_point G in
    let eta ≔ rezk_delooping_unit G in
    let reach : (x : R) → Mere (Id R pt x)
      ≔ x ↦ mere_rec (BookFiber Unit R (eta .obj) x) (Mere (Id R pt x)) (mere_isprop (Id R pt x))
          (w ↦ mere (Id R pt x)
            (concat R pt (eta .obj (w .fst)) x (rezk_delooping_unit_point_path G (w .fst))
              (inverse R x (eta .obj (w .fst)) (w .snd))))
          (rezk_unit_obj_surjective (abstract_group_one_object_precat G) x) in
    (mere R pt, x y ↦ merely_paths_compose native_truncation R pt x y (reach x) (reach y))

def rezk_delooping_group (G : AbstractGroup) : Group
  ≔ mkgroup (rezk_delooping_category G .wild .ob, rezk_delooping_point G, rezk_delooping_connected G,
      category_objects_groupoid (rezk_delooping_category G))

{` Every arrow of the one-object precategory is an isomorphism. `}
def one_object_iso (G : AbstractGroup) (s : G .carrier) : CatIsIso (abstract_group_one_object_wild G) star. star. s
  ≔ ((G .inv s, G .laws .inv_right s), (G .inv s, ag_inv_left G s))

def one_object_iso_equiv (G : AbstractGroup) : Equiv (G .carrier) (CatIso (abstract_group_one_object_wild G) star. star.)
  ≔ let C ≔ abstract_group_one_object_wild G in
    canonical_inverse_equiv (CatIso C star. star.) (G .carrier)
      (contractible_fiber_projection (G .carrier) (s ↦ CatIsIso C star. star. s)
        (s ↦ (one_object_iso G s, x ↦ cat_is_iso_prop C star. star. s x (one_object_iso G s))))

{` The symmetries of the base point are the elements of G:
   S ≃ Iso_{BG_pre}(★, ★) ≃ Iso_R(η★, η★) ≃ (η★ = η★). `}
def rezk_delooping_usym_equiv (G : AbstractGroup) : Equiv (G .carrier) (USym (rezk_delooping_group G))
  ≔ let C ≔ abstract_group_one_object_wild G in
    let R ≔ rezk_delooping_category G in
    let pt ≔ rezk_delooping_point G in
    compose_equiv (G .carrier) (CatIso C star. star.) (USym (rezk_delooping_group G)) (one_object_iso_equiv G)
      (compose_equiv (CatIso C star. star.) (CatIso (R .wild) pt pt) (Id (R .wild .ob) pt pt)
        (ff_functor_iso_equiv C (R .wild) (rezk_delooping_unit G) (rezk_unit_ff (abstract_group_one_object_precat G)) star. star.)
        (canonical_inverse_equiv (Id (R .wild .ob) pt pt) (CatIso (R .wild) pt pt) (cat_idtoiso_equiv (R .wild) (R .univalent) pt pt)))

def rezk_delooping_symmetry (G : AbstractGroup) (s : G .carrier) : USym (rezk_delooping_group G)
  ≔ rezk_delooping_usym_equiv G .map s

{` Arrows of isomorphisms along an identification of isomorphisms. `}
def rezk_cat_iso_arrow_path (C : WildPrecat) (a b : C .ob) (e d : CatIso C a b) (p : Id (CatIso C a b) e d)
  : Id (C .hom a b) (e .fst) (d .fst)
  ≔ refl ((i ↦ i .fst) : CatIso C a b → C .hom a b) p

{` idtoiso of the symmetry attached to s is η(s). `}
def rezk_delooping_symmetry_arrow (G : AbstractGroup) (s : G .carrier)
  : Id (rezk_delooping_category G .wild .hom (rezk_delooping_point G) (rezk_delooping_point G))
      (cat_idtoiso (rezk_delooping_category G .wild) (rezk_delooping_point G) (rezk_delooping_point G)
        (rezk_delooping_symmetry G s) .fst)
      (rezk_delooping_unit G .mor star. star. s)
  ≔ let R ≔ rezk_delooping_category G in let pt ≔ rezk_delooping_point G in
    let ie ≔ cat_idtoiso_equiv (R .wild) (R .univalent) pt pt in
    rezk_cat_iso_arrow_path (R .wild) pt pt
      (cat_idtoiso (R .wild) pt pt (rezk_delooping_symmetry G s))
      (functor_iso (abstract_group_one_object_wild G) (R .wild) (rezk_delooping_unit G) star. star.
        (one_object_iso_equiv G .map s))
      (equiv_counit (Id (R .wild .ob) pt pt) (CatIso (R .wild) pt pt) ie
        (functor_iso (abstract_group_one_object_wild G) (R .wild) (rezk_delooping_unit G) star. star.
          (one_object_iso_equiv G .map s)))

{` The equivalence S ≃ USym is an isomorphism of abstract groups
   G ≅ abstr(B_Rezk G). `}
def rezk_delooping_symmetry_mul (G : AbstractGroup) (s t : G .carrier)
  : Id (USym (rezk_delooping_group G)) (rezk_delooping_symmetry G (G .mul s t))
      (usym_mul (rezk_delooping_group G) (rezk_delooping_symmetry G s) (rezk_delooping_symmetry G t))
  ≔ let R ≔ rezk_delooping_category G in let W ≔ R .wild in let pt ≔ rezk_delooping_point G in
    let eta ≔ rezk_delooping_unit G in
    let ie ≔ cat_idtoiso_equiv W (R .univalent) pt pt in
    let L ≔ Id (W .ob) pt pt in let I ≔ CatIso W pt pt in
    let th ≔ rezk_delooping_symmetry G in
    let H ≔ W .hom pt pt in
    equivalence_injective L I ie (th (G .mul s t)) (concat (W .ob) pt pt pt (th t) (th s))
      (cat_iso_path W pt pt (ie .map (th (G .mul s t))) (ie .map (concat (W .ob) pt pt pt (th t) (th s)))
        (calc
           cat_idtoiso W pt pt (th (G .mul s t)) .fst = eta .mor star. star. (G .mul s t)
             by rezk_delooping_symmetry_arrow G (G .mul s t)
           = W .comp pt pt pt (eta .mor star. star. s) (eta .mor star. star. t)
             by eta .map_comp star. star. star. t s
           = W .comp pt pt pt (cat_idtoiso W pt pt (th s) .fst) (cat_idtoiso W pt pt (th t) .fst)
             by inverse H (W .comp pt pt pt (cat_idtoiso W pt pt (th s) .fst) (cat_idtoiso W pt pt (th t) .fst))
               (W .comp pt pt pt (eta .mor star. star. s) (eta .mor star. star. t))
               (refl (W .comp pt pt pt) (rezk_delooping_symmetry_arrow G s) (rezk_delooping_symmetry_arrow G t))
           = cat_idtoiso W pt pt (concat (W .ob) pt pt pt (th t) (th s)) .fst
             by inverse H (cat_idtoiso W pt pt (concat (W .ob) pt pt pt (th t) (th s)) .fst)
               (W .comp pt pt pt (cat_idtoiso W pt pt (th s) .fst) (cat_idtoiso W pt pt (th t) .fst))
               (cat_idtoiso_concat W pt pt pt (th t) (th s)) ∎))

def rezk_delooping_abstract_iso (G : AbstractGroup) : AbstractIso G (abstr (rezk_delooping_group G))
  ≔ (rezk_delooping_usym_equiv G, s t ↦ rezk_delooping_symmetry_mul G s t)

{` Cross-check: the Rezk delooping of G is concr(G). `}
def rezk_delooping_abstr_path (G : AbstractGroup) : Id AbstractGroup (abstr (rezk_delooping_group G)) G
  ≔ inverse AbstractGroup G (abstr (rezk_delooping_group G))
      (abstract_group_path_from_iso G (abstr (rezk_delooping_group G)) (rezk_delooping_abstract_iso G))

def rezk_delooping_concr_path (G : AbstractGroup) : Id Group (rezk_delooping_group G) (concr G)
  ≔ concat Group (rezk_delooping_group G) (concr (abstr (rezk_delooping_group G))) (concr G)
      (inverse Group (concr (abstr (rezk_delooping_group G))) (rezk_delooping_group G)
        (concr_abstr_path (rezk_delooping_group G)))
      (refl concr (rezk_delooping_abstr_path G))
