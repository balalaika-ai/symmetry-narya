import "bridge-00-core"
import "../../../src/606-category-sizes"
import "../../../src/660-slice-categories"

{` Bridges for cats.tex, section "Categories" (blind file 01). `}

{` def:full-subcat. `}
def bridge_def_full_subcat (C : BlindWildPrecat) (P : C .ob → PropTypes)
  : Id WildPrecat (bridge_w (blind_full_subcat C P)) (FullSubcat (bridge_w C) P)
  ≔ refl (FullSubcat (bridge_w C) P)

def bridge_full_subcat_univalent : blind_full_subcat_univalent
  ≔ C P u ↦ full_subcat_univalent (bridge_w C) P u

{` lem:obj-gpd. `}
def bridge_obj_gpd : blind_obj_gpd ≔ C ↦ category_objects_groupoid (bridge_c C)

{` rem:wild. `}
def bridge_def_universe_wild : Id WildPrecat (bridge_w blind_universe_wild_precat) TypeWild
  ≔ refl TypeWild

def bridge_def_pointed_wild : Id WildPrecat (bridge_w blind_pointed_wild_precat) PointedWild
  ≔ refl PointedWild

def bridge_def_unit_coherence (C : BlindWildPrecat)
  : Id Type (BlindUnitCoherence C) (WildUnitCoherence (bridge_w C))
  ≔ refl (BlindUnitCoherence C)

{` eq:pentagon. The blind left boundary is (ap α · α) · ap α, ours is
   ap α · (α · ap α); fillers correspond by precomposition with
   concat_assoc (an equivalence of filler types, pointwise). `}
def bridge_pentagon_assoc (C : BlindWildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c)
  (h : C .hom c d) (k : C .hom d e)
  : Id (Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
        (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f))
      (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
         (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
         (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
         (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
            (C .comp a d e k (C .comp a b d (C .comp b c d h g) f))
            (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
            (refl (C .comp a d e k) (C .assoc a b c d f g h))
            (C .assoc a b d e f (C .comp b c d h g) k))
         (refl (x ↦ C .comp a b e x f) (C .assoc b c d e g h k)))
      (wild_pentagon_left (bridge_w C) a b c d e f g h k)
  ≔ concat_assoc (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
      (C .comp a d e k (C .comp a b d (C .comp b c d h g) f))
      (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
      (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
      (refl (C .comp a d e k) (C .assoc a b c d f g h))
      (C .assoc a b d e f (C .comp b c d h g) k)
      (refl (x ↦ C .comp a b e x f) (C .assoc b c d e g h k))

def bridge_blind_pentagon_filler (C : BlindWildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c)
  (h : C .hom c d) (k : C .hom d e) : Type
  ≔ Id (Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
          (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f))
        (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
           (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
           (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
           (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
              (C .comp a d e k (C .comp a b d (C .comp b c d h g) f))
              (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
              (refl (C .comp a d e k) (C .assoc a b c d f g h))
              (C .assoc a b d e f (C .comp b c d h g) k))
           (refl (x ↦ C .comp a b e x f) (C .assoc b c d e g h k)))
        (wild_pentagon_right (bridge_w C) a b c d e f g h k)

def bridge_def_pentagon_filler (C : BlindWildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c)
  (h : C .hom c d) (k : C .hom d e)
  : Equiv (WildPentagonFiller (bridge_w C) a b c d e f g h k) (bridge_blind_pentagon_filler C a b c d e f g h k)
  ≔ concat_left_equiv (Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
          (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f))
      (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
         (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
         (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
         (concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
            (C .comp a d e k (C .comp a b d (C .comp b c d h g) f))
            (C .comp a b e (C .comp b d e k (C .comp b c d h g)) f)
            (refl (C .comp a d e k) (C .assoc a b c d f g h))
            (C .assoc a b d e f (C .comp b c d h g) k))
         (refl (x ↦ C .comp a b e x f) (C .assoc b c d e g h k)))
      (wild_pentagon_left (bridge_w C) a b c d e f g h k)
      (wild_pentagon_right (bridge_w C) a b c d e f g h k)
      (bridge_pentagon_assoc C a b c d e f g h k)

def bridge_def_pentagon_to_blind (C : BlindWildPrecat) (w : WildPentagon (bridge_w C)) : BlindPentagon C
  ≔ a b c d e f g h k ↦ bridge_def_pentagon_filler C a b c d e f g h k .map (w a b c d e f g h k)

def bridge_def_pentagon_from_blind (C : BlindWildPrecat) (w : BlindPentagon C) : WildPentagon (bridge_w C)
  ≔ a b c d e f g h k ↦ equiv_inverse_map (WildPentagonFiller (bridge_w C) a b c d e f g h k)
      (bridge_blind_pentagon_filler C a b c d e f g h k)
      (bridge_def_pentagon_filler C a b c d e f g h k) (w a b c d e f g h k)

def bridge_def_full_subprecat (C : BlindPrecat) (P : C .fst .ob → PropTypes)
  : Id Precat (bridge_p (blind_full_subprecat C P)) (full_subcat_precat (bridge_p C) P)
  ≔ refl (full_subcat_precat (bridge_p C) P)

{` ex:poset. `}
def bridge_pre (P : BlindPreorder) : Preorder ≔ (bridge_w (P .fst .fst), P .snd)

def bridge_pre_inv (P : Preorder) : BlindPreorder
  ≔ ((bridge_w_inv (P .wild), preorder_homset P), P .homprop)

def bridge_pre_roundtrip (P : BlindPreorder) : Id BlindPreorder (bridge_pre_inv (bridge_pre P)) P
  ≔ ((refl (P .fst .fst), has_hom_sets_prop (bridge_w (P .fst .fst)) (preorder_homset (bridge_pre P)) (P .fst .snd)),
     refl (P .snd))

def bridge_def_preorder : Equiv BlindPreorder Preorder
  ≔ quasi_inverse_equiv BlindPreorder Preorder bridge_pre bridge_pre_inv bridge_pre_roundtrip (P ↦ refl P)

def bridge_poset (P : BlindPoset) : Poset ≔ (bridge_w (P .fst .fst .fst), P .fst .snd, P .snd)

def bridge_poset_inv (P : Poset) : BlindPoset ≔ (bridge_pre_inv (poset_preorder P), P .univalent)

def bridge_def_poset : Equiv BlindPoset Poset
  ≔ quasi_inverse_equiv BlindPoset Poset bridge_poset bridge_poset_inv
      (P ↦ (bridge_pre_roundtrip (P .fst), refl (P .snd))) (P ↦ refl P)

def bridge_rel_to_blind (R : PreorderRelation) : BlindPreorderRelData
  ≔ (R .carrier, (R .rel, (R .reflexive, R .transitive)))

def bridge_rel_from_blind (R : BlindPreorderRelData) : PreorderRelation
  ≔ (carrier ≔ R .fst, rel ≔ R .snd .fst, reflexive ≔ R .snd .snd .fst, transitive ≔ R .snd .snd .snd)

def bridge_def_preorder_rel_data : Equiv PreorderRelation BlindPreorderRelData
  ≔ quasi_inverse_equiv PreorderRelation BlindPreorderRelData bridge_rel_to_blind bridge_rel_from_blind
      (R ↦ refl R) (R ↦ refl R)

def bridge_ex_poset_preorder_data : blind_ex_poset_preorder_data
  ≔ book_equivalence BlindPreorder BlindPreorderRelData
      (compose_equiv BlindPreorder Preorder BlindPreorderRelData bridge_def_preorder
        (compose_equiv Preorder PreorderRelation BlindPreorderRelData preorder_relation_equiv
          bridge_def_preorder_rel_data))

{` The pointwise contractibility of the λ, ρ, α types: ours states the
   contractibility of the whole Π-types (preorder_*_contractible); the
   pointwise form follows from the same fact, hom types being sets. `}
def bridge_ex_poset_laws_contractible : blind_ex_poset_laws_contractible
  ≔ C ↦ let W ≔ C .fst .fst in
    let hs ≔ preorder_homset (bridge_pre C) in
    ((a b f ↦ prop_paths_contractible (W .hom a b) (C .snd a b) (W .comp a b b (W .idn b) f) f),
     ((a b f ↦ prop_paths_contractible (W .hom a b) (C .snd a b) (W .comp a a b f (W .idn a)) f),
      (a b c d f g h ↦ prop_paths_contractible (W .hom a d) (C .snd a d)
         (W .comp a c d h (W .comp a b c g f)) (W .comp a b d (W .comp b c d h g) f))))

def bridge_ex_poset_objects_set : blind_ex_poset_objects_set ≔ C ↦ poset_objects_set (bridge_poset C)

def bridge_ex_poset_iff_antisymmetric : blind_ex_poset_iff_antisymmetric
  ≔ C ↦ preorder_univalent_iff_antisymmetric (bridge_pre C)

{` Concrete posets: for a prop-valued reflexive transitive relation,
   univalence of the induced preorder follows from antisymmetry (ours). `}
def bridge_rel_is_poset (P : Type) (le : P → P → Type) (hp : (x y : P) → isProp (le x y)) (r : (x : P) → le x x)
  (t : (x y z : P) → le x y → le y z → le x z) (anti : (x y : P) → le x y → le y x → Id P x y)
  : BlindRelIsPoset P le
  ≔ (hp, (r, (t, preorder_antisymmetric_univalent (bridge_pre (blind_preorder_of_rel P le hp r t)) anti)))

def bridge_ex_poset_nat : blind_ex_poset_nat ≔ bridge_rel_is_poset Nat Le le_prop le_refl le_trans le_antisym

def bridge_ex_poset_int : blind_ex_poset_int
  ≔ (int_le_prop, (int_le_refl, (int_le_trans, int_leq_poset .univalent)))

def bridge_ex_poset_prop : blind_ex_poset_prop
  ≔ ((P Q ↦ pi_prop (P .fst) (_ ↦ Q .fst) (_ ↦ Q .snd)),
     ((P ↦ x ↦ x), ((P Q R f g ↦ x ↦ g (f x)), prop_implication_poset .univalent)))

def bridge_ex_poset_sub : blind_ex_poset_sub
  ≔ S ↦ (inclusion_prop (S .fst), (inclusion_refl (S .fst), (inclusion_trans (S .fst),
      subtype_inclusion_poset (S .fst) .univalent)))

def bridge_ex_poset_bool_not_univalent : blind_ex_poset_bool_not_univalent
  ≔ ((_ _ ↦ unit_prop), ((_ ↦ star.), ((_ _ _ _ _ ↦ star.), bool_chaotic_not_univalent)))

{` xca:order-poset. `}
def bridge_xca_order_poset : blind_xca_order_poset
  ≔ (order_divides_prop, (order_divides_refl, (order_divides_trans, order_divisibility_poset .univalent)))

{` def:wild-pre-groupoid. `}
def bridge_def_is_pregroupoid (C : BlindWildPrecat)
  : Id Type (BlindIsPregroupoid C) (IsPregroupoid (bridge_w C)) ≔ refl (BlindIsPregroupoid C)

def bridge_def_wild_pregroupoid : Equiv BlindWildPregroupoid WildPregroupoid
  ≔ quasi_inverse_equiv BlindWildPregroupoid WildPregroupoid (C ↦ (bridge_w (C .fst), C .snd))
      (C ↦ (bridge_w_inv (C .wild), C .invertible)) (C ↦ refl C) (C ↦ refl C)

def bridge_def_pregroupoid : Equiv BlindPregroupoid Pregroupoid
  ≔ quasi_inverse_equiv BlindPregroupoid Pregroupoid (C ↦ (bridge_w (C .fst .fst), C .fst .snd, C .snd))
      (C ↦ ((bridge_w_inv (C .wild), C .homset), C .invertible)) (C ↦ refl C) (C ↦ refl C)

def bridge_def_wild_groupoid : Equiv BlindWildGroupoid WildGroupoid
  ≔ quasi_inverse_equiv BlindWildGroupoid WildGroupoid (C ↦ (bridge_w (C .fst .fst), C .snd, C .fst .snd))
      (C ↦ ((bridge_w_inv (C .wild), C .invertible), C .univalent)) (C ↦ refl C) (C ↦ refl C)

def bridge_def_groupoid : Equiv BlindGroupoid GroupoidCat
  ≔ quasi_inverse_equiv BlindGroupoid GroupoidCat
      (C ↦ (bridge_w (C .fst .fst .fst), C .fst .fst .snd, C .snd, C .fst .snd))
      (C ↦ (((bridge_w_inv (C .wild), C .homset), C .invertible), C .univalent)) (C ↦ refl C) (C ↦ refl C)

{` ex:path-groupoid. `}
def bridge_def_path_wild (X : Type) : Id WildPrecat (bridge_w (blind_path_wild_precat X)) (PathWild X)
  ≔ refl (PathWild X)

def bridge_ex_path_groupoid_wild : blind_ex_path_groupoid_wild
  ≔ X ↦ (PathGroupoid X .invertible, PathGroupoid X .univalent)

def bridge_ex_path_groupoid_one_type : blind_ex_path_groupoid_one_type
  ≔ X h ↦ (path_groupoid_of_groupoid X h .homset,
           (path_groupoid_of_groupoid X h .invertible, path_groupoid_of_groupoid X h .univalent))

{` rem:cat-sizes. `}
def bridge_def_is_small (U : Universe) (C : BlindWildPrecat)
  : Id Type (BlindIsUSmall U C) (IsSmallWildPrecat U (bridge_w C)) ≔ refl (BlindIsUSmall U C)

def bridge_def_is_locally_small (U : Universe) (C : BlindWildPrecat)
  : Id Type (BlindIsLocallyUSmall U C) (IsLocallySmallWildPrecat U (bridge_w C)) ≔ refl (BlindIsLocallyUSmall U C)

def bridge_def_universe_wild_in (U : Universe)
  : Id WildPrecat (bridge_w (blind_universe_wild_precat_in U)) (TypeWildIn U) ≔ refl (TypeWildIn U)

def bridge_def_pointed_wild_in (U : Universe)
  : Id WildPrecat (bridge_w (blind_pointed_wild_precat_in U)) (PointedWildIn U) ≔ refl (PointedWildIn U)

def bridge_rem_cat_sizes_path_small : blind_rem_cat_sizes_path_small ≔ U X sX ↦ path_wild_small U X sX

def bridge_rem_cat_sizes_locally_small : blind_rem_cat_sizes_locally_small
  ≔ U ↦ (type_wild_in_locally_small U,
         (A B ↦ type_wild_in_locally_small U (A .fst, A .snd .fst) (B .fst, B .snd .fst),
          pointed_wild_in_locally_small U))

def bridge_rem_cat_sizes_generalizes : blind_rem_cat_sizes_generalizes
  ≔ U A h ↦ path_wild_locally_small_to_type U A h

def bridge_rem_cat_sizes_generalizes_converse (U : Universe) (A : Type) (h : LocallySmall U A)
  : BlindIsLocallyUSmall U (blind_path_wild_precat A)
  ≔ type_locally_small_to_path_wild U A h

{` def:slice-cat. Objects, arrows, identities and composition of the blind
   slice are ours on the nose; the unit/associativity proofs differ (both
   in sets). Univalence only sees idn/comp, so ours transfers through
   cat_univalent_from_equivalences. `}
def bridge_def_slice_ob (C : BlindPrecat) (c : C .fst .ob)
  : Id Type (blind_slice_precat C c .fst .ob) (SlicePrecat (bridge_p C) c .wild .ob)
  ≔ refl (SliceOb (bridge_w (C .fst)) c)

def bridge_def_slice_hom (C : BlindPrecat) (c : C .fst .ob) (u v : blind_slice_precat C c .fst .ob)
  : Id Type (blind_slice_precat C c .fst .hom u v) (SlicePrecat (bridge_p C) c .wild .hom u v)
  ≔ refl (SliceHom (bridge_w (C .fst)) c u v)

def bridge_def_slice_comp (C : BlindPrecat) (c : C .fst .ob) (u v w : blind_slice_precat C c .fst .ob)
  (k : BlindSliceHom C c v w) (g : BlindSliceHom C c u v)
  : Id (SliceHom (bridge_w (C .fst)) c u w) (blind_slice_comp C c u v w k g) (slice_comp (bridge_w (C .fst)) c u v w k g)
  ≔ refl (slice_comp (bridge_w (C .fst)) c u v w k g)

def bridge_ex_slice_univalent : blind_ex_slice_univalent
  ≔ C c ↦ cat_univalent_from_equivalences (bridge_w (blind_slice_precat (C .fst) c .fst)) (u v ↦
      cat_idtoiso_equiv (SliceCategory (bridge_c C) c .wild) (SliceCategory (bridge_c C) c .univalent) u v)

{` xca:univ-slice-cat. Ours is a wild precategory with exactly the blind
   objects and arrows. `}
def bridge_xca_univ_slice_cat : blind_xca_univ_slice_cat ≔ B ↦ bridge_wstr_of (universe_slice_wild B)

def bridge_def_univ_slice_ob (B : Type) : Id Type (BlindUnivSliceOb B) (UniverseSliceOb B) ≔ refl (BlindUnivSliceOb B)
