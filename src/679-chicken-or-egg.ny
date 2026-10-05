export "677-one-types-are-groupoids"

{` Chapter 6, section 6.8 (cats.tex, rem:chicken-or-egg): precategories and
   categories are connected by an injection Cat ↪ PreCat and a retraction
   L : PreCat → Cat. From the point of view of precategories, categories
   are precategories with an extra property (univalence); from the point
   of view of categories, precategories are categories with extra (higher)
   structure, the flagged structure. `}

{` The fibre of the inclusion Cat → PreCat over P is the proposition that
   P is univalent. `}
def category_precat_fiber_equiv (P : Precat)
  : Equiv (BookFiber Category Precat category_precat P) (IsUnivalentCat (P .wild))
  ≔ let S ≔ Σ Precat (Q ↦ IsUnivalentCat (Q .wild)) in
    compose_equiv (BookFiber Category Precat category_precat P) (BookFiber S Precat (u ↦ u .fst) P)
      (IsUnivalentCat (P .wild))
      (sigma_pullback_equiv Category S category_sigma_equiv (u ↦ Id Precat P (u .fst)))
      (projection_book_fiber_equiv Precat (Q ↦ IsUnivalentCat (Q .wild)) P)

{` The inclusion Cat → PreCat is an injection (def:injection). `}
def category_precat_embedding : IsEmbedding Category Precat category_precat
  ≔ P ↦ prop_from_equiv (BookFiber Category Precat category_precat P) (IsUnivalentCat (P .wild))
      (category_precat_fiber_equiv P) (is_univalent_cat_prop (P .wild))

{` L is a retraction of the inclusion: L(C) = C for every category C,
   since the identity functor C → C is a weak equivalence into a
   category (module 674; identity_weak_equivalence is from module 643). `}
def rezk_completion_retraction (C : Category) : Id Category (RezkCompletion (category_precat C)) C
  ≔ inverse Category C (RezkCompletion (category_precat C))
      (rezk_weak_equivalence_path (category_precat C) C (functor_identity (C .wild)) (identity_weak_equivalence (C .wild)))

{` From the point of view of categories, precategories are categories
   equipped with a flag structure (thm:flagged-cat-equiv), and L is the
   first projection. `}
def precat_category_with_flag_equiv : Equiv Precat (Σ Category FlagStructure) ≔ precat_flagged_equiv

{` The flag structure is extra (higher) structure, not a property: already
   on the path category of Unit (one object) there are distinct flags,
   Unit → 1 and Bool → 1, since Unit ≠ Bool. `}
def unit_category : Category ≔ path_category Unit unit_groupoid

def constant_star_surjective (A : Type) (a : A) : Surjective A Unit (_ ↦ star.)
  ≔ b ↦ mere (BookFiber A Unit (_ ↦ star.) b) (a, unit_prop b star.)

def unit_flag : FlagStructure unit_category ≔ (Unit, ((_ ↦ star.), constant_star_surjective Unit star.))

def bool_flag : FlagStructure unit_category ≔ (Bool, ((_ ↦ star.), constant_star_surjective Bool true.))

def unit_bool_not_equivalent (e : Equiv Unit Bool) : Empty
  ≔ let g ≔ equiv_inverse_map Unit Bool e in
    bool_encode true. false.
      (concat Bool true. (e .map (g true.)) false.
        (inverse Bool (e .map (g true.)) true. (equiv_counit Unit Bool e true.))
        (concat Bool (e .map (g true.)) (e .map (g false.)) false.
          (refl (e .map) (unit_prop (g true.) (g false.)))
          (equiv_counit Unit Bool e false.)))

def flag_structure_not_prop (h : isProp (FlagStructure unit_category)) : Empty
  ≔ unit_bool_not_equivalent (id_to_equiv Unit Bool (h unit_flag bool_flag .fst))
