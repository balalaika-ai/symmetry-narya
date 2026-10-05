export "608-opposite-involution"

{` Chapter 6 (cats.tex), section 6.3: monomorphisms and epimorphisms
   (def:mono-in-cat, def:epi-in-cat), their description in precategories,
   xca:monos-epis-sets-types, the remark on epimorphisms of types, and
   xca:monos-epis-preorder. "Injection" is the book's notion
   (def:injection, IsEmbedding: propositional fibers). `}

{` def:mono-in-cat: post-composition f ∘ - : (C → A) → (C → B) is an
   injection for every object C. `}
def IsMono (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) → IsEmbedding (C .hom c a) (C .hom c b) (k ↦ C .comp c a b f k)

{` def:epi-in-cat: pre-composition - ∘ f : (B → C) → (A → C) is an
   injection for every object C. `}
def IsEpi (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) → IsEmbedding (C .hom b c) (C .hom a c) (k ↦ C .comp a b c k f)

def embedding_prop (A B : Type) (f : A → B) : isProp (IsEmbedding A B f)
  ≔ pi_prop B (b ↦ isProp (BookFiber A B f b)) (b ↦ isprop_isprop (BookFiber A B f b))

def is_mono_prop (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : isProp (IsMono C a b f)
  ≔ pi_prop (C .ob) (c ↦ IsEmbedding (C .hom c a) (C .hom c b) (k ↦ C .comp c a b f k))
      (c ↦ embedding_prop (C .hom c a) (C .hom c b) (k ↦ C .comp c a b f k))

def is_epi_prop (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : isProp (IsEpi C a b f)
  ≔ pi_prop (C .ob) (c ↦ IsEmbedding (C .hom b c) (C .hom a c) (k ↦ C .comp a b c k f))
      (c ↦ embedding_prop (C .hom b c) (C .hom a c) (k ↦ C .comp a b c k f))

{` "Dually": the epimorphisms of C are judgmentally the monomorphisms of
   C^op. `}
def epi_is_mono_op (C : WildPrecat) (a b : C .ob) (f : C .hom a b)
  : Id Type (IsEpi C a b f) (IsMono (OppositeWild C) b a f)
  ≔ refl (IsEpi C a b f)

{` "If C is a precategory, then these conditions reduce to the implications
   f ∘ g = f ∘ h → g = h and g ∘ f = h ∘ f → g = h." `}
def MonoCancellation (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) (g h : C .hom c a) → Id (C .hom c b) (C .comp c a b f g) (C .comp c a b f h) → Id (C .hom c a) g h

def EpiCancellation (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) (g h : C .hom b c) → Id (C .hom a c) (C .comp a b c g f) (C .comp a b c h f) → Id (C .hom b c) g h

def precat_mono_iff_cancellation (C : Precat) (a b : C .wild .ob) (f : C .wild .hom a b)
  : Product (IsMono (C .wild) a b f → MonoCancellation (C .wild) a b f)
      (MonoCancellation (C .wild) a b f → IsMono (C .wild) a b f)
  ≔ let W ≔ C .wild in
    (m c ↦ embedding_reflects_paths (W .hom c a) (W .hom c b) (k ↦ W .comp c a b f k) (m c),
     r c ↦ path_reflecting_set_embedding (W .hom c a) (W .hom c b) (C .homset c b)
       (k ↦ W .comp c a b f k) (r c))

def precat_epi_iff_cancellation (C : Precat) (a b : C .wild .ob) (f : C .wild .hom a b)
  : Product (IsEpi (C .wild) a b f → EpiCancellation (C .wild) a b f)
      (EpiCancellation (C .wild) a b f → IsEpi (C .wild) a b f)
  ≔ let W ≔ C .wild in
    (m c ↦ embedding_reflects_paths (W .hom b c) (W .hom a c) (k ↦ W .comp a b c k f) (m c),
     r c ↦ path_reflecting_set_embedding (W .hom b c) (W .hom a c) (C .homset a c)
       (k ↦ W .comp a b c k f) (r c))

{` xca:monos-epis-sets-types, first part: the monomorphisms in the wild
   category of types are exactly the injections. For the converse
   direction we test with C = 1: a fiber of f is a retract of the
   corresponding fiber of f ∘ - on maps out of 1. `}
def unit_maps_fiber_section (A B : Type) (f : A → B) (b : B) (t : BookFiber A B f b)
  : BookFiber (Unit → A) (Unit → B) (k ↦ x ↦ f (k x)) (_ ↦ b)
  ≔ (_ ↦ t .fst, funext Unit (_ ↦ B) (_ ↦ b) (_ ↦ f (t .fst)) (_ ↦ t .snd))

def unit_maps_fiber_retraction (A B : Type) (f : A → B) (b : B)
  (s : BookFiber (Unit → A) (Unit → B) (k ↦ x ↦ f (k x)) (_ ↦ b)) : BookFiber A B f b
  ≔ (s .fst star., s .snd (refl (star. : Unit)))

def unit_maps_fiber_retract (A B : Type) (f : A → B) (b : B) (t : BookFiber A B f b)
  : Id (BookFiber A B f b) (unit_maps_fiber_retraction A B f b (unit_maps_fiber_section A B f b t)) t
  ≔ (refl (t .fst),
     inverse (Id B b (f (t .fst))) (t .snd)
       (happly Unit (_ ↦ B) (_ ↦ b) (_ ↦ f (t .fst))
         (funext Unit (_ ↦ B) (_ ↦ b) (_ ↦ f (t .fst)) (_ ↦ t .snd)) star.)
       (funext_beta Unit (_ ↦ B) (_ ↦ b) (_ ↦ f (t .fst)) (_ ↦ t .snd) star.))

def type_mono_embedding (A B : Type) (f : A → B) (m : IsMono TypeWild A B f) : IsEmbedding A B f
  ≔ b ↦ retract_prop (BookFiber (Unit → A) (Unit → B) (k ↦ x ↦ f (k x)) (_ ↦ b)) (BookFiber A B f b)
      (m Unit (_ ↦ b)) (unit_maps_fiber_retraction A B f b) (unit_maps_fiber_section A B f b)
      (unit_maps_fiber_retract A B f b)

def type_embedding_mono (A B : Type) (f : A → B) (e : IsEmbedding A B f) : IsMono TypeWild A B f
  ≔ c ↦ postcomposition_embedding c A B f e

def type_mono_iff_embedding (A B : Type) (f : A → B)
  : Product (IsMono TypeWild A B f → IsEmbedding A B f) (IsEmbedding A B f → IsMono TypeWild A B f)
  ≔ (type_mono_embedding A B f, type_embedding_mono A B f)

def type_mono_embedding_equiv (A B : Type) (f : A → B) : Equiv (IsMono TypeWild A B f) (IsEmbedding A B f)
  ≔ iff_equiv (IsMono TypeWild A B f) (IsEmbedding A B f) (is_mono_prop TypeWild A B f) (embedding_prop A B f)
      (type_mono_embedding A B f) (type_embedding_mono A B f)

{` Epimorphisms are surjective: test with the two predicates
   b ↦ ∃ a, b = f(a) and b ↦ True on B with values in the set Prop
   (PropTypes); they agree after precomposition with f. `}
def surjectivity_predicate (A B : Type) (f : A → B) : B → PropTypes
  ≔ b ↦ (Mere (BookFiber A B f b), mere_isprop (BookFiber A B f b))

def surjectivity_predicate_restriction (A B : Type) (f : A → B)
  : Id (A → PropTypes) (a ↦ surjectivity_predicate A B f (f a)) (_ ↦ (Unit, unit_prop))
  ≔ funext A (_ ↦ PropTypes) (a ↦ surjectivity_predicate A B f (f a)) (_ ↦ (Unit, unit_prop))
      (a ↦ proposition_extensionality (surjectivity_predicate A B f (f a)) (Unit, unit_prop)
        (_ ↦ star.) (_ ↦ mere (BookFiber A B f (f a)) (a, refl (f a))))

def surjective_from_prop_cancellation (A B : Type) (f : A → B)
  (r : Id (B → PropTypes) (surjectivity_predicate A B f) (_ ↦ (Unit, unit_prop))) : Surjective A B f
  ≔ b ↦ transport PropTypes (P ↦ P .fst) (Unit, unit_prop) (surjectivity_predicate A B f b)
      (inverse PropTypes (surjectivity_predicate A B f b) (Unit, unit_prop) (r (refl b))) star.

{` "The epimorphisms in the wild category of types are always surjections." `}
def type_epi_surjective (A B : Type) (f : A → B) (e : IsEpi TypeWild A B f) : Surjective A B f
  ≔ surjective_from_prop_cancellation A B f
      (embedding_reflects_paths (B → PropTypes) (A → PropTypes) (k ↦ x ↦ k (f x)) (e PropTypes)
        (surjectivity_predicate A B f) (_ ↦ (Unit, unit_prop)) (surjectivity_predicate_restriction A B f))

{` "... but are much more restricted": the inclusion of the base point of
   the groupoid of two-element sets is a surjection (module 40) but not an
   epimorphism of types; the test object is TwoSets itself. `}
def two_sets_base_not_type_epi (e : IsEpi TypeWild Unit TwoSets two_sets_base_inclusion) : Empty
  ≔ two_sets_identity_not_constant
      (embedding_reflects_paths (TwoSets → TwoSets) (Unit → TwoSets)
        (k ↦ x ↦ k (two_sets_base_inclusion x)) (e TwoSets)
        (identity TwoSets) two_sets_constant_base two_sets_base_restrictions_equal)

{` xca:monos-epis-sets-types, second part: the epimorphisms in the category
   of sets are exactly the surjections. The test object for "epi implies
   surjective" is the set of propositions (PropTypes with propositions_set;
   in a stratified reading this set lies in the next universe, see the
   note in the inventory); the converse is cancellation of surjections
   for set-valued maps (module 40). `}
def prop_set_object : SetCat .wild .ob ≔ (PropTypes, propositions_set)

def set_epi_surjective (A B : SetCat .wild .ob) (f : A .fst → B .fst) (e : IsEpi (SetCat .wild) A B f)
  : Surjective (A .fst) (B .fst) f
  ≔ surjective_from_prop_cancellation (A .fst) (B .fst) f
      (embedding_reflects_paths (B .fst → PropTypes) (A .fst → PropTypes) (k ↦ x ↦ k (f x)) (e prop_set_object)
        (surjectivity_predicate (A .fst) (B .fst) f) (_ ↦ (Unit, unit_prop))
        (surjectivity_predicate_restriction (A .fst) (B .fst) f))

def set_surjective_epi (A B : SetCat .wild .ob) (f : A .fst → B .fst) (s : Surjective (A .fst) (B .fst) f)
  : IsEpi (SetCat .wild) A B f
  ≔ c ↦ path_reflecting_set_embedding (B .fst → c .fst) (A .fst → c .fst)
      (pi_set (A .fst) (_ ↦ c .fst) (_ ↦ c .snd)) (k ↦ x ↦ k (f x))
      (g h ↦ equiv_inverse_map (Id (B .fst → c .fst) g h)
        (Id (A .fst → c .fst) (precompose (A .fst) (B .fst) (c .fst) f g) (precompose (A .fst) (B .fst) (c .fst) f h))
        (cancel_surjection_into_set (A .fst) (B .fst) (c .fst) f s (c .snd) g h))

def set_epi_iff_surjective (A B : SetCat .wild .ob) (f : A .fst → B .fst)
  : Product (IsEpi (SetCat .wild) A B f → Surjective (A .fst) (B .fst) f)
      (Surjective (A .fst) (B .fst) f → IsEpi (SetCat .wild) A B f)
  ≔ (set_epi_surjective A B f, set_surjective_epi A B f)

def set_epi_surjective_equiv (A B : SetCat .wild .ob) (f : A .fst → B .fst)
  : Equiv (IsEpi (SetCat .wild) A B f) (Surjective (A .fst) (B .fst) f)
  ≔ iff_equiv (IsEpi (SetCat .wild) A B f) (Surjective (A .fst) (B .fst) f)
      (is_epi_prop (SetCat .wild) A B f) (surjective_property_prop (A .fst) (B .fst) f)
      (set_epi_surjective A B f) (set_surjective_epi A B f)

{` xca:monos-epis-preorder: every arrow of a preorder is both a mono and an
   epi, since every map between propositions is an injection. `}
def prop_map_embedding (X Y : Type) (hX : isProp X) (hY : isProp Y) (f : X → Y) : IsEmbedding X Y f
  ≔ y ↦ sigma_prop X (x ↦ Id Y y (f x)) hX (x ↦ prop_is_set Y hY y (f x))

def preorder_arrow_mono (P : Preorder) (a b : P .wild .ob) (f : P .wild .hom a b) : IsMono (P .wild) a b f
  ≔ c ↦ prop_map_embedding (P .wild .hom c a) (P .wild .hom c b) (P .homprop c a) (P .homprop c b)
      (k ↦ P .wild .comp c a b f k)

def preorder_arrow_epi (P : Preorder) (a b : P .wild .ob) (f : P .wild .hom a b) : IsEpi (P .wild) a b f
  ≔ c ↦ prop_map_embedding (P .wild .hom b c) (P .wild .hom a c) (P .homprop b c) (P .homprop a c)
      (k ↦ P .wild .comp a b c k f)

def preorder_arrow_mono_epi (P : Preorder) (a b : P .wild .ob) (f : P .wild .hom a b)
  : Product (IsMono (P .wild) a b f) (IsEpi (P .wild) a b f)
  ≔ (preorder_arrow_mono P a b f, preorder_arrow_epi P a b f)

{` Litmus checks: the constant map Bool → 1 is not a mono of types; the
   negation of Bool is an epi of sets; 1 → TwoSets is surjective (module
   40) but not an epi (above). `}
def bool_to_unit_not_mono (m : IsMono TypeWild Bool Unit (_ ↦ star.)) : Empty
  ≔ bool_encode true. false.
      (embedding_reflects_paths Bool Unit (_ ↦ star.) (type_mono_embedding Bool Unit (_ ↦ star.) m)
        true. false. (refl (star. : Unit)))

def bool_negation_set_epi : IsEpi (SetCat .wild) set_cat_bool set_cat_bool bool_not
  ≔ set_surjective_epi set_cat_bool set_cat_bool bool_not
      (b ↦ mere (BookFiber Bool Bool bool_not b) (bool_not b, inverse Bool (bool_not (bool_not b)) b (bool_not_involutive b)))
