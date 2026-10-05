export "1700-choice-principles"

{` Remark after pri:ac. Elements of Π_{x:X} P(x) are the same as sections
   of the projection pr1 : Σ_{x:X} P(x) → X, in the sense of the footnote of
   def:surjection (MapSection: g with pr1 ∘ g = id). `}
def pi_section_equiv (X : Type) (P : X → Type)
  : Equiv ((x : X) → P x) (MapSection (Σ X P) X (t ↦ t .fst))
  ≔ compose_equiv ((x : X) → P x) (SplitSurjection (Σ X P) X (t ↦ t .fst)) (MapSection (Σ X P) X (t ↦ t .fst))
      (pi_equiv X P (x ↦ BookFiber (Σ X P) X (t ↦ t .fst) x)
        (x ↦ canonical_inverse_equiv (BookFiber (Σ X P) X (t ↦ t .fst) x) (P x)
          (native_equivalence (BookFiber (Σ X P) X (t ↦ t .fst) x) (P x) (book_projection_fiber_equiv X P x))))
      (split_surjection_section_equiv (Σ X P) X (t ↦ t .fst))

{` Fibers of a map between sets are sets, and the domain of a map with
   set fibers into a set is a set. `}
def book_fiber_set (B X : Type) (f : B → X) (hB : isSet B) (hX : isSet X) (a : X)
  : isSet (BookFiber B X f a)
  ≔ sigma_set B (b ↦ Id X a (f b)) hB (b ↦ prop_is_set (Id X a (f b)) (hX a (f b)))

def domain_set_of_fiber_sets (B X : Type) (f : B → X) (hX : isSet X)
  (h : (a : X) → isSet (BookFiber B X f a)) : isSet B
  ≔ hlevel_two_to_set B
      (hlevel_equiv (suc. (suc. zero.)) (Σ X (a ↦ BookFiber B X f a)) B (sum_of_fibers_equiv B X f)
        (set_to_hlevel_two (Σ X (a ↦ BookFiber B X f a))
          (sigma_set X (a ↦ BookFiber B X f a) hX h)))

{` Families of non-empty sets over a set X correspond to surjections
   between sets onto X. `}
def SetSurjectionsOnto (X : Type) : Type
  ≔ Σ SetTypes (Y ↦ Σ (Y .fst → X) (p ↦ Surjective (Y .fst) X p))

def NonemptySetStructure (T : Type) : Type ≔ Product (isSet T) (Mere T)

def nonempty_sets_reassociate : Equiv NonemptySets (Σ Type NonemptySetStructure)
  ≔ sigma_assoc Type isSet (T _ ↦ Mere T)

def nonempty_fibers_iff_set_surjection (X : Type) (hX : isSet X) (B : Type) (f : B → X)
  : Equiv ((a : X) → NonemptySetStructure (BookFiber B X f a)) (Product (isSet B) (Surjective B X f))
  ≔ iff_equiv ((a : X) → NonemptySetStructure (BookFiber B X f a)) (Product (isSet B) (Surjective B X f))
      (pi_prop X (a ↦ NonemptySetStructure (BookFiber B X f a))
        (a ↦ product_prop (isSet (BookFiber B X f a)) (Mere (BookFiber B X f a))
          (isset_isprop (BookFiber B X f a)) (mere_isprop (BookFiber B X f a))))
      (product_prop (isSet B) (Surjective B X f) (isset_isprop B)
        (pi_prop X (a ↦ Mere (BookFiber B X f a)) (a ↦ mere_isprop (BookFiber B X f a))))
      (h ↦ (domain_set_of_fiber_sets B X f hX (a ↦ h a .fst), a ↦ h a .snd))
      (h a ↦ (book_fiber_set B X f (h .fst) hX a, h .snd a))

def set_surjections_regroup (X : Type)
  : Equiv (Σ Type (B ↦ Σ (B → X) (f ↦ Product (isSet B) (Surjective B X f)))) (SetSurjectionsOnto X)
  ≔ quasi_inverse_equiv (Σ Type (B ↦ Σ (B → X) (f ↦ Product (isSet B) (Surjective B X f)))) (SetSurjectionsOnto X)
      (t ↦ ((t .fst, t .snd .snd .fst), (t .snd .fst, t .snd .snd .snd)))
      (t ↦ (t .fst .fst, (t .snd .fst, (t .fst .snd, t .snd .snd))))
      (t ↦ refl t) (t ↦ refl t)

def nonempty_families_surjections_equiv (X : Type) (hX : isSet X)
  : Equiv (X → NonemptySets) (SetSurjectionsOnto X)
  ≔ let N ≔ Σ Type NonemptySetStructure in
    let M ≔ Σ Type (B ↦ Σ (B → X) (f ↦ (a : X) → NonemptySetStructure (BookFiber B X f a))) in
    let R ≔ Σ Type (B ↦ Σ (B → X) (f ↦ Product (isSet B) (Surjective B X f))) in
    compose_equiv (X → NonemptySets) (X → N) (SetSurjectionsOnto X)
      (pi_equiv X (_ ↦ NonemptySets) (_ ↦ N) (_ ↦ nonempty_sets_reassociate))
      (compose_equiv (X → N) M (SetSurjectionsOnto X)
        (structured_families_equiv X NonemptySetStructure)
        (compose_equiv M R (SetSurjectionsOnto X)
          (family_equiv Type (B ↦ Σ (B → X) (f ↦ (a : X) → NonemptySetStructure (BookFiber B X f a)))
            (B ↦ Σ (B → X) (f ↦ Product (isSet B) (Surjective B X f)))
            (B ↦ family_equiv (B → X) (f ↦ (a : X) → NonemptySetStructure (BookFiber B X f a))
              (f ↦ Product (isSet B) (Surjective B X f)) (f ↦ nonempty_fibers_iff_set_surjection X hX B f)))
          (set_surjections_regroup X)))

{` "The axiom of choice equivalently says that any surjection between sets
   admits a section" (merely, since AC asserts existence). `}
def SurjectionsBetweenSetsSplit : Type
  ≔ (X Y : SetTypes) (p : Y .fst → X .fst) → Surjective (Y .fst) (X .fst) p
    → Mere (MapSection (Y .fst) (X .fst) p)

def surjections_between_sets_split_prop : isProp SurjectionsBetweenSetsSplit
  ≔ pi_prop SetTypes (X ↦ (Y : SetTypes) (p : Y .fst → X .fst) → Surjective (Y .fst) (X .fst) p
      → Mere (MapSection (Y .fst) (X .fst) p))
      (X ↦ pi_prop SetTypes (Y ↦ (p : Y .fst → X .fst) → Surjective (Y .fst) (X .fst) p
          → Mere (MapSection (Y .fst) (X .fst) p))
        (Y ↦ pi_prop (Y .fst → X .fst) (p ↦ Surjective (Y .fst) (X .fst) p → Mere (MapSection (Y .fst) (X .fst) p))
          (p ↦ pi_prop (Surjective (Y .fst) (X .fst) p) (_ ↦ Mere (MapSection (Y .fst) (X .fst) p))
            (_ ↦ mere_isprop (MapSection (Y .fst) (X .fst) p)))))

def choice_splits_surjections (ac : AxiomOfChoice) : SurjectionsBetweenSetsSplit
  ≔ X Y p s ↦ trunc_map native_truncation (SplitSurjection (Y .fst) (X .fst) p) (MapSection (Y .fst) (X .fst) p)
      (split_surjection_to_section (Y .fst) (X .fst) p)
      (ac X (x ↦ (BookFiber (Y .fst) (X .fst) p x, book_fiber_set (Y .fst) (X .fst) p (Y .snd) (X .snd) x)) s)

def projection_surjective (X : Type) (P : X → Type) (h : (x : X) → Mere (P x))
  : Surjective (Σ X P) X (t ↦ t .fst)
  ≔ x ↦ trunc_map native_truncation (P x) (BookFiber (Σ X P) X (t ↦ t .fst) x)
      (u ↦ ((x, u), refl x)) (h x)

def split_surjections_choice (h : SurjectionsBetweenSetsSplit) : AxiomOfChoice
  ≔ X P ne ↦
    let T ≔ Σ (X .fst) (x ↦ P x .fst) in
    trunc_map native_truncation (MapSection T (X .fst) (t ↦ t .fst)) ((x : X .fst) → P x .fst)
      (equiv_inverse_map ((x : X .fst) → P x .fst) (MapSection T (X .fst) (t ↦ t .fst))
        (pi_section_equiv (X .fst) (x ↦ P x .fst)))
      (h X (T, sigma_set (X .fst) (x ↦ P x .fst) (X .snd) (x ↦ P x .snd)) (t ↦ t .fst)
        (projection_surjective (X .fst) (x ↦ P x .fst) ne))

def choice_surjections_split_equiv : Equiv AxiomOfChoice SurjectionsBetweenSetsSplit
  ≔ iff_equiv AxiomOfChoice SurjectionsBetweenSetsSplit axiom_of_choice_prop surjections_between_sets_split_prop
      choice_splits_surjections split_surjections_choice
