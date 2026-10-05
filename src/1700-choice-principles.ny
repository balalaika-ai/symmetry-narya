export "280-book-equivalence-maps"
export "284-chapter-two-completions"
export "400-groups"

{` Appendix B, section "Choice for finite sets" (choicefin.tex).
   All choice principles below are types of hypotheses; no inhabitant is
   postulated. Sets range over Narya's single universe Type, as for
   ExcludedMiddle (module 70). `}

{` pri:ac, first formulation. Set_{≠∅} is NonemptySets of module 284
   (sets with a mere point). `}

def AxiomOfChoiceNonempty : Type
  ≔ (X : SetTypes) (P : X .fst → NonemptySets) → Mere ((x : X .fst) → P x .fst .fst)

{` eq:ac-impl for a fixed index type X: the X-local axiom of choice X-AC
   (definition after the Diaconescu theorem), for families of sets. `}
def LocalChoice (X : Type) : Type
  ≔ (P : X → SetTypes) → ((x : X) → Mere (P x .fst)) → Mere ((x : X) → P x .fst)

{` pri:ac, second formulation (eq:ac-impl), and the book's AC. `}
def AxiomOfChoice : Type ≔ (X : SetTypes) → LocalChoice (X .fst)

def local_choice_prop (X : Type) : isProp (LocalChoice X)
  ≔ pi_prop (X → SetTypes) (P ↦ ((x : X) → Mere (P x .fst)) → Mere ((x : X) → P x .fst))
      (P ↦ pi_prop ((x : X) → Mere (P x .fst)) (_ ↦ Mere ((x : X) → P x .fst))
        (_ ↦ mere_isprop ((x : X) → P x .fst)))

def axiom_of_choice_prop : isProp AxiomOfChoice
  ≔ pi_prop SetTypes (X ↦ LocalChoice (X .fst)) (X ↦ local_choice_prop (X .fst))

def axiom_of_choice_nonempty_prop : isProp AxiomOfChoiceNonempty
  ≔ pi_prop SetTypes (X ↦ (P : X .fst → NonemptySets) → Mere ((x : X .fst) → P x .fst .fst))
      (X ↦ pi_prop (X .fst → NonemptySets) (P ↦ Mere ((x : X .fst) → P x .fst .fst))
        (P ↦ mere_isprop ((x : X .fst) → P x .fst .fst)))

def axiom_of_choice_from_nonempty (ac : AxiomOfChoiceNonempty) : AxiomOfChoice
  ≔ X P h ↦ ac X (x ↦ (P x, h x))

def axiom_of_choice_to_nonempty (ac : AxiomOfChoice) : AxiomOfChoiceNonempty
  ≔ X P ↦ ac X (x ↦ P x .fst) (x ↦ P x .snd)

{` The two formulations of pri:ac ("In other terms") are equivalent. `}
def axiom_of_choice_formulations_equiv : Equiv AxiomOfChoiceNonempty AxiomOfChoice
  ≔ iff_equiv AxiomOfChoiceNonempty AxiomOfChoice axiom_of_choice_nonempty_prop axiom_of_choice_prop
      axiom_of_choice_from_nonempty axiom_of_choice_to_nonempty

{` Definition after the Diaconescu theorem: AC(n) and X-AC(n) restrict to
   families P : X → BΣ_n = FinSet_n (FiniteSetsAt n), keeping the hypothesis
   Π_x ‖P(x)‖ of eq:ac-impl. `}
def LocalChoiceOfSize (X : Type) (n : Nat) : Type
  ≔ (P : X → FiniteSetsAt n) → ((x : X) → Mere (P x .fst .fst)) → Mere ((x : X) → P x .fst .fst)

def ChoiceOfSize (n : Nat) : Type ≔ (X : SetTypes) → LocalChoiceOfSize (X .fst) n

def local_choice_of_size_prop (X : Type) (n : Nat) : isProp (LocalChoiceOfSize X n)
  ≔ pi_prop (X → FiniteSetsAt n)
      (P ↦ ((x : X) → Mere (P x .fst .fst)) → Mere ((x : X) → P x .fst .fst))
      (P ↦ pi_prop ((x : X) → Mere (P x .fst .fst)) (_ ↦ Mere ((x : X) → P x .fst .fst))
        (_ ↦ mere_isprop ((x : X) → P x .fst .fst)))

def choice_of_size_prop (n : Nat) : isProp (ChoiceOfSize n)
  ≔ pi_prop SetTypes (X ↦ LocalChoiceOfSize (X .fst) n) (X ↦ local_choice_of_size_prop (X .fst) n)

{` X-AC implies X-AC(n), and AC implies AC(n). `}
def local_choice_of_size (X : Type) (ac : LocalChoice X) (n : Nat) : LocalChoiceOfSize X n
  ≔ P h ↦ ac (x ↦ P x .fst) h

def choice_of_size (ac : AxiomOfChoice) (n : Nat) : ChoiceOfSize n
  ≔ X ↦ local_choice_of_size (X .fst) (ac X) n

{` The untruncated X-local axiom of choice X-AC_∞ (families of arbitrary
   types). Its formula is FiniteChoice X of module 34, whose name refers to
   its use for finite X; it is reused here, not redefined. AC_∞ fixes a set X. `}
def UntruncatedLocalChoice (X : Type) : Type ≔ FiniteChoice X

def UntruncatedChoice : Type ≔ (X : SetTypes) → UntruncatedLocalChoice (X .fst)

def untruncated_choice_prop : isProp UntruncatedChoice
  ≔ pi_prop SetTypes (X ↦ UntruncatedLocalChoice (X .fst)) (X ↦ finite_choice_prop (X .fst))

def untruncated_local_choice_restrict (X : Type) (ac : UntruncatedLocalChoice X) : LocalChoice X
  ≔ P h ↦ ac (x ↦ P x .fst) h

def untruncated_choice_restrict (ac : UntruncatedChoice) : AxiomOfChoice
  ≔ X ↦ untruncated_local_choice_restrict (X .fst) (ac X)

{` pri:sc, Sets Cover: every type merely admits a surjection from a set. `}
def SetCovers (A : Type) : Type
  ≔ Σ SetTypes (X ↦ Σ (X .fst → A) (f ↦ Surjective (X .fst) A f))

def SetsCover : Type ≔ (A : Type) → Mere (SetCovers A)

def sets_cover_prop : isProp SetsCover
  ≔ pi_prop Type (A ↦ Mere (SetCovers A)) (A ↦ mere_isprop (SetCovers A))

{` xca after the definition: X-AC holds for every finite set X; in fact
   X-AC_∞ holds (finite_choice, module 34). `}
def finite_untruncated_local_choice (X : Type) (h : IsFinite X) : UntruncatedLocalChoice X
  ≔ finite_choice X h

def finite_local_choice (X : Type) (h : IsFinite X) : LocalChoice X
  ≔ untruncated_local_choice_restrict X (finite_choice X h)

{` Litmus checks: X-AC(1) holds for every X (one-element sets are
   contractible), and X-AC(0) holds because Π_x ‖P(x)‖ already forces X to
   be empty. Both are exact instances of LocalChoiceOfSize. `}
def one_element_point (S : FiniteSetsAt (suc. zero.)) : Mere (S .fst .fst)
  ≔ mere_rec (Id Type (Fin (suc. zero.)) (S .fst .fst)) (Mere (S .fst .fst)) (mere_isprop (S .fst .fst))
      (p ↦ mere (S .fst .fst) (transport Type (T ↦ T) (Fin (suc. zero.)) (S .fst .fst) p (inr. star.)))
      (S .snd)

def one_element_prop (S : FiniteSetsAt (suc. zero.)) : isProp (S .fst .fst)
  ≔ mere_rec (Id Type (Fin (suc. zero.)) (S .fst .fst)) (isProp (S .fst .fst)) (isprop_isprop (S .fst .fst))
      (p ↦ transport Type isProp (Fin (suc. zero.)) (S .fst .fst) p
        (x y ↦ match x [
        | inl. e ↦ match e []
        | inr. u ↦ match y [ inl. e ↦ match e [] | inr. v ↦ inr. (unit_prop u v) ] ]))
      (S .snd)

def local_choice_of_size_one (X : Type) : LocalChoiceOfSize X (suc. zero.)
  ≔ P h ↦ mere ((x : X) → P x .fst .fst)
      (x ↦ mere_rec (P x .fst .fst) (P x .fst .fst) (one_element_prop (P x)) (identity (P x .fst .fst)) (h x))

def choice_of_size_one : ChoiceOfSize (suc. zero.) ≔ X ↦ local_choice_of_size_one (X .fst)

def local_choice_of_size_zero (X : Type) : LocalChoiceOfSize X zero.
  ≔ P h ↦ mere ((x : X) → P x .fst .fst)
      (x ↦ mere_rec (P x .fst .fst) (P x .fst .fst)
        (mere_rec (Id Type (Fin zero.) (P x .fst .fst)) (isProp (P x .fst .fst)) (isprop_isprop (P x .fst .fst))
          (p ↦ transport Type isProp Empty (P x .fst .fst) p empty_prop) (P x .snd))
        (identity (P x .fst .fst)) (h x))

def choice_of_size_zero : ChoiceOfSize zero. ≔ X ↦ local_choice_of_size_zero (X .fst)

def bool_local_choice : LocalChoice Bool
  ≔ finite_local_choice Bool
      (mere (Σ Nat (n ↦ Id Type Bool (Fin n))) (two, inverse Type (Fin two) Bool fin_two_path))
