import "../../../src/404-group-examples"
import "01-lpo-topology"

{` Blind statements for choicefin.tex ("Choice for finite sets"):
   the choice principles and the claims that only involve them.
   Set = SetTypes = Σ(A : Type) isSet A; ‖-‖ = Mere; "there exists" = Mere Σ. `}

{` Set_{≠∅}: sets with an element of ‖A‖ (def:non-empty). `}
def BlindNonEmptySets : Type ≔ Σ SetTypes (A ↦ Mere (A .fst))

{` pri:ac, first form: for every set X and P : X → Set_{≠∅} there (merely)
   exists a dependent function of type Π_{x:X} P(x). `}
def BlindACNonEmptyForm : Type
  ≔ (X : Type) → isSet X → (P : X → BlindNonEmptySets) → Mere ((x : X) → P x .fst .fst)

{` pri:ac, second form (eq:ac-impl): for every set X and P : X → Set,
   Π_x ‖P(x)‖ → ‖Π_x P(x)‖. This is AC (also in the definition at line 65). `}
def BlindAC : Type
  ≔ (X : Type) → isSet X → (P : X → SetTypes)
    → ((x : X) → Mere (P x .fst)) → Mere ((x : X) → P x .fst)

{` pri:ac, "In other terms": the two forms are logically equivalent. `}
def blind_ac_forms_iff : Type ≔ BlindIff BlindACNonEmptyForm BlindAC

{` Remark after pri:ac. A section of f : A → B is g : B → A with f ∘ g = id_B
   (def:surjection, footnote). `}
def BlindSections (A B : Type) (f : A → B) : Type
  ≔ Σ (B → A) (g ↦ Id (B → B) (b ↦ f (g b)) (b ↦ b))

def blind_choice_remark_pi_sections_equiv : Type
  ≔ (X : Type) (P : X → Type)
    → BookEquiv ((x : X) → P x) (BlindSections (Σ X P) X (u ↦ u .fst))

{` "families of non-empty sets correspond to surjections between sets": the
   values of P are non-empty iff the projection is a surjection, ... `}
def blind_choice_remark_nonempty_iff_projection_surjective : Type
  ≔ (X : Type) (P : X → Type)
    → BlindIff ((x : X) → Mere (P x)) (Surjective (Σ X P) X (u ↦ u .fst))

{` ... and (using that X is a set) the total type of a family of sets is a set. `}
def blind_choice_remark_total_set : Type
  ≔ (X : Type) → isSet X → (P : X → SetTypes) → isSet (Σ X (x ↦ P x .fst))

{` The correspondence itself: for a set X, P ↦ (Σ_x P(x), pr1) is an
   equivalence from families of non-empty sets over X to surjections from a
   set onto X. The two small proofs below are needed to define the map. `}
def BlindSurjectionsOnto (X : Type) : Type
  ≔ Σ SetTypes (Y ↦ Σ (Y .fst → X) (p ↦ Surjective (Y .fst) X p))

def blind_projection_surjective (X : Type) (P : X → BlindNonEmptySets)
  : Surjective (Σ X (x ↦ P x .fst .fst)) X (u ↦ u .fst)
  ≔ x ↦ mere_rec (P x .fst .fst)
      (Mere (BookFiber (Σ X (x ↦ P x .fst .fst)) X (u ↦ u .fst) x))
      (mere_isprop (BookFiber (Σ X (x ↦ P x .fst .fst)) X (u ↦ u .fst) x))
      (a ↦ mere (BookFiber (Σ X (x ↦ P x .fst .fst)) X (u ↦ u .fst) x) ((x, a), refl x))
      (P x .snd)

def blind_family_to_surjection (X : Type) (hX : isSet X) (P : X → BlindNonEmptySets)
  : BlindSurjectionsOnto X
  ≔ ((Σ X (x ↦ P x .fst .fst), sigma_set X (x ↦ P x .fst .fst) hX (x ↦ P x .fst .snd)),
      (u ↦ u .fst, blind_projection_surjective X P))

def blind_choice_remark_families_surjections_equiv : Type
  ≔ (X : Type) (hX : isSet X)
    → BookIsEquiv (X → BlindNonEmptySets) (BlindSurjectionsOnto X) (blind_family_to_surjection X hX)

{` "Thus, the axiom of choice equivalently says that any surjection between
   sets admits a section" (merely, as AC concludes ‖Π‖). `}
def BlindSurjectionsSplit : Type
  ≔ (A B : Type) → isSet A → isSet B → (f : A → B) → Surjective A B f → Mere (BlindSections A B f)

def blind_choice_remark_ac_iff_surjections_split : Type ≔ BlindIff BlindAC BlindSurjectionsSplit

{` Theorem (Diaconescu): AC implies LEM (pri:lem: P + ¬P for every
   proposition P; ExcludedMiddle of module 70 is literally that). `}
def blind_ac_implies_lem : Type ≔ BlindAC → ExcludedMiddle

{` Definition (line 65). X-AC: (eq:ac-impl) for a fixed X and all families of
   sets over X. X is any type here: the definition is used for X = S¹ later. `}
def BlindLocalAC (X : Type) : Type
  ≔ (P : X → SetTypes) → ((x : X) → Mere (P x .fst)) → Mere ((x : X) → P x .fst)

{` AC(n): (eq:ac-impl) for all sets X and families P : X → BΣ_n of n-element
   sets (BΣ_n = FinSet_n = Set_(Fin n), the classifying type of Σ_n). `}
def BlindFinSetsAt (n : Nat) : Type ≔ BG (symmetric_group n) .carrier

{` Litmus: the base point of BΣ_n has underlying type Fin n. `}
def blind_finsets_base_carrier (n : Nat)
  : Id Type (shape (symmetric_group n) .fst .fst) (Fin n)
  ≔ refl (Fin n)

def BlindACn (n : Nat) : Type
  ≔ (X : Type) → isSet X → (P : X → BlindFinSetsAt n)
    → ((x : X) → Mere (P x .fst .fst)) → Mere ((x : X) → P x .fst .fst)

{` X-AC(n). `}
def BlindLocalACn (X : Type) (n : Nat) : Type
  ≔ (P : X → BlindFinSetsAt n)
    → ((x : X) → Mere (P x .fst .fst)) → Mere ((x : X) → P x .fst .fst)

{` Consistency of the definitions: AC is X-AC for every set X, by unfolding. `}
def blind_ac_is_local_ac_everywhere : Id Type BlindAC ((X : Type) → isSet X → BlindLocalAC X)
  ≔ refl BlindAC

{` xca: X-AC holds whenever X is a finite set (def:is-finite: ∃n. X = Fin n). `}
def blind_xca_finite_local_ac : Type ≔ (X : Type) → IsFinite X → BlindLocalAC X

{` Text before pri:sc: the untruncated axiom of choice AC_∞ (the family P is
   allowed to be arbitrary) and its local version X-AC_∞. `}
def BlindLocalACInfty (X : Type) : Type
  ≔ (P : X → Type) → ((x : X) → Mere (P x)) → Mere ((x : X) → P x)

def BlindACInfty : Type ≔ (X : Type) → isSet X → BlindLocalACInfty X

{` pri:sc (Sets Cover): for any type A there (merely) exists a set X with a
   surjection X → A. `}
def BlindSetsCover : Type
  ≔ (A : Type) → Mere (Σ Type (X ↦ Product (isSet X) (Σ (X → A) (f ↦ Surjective X A f))))

{` xca: AC_∞ is equivalent to AC ∧ SC (all three are propositions). `}
def blind_xca_ac_infty_iff_ac_and_sc : Type ≔ BlindIff BlindACInfty (Product BlindAC BlindSetsCover)

{` xca: S¹-AC(2) is false (for the circle, given as any CircleSignature). `}
def blind_xca_circle_local_ac_two_false : Type
  ≔ (C : CircleSignature) → Not (BlindLocalACn (C .carrier) 2)
