export "03-integers"
export "04-path-algebra"

{` Specifications for the two higher inductive types needed here.
   They are PARAMETERS, not axiom declarations and not constructions of HITs.
   No inhabitant is asserted here; both are inhabited later by constructions
   without axioms: native_truncation (module 29) and constructed_circle
   (module 223). Narya efafad2 has no HIT declarations.
   The beta law is an identity of the full dependent boundary datum, keeping
   the base-point and loop computations coherent in one sigma path. `}
def CircleBoundary (C : Type) (base : C) (loop : Id C base base)
  (P : C → Type) : Type ≔ Σ (P base) (b ↦ Id P loop b b)

def circle_evaluate (C : Type) (base : C) (loop : Id C base base)
  (P : C → Type) (f : (x : C) → P x) : CircleBoundary C base loop P
  ≔ (f base, refl f loop)

def CircleSignature : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop : Id carrier base base,
  induction : (P : carrier → Type) (d : CircleBoundary carrier base loop P)
    → Σ ((x : carrier) → P x)
        (f ↦ Id (CircleBoundary carrier base loop P)
          (circle_evaluate carrier base loop P f) d))

def TruncationSignature : Type ≔ sig (
  carrier : Type → Type,
  include : (A : Type) → A → carrier A,
  proposition : (A : Type) → isProp (carrier A),
  eliminate : (A : Type) (P : carrier A → Type)
    → ((x : carrier A) → isProp (P x))
    → ((a : A) → P (include A a)) → (x : carrier A) → P x)

def circle_ind_prop (C : CircleSignature) (P : C .carrier → Type)
  (hP : (x : C .carrier) → isProp (P x)) (b : P (C .base))
  : (x : C .carrier) → P x
  ≔ C .induction P
      (b, pathover_of_eq (C .carrier) P (C .base) (C .base) (C .loop) b b
        (hP (C .base)
          (transport (C .carrier) P (C .base) (C .base) (C .loop) b) b)) .fst

{` lem:circleisconnected, for every TruncationSignature and CircleSignature (both inhabited: native_truncation, constructed_circle). `}
def circle_connected (T : TruncationSignature) (C : CircleSignature)
  : (x : C .carrier) → T .carrier (Id (C .carrier) (C .base) x)
  ≔ circle_ind_prop C (x ↦ T .carrier (Id (C .carrier) (C .base) x))
      (x ↦ T .proposition (Id (C .carrier) (C .base) x))
      (T .include (Id (C .carrier) (C .base) (C .base)) (refl (C .base)))

{` The map used in the universal property. Being an equivalence is NOT
   assumed by CircleSignature and remains a theorem to prove. `}
def circle_eval (C : CircleSignature) (A : Type) : (C .carrier → A) → FreeLoop A
  ≔ f ↦ (f (C .base), refl f (C .loop))

def circle_rec (C : CircleSignature) (A : Type) (d : FreeLoop A) : C .carrier → A
  ≔ C .induction (_ ↦ A) d .fst

def circle_rec_beta (C : CircleSignature) (A : Type) (d : FreeLoop A)
  : Id (FreeLoop A) (circle_eval C A (circle_rec C A d)) d
  ≔ C .induction (_ ↦ A) d .snd

{` A family with the intended integer monodromy and its boundary law. `}
def circle_integer_family (C : CircleSignature) : C .carrier → Type
  ≔ circle_rec C Type (Int, int_universe_loop)

def circle_integer_family_beta (C : CircleSignature)
  : Id (FreeLoop Type)
      (circle_eval C Type (circle_integer_family C)) (Int, int_universe_loop)
  ≔ circle_rec_beta C Type (Int, int_universe_loop)

{` The uniqueness part of lem:freeloopspace follows from induction.
   The square in the boundary equality is transposed to obtain the loop
   datum for the pointwise homotopy. `}
def circle_maps_equal (C : CircleSignature) (A : Type)
  (f g : C .carrier → A)
  (d : Id (FreeLoop A) (circle_eval C A f) (circle_eval C A g))
  : Id (C .carrier → A) f g
  ≔ funext (C .carrier) (_ ↦ A) f g
      (C .induction (x ↦ Id A (f x) (g x)) (d .fst, sym (d .snd)) .fst)

def circle_rec_eta (C : CircleSignature) (A : Type) (f : C .carrier → A)
  : Id (C .carrier → A) (circle_rec C A (circle_eval C A f)) f
  ≔ circle_maps_equal C A (circle_rec C A (circle_eval C A f)) f
      (circle_rec_beta C A (circle_eval C A f))
