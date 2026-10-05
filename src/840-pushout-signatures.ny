export "404-group-examples"

{` Chapter 8 (congp.tex), section "Pushouts of types" (printed as "(TBW)",
   no blocks).  Pushouts are the general notion behind def:wedge,
   def:sumofgroup and def:bfree.

   The pinned Narya has no higher inductive types.  A pushout of a span
   A <-f- C -g-> B is therefore a PARAMETER: a PushoutSignature is a type
   with point constructors incl_left, incl_right, a path constructor glue,
   and the dependent eliminator.  As for CircleSignature (module 05), the
   computation laws are ONE identification of boundary data (the point laws
   together with the path law over them); they are not judgmental.  No
   inhabitant is asserted here.  All results below hold for every
   signature. `}

def PushoutBoundary (A B C : Type) (f : C → A) (g : C → B) (X : Type)
  (il : A → X) (ir : B → X) (gl : (c : C) → Id X (il (f c)) (ir (g c)))
  (P : X → Type) : Type
  ≔ Σ ((a : A) → P (il a)) (l ↦ Σ ((b : B) → P (ir b)) (r ↦
      (c : C) → Id P (gl c) (l (f c)) (r (g c))))

def pushout_evaluate (A B C : Type) (f : C → A) (g : C → B) (X : Type)
  (il : A → X) (ir : B → X) (gl : (c : C) → Id X (il (f c)) (ir (g c)))
  (P : X → Type) (h : (x : X) → P x) : PushoutBoundary A B C f g X il ir gl P
  ≔ (a ↦ h (il a), (b ↦ h (ir b), c ↦ refl h (gl c)))

def PushoutSignature (A B C : Type) (f : C → A) (g : C → B) : Type ≔ sig (
  carrier : Type,
  incl_left : A → carrier,
  incl_right : B → carrier,
  glue : (c : C) → Id carrier (incl_left (f c)) (incl_right (g c)),
  induction : (P : carrier → Type)
    (d : PushoutBoundary A B C f g carrier incl_left incl_right glue P)
    → Σ ((x : carrier) → P x) (h ↦
        Id (PushoutBoundary A B C f g carrier incl_left incl_right glue P)
          (pushout_evaluate A B C f g carrier incl_left incl_right glue P h) d))

{` Boundary data of a family over a given pushout signature. `}
def pushout_boundary (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) : Type
  ≔ PushoutBoundary A B C f g (W .carrier) (W .incl_left) (W .incl_right) (W .glue) P

def pushout_eval (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (h : (x : W .carrier) → P x) : pushout_boundary A B C f g W P
  ≔ pushout_evaluate A B C f g (W .carrier) (W .incl_left) (W .incl_right) (W .glue) P h

def pushout_ind (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (d : pushout_boundary A B C f g W P) : (x : W .carrier) → P x
  ≔ W .induction P d .fst

def pushout_ind_beta (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (d : pushout_boundary A B C f g W P)
  : Id (pushout_boundary A B C f g W P) (pushout_eval A B C f g W P (pushout_ind A B C f g W P d)) d
  ≔ W .induction P d .snd

{` The point laws, extracted from the boundary identification. `}
def pushout_ind_left (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (d : pushout_boundary A B C f g W P) (a : A)
  : Id (P (W .incl_left a)) (pushout_ind A B C f g W P d (W .incl_left a)) (d .fst a)
  ≔ pushout_ind_beta A B C f g W P d .fst (refl a)

def pushout_ind_right (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (d : pushout_boundary A B C f g W P) (b : B)
  : Id (P (W .incl_right b)) (pushout_ind A B C f g W P d (W .incl_right b)) (d .snd .fst b)
  ≔ pushout_ind_beta A B C f g W P d .snd .fst (refl b)

{` Cocones under the span with vertex T (the nondependent boundary data). `}
def PushoutCocone (A B C : Type) (f : C → A) (g : C → B) (T : Type) : Type
  ≔ Σ (A → T) (l ↦ Σ (B → T) (r ↦ (c : C) → Id T (l (f c)) (r (g c))))

def pushout_cocone (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (h : W .carrier → T) : PushoutCocone A B C f g T
  ≔ (a ↦ h (W .incl_left a), (b ↦ h (W .incl_right b), c ↦ refl h (W .glue c)))

def pushout_rec (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (d : PushoutCocone A B C f g T) : W .carrier → T
  ≔ W .induction (_ ↦ T) d .fst

def pushout_rec_beta (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (d : PushoutCocone A B C f g T)
  : Id (PushoutCocone A B C f g T) (pushout_cocone A B C f g W T (pushout_rec A B C f g W T d)) d
  ≔ W .induction (_ ↦ T) d .snd

def pushout_rec_left (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (d : PushoutCocone A B C f g T) (a : A)
  : Id T (pushout_rec A B C f g W T d (W .incl_left a)) (d .fst a)
  ≔ pushout_rec_beta A B C f g W T d .fst (refl a)

def pushout_rec_right (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (d : PushoutCocone A B C f g T) (b : B)
  : Id T (pushout_rec A B C f g W T d (W .incl_right b)) (d .snd .fst b)
  ≔ pushout_rec_beta A B C f g W T d .snd .fst (refl b)

{` Uniqueness: maps with identified cocones are identified.  The glue
   component of the cocone identification is a square, transposed to give
   the path datum of the family x ↦ (h x = k x). `}
def pushout_maps_equal (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (h k : W .carrier → T)
  (e : Id (PushoutCocone A B C f g T) (pushout_cocone A B C f g W T h) (pushout_cocone A B C f g W T k))
  : Id (W .carrier → T) h k
  ≔ funext (W .carrier) (_ ↦ T) h k
      (W .induction (x ↦ Id T (h x) (k x))
        (a ↦ e .fst (refl a), (b ↦ e .snd .fst (refl b), c ↦ sym (e .snd .snd (refl c)))) .fst)

def pushout_rec_eta (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) (h : W .carrier → T)
  : Id (W .carrier → T) (pushout_rec A B C f g W T (pushout_cocone A B C f g W T h)) h
  ≔ pushout_maps_equal A B C f g W T (pushout_rec A B C f g W T (pushout_cocone A B C f g W T h)) h
      (pushout_rec_beta A B C f g W T (pushout_cocone A B C f g W T h))

{` The universal property of the pushout: evaluation on the constructors
   is an equivalence (W → T) ≃ cocones, for every type T. `}
def pushout_universal_property (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (T : Type) : Equiv (W .carrier → T) (PushoutCocone A B C f g T)
  ≔ quasi_inverse_equiv (W .carrier → T) (PushoutCocone A B C f g T)
      (pushout_cocone A B C f g W T) (pushout_rec A B C f g W T)
      (pushout_rec_eta A B C f g W T) (pushout_rec_beta A B C f g W T)

{` Dependent uniqueness and the dependent universal property. `}
def pushout_sections_equal (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (h k : (x : W .carrier) → P x)
  (e : Id (pushout_boundary A B C f g W P) (pushout_eval A B C f g W P h) (pushout_eval A B C f g W P k))
  : Id ((x : W .carrier) → P x) h k
  ≔ funext (W .carrier) P h k
      (W .induction (x ↦ Id (P x) (h x) (k x))
        (a ↦ e .fst (refl a), (b ↦ e .snd .fst (refl b), c ↦ sym (e .snd .snd (refl c)))) .fst)

def pushout_ind_eta (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (h : (x : W .carrier) → P x)
  : Id ((x : W .carrier) → P x) (pushout_ind A B C f g W P (pushout_eval A B C f g W P h)) h
  ≔ pushout_sections_equal A B C f g W P (pushout_ind A B C f g W P (pushout_eval A B C f g W P h)) h
      (pushout_ind_beta A B C f g W P (pushout_eval A B C f g W P h))

def pushout_dependent_universal_property (A B C : Type) (f : C → A) (g : C → B)
  (W : PushoutSignature A B C f g) (P : W .carrier → Type)
  : Equiv ((x : W .carrier) → P x) (pushout_boundary A B C f g W P)
  ≔ quasi_inverse_equiv ((x : W .carrier) → P x) (pushout_boundary A B C f g W P)
      (pushout_eval A B C f g W P) (pushout_ind A B C f g W P)
      (pushout_ind_eta A B C f g W P) (pushout_ind_beta A B C f g W P)

{` Induction into families of propositions needs only the point data. `}
def pushout_ind_prop (A B C : Type) (f : C → A) (g : C → B) (W : PushoutSignature A B C f g)
  (P : W .carrier → Type) (hP : (x : W .carrier) → isProp (P x))
  (l : (a : A) → P (W .incl_left a)) (r : (b : B) → P (W .incl_right b))
  : (x : W .carrier) → P x
  ≔ W .induction P
      (l, (r, c ↦ pathover_of_eq (W .carrier) P (W .incl_left (f c)) (W .incl_right (g c)) (W .glue c)
        (l (f c)) (r (g c))
        (hP (W .incl_right (g c))
          (transport (W .carrier) P (W .incl_left (f c)) (W .incl_right (g c)) (W .glue c) (l (f c)))
          (r (g c))))) .fst
