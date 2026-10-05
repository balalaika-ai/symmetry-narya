export "127-symmetries-of-circle"

def circle_sections_equal (C : CircleSignature) (P : C .carrier → Type)
  (f g : (x : C .carrier) → P x)
  (d : Id (CircleBoundary (C .carrier) (C .base) (C .loop) P)
    (circle_evaluate (C .carrier) (C .base) (C .loop) P f)
    (circle_evaluate (C .carrier) (C .base) (C .loop) P g))
  : Id ((x : C .carrier) → P x) f g
  ≔ funext (C .carrier) P f g
      (C .induction (x ↦ Id (P x) (f x) (g x)) (d .fst, sym (d .snd)) .fst)

def circle_dependent_rec (C : CircleSignature) (P : C .carrier → Type)
  (d : CircleBoundary (C .carrier) (C .base) (C .loop) P)
  : (x : C .carrier) → P x
  ≔ C .induction P d .fst

def circle_dependent_rec_eta (C : CircleSignature) (P : C .carrier → Type)
  (f : (x : C .carrier) → P x)
  : Id ((x : C .carrier) → P x)
      (circle_dependent_rec C P (circle_evaluate (C .carrier) (C .base) (C .loop) P f)) f
  ≔ circle_sections_equal C P
      (circle_dependent_rec C P (circle_evaluate (C .carrier) (C .base) (C .loop) P f)) f
      (C .induction P (circle_evaluate (C .carrier) (C .base) (C .loop) P f) .snd)

{` rem:dep-univ-prop-circle. The forward map is dependent evaluation,
   and both inverse laws include the whole boundary square. No set or
   groupoid restriction is placed on the family. `}
def circle_dependent_universal_property (C : CircleSignature) (P : C .carrier → Type)
  : Equiv ((x : C .carrier) → P x) (CircleBoundary (C .carrier) (C .base) (C .loop) P)
  ≔ quasi_inverse_equiv ((x : C .carrier) → P x) (CircleBoundary (C .carrier) (C .base) (C .loop) P)
      (circle_evaluate (C .carrier) (C .base) (C .loop) P) (circle_dependent_rec C P)
      (circle_dependent_rec_eta C P) (d ↦ C .induction P d .snd)
