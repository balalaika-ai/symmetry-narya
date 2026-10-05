export "05-circle-interface"
export "08-quasi-inverses"

{` lem:freeloopspace. Relative to the book's circle induction signature,
   evaluation has contractible fibers, using the chapter-2 definition. `}
def circle_universal_property (C : CircleSignature) (A : Type)
  : Equiv (C .carrier → A) (FreeLoop A)
  ≔ quasi_inverse_equiv (C .carrier → A) (FreeLoop A)
      (circle_eval C A) (circle_rec C A)
      (circle_rec_eta C A) (circle_rec_beta C A)
