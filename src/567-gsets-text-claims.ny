export "505-gset-core-litmus"

{` Chapter 5 (actions.tex), running text of sec:gsets: "the loop is a
   non-trivial transformation of the base point" (for every circle C). The
   other claims of this part of the text are mapped to declarations of the
   chapter-5 modules and of chapters 3–4 (see the claims file). `}

def gsets_int_zero_code : Int → Type ≔ [ pos. n ↦ match n [ zero. ↦ Unit | suc. _ ↦ Empty ] | neg. _ ↦ Empty ]

{` loop ≠ refl_base: its winding number is 1, that of refl is 0. `}
def gsets_circle_loop_nontrivial (C : CircleSignature)
  (h : Id (Id (C .carrier) (C .base) (C .base)) (C .loop) (refl (C .base))) : Empty
  ≔ let A ≔ C .carrier in
    let b ≔ C .base in
    let one : Int ≔ pos. (suc. zero.) in
    let e : Id Int one int_zero
      ≔ calc
          one
          = circle_winding C (loop_power A b (C .loop) one)
            by inverse Int (circle_winding C (loop_power A b (C .loop) one)) one (circle_winding_power C one)
          = circle_winding C (C .loop)
            by refl (circle_winding C) (concat_1p A b b (C .loop))
          = circle_winding C (refl b) by refl (circle_winding C) h
          = int_zero by circle_winding_power C int_zero ∎ in
    transport Int gsets_int_zero_code int_zero one (inverse Int one int_zero e) star.
