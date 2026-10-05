export "1704-sets-cover"

{` xca "we cannot relax the requirement that X is a set": S¹-AC(2) is false.
   The circle is any CircleSignature (instantiated at the constructed circle
   in module 1759). The counterexample is the swapping double cover of
   module 120: a family of 2-element sets over S¹ whose monodromy is the
   swap, which has no fixed point; a section would give one. `}
def FixedPointOf (p : Permutations) : Type ≔ Σ (p .fst .fst) (x ↦ Id (p .fst .fst) (p .snd .map x) x)

def bool_swap_no_fixed_point (f : FixedPointOf boolean_swap_permutation) : Empty
  ≔ bool_not_no_fixed_point (f .fst) (f .snd)

def circle_section_fixed_point (C : CircleSignature) (F : C .carrier → SetTypes)
  (s : (z : C .carrier) → F z .fst) : FixedPointOf (circle_setfamilies_permutations C .map F)
  ≔ (s (C .base),
      pathover_transport_equiv (C .carrier) (z ↦ F z .fst) (C .base) (C .base) (C .loop) (s (C .base)) (s (C .base))
        .map (refl s (C .loop)))

{` A family of sets over S¹ with a section has a monodromy with a fixed point;
   the swapping family has none, so it has no section. `}
def swapping_family_no_section (C : CircleSignature)
  (s : (z : C .carrier) → swapping_boolean_circle_family C z .fst) : Empty
  ≔ bool_swap_no_fixed_point
      (transport Permutations FixedPointOf
        (circle_setfamilies_permutations C .map (swapping_boolean_circle_family C)) boolean_swap_permutation
        (swapping_boolean_circle_monodromy C)
        (circle_section_fixed_point C (swapping_boolean_circle_family C) s))

{` The fibers of the swapping family are 2-element sets. `}
def swapping_family_base_bool (C : CircleSignature)
  : Id Type (swapping_boolean_circle_family C (C .base) .fst) Bool
  ≔ circle_rec_beta C SetTypes (boolean_set, boolean_set_swap) .fst .fst

def swapping_family_two_element (C : CircleSignature) (z : C .carrier)
  : Mere (Id Type (Fin two) (swapping_boolean_circle_family C z .fst))
  ≔ circle_ind_prop C (z ↦ Mere (Id Type (Fin two) (swapping_boolean_circle_family C z .fst)))
      (z ↦ mere_isprop (Id Type (Fin two) (swapping_boolean_circle_family C z .fst)))
      (mere (Id Type (Fin two) (swapping_boolean_circle_family C (C .base) .fst))
        (concat Type (Fin two) Bool (swapping_boolean_circle_family C (C .base) .fst) fin_two_path
          (inverse Type (swapping_boolean_circle_family C (C .base) .fst) Bool (swapping_family_base_bool C))))
      z

def swapping_two_sets_family (C : CircleSignature) : C .carrier → FiniteSetsAt two
  ≔ z ↦ (swapping_boolean_circle_family C z, swapping_family_two_element C z)

def two_sets_inhabited (S : FiniteSetsAt two) : Mere (S .fst .fst)
  ≔ trunc_map native_truncation (Id Type (Fin two) (S .fst .fst)) (S .fst .fst)
      (p ↦ transport Type (T ↦ T) (Fin two) (S .fst .fst) p (inr. star.)) (S .snd)

def circle_local_choice_two_false (C : CircleSignature) (lac : LocalChoiceOfSize (C .carrier) two) : Empty
  ≔ mere_rec ((z : C .carrier) → swapping_boolean_circle_family C z .fst) Empty empty_prop
      (swapping_family_no_section C)
      (lac (swapping_two_sets_family C) (z ↦ two_sets_inhabited (swapping_two_sets_family C z)))

{` Hence choice for families of 2-element sets cannot hold over every type,
   and neither can X-AC or X-AC_∞ for X = S¹. `}
def circle_local_choice_false (C : CircleSignature) (lac : LocalChoice (C .carrier)) : Empty
  ≔ circle_local_choice_two_false C (local_choice_of_size (C .carrier) lac two)

def circle_untruncated_local_choice_false (C : CircleSignature) (lac : UntruncatedLocalChoice (C .carrier)) : Empty
  ≔ circle_local_choice_false C (untruncated_local_choice_restrict (C .carrier) lac)

{` Litmus: the constant family Bool over the same circle does have a section. `}
def constant_bool_circle_section (C : CircleSignature) : (z : C .carrier) → constant_boolean_circle_family C z .fst
  ≔ _ ↦ false.
