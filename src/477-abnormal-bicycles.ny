export "476-dihedral-frieze"
export "406-symmetric-group-three"

{` The "abnormal" bicycles of fig:abnormal-bicycle and
   fig:somewhat-abnormal-bicycle (group.tex 2019–2061), read off the TikZ
   code: nodes n1, n2, ... are 0, 1, ... of Fin n (k = inl^k(inr ⋆)), red
   arrows are a, blue arrows (including loops) are b.

   fig:abnormal-bicycle (3 nodes): a = (0 1 2), b fixes 0 and swaps 1, 2.
   Its only symmetry is the identity (and it is not normal).
   fig:somewhat-abnormal-bicycle (4 nodes): a = (0 1 2 3), b swaps 0, 2 and
   fixes 1, 3. It has exactly two symmetries: the identity and a². `}

{` fig:abnormal-bicycle. `}
def abnormal_a_map : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_a_inverse_map : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_a_equiv_retraction (x : Fin three)
  : Id (Fin three) (abnormal_a_inverse_map (abnormal_a_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_a_equiv_section (x : Fin three)
  : Id (Fin three) (abnormal_a_map (abnormal_a_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_a_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) abnormal_a_map abnormal_a_inverse_map abnormal_a_equiv_retraction abnormal_a_equiv_section

def abnormal_b_map : Fin three → Fin three ≔ [
  | inr. u ↦ inr. u
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_b_equiv_retraction (x : Fin three)
  : Id (Fin three) (abnormal_b_map (abnormal_b_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_b_equiv_section (x : Fin three)
  : Id (Fin three) (abnormal_b_map (abnormal_b_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_b_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) abnormal_b_map abnormal_b_map abnormal_b_equiv_retraction abnormal_b_equiv_section

def abnormal_word_from_zero (y : Fin three)
  : BicycleWordFrom (Fin three) abnormal_a_equiv abnormal_b_equiv (inr. star.) y
  ≔ match y [
  | inr. star. ↦ (nil., refl (inr. star. : Fin three))
  | inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (inl. (inr. star.) : Fin three))
  | inl. (inl. (inr. star.)) ↦ (cons. (inl. (pos. (suc. (suc. zero.)))) nil., refl (inl. (inl. (inr. star.)) : Fin three))
  | inl. (inl. (inl. e)) ↦ match e [] ]

def abnormal_bicycle : Bicycles
  ≔ mkbicycle (Fin three, fin_set three) abnormal_a_equiv abnormal_b_equiv
      (bicycle_connected_from_point (Fin three) abnormal_a_equiv abnormal_b_equiv (inr. star.)
        (y ↦ mere (BicycleWordFrom (Fin three) abnormal_a_equiv abnormal_b_equiv (inr. star.) y) (abnormal_word_from_zero y)))

{` The only fixed point of b is 0. `}
def abnormal_b_fixed (y : Fin three) : Id (Fin three) y (abnormal_b_map y) → Id (Fin three) y (inr. star.)
  ≔ match y [
  | inr. star. ↦ _ ↦ refl (inr. star. : Fin three)
  | inl. (inr. star.) ↦ h ↦ absurd (Id (Fin three) (inl. (inr. star.)) (inr. star.))
      (transport (Fin three) fin3_two_code (inl. (inl. (inr. star.))) (inl. (inr. star.))
        (inverse (Fin three) (inl. (inr. star.)) (inl. (inl. (inr. star.))) h) star.)
  | inl. (inl. (inr. star.)) ↦ h ↦ absurd (Id (Fin three) (inl. (inl. (inr. star.))) (inr. star.))
      (transport (Fin three) fin3_two_code (inl. (inl. (inr. star.))) (inl. (inr. star.)) h star.)
  | inl. (inl. (inl. e)) ↦ match e [] ]

{` Every symmetry fixes 0 (it commutes with b), hence is the identity by
   lem:evisinj-bicycle. `}
def abnormal_symmetry_fixes_zero (p : Id Bicycles abnormal_bicycle abnormal_bicycle)
  : Id (Fin three) (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle p (inr. star.)) (inr. star.)
  ≔ abnormal_b_fixed (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle p (inr. star.))
      (bicycle_paths_equiv abnormal_bicycle abnormal_bicycle .map p .snd .snd (inr. star.))

def abnormal_symmetry_trivial (p : Id Bicycles abnormal_bicycle abnormal_bicycle)
  : Id (Id Bicycles abnormal_bicycle abnormal_bicycle) p (refl abnormal_bicycle)
  ≔ bicycle_evaluation_path_reflecting abnormal_bicycle abnormal_bicycle (inr. star.) p (refl abnormal_bicycle)
      (concat (Fin three) (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle p (inr. star.)) (inr. star.)
        (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle (refl abnormal_bicycle) (inr. star.))
        (abnormal_symmetry_fixes_zero p)
        (inverse (Fin three) (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle (refl abnormal_bicycle) (inr. star.)) (inr. star.)
          (bicycle_path_evaluate_refl abnormal_bicycle (inr. star.))))

{` "only the identity symmetry": the type of symmetries is contractible,
   so Aut_Bicyc of it is a trivial group. `}
def abnormal_bicycle_only_identity : BookIsContr (Id Bicycles abnormal_bicycle abnormal_bicycle)
  ≔ (refl abnormal_bicycle, p ↦ inverse (Id Bicycles abnormal_bicycle abnormal_bicycle) p (refl abnormal_bicycle)
      (abnormal_symmetry_trivial p))

def abnormal_bicycle_group_trivial : BookIsContr (USym (bicycle_automorphism_group abnormal_bicycle))
  ≔ book_contractibility_equiv (Id Bicycles abnormal_bicycle abnormal_bicycle) (USym (bicycle_automorphism_group abnormal_bicycle))
      (canonical_inverse_equiv (USym (bicycle_automorphism_group abnormal_bicycle)) (Id Bicycles abnormal_bicycle abnormal_bicycle)
        (automorphism_group_usym_equiv Bicycles bicycles_groupoid abnormal_bicycle))
      .map abnormal_bicycle_only_identity

def abnormal_zero_code : Fin three → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

{` Litmus: it is not normal (no symmetry sends 0 to 1). `}
def abnormal_bicycle_not_normal (h : IsNormalBicycle abnormal_bicycle) : Empty
  ≔ let p ≔ h (inr. star.) (inl. (inr. star.)) .center in
    transport (Fin three) abnormal_zero_code (inr. star.) (inl. (inr. star.))
      (inverse (Fin three) (inl. (inr. star.)) (inr. star.)
        (concat (Fin three) (inl. (inr. star.)) (bicycle_path_evaluate abnormal_bicycle abnormal_bicycle (p .fst) (inr. star.)) (inr. star.)
          (p .snd) (abnormal_symmetry_fixes_zero (p .fst)))) star.

{` fig:somewhat-abnormal-bicycle. `}
def bicycle_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))

def somewhat_abnormal_a_map : Fin bicycle_four → Fin bicycle_four ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inr. u
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_a_inverse_map : Fin bicycle_four → Fin bicycle_four ≔ [
  | inr. u ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_a_equiv_retraction (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_a_inverse_map (somewhat_abnormal_a_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_a_equiv_section (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_a_map (somewhat_abnormal_a_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_a_equiv : Equiv (Fin bicycle_four) (Fin bicycle_four)
  ≔ quasi_inverse_equiv (Fin bicycle_four) (Fin bicycle_four) somewhat_abnormal_a_map somewhat_abnormal_a_inverse_map somewhat_abnormal_a_equiv_retraction somewhat_abnormal_a_equiv_section

def somewhat_abnormal_b_map : Fin bicycle_four → Fin bicycle_four ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inl. (inr. u)
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_b_equiv_retraction (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_b_map (somewhat_abnormal_b_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_b_equiv_section (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_b_map (somewhat_abnormal_b_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_b_equiv : Equiv (Fin bicycle_four) (Fin bicycle_four)
  ≔ quasi_inverse_equiv (Fin bicycle_four) (Fin bicycle_four) somewhat_abnormal_b_map somewhat_abnormal_b_map somewhat_abnormal_b_equiv_retraction somewhat_abnormal_b_equiv_section

def somewhat_abnormal_word_from_zero (y : Fin bicycle_four)
  : BicycleWordFrom (Fin bicycle_four) somewhat_abnormal_a_equiv somewhat_abnormal_b_equiv (inr. star.) y
  ≔ match y [
  | inr. star. ↦ (nil., refl (inr. star. : Fin bicycle_four))
  | inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (inl. (inr. star.) : Fin bicycle_four))
  | inl. (inl. (inr. star.)) ↦ (cons. (inl. (pos. (suc. (suc. zero.)))) nil., refl (inl. (inl. (inr. star.)) : Fin bicycle_four))
  | inl. (inl. (inl. (inr. star.))) ↦ (cons. (inl. (pos. (suc. (suc. (suc. zero.))))) nil., refl (inl. (inl. (inl. (inr. star.))) : Fin bicycle_four))
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_bicycle : Bicycles
  ≔ mkbicycle (Fin bicycle_four, fin_set bicycle_four) somewhat_abnormal_a_equiv somewhat_abnormal_b_equiv
      (bicycle_connected_from_point (Fin bicycle_four) somewhat_abnormal_a_equiv somewhat_abnormal_b_equiv (inr. star.)
        (y ↦ mere (BicycleWordFrom (Fin bicycle_four) somewhat_abnormal_a_equiv somewhat_abnormal_b_equiv (inr. star.) y)
          (somewhat_abnormal_word_from_zero y)))

{` The nontrivial symmetry a² : k ↦ k + 2. `}
def somewhat_abnormal_half_turn_map : Fin bicycle_four → Fin bicycle_four ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_half_turn_equiv_retraction (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_half_turn_map (somewhat_abnormal_half_turn_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_half_turn_equiv_section (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_half_turn_map (somewhat_abnormal_half_turn_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_half_turn_equiv : Equiv (Fin bicycle_four) (Fin bicycle_four)
  ≔ quasi_inverse_equiv (Fin bicycle_four) (Fin bicycle_four) somewhat_abnormal_half_turn_map somewhat_abnormal_half_turn_map somewhat_abnormal_half_turn_equiv_retraction somewhat_abnormal_half_turn_equiv_section

def somewhat_abnormal_half_turn_commutes_a (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_half_turn_map (somewhat_abnormal_a_map x)) (somewhat_abnormal_a_map (somewhat_abnormal_half_turn_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_half_turn_commutes_b (x : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_half_turn_map (somewhat_abnormal_b_map x)) (somewhat_abnormal_b_map (somewhat_abnormal_half_turn_map x))
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_four)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_four)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_four)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inr. u) : Fin bicycle_four)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_half_turn : Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle
  ≔ bicycle_path_from_iso somewhat_abnormal_bicycle somewhat_abnormal_bicycle
      (somewhat_abnormal_half_turn_equiv, (somewhat_abnormal_half_turn_commutes_a, somewhat_abnormal_half_turn_commutes_b))

{` A symmetry sends 0 to 0 or 2: e(1) is a fixed point of b (1 or 3), and
   e(1) = a(e(0)). `}
def somewhat_abnormal_two_code : Fin bicycle_four → Type ≔ [
  | inr. _ ↦ Empty
  | inl. (inr. _) ↦ Empty
  | inl. (inl. (inr. _)) ↦ Unit
  | inl. (inl. (inl. (inr. _))) ↦ Empty
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_value_cases (y : Fin bicycle_four)
  : Id (Fin bicycle_four) (somewhat_abnormal_a_map y) (somewhat_abnormal_b_map (somewhat_abnormal_a_map y))
    → Sum (Id (Fin bicycle_four) y (inr. star.)) (Id (Fin bicycle_four) y (inl. (inl. (inr. star.))))
  ≔ match y [
  | inr. star. ↦ _ ↦ inl. (refl (inr. star. : Fin bicycle_four))
  | inl. (inr. star.) ↦ h ↦ absurd (Sum (Id (Fin bicycle_four) (inl. (inr. star.)) (inr. star.)) (Id (Fin bicycle_four) (inl. (inr. star.)) (inl. (inl. (inr. star.)))))
      (transport (Fin bicycle_four) somewhat_abnormal_two_code (inl. (inl. (inr. star.))) (inr. star.) h star.)
  | inl. (inl. (inr. star.)) ↦ _ ↦ inr. (refl (inl. (inl. (inr. star.)) : Fin bicycle_four))
  | inl. (inl. (inl. (inr. star.))) ↦ h ↦ absurd (Sum (Id (Fin bicycle_four) (inl. (inl. (inl. (inr. star.)))) (inr. star.))
        (Id (Fin bicycle_four) (inl. (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.)))))
      (transport (Fin bicycle_four) somewhat_abnormal_two_code (inl. (inl. (inr. star.))) (inr. star.)
        (inverse (Fin bicycle_four) (inr. star.) (inl. (inl. (inr. star.))) h) star.)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_symmetry_value (p : Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle)
  : Sum (Id (Fin bicycle_four) (bicycle_path_evaluate somewhat_abnormal_bicycle somewhat_abnormal_bicycle p (inr. star.)) (inr. star.))
      (Id (Fin bicycle_four) (bicycle_path_evaluate somewhat_abnormal_bicycle somewhat_abnormal_bicycle p (inr. star.)) (inl. (inl. (inr. star.))))
  ≔ let e ≔ bicycle_paths_equiv somewhat_abnormal_bicycle somewhat_abnormal_bicycle .map p in
    let y ≔ e .fst .map (inr. star.) in
    somewhat_abnormal_value_cases y
      (calc somewhat_abnormal_a_map y
        = e .fst .map (inl. (inr. star.))
          by inverse (Fin bicycle_four) (e .fst .map (inl. (inr. star.))) (somewhat_abnormal_a_map y) (e .snd .fst (inr. star.))
        = somewhat_abnormal_b_map (e .fst .map (inl. (inr. star.))) by e .snd .snd (inl. (inr. star.))
        = somewhat_abnormal_b_map (somewhat_abnormal_a_map y)
          by refl somewhat_abnormal_b_map (e .snd .fst (inr. star.)) ∎)

{` "four elements, but only two symmetries": the symmetries are equivalent to Bool,
   false ↦ the identity, true ↦ the half turn a². `}
def somewhat_abnormal_is_two : Fin bicycle_four → Bool ≔ [
  | inr. _ ↦ false.
  | inl. (inr. _) ↦ false.
  | inl. (inl. (inr. _)) ↦ true.
  | inl. (inl. (inl. (inr. _))) ↦ false.
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def somewhat_abnormal_symmetry_of_bool : Bool → Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle
  ≔ [ false. ↦ refl somewhat_abnormal_bicycle | true. ↦ somewhat_abnormal_half_turn ]

def somewhat_abnormal_bool_of_symmetry (p : Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle) : Bool
  ≔ somewhat_abnormal_is_two (bicycle_path_evaluate somewhat_abnormal_bicycle somewhat_abnormal_bicycle p (inr. star.))

def somewhat_abnormal_bool_roundtrip (c : Bool)
  : Id Bool (somewhat_abnormal_bool_of_symmetry (somewhat_abnormal_symmetry_of_bool c)) c
  ≔ match c [
  | false. ↦ refl somewhat_abnormal_is_two (bicycle_path_evaluate_refl somewhat_abnormal_bicycle (inr. star.))
  | true. ↦ refl (true. : Bool) ]

def somewhat_abnormal_symmetry_roundtrip (p : Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle)
  : Id (Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle)
      (somewhat_abnormal_symmetry_of_bool (somewhat_abnormal_bool_of_symmetry p)) p
  ≔ let B ≔ somewhat_abnormal_bicycle in
    let ev ≔ (s ↦ bicycle_path_evaluate B B s (inr. star.)) : Id Bicycles B B → Fin bicycle_four in
    let F ≔ (z ↦ somewhat_abnormal_symmetry_of_bool (somewhat_abnormal_is_two z)) : Fin bicycle_four → Id Bicycles B B in
    match somewhat_abnormal_symmetry_value p [
    | inl. q ↦ concat (Id Bicycles B B) (F (ev p)) (refl B) p
        (refl F q)
        (bicycle_evaluation_path_reflecting B B (inr. star.) (refl B) p
          (concat (Fin bicycle_four) (ev (refl B)) (inr. star.) (ev p) (bicycle_path_evaluate_refl B (inr. star.))
            (inverse (Fin bicycle_four) (ev p) (inr. star.) q)))
    | inr. q ↦ concat (Id Bicycles B B) (F (ev p)) somewhat_abnormal_half_turn p
        (refl F q)
        (bicycle_evaluation_path_reflecting B B (inr. star.) somewhat_abnormal_half_turn p
          (inverse (Fin bicycle_four) (ev p) (inl. (inl. (inr. star.))) q)) ]

def somewhat_abnormal_symmetries_bool : Equiv (Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle) Bool
  ≔ quasi_inverse_equiv (Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle) Bool
      somewhat_abnormal_bool_of_symmetry somewhat_abnormal_symmetry_of_bool
      somewhat_abnormal_symmetry_roundtrip somewhat_abnormal_bool_roundtrip

{` Litmus: the two symmetries are different; Aut_Bicyc has two symmetries. `}
def somewhat_abnormal_true_code : Bool → Type ≔ [ true. ↦ Unit | false. ↦ Empty ]

def somewhat_abnormal_half_turn_nontrivial
  (h : Id (Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle) somewhat_abnormal_half_turn (refl somewhat_abnormal_bicycle))
  : Empty
  ≔ transport Bool somewhat_abnormal_true_code true. false.
      (concat Bool true. (somewhat_abnormal_bool_of_symmetry (refl somewhat_abnormal_bicycle)) false.
        (refl somewhat_abnormal_bool_of_symmetry h) (somewhat_abnormal_bool_roundtrip false.))
      star.

def somewhat_abnormal_group_usym_bool : Equiv (USym (bicycle_automorphism_group somewhat_abnormal_bicycle)) Bool
  ≔ compose_equiv (USym (bicycle_automorphism_group somewhat_abnormal_bicycle))
      (Id Bicycles somewhat_abnormal_bicycle somewhat_abnormal_bicycle) Bool
      (automorphism_group_usym_equiv Bicycles bicycles_groupoid somewhat_abnormal_bicycle)
      somewhat_abnormal_symmetries_bool
