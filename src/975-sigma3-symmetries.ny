export "972-sigma3-subgroup-orbits"
export "954-abstract-kernel"
export "961-composite-fibers-mod-example"
export "434-permutation-hom-litmus"

{` Chapter 9 (subgroups.tex), xca:Sub(Sigma3) (line 1311), tools for the
   classification of subgroups of Σ_3 (module 976): the six symmetries of
   Σ_3 named by a data type (Sigma3Name), every symmetry is one of them
   (sigma3_enum, by its action on Fin 3), the products needed, the
   memberships of the six symmetries in 1, A_3, Σ_3 and T_0, T_1, T_2, and
   "subgroups of Σ_3 with the same named symmetries are equal"
   (sigma3_same_members, through subgroup_le_antisym of module 1030). `}

{` The 3-cycles (0 1 2) and (0 2 1) of Fin 3. `}
def fin3_rot : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_rot_inv : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_rot_retraction (x : Fin three) : Id (Fin three) (fin3_rot_inv (fin3_rot x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_rot_section (x : Fin three) : Id (Fin three) (fin3_rot (fin3_rot_inv x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_rot_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) fin3_rot fin3_rot_inv fin3_rot_retraction fin3_rot_section

def fin3_rot_inv_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) fin3_rot_inv fin3_rot fin3_rot_section fin3_rot_retraction

{` Names of the six symmetries: e, (0 1), (0 2), (1 2), (0 1 2), (0 2 1). `}
def Sigma3Name : Type ≔ data [ ide. | t01. | t02. | t12. | cyc. | cin. ]

def sigma3_sym : Sigma3Name → USym (symmetric_group three) ≔ [
  | ide. ↦ permutation_symmetry (standard_set three) (identity_equiv (Fin three))
  | t01. ↦ permutation_symmetry (standard_set three) (fin3_swap01_equiv)
  | t02. ↦ permutation_symmetry (standard_set three) (fin3_swap02_equiv)
  | t12. ↦ permutation_symmetry (standard_set three) (fin3_swap12_equiv)
  | cyc. ↦ permutation_symmetry (standard_set three) (fin3_rot_equiv)
  | cin. ↦ permutation_symmetry (standard_set three) (fin3_rot_inv_equiv)
  ]

def sigma3_act (g : USym (symmetric_group three)) (i : Fin three) : Fin three
  ≔ gset_usym_act (symmetric_group three) (standard_symmetric_gset three) g i

{` Symmetries of Σ_3 with the same action on Fin 3 are equal. `}
def sigma3_ext (g h : USym (symmetric_group three)) (H : (i : Fin three) → Id (Fin three) (sigma3_act g i) (sigma3_act h i))
  : Id (USym (symmetric_group three)) g h
  ≔ permutation_symmetry_ext (standard_set three) g h H

def sigma3_mul_ext (g h k : USym (symmetric_group three))
  (H : (i : Fin three) → Id (Fin three) (sigma3_act g (sigma3_act h i)) (sigma3_act k i))
  : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) g h) k
  ≔ let G ≔ symmetric_group three in
    let s ≔ shape G in
    sigma3_ext (usym_mul G g h) k
      (i ↦ concat (Fin three) (sigma3_act (usym_mul G g h) i) (sigma3_act g (sigma3_act h i)) (sigma3_act k i)
        (gset_act_concat G (standard_symmetric_gset three) s s s h g i) (H i))

def sigma3_unit_named : Id (USym (symmetric_group three)) (usym_unit (symmetric_group three)) (sigma3_sym ide.)
  ≔ let G ≔ symmetric_group three in
    sigma3_ext (usym_unit G) (sigma3_sym ide.) (i ↦ gset_act_refl G (standard_symmetric_gset three) (shape G) i)

{` Every symmetry of Σ_3 is one of the six named ones (case analysis on
   its values at 0, 1, 2; repeated values contradict injectivity). `}
def sigma3_enum_values (g : USym (symmetric_group three)) (a b c : Fin three)
  : Id (Fin three) (sigma3_act g fin3_zero) a → Id (Fin three) (sigma3_act g fin3_one) b → Id (Fin three) (sigma3_act g fin3_two) c
    → Σ Sigma3Name (n ↦ Id (USym (symmetric_group three)) g (sigma3_sym n))
  ≔ match a [
  | inr. star. ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inr. star. : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inr. star. : Fin three) eb))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inr. star. : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inr. star. : Fin three) eb))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inr. star. : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inr. star. : Fin three) eb))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inr. star. : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inr. star. : Fin three) ec))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inr. star.) : Fin three) ec))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ (ide., sigma3_ext g (sigma3_sym ide.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inr. star. : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inr. star. : Fin three) ec))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ (t12., sigma3_ext g (sigma3_sym t12.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inl. (inr. star.)) : Fin three) ec))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inl. v)) ↦ match v [] ]
  | inl. (inr. star.) ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inr. star. : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inr. star. : Fin three) ec))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inr. star.) : Fin three) ec))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ (t01., sigma3_ext g (sigma3_sym t01.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inr. star.) : Fin three) eb))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inr. star.) : Fin three) eb))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inr. star.) : Fin three) eb))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ (cyc., sigma3_ext g (sigma3_sym cyc.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inr. star.) : Fin three) ec))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inl. (inr. star.)) : Fin three) ec))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inl. v)) ↦ match v [] ]
  | inl. (inl. (inr. star.)) ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inr. star. : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inr. star. : Fin three) ec))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ (cin., sigma3_ext g (sigma3_sym cin.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inl. (inr. star.)) : Fin three) ec))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ (t02., sigma3_ext g (sigma3_sym t02.) (i ↦ match i [ | inr. star. ↦ ea | inl. (inr. star.) ↦ eb | inl. (inl. (inr. star.)) ↦ ec | inl. (inl. (inl. v)) ↦ match v [] ]))
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_one fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_one fin3_two (concat (Fin three) (sigma3_act g fin3_one) (inl. (inr. star.) : Fin three) (sigma3_act g fin3_two) eb (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inr. star.) : Fin three) ec))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_two (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_two (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_two) ea (inverse (Fin three) (sigma3_act g fin3_two) (inl. (inl. (inr. star.)) : Fin three) ec))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inl. (inr. star.)) : Fin three) eb))) []
      | inl. (inr. star.) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inl. (inr. star.)) : Fin three) eb))) []
      | inl. (inl. (inr. star.)) ↦ ea eb ec ↦ match fin3_differ fin3_zero fin3_one (refl (false. : Bool)) (gset_usym_act_cancel (symmetric_group three) (standard_symmetric_gset three) g fin3_zero fin3_one (concat (Fin three) (sigma3_act g fin3_zero) (inl. (inl. (inr. star.)) : Fin three) (sigma3_act g fin3_one) ea (inverse (Fin three) (sigma3_act g fin3_one) (inl. (inl. (inr. star.)) : Fin three) eb))) []
      | inl. (inl. (inl. v)) ↦ match v [] ]
    | inl. (inl. (inl. v)) ↦ match v [] ]
  | inl. (inl. (inl. v)) ↦ match v [] ]

def sigma3_enum (g : USym (symmetric_group three)) : Σ Sigma3Name (n ↦ Id (USym (symmetric_group three)) g (sigma3_sym n))
  ≔ sigma3_enum_values g (sigma3_act g fin3_zero) (sigma3_act g fin3_one) (sigma3_act g fin3_two)
      (refl (sigma3_act g fin3_zero)) (refl (sigma3_act g fin3_one)) (refl (sigma3_act g fin3_two))

{` The products used in the classification. `}
def sigma3_prod_cyc_cyc : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym cyc.) (sigma3_sym cyc.)) (sigma3_sym cin.)
  ≔ sigma3_mul_ext (sigma3_sym cyc.) (sigma3_sym cyc.) (sigma3_sym cin.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inr. star.) ↦ refl (inr. star. : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inl. (inr. star.) : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_cin_cin : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym cin.) (sigma3_sym cin.)) (sigma3_sym cyc.)
  ≔ sigma3_mul_ext (sigma3_sym cin.) (sigma3_sym cin.) (sigma3_sym cyc.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inr. star.) : Fin three) | inl. (inr. star.) ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inr. star. : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t01_t02 : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t01.) (sigma3_sym t02.)) (sigma3_sym cin.)
  ≔ sigma3_mul_ext (sigma3_sym t01.) (sigma3_sym t02.) (sigma3_sym cin.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inr. star.) ↦ refl (inr. star. : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inl. (inr. star.) : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t01_t12 : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t01.) (sigma3_sym t12.)) (sigma3_sym cyc.)
  ≔ sigma3_mul_ext (sigma3_sym t01.) (sigma3_sym t12.) (sigma3_sym cyc.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inr. star.) : Fin three) | inl. (inr. star.) ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inr. star. : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t02_t12 : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t02.) (sigma3_sym t12.)) (sigma3_sym cin.)
  ≔ sigma3_mul_ext (sigma3_sym t02.) (sigma3_sym t12.) (sigma3_sym cin.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inr. star.) ↦ refl (inr. star. : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inl. (inr. star.) : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t01_cyc : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t01.) (sigma3_sym cyc.)) (sigma3_sym t12.)
  ≔ sigma3_mul_ext (sigma3_sym t01.) (sigma3_sym cyc.) (sigma3_sym t12.) (i ↦ match i [ | inr. star. ↦ refl (inr. star. : Fin three) | inl. (inr. star.) ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inl. (inr. star.) : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t02_cyc : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t02.) (sigma3_sym cyc.)) (sigma3_sym t01.)
  ≔ sigma3_mul_ext (sigma3_sym t02.) (sigma3_sym cyc.) (sigma3_sym t01.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inr. star.) : Fin three) | inl. (inr. star.) ↦ refl (inr. star. : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

def sigma3_prod_t12_cyc : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t12.) (sigma3_sym cyc.)) (sigma3_sym t02.)
  ≔ sigma3_mul_ext (sigma3_sym t12.) (sigma3_sym cyc.) (sigma3_sym t02.) (i ↦ match i [ | inr. star. ↦ refl (inl. (inl. (inr. star.)) : Fin three) | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Fin three) | inl. (inl. (inr. star.)) ↦ refl (inr. star. : Fin three) | inl. (inl. (inl. v)) ↦ match v [] ])

{` Membership of the named symmetries in a subgroup S of Σ_3. `}
def Sigma3Mem (S : Subgroups (symmetric_group three)) (n : Sigma3Name) : Type
  ≔ SubgroupHasSymmetry (symmetric_group three) S (sigma3_sym n)

{` The symmetries of a subgroup are closed under multiplication. `}
def subgroup_symmetry_mul (G : Group) (S : Subgroups G) (k k' : USym G) (r : SubgroupHasSymmetry G S k)
  (r' : SubgroupHasSymmetry G S k') : SubgroupHasSymmetry G S (usym_mul G k k')
  ≔ let X ≔ S .gset in
    let x ≔ S .point in
    let s ≔ shape G in
    calc
      gset_usym_act G X (usym_mul G k k') x = gset_usym_act G X k (gset_usym_act G X k' x)
        by gset_act_concat G X s s s k' k x
      = gset_usym_act G X k x by refl (gset_usym_act G X k) r'
      = x by r ∎

def sigma3_mem_ide (S : Subgroups (symmetric_group three)) : Sigma3Mem S ide.
  ≔ let G ≔ symmetric_group three in
    transport (USym G) (SubgroupHasSymmetry G S) (usym_unit G) (sigma3_sym ide.) sigma3_unit_named
      (gset_act_refl G (S .gset) (shape G) (S .point))

def sigma3_mem_prod (S : Subgroups (symmetric_group three)) (x y z : Sigma3Name)
  (p : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym x) (sigma3_sym y)) (sigma3_sym z))
  (rx : Sigma3Mem S x) (ry : Sigma3Mem S y) : Sigma3Mem S z
  ≔ let G ≔ symmetric_group three in
    transport (USym G) (SubgroupHasSymmetry G S) (usym_mul G (sigma3_sym x) (sigma3_sym y)) (sigma3_sym z) p
      (subgroup_symmetry_mul G S (sigma3_sym x) (sigma3_sym y) rx ry)

{` A named symmetry moving some point is not the unit; hence it is not a
   symmetry of the trivial subgroup 1. `}
def sigma3_sym_ne_unit (n : Sigma3Name) (i : Fin three) (d : Not (Id (Fin three) (sigma3_act (sigma3_sym n) i) i))
  (e : Id (USym (symmetric_group three)) (sigma3_sym n) (usym_unit (symmetric_group three))) : Empty
  ≔ let G ≔ symmetric_group three in
    d (concat (Fin three) (sigma3_act (sigma3_sym n) i) (sigma3_act (usym_unit G) i) i
        (refl ((p ↦ sigma3_act p i) : USym G → Fin three) e)
        (gset_act_refl G (standard_symmetric_gset three) (shape G) i))

def sigma3_not_trivial_mem (n : Sigma3Name) (i : Fin three) (d : Not (Id (Fin three) (sigma3_act (sigma3_sym n) i) i))
  : Not (Sigma3Mem (principal_subgroup (symmetric_group three)) n)
  ≔ r ↦ sigma3_sym_ne_unit n i d (principal_subgroup_symmetry_unit (symmetric_group three) (sigma3_sym n) r)

{` Symmetries of A_3 = E(ker sgn): k is one iff sgn(k) = + (kernel_member_iff
   of module 954, through E(ker sgn) = (sgn^* P_{Σ_2}, sgn_pt)). `}
def sigma3_a3_kernel_path
  : Id (Subgroups (symmetric_group three)) (alternating_subgroup (suc. zero.))
      (kernel_gset (symmetric_group three) sign_sigma_two (sign_hom three),
       hom_point (symmetric_group three) sign_sigma_two (sign_hom three),
       kernel_gset_transitive (symmetric_group three) sign_sigma_two (sign_hom three) (sign_hom_connected (suc. zero.)))
  ≔ kernel_subgroup_path (symmetric_group three) sign_sigma_two (sign_hom three) (sign_hom_connected (suc. zero.))

def sigma3_a3_mem_of_plus (k : USym (symmetric_group three)) (e : Id Sign (sigma_two_sign (usgn three k)) plus.)
  : SubgroupHasSymmetry (symmetric_group three) (alternating_subgroup (suc. zero.)) k
  ≔ let G ≔ symmetric_group three in
    let A3 ≔ alternating_subgroup (suc. zero.) in
    let A3' : Subgroups G ≔ (kernel_gset G sign_sigma_two (sign_hom three), hom_point G sign_sigma_two (sign_hom three),
               kernel_gset_transitive G sign_sigma_two (sign_hom three) (sign_hom_connected (suc. zero.))) in
    subgroup_symmetry_transport G A3' A3 (inverse (Subgroups G) A3 A3' sigma3_a3_kernel_path) k
      (kernel_member_iff G sign_sigma_two (sign_hom three) k .snd (sigma_two_unit_of_plus (usgn three k) e))

def sigma3_a3_not_mem_of_minus (k : USym (symmetric_group three)) (e : Id Sign (sigma_two_sign (usgn three k)) minus.)
  : Not (SubgroupHasSymmetry (symmetric_group three) (alternating_subgroup (suc. zero.)) k)
  ≔ r ↦
    let G ≔ symmetric_group three in
    let A3 ≔ alternating_subgroup (suc. zero.) in
    let A3' : Subgroups G ≔ (kernel_gset G sign_sigma_two (sign_hom three), hom_point G sign_sigma_two (sign_hom three),
               kernel_gset_transitive G sign_sigma_two (sign_hom three) (sign_hom_connected (suc. zero.))) in
    sigma_two_not_unit_of_minus (usgn three k) e
      (kernel_member_iff G sign_sigma_two (sign_hom three) k .fst
        (subgroup_symmetry_transport G A3 A3' sigma3_a3_kernel_path k r))

{` Signs of the named symmetries (inversion numbers, by computation). `}
def sigma3_sign_t01 : Id Sign (sigma_two_sign (usgn three (sigma3_sym t01.))) minus.
  ≔ usgn_inversion_number (suc. zero.) fin3_swap01_equiv

def sigma3_sign_t02 : Id Sign (sigma_two_sign (usgn three (sigma3_sym t02.))) minus.
  ≔ usgn_inversion_number (suc. zero.) fin3_swap02_equiv

def sigma3_sign_t12 : Id Sign (sigma_two_sign (usgn three (sigma3_sym t12.))) minus.
  ≔ usgn_inversion_number (suc. zero.) fin3_swap12_equiv

def sigma3_sign_cyc : Id Sign (sigma_two_sign (usgn three (sigma3_sym cyc.))) plus.
  ≔ usgn_inversion_number (suc. zero.) fin3_rot_equiv

def sigma3_sign_cin : Id Sign (sigma_two_sign (usgn three (sigma3_sym cin.))) plus.
  ≔ usgn_inversion_number (suc. zero.) fin3_rot_inv_equiv

{` Subgroups of Σ_3 with the same named symmetries are equal. `}
def sigma3_same_members (S T : Subgroups (symmetric_group three))
  (H : (n : Sigma3Name) → Product (Sigma3Mem S n → Sigma3Mem T n) (Sigma3Mem T n → Sigma3Mem S n))
  : Id (Subgroups (symmetric_group three)) S T
  ≔ let G ≔ symmetric_group three in
    let move : (U V : Subgroups G) → ((n : Sigma3Name) → Sigma3Mem U n → Sigma3Mem V n) → SubgroupLe G U V
      ≔ U V h k r ↦
        let w ≔ sigma3_enum k in
        transport (USym G) (SubgroupHasSymmetry G V) (sigma3_sym (w .fst)) k
          (inverse (USym G) k (sigma3_sym (w .fst)) (w .snd))
          (h (w .fst) (transport (USym G) (SubgroupHasSymmetry G U) k (sigma3_sym (w .fst)) (w .snd) r)) in
    subgroup_le_antisym G S T (move S T (n ↦ H n .fst)) (move T S (n ↦ H n .snd))
