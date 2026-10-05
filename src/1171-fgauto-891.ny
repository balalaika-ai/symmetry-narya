export "1170-fgauto-recognizable-regular"

{` Chapter 11, automata part 22: assembling fggroups.tex:891 "<=" (see
   module 1170) and the theorem as an equivalence. `}

def fgauto_vec (S : Type) (B : FgautoNFA S) : Type ≔ Fin (fgauto_nfa_k S B) → Bool

def fgauto_vpair (S : Type) (B : FgautoNFA S) : Type ≔ Product (fgauto_vec S B) (fgauto_vec S B)

def fgauto_vpair_dec (S : Type) (B : FgautoNFA S) : DecidableEquality (fgauto_vpair S B)
  ≔ fgauto_pair_decidable_equality (fgauto_vec S B) (fgauto_vec S B) (fgauto_vec_decidable_equality (fgauto_nfa_k S B))
      (fgauto_vec_decidable_equality (fgauto_nfa_k S B))

def fgauto_vpair_list (S : Type) (B : FgautoNFA S) : List (fgauto_vpair S B)
  ≔ fgauto_pair_list (fgauto_vec S B) (fgauto_vec S B) (fgauto_vec_list (fgauto_nfa_k S B)) (fgauto_vec_list (fgauto_nfa_k S B))

def fgauto_vpair_list_complete (S : Type) (B : FgautoNFA S) (u : fgauto_vpair S B) : FgautoMem (fgauto_vpair S B) u (fgauto_vpair_list S B)
  ≔ fgauto_pair_list_complete (fgauto_vec S B) (fgauto_vec S B) (fgauto_vec_list (fgauto_nfa_k S B)) (fgauto_vec_list (fgauto_nfa_k S B))
      (fgauto_vec_list_complete (fgauto_nfa_k S B)) (fgauto_vec_list_complete (fgauto_nfa_k S B)) u

def fgauto_pair_edges (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (L : List (SignedLetter S))
  : List (FgautoEdge S (fgauto_vpair S B))
  ≔ fgauto_fun_edges S (fgauto_vpair S B) (fgauto_pair_step S dec B) (fgauto_vpair_list S B) L

def fgauto_vec_edges (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (L : List (SignedLetter S))
  : List (FgautoEdge S (fgauto_vec S B))
  ≔ fgauto_fun_edges S (fgauto_vec S B) (fgauto_nfa_delta S dec B) (fgauto_vec_list (fgauto_nfa_k S B)) L

def FgautoMeetsAgree (S : Type) (B : FgautoNFA S) (q : fgauto_vpair S B) : Type
  ≔ Id Bool (fgauto_nfa_meets S B (q .fst)) (fgauto_nfa_meets S B (q .snd))

{` Deciding the syntactic congruence on words. `}
def fgauto_891_decide_words (S : Type) (dec : DecidableEquality S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier)) (B : FgautoNFA S)
  (hB : (w : SignedWord S) → FgautoIff (X (fgauto_matched_hom S G a w) .fst) (FgautoNFAAccepts S B w))
  (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L) (u u' : SignedWord S)
  : Decidable (FgautoSyntacticRight G X (fgauto_matched_hom S G a u) (fgauto_matched_hom S G a u'))
  ≔ let V2 ≔ fgauto_vpair S B in
    let I ≔ fgauto_nfa_init_vec S B in
    let P ≔ fgauto_nfa_sim S dec B I u in
    let P' ≔ fgauto_nfa_sim S dec B I u' in
    let E2 ≔ fgauto_pair_edges S dec B L in
    let st2 ≔ fgauto_pair_step S dec B in
    let p0 : V2 ≔ (P, P') in
    let R2 ≔ fgauto_reached S V2 (fgauto_vpair_dec S B) E2 p0 in
    let agree : (v : SignedWord S) → FgautoMeetsAgree S B (fgauto_fun_iterate S V2 st2 p0 v)
        → Id Bool (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B P v)) (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B P' v))
      ≔ v h ↦ transport V2 (FgautoMeetsAgree S B) (fgauto_fun_iterate S V2 st2 p0 v)
          (fgauto_nfa_sim S dec B P v, fgauto_nfa_sim S dec B P' v) (fgauto_pair_iterate S dec B P P' v) h in
    match fgauto_list_all_decide V2 (FgautoMeetsAgree S B) (q ↦ fgauto_bool_decidable_equality (fgauto_nfa_meets S B (q .fst)) (fgauto_nfa_meets S B (q .snd))) R2 [
    | inl. f ↦ inl. (fgauto_891_same_sim S dec G a gen X B hB u u'
        (v ↦ agree v (f (fgauto_fun_iterate S V2 st2 p0 v)
          (fgauto_reach_complete S V2 (fgauto_vpair_dec S B) E2 p0 v (fgauto_fun_iterate S V2 st2 p0 v)
            (fgauto_fun_run_exists S V2 st2 (fgauto_vpair_list S B) (fgauto_vpair_list_complete S B) L cL p0 v)))))
    | inr. y ↦
      let q ≔ y .fst in
      let v ≔ fgauto_tree_word S V2 (fgauto_vpair_dec S B) E2 p0 q in
      let rq ≔ fgauto_tree_word_run S V2 (fgauto_vpair_dec S B) E2 p0 q (y .snd .fst) in
      let eq ≔ fgauto_fun_run_value S V2 st2 (fgauto_vpair_list S B) L p0 v q rq in
      inr. (r ↦
        let iu ≔ fgauto_891_word_iff S dec G a X B hB u v in
        let iu' ≔ fgauto_891_word_iff S dec G a X B hB u' v in
        let rr ≔ r (fgauto_matched_hom S G a v) in
        y .snd .snd (transport V2 (FgautoMeetsAgree S B) (fgauto_fun_iterate S V2 st2 p0 v) q (inverse V2 q (fgauto_fun_iterate S V2 st2 p0 v) eq)
          (transport V2 (FgautoMeetsAgree S B) (fgauto_nfa_sim S dec B P v, fgauto_nfa_sim S dec B P' v) (fgauto_fun_iterate S V2 st2 p0 v)
            (inverse V2 (fgauto_fun_iterate S V2 st2 p0 v) (fgauto_nfa_sim S dec B P v, fgauto_nfa_sim S dec B P' v) (fgauto_pair_iterate S dec B P P' v))
            (fgauto_bool_of_iff (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B P v)) (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B P' v))
              (t ↦ iu' .fst (rr .fst (iu .snd t)), t ↦ iu .fst (rr .snd (iu' .snd t))))))) ]

def fgauto_syntactic_right_prop (G : AbstractGroup) (X : Subtypes (G .carrier)) (g g' : G .carrier)
  : isProp (FgautoSyntacticRight G X g g')
  ≔ fgauto_syntactic_relation G X .predicate g g' .snd

def fgauto_891_decidable_relation (S : Type) (dec : DecidableEquality S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier)) (B : FgautoNFA S)
  (hB : (w : SignedWord S) → FgautoIff (X (fgauto_matched_hom S G a w) .fst) (FgautoNFAAccepts S B w))
  (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L)
  : DecidableRelation (G .carrier) (fgauto_syntactic_relation G X)
  ≔ x y ↦
    let C ≔ G .carrier in
    let D ≔ (g g' : C) ↦ Decidable (FgautoSyntacticRight G X g g') in
    let hD ≔ decidability_prop (FgautoSyntacticRight G X x y) (fgauto_syntactic_right_prop G X x y) in
    mere_rec (Σ (SignedWord S) (u ↦ Id C (fgauto_matched_hom S G a u) x)) (D x y) hD
      (zu ↦ mere_rec (Σ (SignedWord S) (u ↦ Id C (fgauto_matched_hom S G a u) y)) (D x y) hD
        (zv ↦ transport C (g ↦ D g y) (fgauto_matched_hom S G a (zu .fst)) x (zu .snd)
          (transport C (g ↦ D (fgauto_matched_hom S G a (zu .fst)) g) (fgauto_matched_hom S G a (zv .fst)) y (zv .snd)
            (fgauto_891_decide_words S dec G a gen X B hB L cL (zu .fst) (zv .fst)))) (gen y)) (gen x)

{` Deciding membership in X. `}
def fgauto_891_decide_member (S : Type) (dec : DecidableEquality S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier)) (B : FgautoNFA S)
  (hB : (w : SignedWord S) → FgautoIff (X (fgauto_matched_hom S G a w) .fst) (FgautoNFAAccepts S B w)) (g : G .carrier)
  : Decidable (X g .fst)
  ≔ let C ≔ G .carrier in
    mere_rec (Σ (SignedWord S) (u ↦ Id C (fgauto_matched_hom S G a u) g)) (Decidable (X g .fst)) (decidability_prop (X g .fst) (X g .snd))
      (zu ↦ transport C (h ↦ Decidable (X h .fst)) (fgauto_matched_hom S G a (zu .fst)) g (zu .snd)
        (let acc ≔ fgauto_nfa_accepts_sim S dec B (zu .fst) in
         match fgauto_bool_decide_true (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B (fgauto_nfa_init_vec S B) (zu .fst))) [
         | inl. t ↦ inl. (hB (zu .fst) .snd (acc .snd t))
         | inr. n ↦ inr. (x ↦ n (acc .fst (hB (zu .fst) .fst x))) ]))
      (gen g)

{` fggroups.tex:891, "<=". `}
def fgauto_regular_preimage_recognizable_at (S : Type) (dec : DecidableEquality S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier)) (B : FgautoNFA S)
  (hB : (w : SignedWord S) → FgautoIff (X (fgauto_matched_hom S G a w) .fst) (FgautoNFAAccepts S B w))
  (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L)
  : FgautoRecognizable (fgauto_group_monoid G) (g ↦ X g .fst)
  ≔ let C ≔ G .carrier in
    let R ≔ fgauto_syntactic_relation G X in
    let Y ≔ FgautoSyntacticClasses G X in
    let V1 ≔ fgauto_vec S B in
    let I ≔ fgauto_nfa_init_vec S B in
    let E1 ≔ fgauto_vec_edges S dec B L in
    let dV1 ≔ fgauto_vec_decidable_equality (fgauto_nfa_k S B) in
    let Rv ≔ fgauto_reached S V1 dV1 E1 I in
    let nR ≔ length V1 Rv in
    let wordOf : Fin nR → SignedWord S ≔ j ↦ fgauto_tree_word S V1 dV1 E1 I (fgauto_list_nth V1 Rv j) in
    let f : Fin nR → Y ≔ j ↦ quotient_class C R (fgauto_matched_hom S G a (wordOf j)) in
    let surj : Surjective (Fin nR) Y f
      ≔ fgauto_quotient_ind_prop C R (z ↦ Mere (BookFiber (Fin nR) Y f z)) (z ↦ mere_isprop (BookFiber (Fin nR) Y f z))
          (g ↦ mere_rec (Σ (SignedWord S) (u ↦ Id C (fgauto_matched_hom S G a u) g)) (Mere (BookFiber (Fin nR) Y f (quotient_class C R g)))
            (mere_isprop (BookFiber (Fin nR) Y f (quotient_class C R g)))
            (zu ↦
              let u ≔ zu .fst in
              let vu ≔ fgauto_nfa_sim S dec B I u in
              let mv ≔ fgauto_reach_complete S V1 dV1 E1 I u vu
                (fgauto_fun_run_exists S V1 (fgauto_nfa_delta S dec B) (fgauto_vec_list (fgauto_nfa_k S B))
                  (fgauto_vec_list_complete (fgauto_nfa_k S B)) L cL I u) in
              let j ≔ fgauto_list_pos V1 dV1 vu Rv mv in
              let t ≔ wordOf j in
              let rt ≔ fgauto_tree_word_run S V1 dV1 E1 I (fgauto_list_nth V1 Rv j) (fgauto_list_nth_mem V1 Rv j) in
              let st : Id V1 (fgauto_nfa_sim S dec B I t) vu
                ≔ concat V1 (fgauto_nfa_sim S dec B I t) (fgauto_list_nth V1 Rv j) vu
                    (inverse V1 (fgauto_list_nth V1 Rv j) (fgauto_nfa_sim S dec B I t)
                      (fgauto_fun_run_value S V1 (fgauto_nfa_delta S dec B) (fgauto_vec_list (fgauto_nfa_k S B)) L I t (fgauto_list_nth V1 Rv j) rt))
                    (fgauto_list_pos_nth V1 dV1 vu Rv mv) in
              mere (BookFiber (Fin nR) Y f (quotient_class C R g))
                (j, concat Y (quotient_class C R g) (quotient_class C R (fgauto_matched_hom S G a u)) (f j)
                  (refl (quotient_class C R) (inverse C (fgauto_matched_hom S G a u) g (zu .snd)))
                  (quotient_encode C R (fgauto_matched_hom S G a u) (fgauto_matched_hom S G a t)
                    (fgauto_891_same_sim S dec G a gen X B hB u t
                      (v ↦ refl ((P ↦ fgauto_nfa_meets S B (fgauto_nfa_sim S dec B P v)) : V1 → Bool)
                        (inverse V1 (fgauto_nfa_sim S dec B I t) vu st))))))
            (gen g)) in
    let hY : IsFinite Y ≔ finite_surjection_target (Fin nR) Y (fin_is_finite nR)
      (quotient_decidable_equality C R (fgauto_891_decidable_relation S dec G a gen X B hB L cL)) f surj in
    let FY : Y → Bool ≔ quotient_rec C Bool R (z w ↦ bool_set z w)
      (g ↦ fgauto_decision_bool (X g .fst) (fgauto_891_decide_member S dec G a gen X B hB g))
      (g g' r ↦ fgauto_decision_bool_iff (X g .fst) (X g' .fst) (fgauto_891_decide_member S dec G a gen X B hB g)
         (fgauto_891_decide_member S dec G a gen X B hB g')
         (x ↦ transport C (h ↦ X h .fst) (G .mul g' (G .unit)) g' (G .laws .unit_right g')
            (r (G .unit) .fst (transport C (h ↦ X h .fst) g (G .mul g (G .unit)) (inverse C (G .mul g (G .unit)) g (G .laws .unit_right g)) x)))
         (x ↦ transport C (h ↦ X h .fst) (G .mul g (G .unit)) g (G .laws .unit_right g)
            (r (G .unit) .snd (transport C (h ↦ X h .fst) g' (G .mul g' (G .unit)) (inverse C (G .mul g' (G .unit)) g' (G .laws .unit_right g')) x)))) in
    fgauto_finite_gset_recognizable (fgauto_group_monoid G) Y hY (fgauto_syntactic_act G X)
      (fgauto_quotient_ind_prop C R (z ↦ Id Y (fgauto_syntactic_act G X z (G .unit)) z)
        (z ↦ quotient_set C R (fgauto_syntactic_act G X z (G .unit)) z)
        (g ↦ refl (quotient_class C R) (G .laws .unit_right g)))
      (z m m' ↦ fgauto_quotient_ind_prop C R (z0 ↦ Id Y (fgauto_syntactic_act G X z0 (G .mul m m')) (fgauto_syntactic_act G X (fgauto_syntactic_act G X z0 m) m'))
        (z0 ↦ quotient_set C R (fgauto_syntactic_act G X z0 (G .mul m m')) (fgauto_syntactic_act G X (fgauto_syntactic_act G X z0 m) m'))
        (g ↦ refl (quotient_class C R) (G .laws .assoc g m m')) z)
      (quotient_class C R (G .unit)) FY (g ↦ X g .fst)
      (g ↦
        let dg ≔ fgauto_891_decide_member S dec G a gen X B hB (G .mul (G .unit) g) in
        (x ↦ fgauto_decision_bool_true (X (G .mul (G .unit) g) .fst) dg
           (transport C (h ↦ X h .fst) g (G .mul (G .unit) g) (inverse C (G .mul (G .unit) g) g (G .laws .unit_left g)) x),
         t ↦ transport C (h ↦ X h .fst) (G .mul (G .unit) g) g (G .laws .unit_left g)
           (fgauto_decision_bool_reflect (X (G .mul (G .unit) g) .fst) dg t)))

def fgauto_regular_preimage_recognizable (S : Type) (dec : DecidableEquality S) (hS : IsFinite S) (G : AbstractGroup)
  (a : S → G .carrier) (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier))
  (hX : FgautoRegular S (FgautoPreimage S G a (g ↦ X g .fst))) : FgautoRecognizable (fgauto_group_monoid G) (g ↦ X g .fst)
  ≔ let M ≔ fgauto_group_monoid G in
    let goal ≔ FgautoRecognizable M (g ↦ X g .fst) in
    let hg ≔ mere_isprop (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦
      FgautoRecognizes M A q0 F (g ↦ X g .fst))))) in
    mere_rec (Σ Nat (m ↦ Id Type S (Fin m))) goal hg
      (sm ↦
        let en ≔ fgauto_finite_enumeration S (sm .fst) (id_to_equiv S (Fin (sm .fst)) (sm .snd)) in
        mere_rec (Σ (FgautoNFA S) (B ↦ (w : SignedWord S) → FgautoIff (FgautoPreimage S G a (g ↦ X g .fst) w) (FgautoNFAAccepts S B w)))
          goal hg
          (z ↦ fgauto_regular_preimage_recognizable_at S dec G a gen X (z .fst) (z .snd) (fgauto_signed_letters S (en .fst))
            (fgauto_signed_letters_complete S (en .fst) (en .snd))) hX) hS

{` fggroups.tex:891. `}
def fgauto_recognizable_iff_regular_preimage (S : Type) (dec : DecidableEquality S) (hS : IsFinite S) (G : AbstractGroup)
  (a : S → G .carrier) (gen : FgautoGeneratesGroup S G a) (X : Subtypes (G .carrier))
  : FgautoIff (FgautoRecognizable (fgauto_group_monoid G) (g ↦ X g .fst)) (FgautoRegular S (FgautoPreimage S G a (g ↦ X g .fst)))
  ≔ (fgauto_recognizable_preimage_regular S hS G a (g ↦ X g .fst), fgauto_regular_preimage_recognizable S dec hS G a gen X)
