import "../../../src/1705-circle-choice"
import "01-lpo-topology"
import "02-choice-principles"

{` Bridges for choicefin.tex: choice principles (pri:ac, the remark
   after it, Diaconescu, X-AC / AC(n) / X-AC(n), finite X, pri:sc, AC_∞,
   S¹-AC(2)). Blind declarations on the left, ours (modules 1700–1705) on
   the right. `}

{` Definition bridges. `}
def bridge_def_nonempty_sets : Id Type BlindNonEmptySets NonemptySets ≔ refl NonemptySets

def bridge_def_ac_to_ours (ac : BlindAC) : AxiomOfChoice ≔ X ↦ ac (X .fst) (X .snd)

def bridge_def_ac_from_ours (ac : AxiomOfChoice) : BlindAC ≔ X hX ↦ ac (X, hX)

def bridge_def_ac : BlindIff BlindAC AxiomOfChoice ≔ (bridge_def_ac_to_ours, bridge_def_ac_from_ours)

def bridge_def_ac_nonempty : BlindIff BlindACNonEmptyForm AxiomOfChoiceNonempty
  ≔ (ac X ↦ ac (X .fst) (X .snd), ac X hX ↦ ac (X, hX))

def bridge_def_sections (A B : Type) (f : A → B) : Id Type (BlindSections A B f) (MapSection A B f)
  ≔ refl (MapSection A B f)

def bridge_def_surjections_onto (X : Type) : Id Type (BlindSurjectionsOnto X) (SetSurjectionsOnto X)
  ≔ refl (SetSurjectionsOnto X)

def bridge_def_surjections_split : BlindIff BlindSurjectionsSplit SurjectionsBetweenSetsSplit
  ≔ (h X Y p s ↦ h (Y .fst) (X .fst) (Y .snd) (X .snd) p s,
     h A B hA hB f s ↦ h (B, hB) (A, hA) f s)

def bridge_def_local_ac (X : Type) : Id Type (BlindLocalAC X) (LocalChoice X) ≔ refl (LocalChoice X)

{` BΣ_n of the blind file is BookFiniteSetsAt n (mere SetTypes paths to
   Fin n); ours is FiniteSetsAt n (mere Type paths). Carrier-preserving maps
   both ways, and the equivalence of module 186. `}
def bridge_b_finsets_to_blind (n : Nat) (S : FiniteSetsAt n) : BlindFinSetsAt n
  ≔ (S .fst, trunc_map native_truncation (Id Type (Fin n) (S .fst .fst)) (Id SetTypes (Fin n, fin_set n) (S .fst))
       (p ↦ subtype_equal Type isSet isset_isprop (Fin n, fin_set n) (S .fst) p) (S .snd))

def bridge_b_finsets_from_blind (n : Nat) (S : BlindFinSetsAt n) : FiniteSetsAt n
  ≔ (S .fst, trunc_map native_truncation (Id SetTypes (Fin n, fin_set n) (S .fst)) (Id Type (Fin n) (S .fst .fst))
       (q ↦ map_path SetTypes Type (T ↦ T .fst) (Fin n, fin_set n) (S .fst) q) (S .snd))

def bridge_def_finsets_at (n : Nat) : Equiv (BlindFinSetsAt n) (FiniteSetsAt n) ≔ book_finite_sets_at_equiv n

def bridge_def_local_acn_to_ours (X : Type) (n : Nat) (l : BlindLocalACn X n) : LocalChoiceOfSize X n
  ≔ P h ↦ l (x ↦ bridge_b_finsets_to_blind n (P x)) h

def bridge_def_local_acn_from_ours (X : Type) (n : Nat) (l : LocalChoiceOfSize X n) : BlindLocalACn X n
  ≔ P h ↦ l (x ↦ bridge_b_finsets_from_blind n (P x)) h

def bridge_def_local_acn (X : Type) (n : Nat) : BlindIff (BlindLocalACn X n) (LocalChoiceOfSize X n)
  ≔ (bridge_def_local_acn_to_ours X n, bridge_def_local_acn_from_ours X n)

def bridge_def_acn_to_ours (n : Nat) (a : BlindACn n) : ChoiceOfSize n
  ≔ X ↦ bridge_def_local_acn_to_ours (X .fst) n (a (X .fst) (X .snd))

def bridge_def_acn_from_ours (n : Nat) (a : ChoiceOfSize n) : BlindACn n
  ≔ X hX ↦ bridge_def_local_acn_from_ours X n (a (X, hX))

def bridge_def_acn (n : Nat) : BlindIff (BlindACn n) (ChoiceOfSize n)
  ≔ (bridge_def_acn_to_ours n, bridge_def_acn_from_ours n)

def bridge_def_local_ac_infty (X : Type) : Id Type (BlindLocalACInfty X) (UntruncatedLocalChoice X)
  ≔ refl (FiniteChoice X)

def bridge_def_ac_infty : BlindIff BlindACInfty UntruncatedChoice
  ≔ (a X ↦ a (X .fst) (X .snd), a X hX ↦ a (X, hX))

def bridge_def_sets_cover : BlindIff BlindSetsCover SetsCover
  ≔ (sc A ↦ trunc_map native_truncation (Σ Type (X ↦ Product (isSet X) (Σ (X → A) (f ↦ Surjective X A f))))
         (SetCovers A) (w ↦ ((w .fst, w .snd .fst), w .snd .snd)) (sc A),
     sc A ↦ trunc_map native_truncation (SetCovers A)
         (Σ Type (X ↦ Product (isSet X) (Σ (X → A) (f ↦ Surjective X A f))))
         (w ↦ (w .fst .fst, (w .fst .snd, w .snd))) (sc A))

{` pri:ac. `}
def bridge_ac_forms_iff : blind_ac_forms_iff
  ≔ (f ↦ bridge_def_ac_from_ours (axiom_of_choice_formulations_equiv .map (bridge_def_ac_nonempty .fst f)),
     a ↦ bridge_def_ac_nonempty .snd
       (equiv_inverse_map AxiomOfChoiceNonempty AxiomOfChoice axiom_of_choice_formulations_equiv
         (bridge_def_ac_to_ours a)))

{` Remark after pri:ac. `}
def bridge_choice_remark_pi_sections_equiv : blind_choice_remark_pi_sections_equiv
  ≔ X P ↦ book_equivalence ((x : X) → P x) (MapSection (Σ X P) X (u ↦ u .fst)) (pi_section_equiv X P)

def bridge_choice_remark_nonempty_iff_projection_surjective : blind_choice_remark_nonempty_iff_projection_surjective
  ≔ X P ↦ (projection_surjective X P,
     s x ↦ trunc_map native_truncation (BookFiber (Σ X P) X (u ↦ u .fst) x) (P x)
       (book_projection_fiber_equiv X P x .map) (s x))

def bridge_choice_remark_total_set : blind_choice_remark_total_set
  ≔ X hX P ↦ sigma_set X (x ↦ P x .fst) hX (x ↦ P x .snd)

{` The blind map P ↦ (Σ_x P(x), pr1) is an equivalence. Ours
   (nonempty_families_surjections_equiv) is an equivalence between the same
   types whose map is not definitionally the total-space projection; the
   bridge uses the same ingredients (module 19's maps_families_eta and the
   projection-fiber equivalence) with the blind map as forward map. `}
def bridge_b_surjection_to_family (X : Type) (hX : isSet X) (t : BlindSurjectionsOnto X) : X → BlindNonEmptySets
  ≔ x ↦ ((BookFiber (t .fst .fst) X (t .snd .fst) x,
          book_fiber_set (t .fst .fst) X (t .snd .fst) (t .fst .snd) hX x),
         t .snd .snd x)

def bridge_b_family_roundtrip (X : Type) (hX : isSet X) (P : X → BlindNonEmptySets)
  : Id (X → BlindNonEmptySets) (bridge_b_surjection_to_family X hX (blind_family_to_surjection X hX P)) P
  ≔ funext X (_ ↦ BlindNonEmptySets) (bridge_b_surjection_to_family X hX (blind_family_to_surjection X hX P)) P
      (x ↦ subtype_equal SetTypes (S ↦ Mere (S .fst)) (S ↦ mere_isprop (S .fst))
        (bridge_b_surjection_to_family X hX (blind_family_to_surjection X hX P) x) (P x)
        (subtype_equal Type isSet isset_isprop
          (bridge_b_surjection_to_family X hX (blind_family_to_surjection X hX P) x .fst) (P x .fst)
          (ua (BookFiber (Σ X (y ↦ P y .fst .fst)) X (u ↦ u .fst) x) (P x .fst .fst)
            (native_equivalence (BookFiber (Σ X (y ↦ P y .fst .fst)) X (u ↦ u .fst) x) (P x .fst .fst)
              (book_projection_fiber_equiv X (y ↦ P y .fst .fst) x)))))

def BridgeBSurjData (X : Type) : Type
  ≔ Σ (MapsInto X) (m ↦ Product (isSet (m .fst)) (Surjective (m .fst) X (m .snd)))

def bridge_b_surj_reshuffle (X : Type) (w : BridgeBSurjData X) : BlindSurjectionsOnto X
  ≔ ((w .fst .fst, w .snd .fst), (w .fst .snd, w .snd .snd))

def bridge_b_surj_unshuffle (X : Type) (t : BlindSurjectionsOnto X) : BridgeBSurjData X
  ≔ ((t .fst .fst, t .snd .fst), (t .fst .snd, t .snd .snd))

def bridge_b_surj_path (X : Type) (t t' : BlindSurjectionsOnto X)
  (q : Id (MapsInto X) (t .fst .fst, t .snd .fst) (t' .fst .fst, t' .snd .fst)) : Id (BlindSurjectionsOnto X) t t'
  ≔ map_path (BridgeBSurjData X) (BlindSurjectionsOnto X) (bridge_b_surj_reshuffle X)
      (bridge_b_surj_unshuffle X t) (bridge_b_surj_unshuffle X t')
      (subtype_equal (MapsInto X) (m ↦ Product (isSet (m .fst)) (Surjective (m .fst) X (m .snd)))
        (m ↦ product_prop (isSet (m .fst)) (Surjective (m .fst) X (m .snd)) (isset_isprop (m .fst))
          (surjective_property_prop (m .fst) X (m .snd)))
        (bridge_b_surj_unshuffle X t) (bridge_b_surj_unshuffle X t') q)

def bridge_b_surjection_roundtrip (X : Type) (hX : isSet X) (t : BlindSurjectionsOnto X)
  : Id (BlindSurjectionsOnto X) (blind_family_to_surjection X hX (bridge_b_surjection_to_family X hX t)) t
  ≔ bridge_b_surj_path X (blind_family_to_surjection X hX (bridge_b_surjection_to_family X hX t)) t
      (maps_families_eta X (t .fst .fst, t .snd .fst))

def bridge_choice_remark_families_surjections_equiv : blind_choice_remark_families_surjections_equiv
  ≔ X hX ↦ book_quasi_inverse_equiv (X → BlindNonEmptySets) (BlindSurjectionsOnto X)
      (blind_family_to_surjection X hX) (bridge_b_surjection_to_family X hX)
      (bridge_b_family_roundtrip X hX) (bridge_b_surjection_roundtrip X hX) .equiv

def bridge_choice_remark_ac_iff_surjections_split : blind_choice_remark_ac_iff_surjections_split
  ≔ (a ↦ bridge_def_surjections_split .snd (choice_surjections_split_equiv .map (bridge_def_ac_to_ours a)),
     h ↦ bridge_def_ac_from_ours
       (equiv_inverse_map AxiomOfChoice SurjectionsBetweenSetsSplit choice_surjections_split_equiv
         (bridge_def_surjections_split .fst h)))

{` Diaconescu. `}
def bridge_ac_implies_lem : blind_ac_implies_lem ≔ ac ↦ choice_implies_excluded_middle (bridge_def_ac_to_ours ac)

{` xca: X-AC for finite X. `}
def bridge_xca_finite_local_ac : blind_xca_finite_local_ac ≔ X h ↦ finite_local_choice X h

{` xca: AC_∞ ⇔ AC ∧ SC. `}
def bridge_xca_ac_infty_iff_ac_and_sc : blind_xca_ac_infty_iff_ac_and_sc
  ≔ (a ↦
      let h ≔ untruncated_choice_iff .map (bridge_def_ac_infty .fst a) in
      (bridge_def_ac_from_ours (h .fst), bridge_def_sets_cover .snd (h .snd)),
     h ↦ bridge_def_ac_infty .snd
       (equiv_inverse_map UntruncatedChoice (Product AxiomOfChoice SetsCover) untruncated_choice_iff
         (bridge_def_ac_to_ours (h .fst), bridge_def_sets_cover .fst (h .snd))))

{` xca: S¹-AC(2) is false. `}
def bridge_xca_circle_local_ac_two_false : blind_xca_circle_local_ac_two_false
  ≔ C l ↦ circle_local_choice_two_false C (bridge_def_local_acn_to_ours (C .carrier) 2 l)
