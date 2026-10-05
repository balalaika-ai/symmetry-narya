export "bridge-00-core"
export "04-sign"
export "../../../src/461-alternating-three"
export "../../../src/462-sign-aut-agreement"
export "../../../src/286-cycle-notation-equivalence"

{` Bridges for 04-sign.ny (group.tex, sec:sign-homomorphism).
   Judgmental agreements (checked by refl below): BlindBSG2 is
   BookFiniteSetsAt two (= BΣ_2, our shape sign_sigma_two is blind_bsg2_pt),
   BlindBSGn n is BookFiniteSetsAt n, BlindLocalSections is LocalSections, the
   blind loop of a permutation σ in blind_sgn_action is our permutation_loop,
   and the carrier of blind_two_subset_family A e is that of two_subset_bsigma.
   Differences: BlindEvenCard / BlindParityRel versus IsEvenNat of a
   cardinality (logically equivalent propositions), the blind quotient is the
   image of the blind predicate (equal to ours by a path of predicates),
   BlindTwoSubsets has the inverse identification with Fin 2, and
   blind_fin_val orders Fin n in reverse (inr is the largest element).

   The (revised) blind μ_E matches on a decision variable and Bsgn uses the
   decision blind_two_subsets_dec n A (a match on n), so everything computes
   and every statement is bridged for every H : BlindSignHyps. The pointing
   data ptg / ord of H only enter the pointings of μ_E and Bsgn; the free
   map blind_Bsgn_map H n agrees with our bsgn n pointwise for every H
   (bridge_sgn_K), and USym only depends on the free map (Σ_2 is abelian). `}

def bridge_sg_defeq_bsg2 : Id Type BlindBSG2 (BookFiniteSetsAt two) ≔ refl BlindBSG2
def bridge_sg_defeq_bsgn (n : Nat) : Id Type (BlindBSGn n) (BookFiniteSetsAt n) ≔ refl (BlindBSGn n)
def bridge_sg_defeq_pt : Id BlindBSG2 blind_bsg2_pt (shape sign_sigma_two) ≔ refl blind_bsg2_pt
def bridge_def_local_sections (E : Type) (P : E → BlindBSG2) : Id Type (BlindLocalSections E P) (LocalSections E P)
  ≔ refl (LocalSections E P)
{` The blind loop of σ (an explicit pair) is our permutation_loop. `}
def bridge_sg_loop_path (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : Id (Id (BlindBSGn n) A A) (blind_bsgn_loop n A σ) (permutation_loop n A σ)
  ≔ bsigma_path_ext n A A (blind_bsgn_loop n A σ) (permutation_loop n A σ) (x ↦ refl (σ .map x))

{` ---- group.tex:1473, the parity relation. ---- `}

def bridge_nat_even_odd (k : Nat) : Id Bool (blind_nat_even k) (bool_not (nat_odd k))
  ≔ match k [ zero. ↦ refl (true. : Bool) | suc. j ↦ refl bool_not (bridge_nat_even_odd j) ]

def bridge_nat_even_true_to (k : Nat) (q : Id Bool (blind_nat_even k) true.) : Id Bool (nat_odd k) false.
  ≔ bool_not_true_false (nat_odd k)
      (concat Bool (bool_not (nat_odd k)) (blind_nat_even k) true.
        (inverse Bool (blind_nat_even k) (bool_not (nat_odd k)) (bridge_nat_even_odd k)) q)

def bridge_nat_even_true_from (k : Nat) (q : Id Bool (nat_odd k) false.) : Id Bool (blind_nat_even k) true.
  ≔ concat Bool (blind_nat_even k) (bool_not (nat_odd k)) true. (bridge_nat_even_odd k) (refl bool_not q)

def bridge_nat_even_false_to (k : Nat) (q : Id Bool (blind_nat_even k) false.) : Id Bool (nat_odd k) true.
  ≔ bool_not_false_true (nat_odd k)
      (concat Bool (bool_not (nat_odd k)) (blind_nat_even k) false.
        (inverse Bool (blind_nat_even k) (bool_not (nat_odd k)) (bridge_nat_even_odd k)) q)

def bridge_card_from_mere (S : Type) (hS : IsFinite S) (k : Nat) (m : Mere (Id Type S (Fin k)))
  : Id Nat (cardinality S hS) k
  ≔ mere_rec (Id Type S (Fin k)) (Id Nat (cardinality S hS) k) (nat_set (cardinality S hS) k)
      (p ↦ cardinality_from_path S hS k p) m

{` "S has an even number of elements": the blind cardinality witness versus
   IsEvenNat of our cardinality. `}
def bridge_def_even_card (S : Type) (hS : IsFinite S) : Equiv (BlindEvenCard S) (IsEvenNat (cardinality S hS))
  ≔ iff_equiv (BlindEvenCard S) (IsEvenNat (cardinality S hS)) (blind_even_card_prop S) (is_even_nat_prop (cardinality S hS))
      (u ↦ equiv_inverse_map (IsEvenNat (cardinality S hS)) (Id Bool (nat_odd (cardinality S hS)) false.)
        (is_even_nat_iff (cardinality S hS))
        (concat Bool (nat_odd (cardinality S hS)) (nat_odd (u .fst)) false.
          (refl nat_odd (bridge_card_from_mere S hS (u .fst) (u .snd .fst)))
          (bridge_nat_even_true_to (u .fst) (u .snd .snd))))
      (v ↦ (cardinality S hS, (cardinality_spec S hS,
        bridge_nat_even_true_from (cardinality S hS) (is_even_nat_iff (cardinality S hS) .map v))))

def bridge_def_parity_rel (E : Type) (hE : IsFinite E) (P : E → BlindBSG2) (f g : BlindLocalSections E P)
  : Equiv (BlindParityRel E P f g) (ParityRelated E hE P f g)
  ≔ bridge_def_even_card (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g)

def bridge_parity_predicate_path (E : Type) (hE : IsFinite E) (P : E → BlindBSG2)
  : Id (LocalSections E P → LocalSections E P → PropTypes) (blind_parity_predicate E P) (parity_relation E hE P .predicate)
  ≔ let L ≔ LocalSections E P in
    funext L (_ ↦ L → PropTypes) (blind_parity_predicate E P) (parity_relation E hE P .predicate)
      (f ↦ funext L (_ ↦ PropTypes) (blind_parity_predicate E P f) (parity_relation E hE P .predicate f)
        (g ↦ subtype_equal Type isProp isprop_isprop (blind_parity_predicate E P f g) (parity_relation E hE P .predicate f g)
          (ua (BlindParityRel E P f g) (ParityRelated E hE P f g) (bridge_def_parity_rel E hE P f g))))

{` The blind quotient (image of the blind predicate) is our quotient. `}
def bridge_def_parity_quotient (E : Type) (hE : IsFinite E) (P : E → BlindBSG2)
  : Id Type (BlindParityQuotient E P) (ParityQuotient E hE P)
  ≔ refl (Image (LocalSections E P) (LocalSections E P → PropTypes)) (bridge_parity_predicate_path E hE P)

{` ---- lem:parityequiv (group.tex:1482). ---- `}
def bridge_lem_parityequiv : blind_lem_parityequiv
  ≔ E P ↦
    let X ≔ E .fst .fst in let hE ≔ E .snd in
    let R ≔ parity_relation X hE P in
    let e ≔ bridge_def_parity_rel X hE P in
    let to ≔ (f g : LocalSections X P) (r : BlindParityRel X P f g) ↦ e f g .map r in
    let from ≔ (f g : LocalSections X P) (r : ParityRelated X hE P f g) ↦
      equiv_inverse_map (BlindParityRel X P f g) (ParityRelated X hE P f g) (e f g) r in
    let Qb ≔ BlindParityQuotient X P in let Qo ≔ ParityQuotient X hE P in
    let c ≔ bridge_def_parity_quotient X hE P in
    (f ↦ from f f (R .reflexive f),
     (f g r ↦ from g f (R .symmetric f g (to f g r)),
      (f g h r s ↦ from f h (R .transitive f g h (to f g r) (to g h s)),
       (ne ↦ trunc_map native_truncation (Id Type (Fin two) Qo) (Id Type (Fin two) Qb)
          (p ↦ concat Type (Fin two) Qo Qb p (inverse Type Qb Qo c)) (parity_quotient_two_element X hE P ne),
        no ↦ mere (Id Type (Fin (suc. zero.)) Qb)
          (inverse Type Qb (Fin (suc. zero.))
            (concat Type Qb Qo (Fin (suc. zero.)) c
              (parity_quotient_empty_one_element X hE P (mere_rec X Empty empty_prop no))))))))

{` ---- def:sign-ordering (group.tex:1581). ---- `}

{` E(A): the blind two-element subsets carry ||Fin 2 = S||, ours ||S = Fin 2||. `}
def bridge_two_subsets_to (A : SetTypes) (e : BlindTwoSubsets A) : TwoSubsets (A .fst)
  ≔ (e .fst, trunc_map native_truncation (Id Type (Fin two) (SubtypeCarrier (A .fst) (e .fst)))
      (Id Type (SubtypeCarrier (A .fst) (e .fst)) (Fin two)) (inverse Type (Fin two) (SubtypeCarrier (A .fst) (e .fst))) (e .snd))

def bridge_two_subsets_from (A : SetTypes) (e : TwoSubsets (A .fst)) : BlindTwoSubsets A
  ≔ (e .fst, two_subset_two_element (A .fst) e)

def bridge_two_subsets_from_to (A : SetTypes) (e : BlindTwoSubsets A)
  : Id (BlindTwoSubsets A) (bridge_two_subsets_from A (bridge_two_subsets_to A e)) e
  ≔ (refl (e .fst), two_element_prop (SubtypeCarrier (A .fst) (e .fst))
      (bridge_two_subsets_from A (bridge_two_subsets_to A e) .snd) (e .snd))

def bridge_two_subsets_to_from (A : SetTypes) (e : TwoSubsets (A .fst))
  : Id (TwoSubsets (A .fst)) (bridge_two_subsets_to A (bridge_two_subsets_from A e)) e
  ≔ (refl (e .fst), mere_isprop (Id Type (SubtypeCarrier (A .fst) (e .fst)) (Fin two))
      (bridge_two_subsets_to A (bridge_two_subsets_from A e) .snd) (e .snd))

def bridge_def_two_subsets (A : SetTypes) : Equiv (BlindTwoSubsets A) (TwoSubsets (A .fst))
  ≔ quasi_inverse_equiv (BlindTwoSubsets A) (TwoSubsets (A .fst)) (bridge_two_subsets_to A) (bridge_two_subsets_from A)
      (bridge_two_subsets_from_to A) (bridge_two_subsets_to_from A)

{` P : E(A) → BΣ_2 agrees with ours along this equivalence. `}
def bridge_def_two_subset_family (A : SetTypes) (e : BlindTwoSubsets A)
  : Id (BookFiniteSetsAt two) (blind_two_subset_family A e) (two_subset_bsigma (A .fst) (A .snd) (bridge_two_subsets_to A e))
  ≔ component_path SetTypes (Fin two, fin_set two) (blind_two_subset_family A e)
      (two_subset_bsigma (A .fst) (A .snd) (bridge_two_subsets_to A e)) (refl (blind_two_subset_family A e .fst))

def bridge_def_local_orderings (A : SetTypes) : Equiv (BlindLocalOrderings A) (LocalOrderings (A .fst) (A .snd))
  ≔ quasi_inverse_equiv (BlindLocalOrderings A) (LocalOrderings (A .fst) (A .snd))
      (w e ↦ w (bridge_two_subsets_from A e)) (w e ↦ w (bridge_two_subsets_to A e))
      (w ↦ funext (BlindTwoSubsets A) (e ↦ SubtypeCarrier (A .fst) (e .fst)) (e ↦ w (bridge_two_subsets_from A (bridge_two_subsets_to A e))) w
        (e ↦ refl w (bridge_two_subsets_from_to A e)))
      (w ↦ funext (TwoSubsets (A .fst)) (e ↦ SubtypeCarrier (A .fst) (e .fst)) (e ↦ w (bridge_two_subsets_to A (bridge_two_subsets_from A e))) w
        (e ↦ refl w (bridge_two_subsets_to_from A e)))

{` Reindexing the parity quotient along an identification of index types. `}
def bridge_pq_reindex_J (E : Type) (E' : Type) (p : Id Type E E')
  : (hE : IsFinite E) (hE' : IsFinite E') (P : E → BookFiniteSetsAt two) (P' : E' → BookFiniteSetsAt two)
    (hom : (e : E) → Id (BookFiniteSetsAt two) (P e) (P' (transport Type (X ↦ X) E E' p e)))
    → Id Type (ParityQuotient E hE P) (ParityQuotient E' hE' P')
  ≔ J Type E (E' p ↦ (hE : IsFinite E) (hE' : IsFinite E') (P : E → BookFiniteSetsAt two) (P' : E' → BookFiniteSetsAt two)
        (hom : (e : E) → Id (BookFiniteSetsAt two) (P e) (P' (transport Type (X ↦ X) E E' p e)))
        → Id Type (ParityQuotient E hE P) (ParityQuotient E' hE' P'))
      (hE hE' P P' hom ↦ refl (ParityQuotient E) (mere_isprop (Σ Nat (n ↦ Id Type E (Fin n))) hE hE')
        (funext E (_ ↦ BookFiniteSetsAt two) P P'
          (e ↦ concat (BookFiniteSetsAt two) (P e) (P' (transport Type (X ↦ X) E E (refl E) e)) (P' e) (hom e)
            (refl P' (transport_refl Type (X ↦ X) E e)))))
      E' p

def bridge_pq_reindex (E E' : Type) (phi : Equiv E E') (hE : IsFinite E) (hE' : IsFinite E')
  (P : E → BookFiniteSetsAt two) (P' : E' → BookFiniteSetsAt two)
  (hom : (e : E) → Id (BookFiniteSetsAt two) (P e) (P' (phi .map e)))
  : Id Type (ParityQuotient E hE P) (ParityQuotient E' hE' P')
  ≔ bridge_pq_reindex_J E E' (ua E E' phi) hE hE' P P' hom

{` Sign orderings: the blind quotient over E(A) is ours. `}
def bridge_def_sign_orderings (A : SetTypes) (fA : IsFinite (A .fst)) (fE : IsFinite (BlindTwoSubsets A))
  : Id Type (BlindSignOrderings A) (SignOrderings (A .fst) (A .snd) fA)
  ≔ concat Type (BlindSignOrderings A) (ParityQuotient (BlindTwoSubsets A) fE (blind_two_subset_family A))
      (SignOrderings (A .fst) (A .snd) fA)
      (bridge_def_parity_quotient (BlindTwoSubsets A) fE (blind_two_subset_family A))
      (bridge_pq_reindex (BlindTwoSubsets A) (TwoSubsets (A .fst)) (bridge_def_two_subsets A) fE (ksubsets_finite (A .fst) fA two)
        (blind_two_subset_family A) (two_subset_bsigma (A .fst) (A .snd)) (bridge_def_two_subset_family A))

{` ---- def:mu_E (group.tex:1554). ---- `}

def bridge_def_group_power (hp : blind_xca_bigproduct_connected) (E : FiniteSets)
  : Id Group (bridge_g (blind_group_power hp E (blind_SG two))) (power_sigma_two (E .fst .fst) (E .snd))
  ≔ let G1 ≔ bridge_g (blind_group_power hp E (blind_SG two)) in let G2 ≔ power_sigma_two (E .fst .fst) (E .snd) in
    (classifying ≔ pcg_witnesses_unique (BG G2 .carrier) (shape G2) (bg_connected G1) (bg_connected G2) (bg_groupoid G1) (bg_groupoid G2))

def bridge_pq_bsigma_path (E E' : Type) (hE : IsFinite E) (hE' : IsFinite E') (P : E → BookFiniteSetsAt two) (P' : E' → BookFiniteSetsAt two)
  (ne : Mere E) (ne' : Mere E') (c : Id Type (ParityQuotient E hE P) (ParityQuotient E' hE' P'))
  : Id (BookFiniteSetsAt two) (parity_quotient_bsigma_two E hE P ne) (parity_quotient_bsigma_two E' hE' P' ne')
  ≔ component_path SetTypes (Fin two, fin_set two) (parity_quotient_bsigma_two E hE P ne) (parity_quotient_bsigma_two E' hE' P' ne')
      (subtype_equal Type isSet isset_isprop (ParityQuotient E hE P, parity_quotient_set E hE P)
        (ParityQuotient E' hE' P', parity_quotient_set E' hE' P') c)

{` The nonempty branch of Bμ_E: the blind quotient, as a point of BΣ_2, is ours. `}
def bridge_def_bmu_nonempty (lem : blind_lem_parityequiv) (E : FiniteSets) (ne : Mere (E .fst .fst)) (P : E .fst .fst → BlindBSG2)
  : Id (BookFiniteSetsAt two) (blind_Bmu_nonempty lem E ne P) (parity_quotient_bsigma_two (E .fst .fst) (E .snd) P ne)
  ≔ component_path SetTypes (Fin two, fin_set two) (blind_Bmu_nonempty lem E ne P) (parity_quotient_bsigma_two (E .fst .fst) (E .snd) P ne)
      (subtype_equal Type isSet isset_isprop (BlindParityQuotient (E .fst .fst) P, blind_parity_quotient_set (E .fst .fst) P)
        (ParityQuotient (E .fst .fst) (E .snd) P, parity_quotient_set (E .fst .fst) (E .snd) P)
        (bridge_def_parity_quotient (E .fst .fst) (E .snd) P))

def bridge_mu_dec_classifying (hp : blind_xca_bigproduct_connected) (lem : blind_lem_parityequiv)
  (ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne) (E : FiniteSets) (d : Decidable (Mere (E .fst .fst)))
  (P : E .fst .fst → BlindBSG2)
  : Id (BookFiniteSetsAt two) (blind_Bhom (blind_group_power hp E (blind_SG two)) (blind_SG two) (blind_mu_E_dec hp lem ptg E d) .fst P)
      (sign_mu_pointed (E .fst .fst) (E .snd) d .fst P)
  ≔ match d [
    | inl. ne ↦ bridge_def_bmu_nonempty lem E ne P
    | inr. _ ↦ refl (shape sign_sigma_two) ]

{` def:mu_E: the classifying map of blind_mu_E is ours. `}
def bridge_def_mu_E (hp : blind_xca_bigproduct_connected) (lem : blind_lem_parityequiv)
  (ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne) (E : FiniteSets) (P : E .fst .fst → BlindBSG2)
  : Id (BookFiniteSetsAt two) (blind_Bhom (blind_group_power hp E (blind_SG two)) (blind_SG two) (blind_mu_E hp lem ptg E) .fst P)
      (sign_mu_classifying (E .fst .fst) (E .snd) P)
  ≔ bridge_mu_dec_classifying hp lem ptg E (finite_inhabited_decidable (E .fst .fst) (E .snd)) P

{` ---- def:sgn (group.tex:1598). ---- `}

def bridge_sgn_E (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) : FiniteSets
  ≔ blind_two_subsets_finite H (A .fst) (blind_bsn_finite n A)

{` Bsgn computed through the variable-decision μ, for any decisions on both sides. `}
def bridge_sgn_K_dec (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n)
  (db : Decidable (Mere (BlindTwoSubsets (A .fst)))) (dw : Decidable (Mere (TwoSubsets (A .fst .fst))))
  : Id (BookFiniteSetsAt two)
      (blind_Bhom (blind_group_power (H .hp) (bridge_sgn_E H n A) (blind_SG two)) (blind_SG two)
        (blind_mu_E_dec (H .hp) (H .lem) (H .ptg) (bridge_sgn_E H n A) db) .fst (blind_two_subset_family (A .fst)))
      (sign_mu_pointed (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A) dw .fst (sign_family n A))
  ≔ let Eb ≔ bridge_sgn_E H n A in
    let Xb ≔ BlindTwoSubsets (A .fst) in let Xw ≔ TwoSubsets (A .fst .fst) in
    let Pb ≔ blind_two_subset_family (A .fst) in let hw ≔ sign_subsets_finite n A in
    match db, dw [
    | inl. nb, inl. nw ↦
        concat (BookFiniteSetsAt two) (blind_Bmu_nonempty (H .lem) Eb nb Pb) (parity_quotient_bsigma_two Xb (Eb .snd) Pb nb)
          (parity_quotient_bsigma_two Xw hw (sign_family n A) nw)
          (bridge_def_bmu_nonempty (H .lem) Eb nb Pb)
          (bridge_pq_bsigma_path Xb Xw (Eb .snd) hw Pb (sign_family n A) nb nw
            (bridge_pq_reindex Xb Xw (bridge_def_two_subsets (A .fst)) (Eb .snd) hw Pb (sign_family n A)
              (bridge_def_two_subset_family (A .fst))))
    | inr. _, inr. _ ↦ refl (shape sign_sigma_two)
    | inl. nb, inr. nw ↦ match nw (trunc_map native_truncation Xb Xw (bridge_two_subsets_to (A .fst)) nb) []
    | inr. nb, inl. nw ↦ match nb (trunc_map native_truncation Xw Xb (bridge_two_subsets_from (A .fst)) nw) [] ]

{` def:sgn: for every H, the blind Bsgn is ours, pointwise. `}
def bridge_sgn_K (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n)
  : Id (BookFiniteSetsAt two) (blind_Bsgn_map H n A) (bsgn n A)
  ≔ bridge_sgn_K_dec H n A (blind_two_subsets_dec n A) (finite_inhabited_decidable (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A))

{` ---- def:sgn-permutation (group.tex:1649). ---- `}

{` Fixed points of the action of a loop of a two-element set versus "moves". `}
def bridge_sg_even_to (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T)
  (h : (x : T .fst .fst) → Id (T .fst .fst) (transport (BookFiniteSetsAt two) (X ↦ X .fst .fst) T T q x) x)
  : Id Bool (two_loop_moves T q) false.
  ≔ let hT ≔ two_set_two_element T in let tq ≔ bsigma_two_transport T T q in
    two_element_point_elim (T .fst .fst) hT (Id Bool (two_loop_moves T q) false.) (bool_set (two_loop_moves T q) false.)
      (x ↦ concat Bool (two_loop_moves T q) (two_differ (T .fst .fst) hT x (tq .map x)) false.
        (two_moves_value (T .fst .fst) hT tq x)
        (two_differ_eq (T .fst .fst) hT x (tq .map x) (inverse (T .fst .fst) (tq .map x) x (h x))))

def bridge_sg_even_from (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T) (e : Id Bool (two_loop_moves T q) false.)
  (x : T .fst .fst) : Id (T .fst .fst) (transport (BookFiniteSetsAt two) (X ↦ X .fst .fst) T T q x) x
  ≔ two_moves_false_fixed (T .fst .fst) (two_set_two_element T) (bsigma_two_transport T T q) e x

def bridge_sg_odd_to (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T)
  (h : (x : T .fst .fst) → Not (Id (T .fst .fst) (transport (BookFiniteSetsAt two) (X ↦ X .fst .fst) T T q x) x))
  : Id Bool (two_loop_moves T q) true.
  ≔ let hT ≔ two_set_two_element T in let tq ≔ bsigma_two_transport T T q in
    two_element_point_elim (T .fst .fst) hT (Id Bool (two_loop_moves T q) true.) (bool_set (two_loop_moves T q) true.)
      (x ↦ concat Bool (two_loop_moves T q) (two_differ (T .fst .fst) hT x (tq .map x)) true.
        (two_moves_value (T .fst .fst) hT tq x)
        (two_differ_ne (T .fst .fst) hT x (tq .map x) (r ↦ h x (inverse (T .fst .fst) x (tq .map x) r))))

def bridge_sg_odd_from (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T) (e : Id Bool (two_loop_moves T q) true.)
  (x : T .fst .fst) : Not (Id (T .fst .fst) (transport (BookFiniteSetsAt two) (X ↦ X .fst .fst) T T q x) x)
  ≔ r ↦ two_moves_true_moved (T .fst .fst) (two_set_two_element T) (bsigma_two_transport T T q) e x
      (inverse (T .fst .fst) (bsigma_two_transport T T q .map x) x r)

def bridge_sg_moves_K (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : Id Bool (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A σ)))
      (two_loop_moves (blind_Bsgn_map H n A) (refl (blind_Bsgn_map H n) (blind_bsgn_loop n A σ)))
  ≔ let f ≔ blind_Bsgn_map H n in
    concat Bool (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A σ)))
      (two_loop_moves (f A) (refl f (permutation_loop n A σ))) (two_loop_moves (f A) (refl f (blind_bsgn_loop n A σ)))
      (two_loop_moves_homotopy (BookFiniteSetsAt n) f (bsgn n) (bridge_sgn_K H n) A (permutation_loop n A σ))
      (refl ((l ↦ two_loop_moves (f A) (refl f l)) : Id (BookFiniteSetsAt n) A A → Bool)
        (inverse (Id (BookFiniteSetsAt n) A A) (blind_bsgn_loop n A σ) (permutation_loop n A σ) (bridge_sg_loop_path n A σ)))

def bridge_perm_even_prop (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : isProp (BlindPermEven H n A σ)
  ≔ let T ≔ blind_Bsgn_map H n A in
    pi_prop (T .fst .fst) (x ↦ Id (T .fst .fst) (blind_sgn_action H n A σ x) x)
      (x ↦ T .fst .snd (blind_sgn_action H n A σ x) x)

def bridge_perm_odd_prop (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : isProp (BlindPermOdd H n A σ)
  ≔ let T ≔ blind_Bsgn_map H n A in
    pi_prop (T .fst .fst) (x ↦ Not (Id (T .fst .fst) (blind_sgn_action H n A σ x) x))
      (x ↦ negation_prop (Id (T .fst .fst) (blind_sgn_action H n A σ x) x))

{` def:sgn-permutation: blind even/odd is our sign ±1. `}
def bridge_def_perm_even (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : Equiv (BlindPermEven H n A σ) (Id Sign (permutation_sign_at n A σ) plus.)
  ≔ let T ≔ blind_Bsgn_map H n A in let q ≔ refl (blind_Bsgn_map H n) (blind_bsgn_loop n A σ) in
    let mo ≔ two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A σ)) in
    let mb ≔ two_loop_moves T q in
    iff_equiv (BlindPermEven H n A σ) (Id Sign (permutation_sign_at n A σ) plus.) (bridge_perm_even_prop H n A σ)
      (sign_set (permutation_sign_at n A σ) plus.)
      (r ↦ concat Sign (permutation_sign_at n A σ) (bool_sign mo) plus.
        (inverse Sign (bool_sign mo) (permutation_sign_at n A σ) (permutation_sign_at_moves n A σ))
        (refl bool_sign (concat Bool mo mb false. (bridge_sg_moves_K H n A σ) (bridge_sg_even_to T q r))))
      (s ↦ bridge_sg_even_from T q
        (concat Bool mb mo false. (inverse Bool mo mb (bridge_sg_moves_K H n A σ))
          (bool_sign_injective mo false. (concat Sign (bool_sign mo) (permutation_sign_at n A σ) plus. (permutation_sign_at_moves n A σ) s))))

def bridge_def_perm_odd (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : Equiv (BlindPermOdd H n A σ) (Id Sign (permutation_sign_at n A σ) minus.)
  ≔ let T ≔ blind_Bsgn_map H n A in let q ≔ refl (blind_Bsgn_map H n) (blind_bsgn_loop n A σ) in
    let mo ≔ two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A σ)) in
    let mb ≔ two_loop_moves T q in
    iff_equiv (BlindPermOdd H n A σ) (Id Sign (permutation_sign_at n A σ) minus.) (bridge_perm_odd_prop H n A σ)
      (sign_set (permutation_sign_at n A σ) minus.)
      (r ↦ concat Sign (permutation_sign_at n A σ) (bool_sign mo) minus.
        (inverse Sign (bool_sign mo) (permutation_sign_at n A σ) (permutation_sign_at_moves n A σ))
        (refl bool_sign (concat Bool mo mb true. (bridge_sg_moves_K H n A σ) (bridge_sg_odd_to T q r))))
      (s ↦ bridge_sg_odd_from T q
        (concat Bool mb mo true. (inverse Bool mo mb (bridge_sg_moves_K H n A σ))
          (bool_sign_injective mo true. (concat Sign (bool_sign mo) (permutation_sign_at n A σ) minus. (permutation_sign_at_moves n A σ) s))))

def bridge_perm_even_from_sign (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  (s : Id Sign (permutation_sign_at n A σ) plus.) : BlindPermEven H n A σ
  ≔ equiv_inverse_map (BlindPermEven H n A σ) (Id Sign (permutation_sign_at n A σ) plus.) (bridge_def_perm_even H n A σ) s

def bridge_perm_odd_from_sign (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  (s : Id Sign (permutation_sign_at n A σ) minus.) : BlindPermOdd H n A σ
  ≔ equiv_inverse_map (BlindPermOdd H n A σ) (Id Sign (permutation_sign_at n A σ) minus.) (bridge_def_perm_odd H n A σ) s

{` ---- lem:sign-properties (group.tex:1675). ---- `}

{` (1). `}
def bridge_lem_sign_transposition : blind_lem_sign_transposition
  ≔ H n A d a b nab ↦ bridge_perm_odd_from_sign H n A (transposition_equiv (A .fst .fst) d a b)
      (bsigma_transposition_sign n A d a b nab)

{` (2): a k-cycle, k = j+2, has sign (−1)^(j+1). `}
def bridge_sg_cycle_sign (n : Nat) (A : BlindBSGn n) (j : Nat) (σ : Equiv (A .fst .fst) (A .fst .fst)) (kc : IsKCycle (A .fst .fst) j σ)
  : Id Sign (permutation_sign_at n A σ) (bool_sign (nat_odd (suc. j)))
  ≔ let X ≔ A .fst .fst in
    let d ≔ finite_decidable_equality X (bsigma_finite n A) in
    let S ≔ Σ (CycleNotationLists X j) (l ↦ Id (Equiv X X) (cycle_notation_list_equiv X d j l) σ) in
    mere_rec S (Id Sign (permutation_sign_at n A σ) (bool_sign (nat_odd (suc. j))))
      (sign_set (permutation_sign_at n A σ) (bool_sign (nat_odd (suc. j))))
      (u ↦ calc permutation_sign_at n A σ
          = permutation_sign_at n A (cycle_notation_list_equiv X d j (u .fst))
            by refl (permutation_sign_at n A) (inverse (Equiv X X) (cycle_notation_list_equiv X d j (u .fst)) σ (u .snd))
        = bool_sign (nat_odd (length X (u .fst .snd .fst)))
            by cycle_sign_at n A d (u .fst .fst) (u .fst .snd .fst) (u .fst .snd .snd .snd)
        = bool_sign (nat_odd (suc. j))
            by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (u .fst .snd .snd .fst) ∎)
      (is_kcycle_cycle_notation_equiv X (A .fst .snd) d j σ .map kc)

def bridge_lem_sign_cycle : blind_lem_sign_cycle
  ≔ H n A j σ kc ↦
    let cs ≔ bridge_sg_cycle_sign n A j σ kc in
    (q ↦ bridge_perm_even_from_sign H n A σ
        (concat Sign (permutation_sign_at n A σ) (bool_sign (nat_odd (suc. j))) plus. cs
          (refl bool_sign (bool_not_true_false (nat_odd (suc. j)) (bridge_nat_even_false_to (suc. (suc. j)) q)))),
     q ↦ bridge_perm_odd_from_sign H n A σ
        (concat Sign (permutation_sign_at n A σ) (bool_sign (nat_odd (suc. j))) minus. cs
          (refl bool_sign (bool_not_false_true (nat_odd (suc. j)) (bridge_nat_even_true_to (suc. (suc. j)) q)))))

{` (3) bridged . `}
def bridge_lem_sign_identity_even : blind_lem_sign_identity_even
  ≔ A hA d w h ↦
    let FA : FiniteSets ≔ ((A, finite_sethood A hA), hA) in
    bridge_nat_even_true_from (length (Transpositions A) w)
      (is_even_nat_iff (length (Transpositions A) w) .map
        (identity_word_even FA d w (x ↦ inverse A (transposition_word_map A d w x) x (h (refl x)))))

{` ---- cor:sign-defined (group.tex:1703). ---- `}

def bridge_sg_word_sign (n : Nat) (A : BlindBSGn n) (d : DecidableEquality (A .fst .fst)) (σ : Equiv (A .fst .fst) (A .fst .fst))
  (w : List (Transpositions (A .fst .fst)))
  (hw : Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d w) (σ .map))
  : Id Sign (permutation_sign_at n A σ) (bool_sign (nat_odd (length (Transpositions (A .fst .fst)) w)))
  ≔ let X ≔ A .fst .fst in
    concat Sign (permutation_sign_at n A σ) (permutation_sign_at n A (transposition_word_equiv X d w))
      (bool_sign (nat_odd (length (Transpositions X) w)))
      (permutation_sign_at_homotopy n A σ (transposition_word_equiv X d w)
        (x ↦ concat X (σ .map x) (transposition_word_map X d w x) (transposition_word_equiv X d w .map x)
          (inverse X (transposition_word_map X d w x) (σ .map x) (hw (refl x)))
          (inverse X (transposition_word_equiv X d w .map x) (transposition_word_map X d w x) (transposition_word_equiv_map X d w x))))
      (transposition_word_sign n A d w)

{` The parity part, with no condition. `}
def bridge_cor_sign_defined_parity (n : Nat) (A : BlindBSGn n) (d : DecidableEquality (A .fst .fst))
  (σ : Equiv (A .fst .fst) (A .fst .fst)) (w v : List (Transpositions (A .fst .fst)))
  (hw : Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d w) (σ .map))
  (hv : Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d v) (σ .map))
  : Id Bool (blind_nat_even (length (Transpositions (A .fst .fst)) w)) (blind_nat_even (length (Transpositions (A .fst .fst)) v))
  ≔ let X ≔ A .fst .fst in let lw ≔ length (Transpositions X) w in let lv ≔ length (Transpositions X) v in
    calc blind_nat_even lw = bool_not (nat_odd lw) by bridge_nat_even_odd lw
      = bool_not (nat_odd lv)
        by refl bool_not (sign_defined_parity (A .fst, bsigma_finite n A) d σ w v
          (x ↦ inverse X (transposition_word_map X d w x) (σ .map x) (hw (refl x)))
          (x ↦ inverse X (transposition_word_map X d v x) (σ .map x) (hv (refl x))))
      = blind_nat_even lv by inverse Bool (blind_nat_even lv) (bool_not (nat_odd lv)) (bridge_nat_even_odd lv) ∎

def bridge_cor_sign_defined : blind_cor_sign_defined
  ≔ H n A d σ w v hw hv ↦
    let X ≔ A .fst .fst in let lw ≔ length (Transpositions X) w in
    let ws ≔ bridge_sg_word_sign n A d σ w hw in
    (bridge_cor_sign_defined_parity n A d σ w v hw hv,
     (q ↦ bridge_perm_even_from_sign H n A σ
        (concat Sign (permutation_sign_at n A σ) (bool_sign (nat_odd lw)) plus. ws (refl bool_sign (bridge_nat_even_true_to lw q))),
      q ↦ bridge_perm_odd_from_sign H n A σ
        (concat Sign (permutation_sign_at n A σ) (bool_sign (nat_odd lw)) minus. ws (refl bool_sign (bridge_nat_even_false_to lw q)))))

{` ---- xca:sign-by-crossings (group.tex:1729). ---- `}

{` blind_fin_val orders Fin n in reverse: i <_blind j iff j < i for fin_lt. `}
def bridge_fin_val_bound (m : Nat) (y : Fin m) : Lt (blind_fin_val m y) m
  ≔ match m [
  | zero. ↦ match y []
  | suc. k ↦ match y [
    | inl. y' ↦ le_step (suc. (blind_fin_val k y')) k (bridge_fin_val_bound k y')
    | inr. _ ↦ le_refl (suc. k) ] ]

def bridge_fin_val_lt_to (n : Nat) : (i j : Fin n) → Lt (blind_fin_val n i) (blind_fin_val n j) → Id Bool (fin_lt n j i) true.
  ≔ match n [
  | zero. ↦ i _ _ ↦ match i []
  | suc. m ↦ i j h ↦ match i, j [
    | inr. _, inr. _ ↦ match lt_irrefl m h []
    | inr. _, inl. b ↦ match lt_asym m (blind_fin_val m b) h (bridge_fin_val_bound m b) []
    | inl. _, inr. _ ↦ refl (true. : Bool)
    | inl. a, inl. b ↦ bridge_fin_val_lt_to m a b h ] ]

def bridge_fin_val_lt_from (n : Nat) : (i j : Fin n) → Id Bool (fin_lt n j i) true. → Lt (blind_fin_val n i) (blind_fin_val n j)
  ≔ match n [
  | zero. ↦ i _ _ ↦ match i []
  | suc. m ↦ i j h ↦ match i, j [
    | inr. _, inr. _ ↦ match bool_encode false. true. h []
    | inr. _, inl. _ ↦ match bool_encode false. true. h []
    | inl. a, inr. _ ↦ bridge_fin_val_bound m a
    | inl. a, inl. b ↦ bridge_fin_val_lt_from m a b h ] ]

def bridge_fin_val_book_lt (n : Nat) (i j : Fin n)
  : Equiv (BookLt (blind_fin_val n i) (blind_fin_val n j)) (Id Bool (fin_lt n j i) true.)
  ≔ iff_equiv (BookLt (blind_fin_val n i) (blind_fin_val n j)) (Id Bool (fin_lt n j i) true.)
      (book_lt_prop (blind_fin_val n i) (blind_fin_val n j)) (bool_set (fin_lt n j i) true.)
      (b ↦ bridge_fin_val_lt_to n i j (lt_from_book (blind_fin_val n i) (blind_fin_val n j) b))
      (q ↦ lt_to_book (blind_fin_val n i) (blind_fin_val n j) (bridge_fin_val_lt_from n i j q))

{` The blind inversions (i, j) correspond to our inversions (j, i). `}
def bridge_def_inversions (n : Nat) (σ : Equiv (Fin n) (Fin n)) : Equiv (BlindInversions n σ) (Inversions n σ)
  ≔ let L ≔ bridge_fin_val_book_lt n in
    let s ≔ σ .map in
    quasi_inverse_equiv (BlindInversions n σ) (Inversions n σ)
      (u ↦ ((u .snd .fst, u .fst),
        (L (u .fst) (u .snd .fst) .map (u .snd .snd .fst), L (s (u .snd .fst)) (s (u .fst)) .map (u .snd .snd .snd))))
      (v ↦ (v .fst .snd, (v .fst .fst,
        (equiv_inverse_map (BookLt (blind_fin_val n (v .fst .snd)) (blind_fin_val n (v .fst .fst))) (Id Bool (fin_lt n (v .fst .fst) (v .fst .snd)) true.)
          (L (v .fst .snd) (v .fst .fst)) (v .snd .fst),
         equiv_inverse_map (BookLt (blind_fin_val n (s (v .fst .fst))) (blind_fin_val n (s (v .fst .snd))))
          (Id Bool (fin_lt n (s (v .fst .snd)) (s (v .fst .fst))) true.)
          (L (s (v .fst .fst)) (s (v .fst .snd))) (v .snd .snd)))))
      (u ↦ let i ≔ u .fst in let j ≔ u .snd .fst in
        let B1 ≔ BookLt (blind_fin_val n i) (blind_fin_val n j) in
        let B2 ≔ BookLt (blind_fin_val n (s j)) (blind_fin_val n (s i)) in
        (refl i, (refl j,
          (book_lt_prop (blind_fin_val n i) (blind_fin_val n j)
             (equiv_inverse_map B1 (Id Bool (fin_lt n j i) true.) (L i j) (L i j .map (u .snd .snd .fst))) (u .snd .snd .fst),
           book_lt_prop (blind_fin_val n (s j)) (blind_fin_val n (s i))
             (equiv_inverse_map B2 (Id Bool (fin_lt n (s i) (s j)) true.) (L (s j) (s i)) (L (s j) (s i) .map (u .snd .snd .snd)))
             (u .snd .snd .snd)))))
      (v ↦ let j ≔ v .fst .fst in let i ≔ v .fst .snd in
        let B1 ≔ BookLt (blind_fin_val n i) (blind_fin_val n j) in
        let B2 ≔ BookLt (blind_fin_val n (s j)) (blind_fin_val n (s i)) in
        ((refl j, refl i),
          (bool_set (fin_lt n j i) true. (L i j .map (equiv_inverse_map B1 (Id Bool (fin_lt n j i) true.) (L i j) (v .snd .fst))) (v .snd .fst),
           bool_set (fin_lt n (s i) (s j)) true.
             (L (s j) (s i) .map (equiv_inverse_map B2 (Id Bool (fin_lt n (s i) (s j)) true.) (L (s j) (s i)) (v .snd .snd)))
             (v .snd .snd))))

def bridge_xca_sign_by_crossings : blind_xca_sign_by_crossings
  ≔ H n σ k m ↦
    let pt ≔ standard_shape n in
    let ck : Id Nat (inversion_count n σ) k
      ≔ bridge_card_from_mere (Inversions n σ) (inversions_finite n σ) k
          (trunc_map native_truncation (Id Type (BlindInversions n σ) (Fin k)) (Id Type (Inversions n σ) (Fin k))
            (p ↦ concat Type (Inversions n σ) (BlindInversions n σ) (Fin k)
              (inverse Type (BlindInversions n σ) (Inversions n σ) (ua (BlindInversions n σ) (Inversions n σ) (bridge_def_inversions n σ))) p)
            m) in
    let sg : Id Sign (permutation_sign_at n pt σ) (bool_sign (nat_odd k))
      ≔ concat Sign (permutation_sign_at n pt σ) (bool_sign (nat_odd (inversion_count n σ))) (bool_sign (nat_odd k))
          (permutation_sign_at_inversions n σ) (refl ((x ↦ bool_sign (nat_odd x)) : Nat → Sign) ck) in
    (r ↦ bridge_nat_even_true_from k
        (bool_sign_injective (nat_odd k) false.
          (concat Sign (bool_sign (nat_odd k)) (permutation_sign_at n pt σ) plus.
            (inverse Sign (permutation_sign_at n pt σ) (bool_sign (nat_odd k)) sg)
            (bridge_def_perm_even H n pt σ .map r))),
     q ↦ bridge_perm_even_from_sign H n pt σ
        (concat Sign (permutation_sign_at n pt σ) (bool_sign (nat_odd k)) plus. sg (refl bool_sign (bridge_nat_even_true_to k q))))

{` ---- the exercise at group.tex:1779 (n!/2 even permutations). ---- `}

def bridge_fin_two_product_to (S : Type) (a : Fin two) (s : S) : Sum S S
  ≔ match a [ inr. _ ↦ inl. s | inl. (inr. _) ↦ inr. s | inl. (inl. e) ↦ match e [] ]

def bridge_fin_two_product_from (S : Type) : Sum S S → Product (Fin two) S
  ≔ [ inl. s ↦ (inr. star., s) | inr. s ↦ (inl. (inr. star.), s) ]

def bridge_fin_two_product_rt (S : Type) (a : Fin two) (s : S)
  : Id (Product (Fin two) S) (bridge_fin_two_product_from S (bridge_fin_two_product_to S a s)) (a, s)
  ≔ match a [
  | inr. x ↦ (inr. (unit_prop star. x), refl s)
  | inl. (inr. x) ↦ (inl. (inr. (unit_prop star. x)), refl s)
  | inl. (inl. e) ↦ match e [] ]

def bridge_fin_two_product_sum (S : Type) : Equiv (Product (Fin two) S) (Sum S S)
  ≔ quasi_inverse_equiv (Product (Fin two) S) (Sum S S) (u ↦ bridge_fin_two_product_to S (u .fst) (u .snd))
      (bridge_fin_two_product_from S) (u ↦ bridge_fin_two_product_rt S (u .fst) (u .snd))
      [ inl. s ↦ refl (inl. s : Sum S S) | inr. s ↦ refl (inr. s : Sum S S) ]

def bridge_xca_even_count : blind_xca_even_count
  ≔ H n ↦
    let m : Nat ≔ suc. (suc. n) in let pt ≔ standard_shape m in
    let Sb ≔ Σ (Equiv (Fin m) (Fin m)) (BlindPermEven H m pt) in
    let So ≔ EvenPermutations m in
    let hO ≔ signed_permutations_finite m plus. in
    let hS ≔ finite_sum So So hO hO in
    let pS : Id Type Sb So
      ≔ ua Sb So (family_equiv (Equiv (Fin m) (Fin m)) (BlindPermEven H m pt) (s ↦ Id Sign (permutation_sign_at m pt s) plus.)
          (s ↦ bridge_def_perm_even H m pt s)) in
    let cnt : Id Nat (cardinality (Sum So So) hS) (factorial m)
      ≔ concat Nat (cardinality (Sum So So) hS) (add (even_permutations_count m) (even_permutations_count m)) (factorial m)
          (cardinality_sum So So hO hO hS) (even_permutations_half n) in
    trunc_map native_truncation (Id Type (Sum So So) (Fin (cardinality (Sum So So) hS))) (Id Type (Product (Fin two) Sb) (Fin (factorial m)))
      (p ↦ concat Type (Product (Fin two) Sb) (Product (Fin two) So) (Fin (factorial m)) (refl (Product (Fin two)) pS)
        (concat Type (Product (Fin two) So) (Sum So So) (Fin (factorial m))
          (ua (Product (Fin two) So) (Sum So So) (bridge_fin_two_product_sum So))
          (concat Type (Sum So So) (Fin (cardinality (Sum So So) hS)) (Fin (factorial m)) p (refl Fin cnt))))
      (cardinality_spec (Sum So So) hS)

{` ---- def:sgn continued: USym sgn. ---- `}

{` The sign of the image of a loop under a pointed map into BΣ_2 depends only
   on the underlying map (the pointing conjugates, and Σ_2 is abelian). `}
def bridge_sg_loops_sign (X : Pointed) (k1 k2 : BookPointedMap X (BG sign_sigma_two))
  (K : (x : X .carrier) → Id (BookFiniteSetsAt two) (k1 .fst x) (k2 .fst x)) (l : Loop X)
  : Id Sign (sigma_two_sign (loops_map X (BG sign_sigma_two) k1 l)) (sigma_two_sign (loops_map X (BG sign_sigma_two) k2 l))
  ≔ let x0 ≔ X .point in
    calc sigma_two_sign (loops_map X (BG sign_sigma_two) k1 l)
      = two_loop_sign (k1 .fst x0) (refl (k1 .fst) l)
        by two_loop_sign_conjugate (shape sign_sigma_two) (k1 .fst x0) (k1 .snd) (refl (k1 .fst) l)
      = two_loop_sign (k2 .fst x0) (refl (k2 .fst) l)
        by refl bool_sign (inverse Bool (two_loop_moves (k2 .fst x0) (refl (k2 .fst) l)) (two_loop_moves (k1 .fst x0) (refl (k1 .fst) l))
          (two_loop_moves_homotopy (X .carrier) (k1 .fst) (k2 .fst) K x0 l))
      = sigma_two_sign (loops_map X (BG sign_sigma_two) k2 l)
        by inverse Sign (sigma_two_sign (loops_map X (BG sign_sigma_two) k2 l)) (two_loop_sign (k2 .fst x0) (refl (k2 .fst) l))
          (two_loop_sign_conjugate (shape sign_sigma_two) (k2 .fst x0) (k2 .snd) (refl (k2 .fst) l)) ∎

def bridge_def_sgn_usym (H : BlindSignHyps) (n : Nat) (g : USym (symmetric_group n))
  : Id Sign (sigma_two_sign (blind_usym_hom (blind_SG n) (blind_SG two) (blind_sgn H n) g)) (sigma_two_sign (usgn n g))
  ≔ concat Sign (sigma_two_sign (blind_usym_hom (blind_SG n) (blind_SG two) (blind_sgn H n) g))
      (sigma_two_sign (loops_map (BG (symmetric_group n)) (BG sign_sigma_two) (blind_Bsgn_map H n, blind_Bsgn_pt H n) g))
      (sigma_two_sign (usgn n g))
      (refl sigma_two_sign (bridge_usym_hom (blind_SG n) (blind_SG two) (blind_sgn H n) g))
      (bridge_sg_loops_sign (BG (symmetric_group n)) (blind_Bsgn_map H n, blind_Bsgn_pt H n) (bsgn_pointed n) (bridge_sgn_K H n) g)

{` ---- def:alternating-groups (group.tex:1614). ---- `}

def bridge_alt_groupoid (H : BlindSignHyps) (n : Nat) : isGroupoid (BlindAltCarrier H n)
  ≔ hlevel_to_groupoid (BlindAltCarrier H n)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (BookFiniteSetsAt n) (A ↦ blind_Bsgn_map H n A .fst .fst)
        (groupoid_to_hlevel (BookFiniteSetsAt n) (bg_groupoid (symmetric_group n)))
        (A ↦ groupoid_to_hlevel (blind_Bsgn_map H n A .fst .fst)
          (set_is_groupoid (blind_Bsgn_map H n A .fst .fst) (blind_Bsgn_map H n A .fst .snd))))

{` For n ≤ 1, BΣ_n has an actual path from every point to the shape. `}
def bridge_small_center (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (A : BookFiniteSetsAt n)
  : Id (BookFiniteSetsAt n) A (standard_shape n)
  ≔ let pt ≔ standard_shape n in
    mere_rec (Id SetTypes (Fin n, fin_set n) (A .fst)) (Id (BookFiniteSetsAt n) A pt)
      (q r ↦ bsigma_path_ext n A pt q r (x ↦ fin_small_isprop n hn (q .fst .fst .trr x) (r .fst .fst .trr x)))
      (p ↦ inverse (BookFiniteSetsAt n) pt A (component_path SetTypes (Fin n, fin_set n) pt A p))
      (A .snd)

{` For n ≤ 1 the blind total type is not connected, for every H (no condition):
   Bsgn(pt) has two elements and they lie in different components. `}
def bridge_alt_small_not_connected (H : BlindSignHyps) (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.)))
  (c : Connected (BlindAltCarrier H n)) : Empty
  ≔ let f ≔ blind_Bsgn_map H n in let pt ≔ standard_shape n in
    let T ≔ f pt in let hT ≔ two_set_two_element T in
    let F : BlindAltCarrier H n → T .fst .fst
      ≔ u ↦ bsigma_two_transport (f (u .fst)) T (refl f (bridge_small_center n hn (u .fst))) .map (u .snd) in
    two_element_point_elim (T .fst .fst) hT Empty empty_prop
      (s0 ↦ let s1 ≔ two_element_other (T .fst .fst) hT s0 in
        mere_rec (Id (BlindAltCarrier H n) (pt, s0) (pt, s1)) Empty empty_prop
          (p ↦ two_element_other_ne (T .fst .fst) hT s0
            (inverse (T .fst .fst) s0 s1
              (equiv_injective_path (T .fst .fst) (T .fst .fst) (bsigma_two_transport T T (refl f (bridge_small_center n hn pt)))
                s0 s1 (refl F p))))
          (c .snd (pt, s0) (pt, s1)))

def bridge_alt_small_disconnected : blind_alt_small_disconnected
  ≔ H ↦ (c ↦ bridge_alt_small_not_connected H zero. (inl. (refl (zero. : Nat))) c,
         c ↦ bridge_alt_small_not_connected H (suc. zero.) (inr. (refl (suc. zero. : Nat))) c)

{` The blind total type is our AlternatingShapes. `}
def bridge_alt_carrier_path (H : BlindSignHyps) (n : Nat)
  : Id Type (BlindAltCarrier H n) (AlternatingShapes n)
  ≔ refl ((h ↦ Σ (BookFiniteSetsAt n) (A ↦ h A .fst .fst)) : (BookFiniteSetsAt n → BookFiniteSetsAt two) → Type)
      (funext (BookFiniteSetsAt n) (_ ↦ BookFiniteSetsAt two) (blind_Bsgn_map H n) (bsgn n) (bridge_sgn_K H n))

def bridge_alt_ptconn : blind_alt_ptconn
  ≔ H n ↦ (transport Type Connected (AlternatingShapes (suc. (suc. n))) (BlindAltCarrier H (suc. (suc. n)))
            (inverse Type (BlindAltCarrier H (suc. (suc. n))) (AlternatingShapes (suc. (suc. n))) (bridge_alt_carrier_path H (suc. (suc. n))))
            (alternating_shapes_connected n),
           bridge_alt_groupoid H (suc. (suc. n)))

{` ---- xca after def:mu_E (group.tex:1570). ---- `}

def bridge_sg_minus_of_ne_at (l : USym sign_sigma_two) (n : Not (Id (USym sign_sigma_two) l (refl (shape sign_sigma_two))))
  (v : Sign) (q : Id Sign (sigma_two_sign l) v) : Id Bool (sign_is_minus (sigma_two_sign l)) true.
  ≔ match v [
  | plus. ↦ match n (equiv_injective_path (USym sign_sigma_two) Sign sigma_two_sign_equiv l (refl (shape sign_sigma_two))
        (concat Sign (sigma_two_sign l) plus. (sigma_two_sign (refl (shape sign_sigma_two))) q
          (inverse Sign (sigma_two_sign (refl (shape sign_sigma_two))) plus. sigma_two_sign_unit))) []
  | minus. ↦ refl sign_is_minus q ]

def bridge_sg_ne_iff_minus (l : USym sign_sigma_two)
  : Equiv (Not (Id (USym sign_sigma_two) l (refl (shape sign_sigma_two)))) (Id Bool (sign_is_minus (sigma_two_sign l)) true.)
  ≔ iff_equiv (Not (Id (USym sign_sigma_two) l (refl (shape sign_sigma_two)))) (Id Bool (sign_is_minus (sigma_two_sign l)) true.)
      (negation_prop (Id (USym sign_sigma_two) l (refl (shape sign_sigma_two)))) (bool_set (sign_is_minus (sigma_two_sign l)) true.)
      (n ↦ bridge_sg_minus_of_ne_at l n (sigma_two_sign l) (refl (sigma_two_sign l)))
      (q r ↦ bool_encode false. true.
        (calc (false. : Bool) = sign_is_minus (sigma_two_sign (refl (shape sign_sigma_two)))
            by refl sign_is_minus (inverse Sign (sigma_two_sign (refl (shape sign_sigma_two))) plus. sigma_two_sign_unit)
          = sign_is_minus (sigma_two_sign l)
            by refl ((m ↦ sign_is_minus (sigma_two_sign m)) : USym sign_sigma_two → Bool)
              (inverse (USym sign_sigma_two) l (refl (shape sign_sigma_two)) r)
          = true. by q ∎))

def bridge_xca_mu_product : blind_xca_mu_product
  ≔ hp lem ptg E s ↦
    let X ≔ E .fst .fst in let hE ≔ E .snd in
    let B2 ≔ BookFiniteSetsAt two in
    let c : X → B2 ≔ _ ↦ blind_bsg2_pt in
    let G ≔ blind_group_power hp E (blind_SG two) in
    let g ≔ funext X (_ ↦ B2) c c s in
    let ub ≔ blind_usym_hom G (blind_SG two) (blind_mu_E hp lem ptg E) g in
    let pt ≔ shape sign_sigma_two in
    let S ≔ Σ X (e ↦ Not (Id (USym sign_sigma_two) (s e) (refl pt))) in
    let b : X → Bool ≔ e ↦ sign_is_minus (sigma_two_sign (s e)) in
    let T ≔ Σ X (e ↦ Id Bool (b e) true.) in
    let eST ≔ family_equiv X (e ↦ Not (Id (USym sign_sigma_two) (s e) (refl pt))) (e ↦ Id Bool (b e) true.)
      (e ↦ bridge_sg_ne_iff_minus (s e)) in
    let hT ≔ finite_true_subset X hE b in
    let hS ≔ finite_of_equiv S T eST hT in
    let cnt : Id Nat (cardinality S hS) (finite_true_count X hE b) ≔ cardinality_equiv S T eST hS hT in
    let sg : Id Sign (sigma_two_sign ub) (bool_sign (nat_odd (finite_true_count X hE b)))
      ≔ calc sigma_two_sign ub
          = sigma_two_sign (loops_map (BG (power_sigma_two X hE)) (BG sign_sigma_two)
              (blind_Bhom G (blind_SG two) (blind_mu_E hp lem ptg E)) g)
            by refl sigma_two_sign (bridge_usym_hom G (blind_SG two) (blind_mu_E hp lem ptg E) g)
          = sigma_two_sign (usym_hom (power_sigma_two X hE) sign_sigma_two (sign_mu X hE) g)
            by bridge_sg_loops_sign (BG (power_sigma_two X hE)) (blind_Bhom G (blind_SG two) (blind_mu_E hp lem ptg E))
              (sign_mu_pointed X hE (finite_inhabited_decidable X hE)) (bridge_def_mu_E hp lem ptg E) g
          = sign_product X hE (e ↦ sigma_two_sign (power_sigma_two_component X hE g e)) by sign_mu_usym_product X hE g
          = bool_sign (nat_odd (finite_true_count X hE b))
            by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign)
              (finite_true_count_homotopy X hE (e ↦ sign_is_minus (sigma_two_sign (power_sigma_two_component X hE g e))) b
                (e ↦ refl ((m ↦ sign_is_minus (sigma_two_sign m)) : USym sign_sigma_two → Bool)
                  (inverse (USym sign_sigma_two) (s e) (g (refl e)) (funext_beta X (_ ↦ B2) c c s e)))) ∎ in
    (r ↦ equiv_inverse_map (BlindEvenCard S) (IsEvenNat (cardinality S hS)) (bridge_def_even_card S hS)
        (equiv_inverse_map (IsEvenNat (cardinality S hS)) (Id Bool (nat_odd (cardinality S hS)) false.) (is_even_nat_iff (cardinality S hS))
          (concat Bool (nat_odd (cardinality S hS)) (nat_odd (finite_true_count X hE b)) false. (refl nat_odd cnt)
            (bool_sign_injective (nat_odd (finite_true_count X hE b)) false.
              (calc bool_sign (nat_odd (finite_true_count X hE b)) = sigma_two_sign ub
                  by inverse Sign (sigma_two_sign ub) (bool_sign (nat_odd (finite_true_count X hE b))) sg
                = sigma_two_sign (refl pt) by refl sigma_two_sign r
                = plus. by sigma_two_sign_unit ∎)))),
     ev ↦ equiv_injective_path (USym sign_sigma_two) Sign sigma_two_sign_equiv ub (refl pt)
        (calc sigma_two_sign ub = bool_sign (nat_odd (finite_true_count X hE b)) by sg
          = bool_sign (nat_odd (cardinality S hS))
            by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inverse Nat (cardinality S hS) (finite_true_count X hE b) cnt)
          = plus. by refl bool_sign (is_even_nat_iff (cardinality S hS) .map (bridge_def_even_card S hS .map ev))
          = sigma_two_sign (refl pt) by inverse Sign (sigma_two_sign (refl pt)) plus. sigma_two_sign_unit ∎))

{` ---- xca:isos_A3_C3 (group.tex:1631). ---- `}

{` The fiberwise identification of the blind total type with AlternatingShapes. `}
def bridge_alt_map (H : BlindSignHyps) (n : Nat) (u : BlindAltCarrier H n) : AlternatingShapes n
  ≔ (u .fst, bsigma_two_transport (blind_Bsgn_map H n (u .fst)) (bsgn n (u .fst)) (bridge_sgn_K H n (u .fst)) .map (u .snd))

def bridge_alt_map_equiv (H : BlindSignHyps) (n : Nat) : Equiv (BlindAltCarrier H n) (AlternatingShapes n)
  ≔ let t ≔ (A : BookFiniteSetsAt n) ↦ bsigma_two_transport (blind_Bsgn_map H n A) (bsgn n A) (bridge_sgn_K H n A) in
    quasi_inverse_equiv (BlindAltCarrier H n) (AlternatingShapes n) (bridge_alt_map H n)
      (v ↦ (v .fst, equiv_inverse_map (blind_Bsgn_map H n (v .fst) .fst .fst) (bsgn n (v .fst) .fst .fst) (t (v .fst)) (v .snd)))
      (u ↦ (refl (u .fst), inverse (blind_Bsgn_map H n (u .fst) .fst .fst) (u .snd)
          (equiv_inverse_map (blind_Bsgn_map H n (u .fst) .fst .fst) (bsgn n (u .fst) .fst .fst) (t (u .fst)) (t (u .fst) .map (u .snd)))
          (equiv_unit (blind_Bsgn_map H n (u .fst) .fst .fst) (bsgn n (u .fst) .fst .fst) (t (u .fst)) (u .snd))))
      (v ↦ (refl (v .fst), equiv_counit (blind_Bsgn_map H n (v .fst) .fst .fst) (bsgn n (v .fst) .fst .fst) (t (v .fst)) (v .snd)))

{` The blind A_3 is our A_3 (any designated point of the fiber over the shape
   is joined to ours, using the transposition loop if necessary). `}
def bridge_alt_three_path (H : BlindSignHyps) (h : BlindAltPtConn H blind_three)
  : Id Group (bridge_g (blind_AG H blind_three h)) a3_group
  ≔ let u ≔ bridge_alt_map H three (blind_alt_shape H three) in
    let pt ≔ standard_shape three in
    let F : BookFiniteSetsAt three → Type ≔ A ↦ bsgn three A .fst .fst in
    group_path_from_pointed_equiv (bridge_g (blind_AG H blind_three h)) a3_group
      ((bridge_alt_map H three,
        alternating_point_path_step (suc. zero.) u (refl pt)
          (two_element_decidable_equality (F pt) (two_set_two_element (bsgn three pt))
            (transport (BookFiniteSetsAt three) F pt pt (refl pt) (u .snd)) (alternating_point_value three))),
       book_equivalence (BlindAltCarrier H three) (AlternatingShapes three) (bridge_alt_map_equiv H three) .equiv)

def bridge_xca_isos_A3_C3 : blind_xca_isos_A3_C3
  ≔ H h ↦
    let A ≔ blind_AG H blind_three h in let Cy ≔ blind_CG (suc. (suc. zero.)) in
    let P ≔ bridge_alt_three_path H h in
    let Q : Id Group (bridge_g Cy) c3_group ≔ bridge_aut Cycles cycles_groupoid (finite_fin_cycle two) in
    let e : Equiv (BlindIso A Cy) (GroupIso a3_group c3_group)
      ≔ compose_equiv (BlindIso A Cy) (GroupIso (bridge_g A) (bridge_g Cy)) (GroupIso a3_group c3_group) (bridge_def_iso A Cy)
          (id_to_equiv (GroupIso (bridge_g A) (bridge_g Cy)) (GroupIso a3_group c3_group) (refl GroupIso P Q)) in
    let f ≔ equiv_inverse_map (BlindIso A Cy) (GroupIso a3_group c3_group) e a3_c3_target_iso in
    let g ≔ equiv_inverse_map (BlindIso A Cy) (GroupIso a3_group c3_group) e a3_c3_source_iso in
    (f, (g, p ↦ a3_c3_isos_differ
      (calc a3_c3_target_iso = e .map f
          by inverse (GroupIso a3_group c3_group) (e .map f) a3_c3_target_iso (equiv_counit (BlindIso A Cy) (GroupIso a3_group c3_group) e a3_c3_target_iso)
        = e .map g by refl (e .map) p
        = a3_c3_source_iso by equiv_counit (BlindIso A Cy) (GroupIso a3_group c3_group) e a3_c3_source_iso ∎)))

{` ---- Non-vacuity: BlindSignHyps is inhabited. ---- `}

def bridge_hyps_hp : blind_xca_bigproduct_connected
  ≔ S Y c _ ↦ connected_pi_finite (S .fst .fst) (S .snd) Y c

def bridge_hyps_fin (A : SetTypes) (fA : IsFinite (A .fst)) : IsFinite (BlindTwoSubsets A)
  ≔ finite_of_equiv (BlindTwoSubsets A) (TwoSubsets (A .fst)) (bridge_def_two_subsets A) (ksubsets_finite (A .fst) fA two)

{` The pointing of Bμ_E required by the blind file: the blind "0" of Fin 2 is
   inl (inr star) (ours is inr star); it is sent to the class of the constant
   section at it. `}
def bridge_hyps_ptg (E : FiniteSets) (ne : Mere (E .fst .fst)) : BlindMuPointing bridge_lem_parityequiv E ne
  ≔ let X ≔ E .fst .fst in
    let c : X → BlindBSG2 ≔ _ ↦ blind_bsg2_pt in
    let Qb ≔ BlindParityQuotient X c in
    let hQ : TwoElement Qb ≔ bridge_lem_parityequiv E c .snd .snd .snd .fst ne in
    let cl ≔ blind_parity_class X c (_ ↦ blind_fin_two_zero) in
    let psi ≔ two_pointed_equiv Qb hQ (two_element_other Qb hQ cl) in
    (component_path SetTypes (Fin two, fin_set two) blind_bsg2_pt (blind_Bmu_nonempty bridge_lem_parityequiv E ne c)
        (set_types_path (Fin two, fin_set two) (Qb, blind_parity_quotient_set X c) psi),
     two_element_other_other Qb hQ cl)

{` The order identification of a two-element subset {i, j} of Fin n with the
   blind Fin 2: the blind order is the reverse of ours, so the blind "0" goes
   to our maximum and the blind "1" to our minimum. `}
def bridge_hyps_ord (n : Nat) (e : BlindTwoSubsets (blind_bn_set n))
  : Σ (Id BlindBSG2 blind_bsg2_pt (blind_two_subset_family (blind_bn_set n) e)) (q ↦
      let t ≔ transport BlindBSG2 (X ↦ X .fst .fst) blind_bsg2_pt (blind_two_subset_family (blind_bn_set n) e) q in
      BookLt (blind_fin_val n (t blind_fin_two_zero .fst)) (blind_fin_val n (t blind_fin_two_one .fst)))
  ≔ let e' ≔ bridge_two_subsets_to (blind_bn_set n) e in
    (component_path SetTypes (Fin two, fin_set two) blind_bsg2_pt (blind_two_subset_family (blind_bn_set n) e)
        (set_types_path (Fin two, fin_set two) (blind_two_subset_family (blind_bn_set n) e .fst) (standard_order_equiv n e')),
     lt_to_book (blind_fin_val n (two_subset_max n e' .fst)) (blind_fin_val n (two_subset_min n e' .fst))
       (bridge_fin_val_lt_from n (two_subset_max n e' .fst) (two_subset_min n e' .fst) (two_subset_min_lt_max n e')))

def bridge_sign_hyps_inhabited : BlindSignHyps
  ≔ (hp ≔ bridge_hyps_hp, lem ≔ bridge_lem_parityequiv, ptg ≔ bridge_hyps_ptg, fin ≔ bridge_hyps_fin, ord ≔ bridge_hyps_ord)

{` ---- Converses (ours from the blind statements; bonus). ---- `}

def bridge_conv_transposition_sign (b : blind_lem_sign_transposition)
  (n : Nat) (A : BookFiniteSetsAt n) (d : DecidableEquality (A .fst .fst)) (a c : A .fst .fst) (nac : Not (Id (A .fst .fst) a c))
  : Id Sign (permutation_sign_at n A (transposition_equiv (A .fst .fst) d a c)) minus.
  ≔ bridge_def_perm_odd bridge_sign_hyps_inhabited n A (transposition_equiv (A .fst .fst) d a c) .map
      (b bridge_sign_hyps_inhabited n A d a c nac)

def bridge_conv_identity_even (b : blind_lem_sign_identity_even) (A : FiniteSets) (d : DecidableEquality (A .fst .fst))
  (w : List (Transpositions (A .fst .fst))) (h : Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d w) (identity (A .fst .fst)))
  : IsEvenNat (length (Transpositions (A .fst .fst)) w)
  ≔ equiv_inverse_map (IsEvenNat (length (Transpositions (A .fst .fst)) w)) (Id Bool (nat_odd (length (Transpositions (A .fst .fst)) w)) false.)
      (is_even_nat_iff (length (Transpositions (A .fst .fst)) w))
      (bridge_nat_even_true_to (length (Transpositions (A .fst .fst)) w) (b (A .fst .fst) (A .snd) d w h))

def bridge_conv_parity_transitive (b : blind_lem_parityequiv) (E : FiniteSets) (P : E .fst .fst → BookFiniteSetsAt two)
  (f g h : LocalSections (E .fst .fst) P) (r : ParityRelated (E .fst .fst) (E .snd) P f g) (s : ParityRelated (E .fst .fst) (E .snd) P g h)
  : ParityRelated (E .fst .fst) (E .snd) P f h
  ≔ let X ≔ E .fst .fst in let e ≔ bridge_def_parity_rel X (E .snd) P in
    e f h .map (b E P .snd .snd .fst f g h
      (equiv_inverse_map (BlindParityRel X P f g) (ParityRelated X (E .snd) P f g) (e f g) r)
      (equiv_inverse_map (BlindParityRel X P g h) (ParityRelated X (E .snd) P g h) (e g h) s))
