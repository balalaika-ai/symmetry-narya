export "1172-fgauto-reduction-factorization"
export "1169-fgauto-subset-simulation"

{` Chapter 11, automata part 24: deciding Dyck reachability in a finite
   automaton (for fggroups.tex:879).

   A generic saturation procedure (fgauto_saturate): a list of keys from a
   finite set with witnesses is extended one new key at a time as long as a
   search finds one; with fuel = size of the finite set + 1 the search must
   fail at the end, which yields its closure property.

   Instance: for a finite automaton B with states nth : Fin k → states, the
   relation D(i, j) = "some word w with rho(w) = eps labels a run from state
   i to state j" is the least relation containing the diagonal and closed
   under D(i, i'), i' -x-> r, D(r, r'), r' -x-bar-> j', D(j', j) =>
   D(i, j) (fgauto_dyck_closure_complete, by the first-return decomposition
   of Dyck words, module 1172); it is computed by saturation. `}

{` Generic saturation. `}
def fgauto_entry_keys (T : Type) (Ent : T → Type) (R : List (Σ T Ent)) : List T ≔ fgauto_list_map (Σ T Ent) T (z ↦ z .fst) R

def FgautoSatFound (T : Type) (Ent : T → Type) (R : List (Σ T Ent)) : Type
  ≔ Σ T (t ↦ Product (Not (FgautoMem T t (fgauto_entry_keys T Ent R))) (Ent t))

def fgauto_sat_step (T : Type) (Ent : T → Type) (C : List (Σ T Ent) → Type) (k : List (Σ T Ent) → List (Σ T Ent))
  (R : List (Σ T Ent)) (d : Sum (FgautoSatFound T Ent R) (C R)) : List (Σ T Ent)
  ≔ match d [ inr. _ ↦ R | inl. n ↦ k (cons. (n .fst, n .snd .snd) R) ]

def fgauto_saturate (T : Type) (Ent : T → Type) (C : List (Σ T Ent) → Type)
  (search : (R : List (Σ T Ent)) → Sum (FgautoSatFound T Ent R) (C R)) (fuel : Nat) (R : List (Σ T Ent)) : List (Σ T Ent)
  ≔ match fuel [ zero. ↦ R | suc. f ↦ fgauto_sat_step T Ent C (fgauto_saturate T Ent C search f) R (search R) ]

def fgauto_entry_keys_length (T : Type) (Ent : T → Type) (R : List (Σ T Ent))
  : Id Nat (length T (fgauto_entry_keys T Ent R)) (length (Σ T Ent) R)
  ≔ match R [ nil. ↦ refl (zero. : Nat) | cons. z R' ↦ suc. (fgauto_entry_keys_length T Ent R') ]

def fgauto_sat_closed_step (T : Type) (dT : DecidableEquality T) (U : List T) (cU : (t : T) → FgautoMem T t U)
  (Ent : T → Type) (C : List (Σ T Ent) → Type) (search : (R : List (Σ T Ent)) → Sum (FgautoSatFound T Ent R) (C R)) (f : Nat)
  (recur : (R1 : List (Σ T Ent)) → FgautoNoDup T (fgauto_entry_keys T Ent R1)
    → Le (suc. (length T U)) (add (length (Σ T Ent) R1) f) → C (fgauto_saturate T Ent C search f R1))
  (R : List (Σ T Ent)) (nd : FgautoNoDup T (fgauto_entry_keys T Ent R)) (hl : Le (suc. (length T U)) (add (length (Σ T Ent) R) (suc. f)))
  (d : Sum (FgautoSatFound T Ent R) (C R)) : C (fgauto_sat_step T Ent C (fgauto_saturate T Ent C search f) R d)
  ≔ match d [
  | inr. c ↦ c
  | inl. n ↦ recur (cons. (n .fst, n .snd .snd) R) (n .snd .fst, nd)
      (transport Nat (z ↦ Le (suc. (length T U)) z) (suc. (add (length (Σ T Ent) R) f)) (add (suc. (length (Σ T Ent) R)) f)
        (inverse Nat (add (suc. (length (Σ T Ent) R)) f) (suc. (add (length (Σ T Ent) R) f)) (add_suc_left (length (Σ T Ent) R) f)) hl) ]

def fgauto_sat_closed (T : Type) (dT : DecidableEquality T) (U : List T) (cU : (t : T) → FgautoMem T t U)
  (Ent : T → Type) (C : List (Σ T Ent) → Type) (search : (R : List (Σ T Ent)) → Sum (FgautoSatFound T Ent R) (C R)) (fuel : Nat)
  (R : List (Σ T Ent)) (nd : FgautoNoDup T (fgauto_entry_keys T Ent R)) (hl : Le (suc. (length T U)) (add (length (Σ T Ent) R) fuel))
  : C (fgauto_saturate T Ent C search fuel R)
  ≔ match fuel [
  | zero. ↦ match lt_irrefl (length T U)
      (le_trans (suc. (length T U)) (length (Σ T Ent) R) (length T U) hl
        (transport Nat (z ↦ Le z (length T U)) (length T (fgauto_entry_keys T Ent R)) (length (Σ T Ent) R)
          (fgauto_entry_keys_length T Ent R)
          (fgauto_nodup_length T dT (fgauto_entry_keys T Ent R) U nd (t m ↦ cU t)))) []
  | suc. f ↦ fgauto_sat_closed_step T dT U cU Ent C search f (fgauto_sat_closed T dT U cU Ent C search f) R nd hl (search R) ]

def fgauto_sat_run (T : Type) (dT : DecidableEquality T) (U : List T) (cU : (t : T) → FgautoMem T t U)
  (Ent : T → Type) (C : List (Σ T Ent) → Type) (search : (R : List (Σ T Ent)) → Sum (FgautoSatFound T Ent R) (C R))
  : C (fgauto_saturate T Ent C search (suc. (length T U)) nil.)
  ≔ fgauto_sat_closed T dT U cU Ent C search (suc. (length T U)) nil. star.
      (le_from_equal (length T U) (add zero. (length T U)) (inverse Nat (add zero. (length T U)) (length T U) (add_zero_left (length T U))))

{` Generic runs with Dyck labels. `}
def FgautoDyckRunG (S V : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S V)) (p q : V) : Type
  ≔ Σ (SignedWord S) (d ↦ Product (FgautoRun S V E p d q) (FgautoDyck S dec d))

def fgauto_entry_of_key (T : Type) (Ent : T → Type) (t : T) (R : List (Σ T Ent)) (m : FgautoMem T t (fgauto_entry_keys T Ent R)) : Ent t
  ≔ match R [
  | nil. ↦ match m []
  | cons. z R' ↦ match m [
    | inl. e ↦ transport T Ent (z .fst) t (inverse T t (z .fst) e) (z .snd)
    | inr. m' ↦ fgauto_entry_of_key T Ent t R' m' ] ]

{` The instance for an automaton B. `}
def fgauto_nfa_labels (S : Type) (B : FgautoNFA S) : List (SignedLetter S)
  ≔ fgauto_list_map (FgautoEdge S (B .nstate)) (SignedLetter S) (e ↦ e .lab) (B .nedges)

def fgauto_nfa_label_mem (S : Type) (B : FgautoNFA S) (E : List (FgautoEdge S (B .nstate))) (p : B .nstate) (x : SignedLetter S)
  (q : B .nstate) (s : FgautoStep S (B .nstate) E p x q)
  : FgautoMem (SignedLetter S) x (fgauto_list_map (FgautoEdge S (B .nstate)) (SignedLetter S) (e ↦ e .lab) E)
  ≔ match E [ nil. ↦ match s [] | cons. e E' ↦ match s [ inl. t ↦ inl. (t .snd .fst) | inr. s' ↦ inr. (fgauto_nfa_label_mem S B E' p x q s') ] ]

def FgautoDPair (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (Fin (fgauto_nfa_k S B))

def fgauto_dpair_dec (S : Type) (B : FgautoNFA S) : DecidableEquality (FgautoDPair S B)
  ≔ fgauto_pair_decidable_equality (Fin (fgauto_nfa_k S B)) (Fin (fgauto_nfa_k S B))
      (fin_decidable_equality (fgauto_nfa_k S B)) (fin_decidable_equality (fgauto_nfa_k S B))

def fgauto_dpair_list (S : Type) (B : FgautoNFA S) : List (FgautoDPair S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (Fin (fgauto_nfa_k S B)) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_fin_list (fgauto_nfa_k S B))

def fgauto_dpair_list_complete (S : Type) (B : FgautoNFA S) (t : FgautoDPair S B) : FgautoMem (FgautoDPair S B) t (fgauto_dpair_list S B)
  ≔ fgauto_pair_list_complete (Fin (fgauto_nfa_k S B)) (Fin (fgauto_nfa_k S B)) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_fin_list (fgauto_nfa_k S B))
      (fgauto_fin_list_complete (fgauto_nfa_k S B)) (fgauto_fin_list_complete (fgauto_nfa_k S B)) t

def FgautoDEnt (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoDPair S B) : Type
  ≔ FgautoDyckRunG S (B .nstate) dec (B .nedges) (fgauto_nfa_nth S B (t .fst)) (fgauto_nfa_nth S B (t .snd))

def FgautoDKeys (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  : List (FgautoDPair S B)
  ≔ fgauto_entry_keys (FgautoDPair S B) (FgautoDEnt S dec B) R

{` The closure rule, letters indexed by positions in the label list. `}
def FgautoDCore (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' r r' j' : Fin (fgauto_nfa_k S B)) (n : Fin (length (SignedLetter S) (fgauto_nfa_labels S B))) : Type
  ≔ let K ≔ FgautoDKeys S dec B R in
    let nth ≔ fgauto_nfa_nth S B in
    let x ≔ fgauto_list_nth (SignedLetter S) (fgauto_nfa_labels S B) n in
    Product (FgautoMem (FgautoDPair S B) (i, i') K)
      (Product (FgautoStep S (B .nstate) (B .nedges) (nth i') x (nth r))
        (Product (FgautoMem (FgautoDPair S B) (r, r') K)
          (Product (FgautoStep S (B .nstate) (B .nedges) (nth r') (letter_complement S x) (nth j'))
            (FgautoMem (FgautoDPair S B) (j', j) K))))

def FgautoD4 (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' r r' j' : Fin (fgauto_nfa_k S B)) : Type
  ≔ Σ (Fin (length (SignedLetter S) (fgauto_nfa_labels S B))) (FgautoDCore S dec B R i j i' r r' j')
def FgautoD3 (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' r r' : Fin (fgauto_nfa_k S B)) : Type ≔ Σ (Fin (fgauto_nfa_k S B)) (FgautoD4 S dec B R i j i' r r')
def FgautoD2 (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' r : Fin (fgauto_nfa_k S B)) : Type ≔ Σ (Fin (fgauto_nfa_k S B)) (FgautoD3 S dec B R i j i' r)
def FgautoD1 (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' : Fin (fgauto_nfa_k S B)) : Type ≔ Σ (Fin (fgauto_nfa_k S B)) (FgautoD2 S dec B R i j i')
def FgautoD0 (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j : Fin (fgauto_nfa_k S B)) : Type ≔ Σ (Fin (fgauto_nfa_k S B)) (FgautoD1 S dec B R i j)

def FgautoDRule (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j : Fin (fgauto_nfa_k S B)) : Type
  ≔ Sum (Id (Fin (fgauto_nfa_k S B)) i j) (FgautoD0 S dec B R i j)

def FgautoDNew (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (t : FgautoDPair S B) : Type
  ≔ Product (FgautoDRule S dec B R (t .fst) (t .snd)) (Not (FgautoMem (FgautoDPair S B) t (FgautoDKeys S dec B R)))

def fgauto_and_decide (A B : Type) (dA : Decidable A) (dB : Decidable B) : Decidable (Product A B)
  ≔ match dA [
  | inr. n ↦ inr. (h ↦ n (h .fst))
  | inl. a ↦ match dB [ inr. n ↦ inr. (h ↦ n (h .snd)) | inl. b ↦ inl. (a, b) ] ]

def fgauto_or_decide (A B : Type) (dA : Decidable A) (dB : Decidable B) : Decidable (Sum A B)
  ≔ match dA [
  | inl. a ↦ inl. (inl. a)
  | inr. n ↦ match dB [ inl. b ↦ inl. (inr. b) | inr. m ↦ inr. (h ↦ match h [ inl. a ↦ n a | inr. b ↦ m b ]) ] ]

def fgauto_not_decide (A : Type) (dA : Decidable A) : Decidable (Not A)
  ≔ match dA [ inl. a ↦ inr. (n ↦ n a) | inr. n ↦ inl. n ]

def fgauto_dcore_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j i' r r' j' : Fin (fgauto_nfa_k S B)) (n : Fin (length (SignedLetter S) (fgauto_nfa_labels S B)))
  : Decidable (FgautoDCore S dec B R i j i' r r' j' n)
  ≔ let K ≔ FgautoDKeys S dec B R in
    let nth ≔ fgauto_nfa_nth S B in
    let x ≔ fgauto_list_nth (SignedLetter S) (fgauto_nfa_labels S B) n in
    let P ≔ FgautoDPair S B in
    let md ≔ (t : P) ↦ fgauto_mem_decide P (fgauto_dpair_dec S B) t K in
    let sd ≔ (p : B .nstate) (y : SignedLetter S) (q : B .nstate) ↦ fgauto_step_decide S (B .nstate) dec (B .ndec) (B .nedges) p y q in
    let St ≔ (p : B .nstate) (y : SignedLetter S) (q : B .nstate) ↦ FgautoStep S (B .nstate) (B .nedges) p y q in
    fgauto_and_decide (FgautoMem P (i, i') K)
      (Product (St (nth i') x (nth r)) (Product (FgautoMem P (r, r') K) (Product (St (nth r') (letter_complement S x) (nth j')) (FgautoMem P (j', j) K))))
      (md (i, i'))
      (fgauto_and_decide (St (nth i') x (nth r)) (Product (FgautoMem P (r, r') K) (Product (St (nth r') (letter_complement S x) (nth j')) (FgautoMem P (j', j) K)))
        (sd (nth i') x (nth r))
        (fgauto_and_decide (FgautoMem P (r, r') K) (Product (St (nth r') (letter_complement S x) (nth j')) (FgautoMem P (j', j) K))
          (md (r, r'))
          (fgauto_and_decide (St (nth r') (letter_complement S x) (nth j')) (FgautoMem P (j', j) K)
            (sd (nth r') (letter_complement S x) (nth j')) (md (j', j)))))

def fgauto_drule_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j : Fin (fgauto_nfa_k S B)) : Decidable (FgautoDRule S dec B R i j)
  ≔ let k ≔ fgauto_nfa_k S B in
    let nl ≔ length (SignedLetter S) (fgauto_nfa_labels S B) in
    fgauto_or_decide (Id (Fin k) i j) (FgautoD0 S dec B R i j) (fin_decidable_equality k i j)
      (fin_sigma_decidable k (FgautoD1 S dec B R i j) (i' ↦
        fin_sigma_decidable k (FgautoD2 S dec B R i j i') (r ↦
          fin_sigma_decidable k (FgautoD3 S dec B R i j i' r) (r' ↦
            fin_sigma_decidable k (FgautoD4 S dec B R i j i' r r') (j' ↦
              fin_sigma_decidable nl (FgautoDCore S dec B R i j i' r r' j') (n ↦ fgauto_dcore_decide S dec B R i j i' r r' j' n))))))

def fgauto_dnew_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (t : FgautoDPair S B) : Decidable (FgautoDNew S dec B R t)
  ≔ fgauto_and_decide (FgautoDRule S dec B R (t .fst) (t .snd)) (Not (FgautoMem (FgautoDPair S B) t (FgautoDKeys S dec B R)))
      (fgauto_drule_decide S dec B R (t .fst) (t .snd))
      (fgauto_not_decide (FgautoMem (FgautoDPair S B) t (FgautoDKeys S dec B R))
        (fgauto_mem_decide (FgautoDPair S B) (fgauto_dpair_dec S B) t (FgautoDKeys S dec B R)))
