export "1173-fgauto-dyck-saturation"
export "1167-fgauto-thompson-correct"

{` Chapter 11, automata part 25: the Dyck reachability relation of a
   finite automaton B, computed by saturation (module 1173), is sound and
   complete: fgauto_drel_sound and fgauto_drel_complete. `}

def fgauto_dyck_run_combine (S V : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S V)) (p p1 p2 p3 p4 q : V)
  (x : SignedLetter S) (a : FgautoDyckRunG S V dec E p p1) (s1 : FgautoStep S V E p1 x p2) (b : FgautoDyckRunG S V dec E p2 p3)
  (s2 : FgautoStep S V E p3 (letter_complement S x) p4) (c : FgautoDyckRunG S V dec E p4 q) : FgautoDyckRunG S V dec E p q
  ≔ let L ≔ SignedLetter S in
    let W : SignedWord S ≔ cons. x (append L (b .fst) (cons. (letter_complement S x) (c .fst))) in
    (append L (a .fst) W,
     (fgauto_run_append S V E p (a .fst) p1 W q (a .snd .fst)
        (p2, (s1, fgauto_run_append S V E p2 (b .fst) p3 (cons. (letter_complement S x) (c .fst)) q (b .snd .fst) (p4, (s2, c .snd .fst)))),
      fgauto_wtrans S (word_reduction S dec (append L (a .fst) W)) (word_reduction S dec W) nil.
        (fgauto_red_drop_left S dec (a .fst) W (a .snd .snd))
        (fgauto_dyck_wrap S dec x (b .fst) (c .fst) (b .snd .snd) (c .snd .snd))))

def FgautoDClosed (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B))) : Type
  ≔ (t : FgautoDPair S B) → Not (FgautoDNew S dec B R t)

def fgauto_dsat_entry (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  (i j : Fin (fgauto_nfa_k S B)) (h : FgautoDRule S dec B R i j) : FgautoDEnt S dec B (i, j)
  ≔ let P ≔ FgautoDPair S B in
    let K ≔ FgautoDKeys S dec B R in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let ent ≔ (t : P) (m : FgautoMem P t K) ↦ fgauto_entry_of_key P (FgautoDEnt S dec B) t R m in
    match h [
    | inl. e ↦ (nil., (refl nth e, refl (nil. : SignedWord S)))
    | inr. z ↦
      let i' ≔ z .fst in let r ≔ z .snd .fst in let r' ≔ z .snd .snd .fst in let j' ≔ z .snd .snd .snd .fst in
      let n ≔ z .snd .snd .snd .snd .fst in
      let c ≔ z .snd .snd .snd .snd .snd in
      fgauto_dyck_run_combine S V dec (B .nedges) (nth i) (nth i') (nth r) (nth r') (nth j') (nth j)
        (fgauto_list_nth (SignedLetter S) (fgauto_nfa_labels S B) n)
        (ent (i, i') (c .fst)) (c .snd .fst) (ent (r, r') (c .snd .snd .fst)) (c .snd .snd .snd .fst) (ent (j', j) (c .snd .snd .snd .snd)) ]

def fgauto_dsat_search (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (R : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B)))
  : Sum (FgautoSatFound (FgautoDPair S B) (FgautoDEnt S dec B) R) (FgautoDClosed S dec B R)
  ≔ let k ≔ fgauto_nfa_k S B in
    match fin_sigma_decidable k (i ↦ Σ (Fin k) (j ↦ FgautoDNew S dec B R (i, j)))
      (i ↦ fin_sigma_decidable k (j ↦ FgautoDNew S dec B R (i, j)) (j ↦ fgauto_dnew_decide S dec B R (i, j))) [
    | inl. z ↦ inl. ((z .fst, z .snd .fst), (z .snd .snd .snd, fgauto_dsat_entry S dec B R (z .fst) (z .snd .fst) (z .snd .snd .fst)))
    | inr. no ↦ inr. (t nw ↦ no (t .fst, (t .snd, nw))) ]

def fgauto_dsat (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) : List (Σ (FgautoDPair S B) (FgautoDEnt S dec B))
  ≔ fgauto_saturate (FgautoDPair S B) (FgautoDEnt S dec B) (FgautoDClosed S dec B) (fgauto_dsat_search S dec B)
      (suc. (length (FgautoDPair S B) (fgauto_dpair_list S B))) nil.

def fgauto_dsat_closed (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) : FgautoDClosed S dec B (fgauto_dsat S dec B)
  ≔ fgauto_sat_run (FgautoDPair S B) (fgauto_dpair_dec S B) (fgauto_dpair_list S B) (fgauto_dpair_list_complete S B)
      (FgautoDEnt S dec B) (FgautoDClosed S dec B) (fgauto_dsat_search S dec B)

def FgautoDRel (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B)) : Type
  ≔ FgautoMem (FgautoDPair S B) (i, j) (FgautoDKeys S dec B (fgauto_dsat S dec B))

def fgauto_drel_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B))
  : Decidable (FgautoDRel S dec B i j)
  ≔ fgauto_mem_decide (FgautoDPair S B) (fgauto_dpair_dec S B) (i, j) (FgautoDKeys S dec B (fgauto_dsat S dec B))

def fgauto_drel_sound (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B))
  (m : FgautoDRel S dec B i j) : FgautoDEnt S dec B (i, j)
  ≔ fgauto_entry_of_key (FgautoDPair S B) (FgautoDEnt S dec B) (i, j) (fgauto_dsat S dec B) m

def fgauto_drel_of_rule (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B))
  (h : FgautoDRule S dec B (fgauto_dsat S dec B) i j) : FgautoDRel S dec B i j
  ≔ match fgauto_drel_decide S dec B i j [
  | inl. m ↦ m
  | inr. nm ↦ match fgauto_dsat_closed S dec B (i, j) (h, nm) [] ]

def fgauto_drel_refl (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i : Fin (fgauto_nfa_k S B)) : FgautoDRel S dec B i i
  ≔ fgauto_drel_of_rule S dec B i i (inl. (refl i))

{` Length bookkeeping. `}
def fgauto_length_prefix (A : Type) (u v : List A) : Le (length A u) (length A (append A u v))
  ≔ match u [ nil. ↦ star. | cons. a t ↦ fgauto_length_prefix A t v ]

{` Completeness. `}
def fgauto_nfa_endpoint_state_run (S : Type) (B : FgautoNFA S) (p : B .nstate) (mp : FgautoMem (B .nstate) p (fgauto_nfa_states S B))
  (w : SignedWord S) (q : B .nstate) (r : FgautoRun S (B .nstate) (B .nedges) p w q) : FgautoMem (B .nstate) q (fgauto_nfa_states S B)
  ≔ match w [
  | nil. ↦ fgauto_mem_transport (B .nstate) p q (fgauto_nfa_states S B) r mp
  | cons. z w' ↦ fgauto_nfa_endpoint_state_run S B (r .fst) (fgauto_nfa_endpoint_state S B p z (r .fst) (r .snd .fst)) w' q (r .snd .snd) ]

def fgauto_drel_complete (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (n : Nat) (w : SignedWord S)
  (hl : Le (length (SignedLetter S) w) n) (i j : Fin (fgauto_nfa_k S B))
  (r : FgautoRun S (B .nstate) (B .nedges) (fgauto_nfa_nth S B i) w (fgauto_nfa_nth S B j)) (hd : FgautoDyck S dec w)
  : FgautoDRel S dec B i j
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let E ≔ B .nedges in
    let L ≔ SignedLetter S in
    match w [
    | nil. ↦ transport (Fin k) (j0 ↦ FgautoDRel S dec B i j0) i j (fgauto_nfa_nth_injective S B i j r) (fgauto_drel_refl S dec B i)
    | cons. y w' ↦ match n [
      | zero. ↦ match hl []
      | suc. n' ↦
        let fr ≔ fgauto_dyck_first_return S dec y w' hd in
        let d0 ≔ fr .fst in
        let d1 ≔ fr .snd .fst in
        let r0 ≔ r .fst in
        let rest ≔ fgauto_run_word S V E r0 w' (append L d0 (cons. (letter_complement S y) d1)) (nth j) (fr .snd .snd .fst) (r .snd .snd) in
        let sp ≔ fgauto_run_split S V E r0 d0 (cons. (letter_complement S y) d1) (nth j) rest in
        let mm ≔ sp .fst in
        let mm' ≔ sp .snd .snd .fst in
        let m0 ≔ fgauto_nfa_endpoint_state S B (nth i) y r0 (r .snd .fst) in
        let m1 ≔ fgauto_nfa_endpoint_state S B mm (letter_complement S y) mm' (sp .snd .snd .snd .fst) in
        let ri ≔ fgauto_nfa_pos S B r0 m0 in
        let jj ≔ fgauto_nfa_pos S B mm' m1 in
        let mmem ≔ fgauto_nfa_endpoint_state_run S B r0 m0 d0 mm (sp .snd .fst) in
        let rr ≔ fgauto_nfa_pos S B mm mmem in
        let er ≔ fgauto_nfa_nth_pos S B r0 m0 in
        let err ≔ fgauto_nfa_nth_pos S B mm mmem in
        let ej ≔ fgauto_nfa_nth_pos S B mm' m1 in
        let lw' ≔ transport (SignedWord S) (u ↦ Le (length L u) n') w' (append L d0 (cons. (letter_complement S y) d1)) (fr .snd .snd .fst) hl in
        let h0 ≔ fgauto_drel_complete S dec B n' d0
          (le_trans (length L d0) (length L (append L d0 (cons. (letter_complement S y) d1))) n'
            (fgauto_length_prefix L d0 (cons. (letter_complement S y) d1)) lw')
          ri rr
          (fgauto_run_start S V E r0 (nth ri) d0 (nth rr) (inverse V (nth ri) r0 er)
            (fgauto_run_end S V E r0 d0 mm (nth rr) (inverse V (nth rr) mm err) (sp .snd .fst)))
          (fr .snd .snd .snd .fst) in
        let h1 ≔ fgauto_drel_complete S dec B n' d1
          (lt_le (length L d1) n' (le_trans (suc. (length L d1)) (length L (append L d0 (cons. (letter_complement S y) d1))) n'
            (fgauto_length_suffix L d0 (letter_complement S y) d1) lw'))
          jj j
          (fgauto_run_start S V E mm' (nth jj) d1 (nth j) (inverse V (nth jj) mm' ej) (sp .snd .snd .snd .snd))
          (fr .snd .snd .snd .snd) in
        let labs ≔ fgauto_nfa_labels S B in
        let ml ≔ fgauto_nfa_label_mem S B E (nth i) y r0 (r .snd .fst) in
        let ln ≔ fgauto_list_pos L (signed_letter_decidable_equality S dec) y labs ml in
        let el ≔ fgauto_list_pos_nth L (signed_letter_decidable_equality S dec) y labs ml in
        let x ≔ fgauto_list_nth L labs ln in
        fgauto_drel_of_rule S dec B i j (inr. (i, (ri, (rr, (jj, (ln,
          (fgauto_drel_refl S dec B i,
           (fgauto_step_transport S V E (nth i) (nth i) y x r0 (nth ri) (refl (nth i)) (inverse L x y el) (inverse V (nth ri) r0 er) (r .snd .fst),
            (h0,
             (fgauto_step_transport S V E mm (nth rr) (letter_complement S y) (letter_complement S x) mm' (nth jj)
                (inverse V (nth rr) mm err) (refl (letter_complement S) (inverse L x y el)) (inverse V (nth jj) mm' ej)
                (sp .snd .snd .snd .fst),
              h1)))))))))) ] ]
