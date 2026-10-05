export "1174-fgauto-dyck-relation"

{` Chapter 11, automata part 26: the lemma at fggroups.tex:879, "rho maps
   regular languages to regular languages".

   For a finite automaton B, the automaton fgauto_red_nfa B has states
   (i, o): a state i of B and the last letter read (o = none at the start).
   It has an edge (i, o) -x-> (j, x) whenever B can go from i to j reading
   d1 x d2 with Dyck words d1, d2 (relation D of module 1174), provided x
   does not cancel the last letter o; a state (j, o) is final when D(j, f)
   for a final state f of B.  Its language is rho(L(B)): the accepted
   words are reduced and are reductions of words of L(B) (lifting runs),
   and conversely the factorization v = d0 x1 d1 ... xn dn of an accepted
   word (module 1172) gives an accepting run reading rho(v). `}

def fgauto_bind_step (S V A : Type) (U : List A) (k : A → List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V (fgauto_list_bind A (FgautoEdge S V) U k) p x q)
  : Σ A (t ↦ Product (FgautoMem A t U) (FgautoStep S V (k t) p x q))
  ≔ match U [
  | nil. ↦ match s []
  | cons. t U' ↦ match fgauto_step_append_split S V (k t) (fgauto_list_bind A (FgautoEdge S V) U' k) p x q s [
    | inl. s1 ↦ (t, (inl. (refl t), s1))
    | inr. s2 ↦ let z ≔ fgauto_bind_step S V A U' k p x q s2 in (z .fst, (inr. (z .snd .fst), z .snd .snd)) ] ]

def fgauto_pair_list_mem (A B : Type) (la : List A) (lb : List B) (a : A) (b : B) (ma : FgautoMem A a la) (mb : FgautoMem B b lb)
  : FgautoMem (Product A B) (a, b) (fgauto_pair_list A B la lb)
  ≔ fgauto_mem_bind A (Product A B) la (a0 ↦ fgauto_list_map B (Product A B) (b0 ↦ (a0, b0)) lb) a (a, b) ma
      (fgauto_mem_map B (Product A B) (b0 ↦ (a, b0)) b lb mb)

{` Options for the last letter. `}
def FgautoOpt (S : Type) : Type ≔ Sum Unit (SignedLetter S)

def fgauto_opt_dec (S : Type) (dec : DecidableEquality S) : DecidableEquality (FgautoOpt S)
  ≔ sum_decidable_equality Unit (SignedLetter S) (x y ↦ inl. (unit_prop x y)) (signed_letter_decidable_equality S dec)

def FgautoOptOk (S : Type) (o : FgautoOpt S) (x : SignedLetter S) : Type
  ≔ match o [ inl. _ ↦ Unit | inr. y ↦ Not (Id (SignedLetter S) x (letter_complement S y)) ]

def fgauto_opt_ok_decide (S : Type) (dec : DecidableEquality S) (o : FgautoOpt S) (x : SignedLetter S) : Decidable (FgautoOptOk S o x)
  ≔ match o [ inl. _ ↦ inl. star. | inr. y ↦ fgauto_not_decide (Id (SignedLetter S) x (letter_complement S y)) (signed_letter_decidable_equality S dec x (letter_complement S y)) ]

def FgautoOptCompat (S : Type) (o : FgautoOpt S) (u : SignedWord S) : Type
  ≔ match o [ inl. _ ↦ Unit | inr. y ↦ WordHeadNotComplement S y u ]

def fgauto_opts (S : Type) (B : FgautoNFA S) : List (FgautoOpt S)
  ≔ cons. (inl. star.) (fgauto_list_map (SignedLetter S) (FgautoOpt S) (x ↦ inr. x) (fgauto_nfa_labels S B))

{` The tuples (i, i', j', j, n, o) indexing the edges. `}
def FgautoRT5 (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (length (SignedLetter S) (fgauto_nfa_labels S B))) (FgautoOpt S)
def FgautoRT4 (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (FgautoRT5 S B)
def FgautoRT3 (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (FgautoRT4 S B)
def FgautoRT2 (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (FgautoRT3 S B)
def FgautoRTuple (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (FgautoRT2 S B)

def fgauto_rt_l5 (S : Type) (B : FgautoNFA S) : List (FgautoRT5 S B)
  ≔ fgauto_pair_list (Fin (length (SignedLetter S) (fgauto_nfa_labels S B))) (FgautoOpt S)
      (fgauto_fin_list (length (SignedLetter S) (fgauto_nfa_labels S B))) (fgauto_opts S B)
def fgauto_rt_l4 (S : Type) (B : FgautoNFA S) : List (FgautoRT4 S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (FgautoRT5 S B) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_rt_l5 S B)
def fgauto_rt_l3 (S : Type) (B : FgautoNFA S) : List (FgautoRT3 S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (FgautoRT4 S B) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_rt_l4 S B)
def fgauto_rt_l2 (S : Type) (B : FgautoNFA S) : List (FgautoRT2 S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (FgautoRT3 S B) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_rt_l3 S B)
def fgauto_rtuples (S : Type) (B : FgautoNFA S) : List (FgautoRTuple S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (FgautoRT2 S B) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_rt_l2 S B)

def fgauto_rtuple_mem (S : Type) (B : FgautoNFA S) (i i' j' j : Fin (fgauto_nfa_k S B))
  (n : Fin (length (SignedLetter S) (fgauto_nfa_labels S B))) (o : FgautoOpt S) (mo : FgautoMem (FgautoOpt S) o (fgauto_opts S B))
  : FgautoMem (FgautoRTuple S B) (i, (i', (j', (j, (n, o))))) (fgauto_rtuples S B)
  ≔ let k ≔ fgauto_nfa_k S B in
    let nl ≔ length (SignedLetter S) (fgauto_nfa_labels S B) in
    let F ≔ fgauto_fin_list k in
    let c ≔ fgauto_fin_list_complete k in
    fgauto_pair_list_mem (Fin k) (FgautoRT2 S B) F (fgauto_rt_l2 S B) i (i', (j', (j, (n, o)))) (c i)
      (fgauto_pair_list_mem (Fin k) (FgautoRT3 S B) F (fgauto_rt_l3 S B) i' (j', (j, (n, o))) (c i')
        (fgauto_pair_list_mem (Fin k) (FgautoRT4 S B) F (fgauto_rt_l4 S B) j' (j, (n, o)) (c j')
          (fgauto_pair_list_mem (Fin k) (FgautoRT5 S B) F (fgauto_rt_l5 S B) j (n, o) (c j)
            (fgauto_pair_list_mem (Fin nl) (FgautoOpt S) (fgauto_fin_list nl) (fgauto_opts S B) n o (fgauto_fin_list_complete nl n) mo))))

{` The automaton for rho(L(B)). `}
def FgautoRState (S : Type) (B : FgautoNFA S) : Type ≔ Product (Fin (fgauto_nfa_k S B)) (FgautoOpt S)

def fgauto_rstate_dec (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) : DecidableEquality (FgautoRState S B)
  ≔ fgauto_pair_decidable_equality (Fin (fgauto_nfa_k S B)) (FgautoOpt S) (fin_decidable_equality (fgauto_nfa_k S B)) (fgauto_opt_dec S dec)

def fgauto_rt_letter (S : Type) (B : FgautoNFA S) (t : FgautoRTuple S B) : SignedLetter S
  ≔ fgauto_list_nth (SignedLetter S) (fgauto_nfa_labels S B) (t .snd .snd .snd .snd .fst)

def FgautoRCond (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B) : Type
  ≔ let nth ≔ fgauto_nfa_nth S B in
    let i ≔ t .fst in let i' ≔ t .snd .fst in let j' ≔ t .snd .snd .fst in let j ≔ t .snd .snd .snd .fst in
    let o ≔ t .snd .snd .snd .snd .snd in
    let x ≔ fgauto_rt_letter S B t in
    Product (FgautoDRel S dec B i i')
      (Product (FgautoStep S (B .nstate) (B .nedges) (nth i') x (nth j'))
        (Product (FgautoDRel S dec B j' j) (FgautoOptOk S o x)))

def fgauto_rcond_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B) : Decidable (FgautoRCond S dec B t)
  ≔ let nth ≔ fgauto_nfa_nth S B in
    let i ≔ t .fst in let i' ≔ t .snd .fst in let j' ≔ t .snd .snd .fst in let j ≔ t .snd .snd .snd .fst in
    let o ≔ t .snd .snd .snd .snd .snd in
    let x ≔ fgauto_rt_letter S B t in
    fgauto_and_decide (FgautoDRel S dec B i i')
      (Product (FgautoStep S (B .nstate) (B .nedges) (nth i') x (nth j')) (Product (FgautoDRel S dec B j' j) (FgautoOptOk S o x)))
      (fgauto_drel_decide S dec B i i')
      (fgauto_and_decide (FgautoStep S (B .nstate) (B .nedges) (nth i') x (nth j')) (Product (FgautoDRel S dec B j' j) (FgautoOptOk S o x))
        (fgauto_step_decide S (B .nstate) dec (B .ndec) (B .nedges) (nth i') x (nth j'))
        (fgauto_and_decide (FgautoDRel S dec B j' j) (FgautoOptOk S o x) (fgauto_drel_decide S dec B j' j) (fgauto_opt_ok_decide S dec o x)))

def fgauto_rt_edge (S : Type) (B : FgautoNFA S) (t : FgautoRTuple S B) : FgautoEdge S (FgautoRState S B)
  ≔ ((t .fst, t .snd .snd .snd .snd .snd), fgauto_rt_letter S B t, (t .snd .snd .snd .fst, inr. (fgauto_rt_letter S B t)))

def fgauto_rt_pick (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B) (d : Decidable (FgautoRCond S dec B t))
  : List (FgautoEdge S (FgautoRState S B))
  ≔ match d [ inl. _ ↦ cons. (fgauto_rt_edge S B t) nil. | inr. _ ↦ nil. ]

def fgauto_rt_edges_at (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B)
  : List (FgautoEdge S (FgautoRState S B))
  ≔ fgauto_rt_pick S dec B t (fgauto_rcond_decide S dec B t)

def fgauto_red_edges (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) : List (FgautoEdge S (FgautoRState S B))
  ≔ fgauto_list_bind (FgautoRTuple S B) (FgautoEdge S (FgautoRState S B)) (fgauto_rtuples S B) (fgauto_rt_edges_at S dec B)

def FgautoRFinal (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (q : FgautoRState S B) : Type
  ≔ Σ (Fin (fgauto_nfa_k S B)) (jf ↦ Product (FgautoMem (B .nstate) (fgauto_nfa_nth S B jf) (B .nfinal)) (FgautoDRel S dec B (q .fst) jf))

def fgauto_rfinal_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (q : FgautoRState S B) : Decidable (FgautoRFinal S dec B q)
  ≔ fin_sigma_decidable (fgauto_nfa_k S B)
      (jf ↦ Product (FgautoMem (B .nstate) (fgauto_nfa_nth S B jf) (B .nfinal)) (FgautoDRel S dec B (q .fst) jf))
      (jf ↦ fgauto_and_decide (FgautoMem (B .nstate) (fgauto_nfa_nth S B jf) (B .nfinal)) (FgautoDRel S dec B (q .fst) jf)
        (fgauto_mem_decide (B .nstate) (B .ndec) (fgauto_nfa_nth S B jf) (B .nfinal)) (fgauto_drel_decide S dec B (q .fst) jf))

def fgauto_rfinal_bool (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (q : FgautoRState S B) : Bool
  ≔ fgauto_decision_bool (FgautoRFinal S dec B q) (fgauto_rfinal_decide S dec B q)

def fgauto_red_states (S : Type) (B : FgautoNFA S) : List (FgautoRState S B)
  ≔ fgauto_pair_list (Fin (fgauto_nfa_k S B)) (FgautoOpt S) (fgauto_fin_list (fgauto_nfa_k S B)) (fgauto_opts S B)

def fgauto_red_nfa (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) : FgautoNFA S
  ≔ (FgautoRState S B, fgauto_rstate_dec S dec B, fgauto_red_edges S dec B,
     (fgauto_nfa_pos S B (B .ninit) (fgauto_nfa_init_state S B), inl. star.),
     fgauto_list_filter (FgautoRState S B) (fgauto_rfinal_bool S dec B) (fgauto_red_states S B))

{` Steps of the new automaton. `}
def fgauto_rt_pick_mem (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B) (c : FgautoRCond S dec B t)
  (d : Decidable (FgautoRCond S dec B t))
  : FgautoMem (FgautoEdge S (FgautoRState S B)) (fgauto_rt_edge S B t) (fgauto_rt_pick S dec B t d)
  ≔ match d [ inl. _ ↦ inl. (refl (fgauto_rt_edge S B t)) | inr. n ↦ match n c [] ]

def fgauto_red_step_intro (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B)
  (mt : FgautoMem (FgautoRTuple S B) t (fgauto_rtuples S B)) (c : FgautoRCond S dec B t)
  : FgautoStep S (FgautoRState S B) (fgauto_red_edges S dec B) (fgauto_rt_edge S B t .src) (fgauto_rt_letter S B t) (fgauto_rt_edge S B t .tgt)
  ≔ fgauto_mem_edge_step S (FgautoRState S B) (fgauto_red_edges S dec B) (fgauto_rt_edge S B t)
      (fgauto_mem_bind (FgautoRTuple S B) (FgautoEdge S (FgautoRState S B)) (fgauto_rtuples S B) (fgauto_rt_edges_at S dec B) t (fgauto_rt_edge S B t) mt
        (fgauto_rt_pick_mem S dec B t c (fgauto_rcond_decide S dec B t)))

def FgautoRStepData (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (p : FgautoRState S B) (x : SignedLetter S)
  (q : FgautoRState S B) : Type
  ≔ Σ (FgautoRTuple S B) (t ↦ Product (FgautoRCond S dec B t)
      (Product (Id (FgautoRState S B) p (fgauto_rt_edge S B t .src))
        (Product (Id (SignedLetter S) x (fgauto_rt_letter S B t)) (Id (FgautoRState S B) q (fgauto_rt_edge S B t .tgt)))))

def fgauto_rt_pick_step (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (t : FgautoRTuple S B)
  (d : Decidable (FgautoRCond S dec B t)) (p : FgautoRState S B) (x : SignedLetter S) (q : FgautoRState S B)
  (s : FgautoStep S (FgautoRState S B) (fgauto_rt_pick S dec B t d) p x q) : FgautoRStepData S dec B p x q
  ≔ match d [
  | inr. _ ↦ match s []
  | inl. c ↦ match s [ inl. e ↦ (t, (c, e)) | inr. s' ↦ match s' [] ] ]

def fgauto_red_step_elim (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (p : FgautoRState S B) (x : SignedLetter S)
  (q : FgautoRState S B) (s : FgautoStep S (FgautoRState S B) (fgauto_red_edges S dec B) p x q) : FgautoRStepData S dec B p x q
  ≔ let z ≔ fgauto_bind_step S (FgautoRState S B) (FgautoRTuple S B) (fgauto_rtuples S B) (fgauto_rt_edges_at S dec B) p x q s in
    fgauto_rt_pick_step S dec B (z .fst) (fgauto_rcond_decide S dec B (z .fst)) p x q (z .snd .snd)

{` Lifting runs of the new automaton to B. `}
def fgauto_red_lift (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i : Fin (fgauto_nfa_k S B)) (o : FgautoOpt S)
  (u : SignedWord S) (q : FgautoRState S B) (r : FgautoRun S (FgautoRState S B) (fgauto_red_edges S dec B) (i, o) u q)
  : Σ (SignedWord S) (v ↦ Product (FgautoRun S (B .nstate) (B .nedges) (fgauto_nfa_nth S B i) v (fgauto_nfa_nth S B (q .fst)))
      (Id (SignedWord S) (word_reduction S dec v) (word_reduction S dec u)))
  ≔ let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let E ≔ B .nedges in
    let L ≔ SignedLetter S in
    let RS ≔ FgautoRState S B in
    match u [
    | nil. ↦ (nil., (refl ((z ↦ nth (z .fst)) : RS → V) r, refl (nil. : SignedWord S)))
    | cons. x u' ↦
      let sd ≔ fgauto_red_step_elim S dec B (i, o) x (r .fst) (r .snd .fst) in
      let t ≔ sd .fst in
      let c ≔ sd .snd .fst in
      let ti ≔ t .fst in let ti' ≔ t .snd .fst in let tj' ≔ t .snd .snd .fst in let tj ≔ t .snd .snd .snd .fst in
      let xt ≔ fgauto_rt_letter S B t in
      let ei : Id (Fin (fgauto_nfa_k S B)) i ti ≔ refl ((z ↦ z .fst) : RS → Fin (fgauto_nfa_k S B)) (sd .snd .snd .fst) in
      let ex : Id L x xt ≔ sd .snd .snd .snd .fst in
      let ih ≔ fgauto_red_lift S dec B tj (inr. xt) u' q
        (fgauto_run_start S RS (fgauto_red_edges S dec B) (r .fst) (tj, inr. xt) u' q (sd .snd .snd .snd .snd) (r .snd .snd)) in
      let d1 ≔ fgauto_drel_sound S dec B ti ti' (c .fst) in
      let d2 ≔ fgauto_drel_sound S dec B tj' tj (c .snd .snd .fst) in
      let W : SignedWord S ≔ cons. xt (append L (d2 .fst) (ih .fst)) in
      (append L (d1 .fst) W,
       (fgauto_run_append S V E (nth i) (d1 .fst) (nth ti') W (nth (q .fst))
          (fgauto_run_start S V E (nth ti) (nth i) (d1 .fst) (nth ti') (refl nth (inverse (Fin (fgauto_nfa_k S B)) i ti ei)) (d1 .snd .fst))
          (nth tj', (c .snd .fst, fgauto_run_append S V E (nth tj') (d2 .fst) (nth tj) (ih .fst) (nth (q .fst)) (d2 .snd .fst) (ih .snd .fst))),
        calc
          word_reduction S dec (append L (d1 .fst) W)
          = word_reduction S dec W by fgauto_red_drop_left S dec (d1 .fst) W (d1 .snd .snd)
          = word_letter_reduce S dec xt (word_reduction S dec (ih .fst))
            by refl (word_letter_reduce S dec xt) (fgauto_red_drop_left S dec (d2 .fst) (ih .fst) (d2 .snd .snd))
          = word_letter_reduce S dec xt (word_reduction S dec u') by refl (word_letter_reduce S dec xt) (ih .snd .snd)
          = word_letter_reduce S dec x (word_reduction S dec u')
            by refl ((y ↦ word_letter_reduce S dec y (word_reduction S dec u')) : L → SignedWord S) (inverse L x xt ex) ∎)) ]

{` Accepted words are reduced. `}
def fgauto_opt_compat_nil (S : Type) (o : FgautoOpt S) : FgautoOptCompat S o nil.
  ≔ match o [ inl. _ ↦ star. | inr. _ ↦ star. ]

def fgauto_opt_ok_compat (S : Type) (o : FgautoOpt S) (x : SignedLetter S) (u' : SignedWord S) (h : FgautoOptOk S o x)
  : FgautoOptCompat S o (cons. x u')
  ≔ match o [ inl. _ ↦ h | inr. _ ↦ h ]

def fgauto_red_compat (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (i : Fin (fgauto_nfa_k S B)) (o : FgautoOpt S)
  (u : SignedWord S) (q : FgautoRState S B) (r : FgautoRun S (FgautoRState S B) (fgauto_red_edges S dec B) (i, o) u q)
  : Product (FgautoOptCompat S o u) (IsReducedWord S u)
  ≔ let L ≔ SignedLetter S in
    let RS ≔ FgautoRState S B in
    match u [
    | nil. ↦ (fgauto_opt_compat_nil S o, star.)
    | cons. x u' ↦
      let sd ≔ fgauto_red_step_elim S dec B (i, o) x (r .fst) (r .snd .fst) in
      let t ≔ sd .fst in
      let xt ≔ fgauto_rt_letter S B t in
      let eo : Id (FgautoOpt S) o (t .snd .snd .snd .snd .snd) ≔ refl ((z ↦ z .snd) : RS → FgautoOpt S) (sd .snd .snd .fst) in
      let ex : Id L x xt ≔ sd .snd .snd .snd .fst in
      let ih ≔ fgauto_red_compat S dec B (t .snd .snd .snd .fst) (inr. xt) u' q
        (fgauto_run_start S RS (fgauto_red_edges S dec B) (r .fst) (t .snd .snd .snd .fst, inr. xt) u' q (sd .snd .snd .snd .snd) (r .snd .snd)) in
      (fgauto_opt_ok_compat S o x u'
         (transport (FgautoOpt S) (z ↦ FgautoOptOk S z x) (t .snd .snd .snd .snd .snd) o (inverse (FgautoOpt S) o (t .snd .snd .snd .snd .snd) eo)
           (transport L (y ↦ FgautoOptOk S (t .snd .snd .snd .snd .snd) y) xt x (inverse L x xt ex) (sd .snd .fst .snd .snd .snd))),
       (transport L (y ↦ WordHeadNotComplement S y u') xt x (inverse L x xt ex) (ih .fst), ih .snd)) ]

{` Building accepting runs from factorizations. `}
def fgauto_opt_compat_ok (S : Type) (o : FgautoOpt S) (x : SignedLetter S) (u' : SignedWord S) (h : FgautoOptCompat S o (cons. x u'))
  : FgautoOptOk S o x
  ≔ match o [ inl. _ ↦ h | inr. _ ↦ h ]

def fgauto_red_build (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (ps : List (FgautoFactorPiece S))
  (hps : FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) ps) (i i1 : Fin (fgauto_nfa_k S B))
  (hD : FgautoDRel S dec B i i1) (o : FgautoOpt S) (mo : FgautoMem (FgautoOpt S) o (fgauto_opts S B))
  (compat : FgautoOptCompat S o (fgauto_factor_letters S ps)) (red : IsReducedWord S (fgauto_factor_letters S ps))
  (q : B .nstate) (mq : FgautoMem (B .nstate) q (fgauto_nfa_states S B))
  (run : FgautoRun S (B .nstate) (B .nedges) (fgauto_nfa_nth S B i1) (fgauto_factor_concat S ps) q)
  : Σ (Fin (fgauto_nfa_k S B)) (j ↦ Σ (FgautoOpt S) (o' ↦ Product (FgautoMem (FgautoOpt S) o' (fgauto_opts S B))
      (Product (FgautoRun S (FgautoRState S B) (fgauto_red_edges S dec B) (i, o) (fgauto_factor_letters S ps) (j, o'))
        (FgautoDRel S dec B j (fgauto_nfa_pos S B q mq)))))
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let E ≔ B .nedges in
    let L ≔ SignedLetter S in
    let RS ≔ FgautoRState S B in
    match ps [
    | nil. ↦ (i, (o, (mo, (refl ((i, o) : RS),
        transport (Fin k) (z ↦ FgautoDRel S dec B i z) i1 (fgauto_nfa_pos S B q mq)
          (fgauto_nfa_nth_injective S B i1 (fgauto_nfa_pos S B q mq)
            (concat V (nth i1) q (nth (fgauto_nfa_pos S B q mq)) run
              (inverse V (nth (fgauto_nfa_pos S B q mq)) q (fgauto_nfa_nth_pos S B q mq)))) hD))))
    | cons. pd t ↦
      let x ≔ pd .fst in
      let d ≔ pd .snd in
      let r1 ≔ run .fst in
      let s1 ≔ run .snd .fst in
      let sp ≔ fgauto_run_split S V E r1 d (fgauto_factor_concat S t) q (run .snd .snd) in
      let m ≔ sp .fst in
      let mr1 ≔ fgauto_nfa_endpoint_state S B (nth i1) x r1 s1 in
      let a ≔ fgauto_nfa_pos S B r1 mr1 in
      let ea ≔ fgauto_nfa_nth_pos S B r1 mr1 in
      let mm ≔ fgauto_nfa_endpoint_state_run S B r1 mr1 d m (sp .snd .fst) in
      let b ≔ fgauto_nfa_pos S B m mm in
      let eb ≔ fgauto_nfa_nth_pos S B m mm in
      let labs ≔ fgauto_nfa_labels S B in
      let ml ≔ fgauto_nfa_label_mem S B E (nth i1) x r1 s1 in
      let n ≔ fgauto_list_pos L (signed_letter_decidable_equality S dec) x labs ml in
      let el ≔ fgauto_list_pos_nth L (signed_letter_decidable_equality S dec) x labs ml in
      let x' ≔ fgauto_list_nth L labs n in
      let t6 : FgautoRTuple S B ≔ (i, (i1, (a, (a, (n, o))))) in
      let cond : FgautoRCond S dec B t6
        ≔ (hD, (fgauto_step_transport S V E (nth i1) (nth i1) x x' r1 (nth a) (refl (nth i1)) (inverse L x' x el) (inverse V (nth a) r1 ea) s1,
            (fgauto_drel_refl S dec B a,
             transport L (y ↦ FgautoOptOk S o y) x x' (inverse L x' x el)
               (fgauto_opt_compat_ok S o x (fgauto_factor_letters S t) compat)))) in
      let st ≔ fgauto_red_step_intro S dec B t6 (fgauto_rtuple_mem S B i i1 a a n o mo) cond in
      let hD' ≔ fgauto_drel_complete S dec B (length L d) d (le_refl (length L d)) a b
        (fgauto_run_start S V E r1 (nth a) d (nth b) (inverse V (nth a) r1 ea)
          (fgauto_run_end S V E r1 d m (nth b) (inverse V (nth b) m eb) (sp .snd .fst)))
        (hps .fst) in
      let rb ≔ fgauto_red_build S dec B t (hps .snd) a b hD' (inr. x')
        (inr. (fgauto_mem_map L (FgautoOpt S) (y ↦ inr. y) x' labs (fgauto_list_nth_mem L labs n)))
        (transport L (y ↦ WordHeadNotComplement S y (fgauto_factor_letters S t)) x x' (inverse L x' x el) (red .fst))
        (red .snd) q mq
        (fgauto_run_start S V E m (nth b) (fgauto_factor_concat S t) q (inverse V (nth b) m eb) (sp .snd .snd)) in
      let tgt : RS ≔ (a, inr. x') in
      let st' : FgautoStep S RS (fgauto_red_edges S dec B) (i, o) x tgt
        ≔ fgauto_step_transport S RS (fgauto_red_edges S dec B) (i, o) (i, o) x' x tgt tgt (refl ((i, o) : RS)) el (refl tgt) st in
      let runA : FgautoRun S RS (fgauto_red_edges S dec B) (i, o) (cons. x (fgauto_factor_letters S t)) (rb .fst, rb .snd .fst)
        ≔ (tgt, (st', rb .snd .snd .snd .fst)) in
      (rb .fst, (rb .snd .fst, (rb .snd .snd .fst, (runA, rb .snd .snd .snd .snd)))) ]

{` fggroups.tex:879 for one automaton. `}
def fgauto_red_nfa_language (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (u : SignedWord S)
  : FgautoIff (FgautoReductionImage S dec (FgautoNFAAccepts S B) u) (FgautoNFAAccepts S (fgauto_red_nfa S dec B) u)
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let E ≔ B .nedges in
    let L ≔ SignedLetter S in
    let RS ≔ FgautoRState S B in
    let A' ≔ fgauto_red_nfa S dec B in
    let mi ≔ fgauto_nfa_init_state S B in
    let i0 ≔ fgauto_nfa_pos S B (B .ninit) mi in
    let ei ≔ fgauto_nfa_nth_pos S B (B .ninit) mi in
    let TA' ≔ Σ RS (f ↦ Product (FgautoMem RS f (A' .nfinal)) (FgautoRun S RS (fgauto_red_edges S dec B) (i0, inl. star.) u f)) in
    let TB ≔ (w : SignedWord S) ↦ Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (FgautoRun S V E (B .ninit) w f)) in
    (h ↦ mere_rec (Σ (SignedWord S) (v ↦ Product (FgautoNFAAccepts S B v) (Id (SignedWord S) (word_reduction S dec v) u)))
       (FgautoNFAAccepts S A' u) (mere_isprop TA')
       (z ↦ mere_rec (TB (z .fst)) (FgautoNFAAccepts S A' u) (mere_isprop TA')
         (y ↦
           let v ≔ z .fst in
           let fa ≔ fgauto_red_factorization S dec v in
           let d0 ≔ fa .fst in
           let ps ≔ fa .snd .fst in
           let rv ≔ fgauto_run_word S V E (B .ninit) v (append L d0 (fgauto_factor_concat S ps)) (y .fst) (fa .snd .snd .fst) (y .snd .snd) in
           let sp ≔ fgauto_run_split S V E (B .ninit) d0 (fgauto_factor_concat S ps) (y .fst) rv in
           let s ≔ sp .fst in
           let ms ≔ fgauto_nfa_endpoint_state_run S B (B .ninit) mi d0 s (sp .snd .fst) in
           let i1 ≔ fgauto_nfa_pos S B s ms in
           let e1 ≔ fgauto_nfa_nth_pos S B s ms in
           let hD ≔ fgauto_drel_complete S dec B (length L d0) d0 (le_refl (length L d0)) i0 i1
             (fgauto_run_start S V E (B .ninit) (nth i0) d0 (nth i1) (inverse V (nth i0) (B .ninit) ei)
               (fgauto_run_end S V E (B .ninit) d0 s (nth i1) (inverse V (nth i1) s e1) (sp .snd .fst)))
             (fa .snd .snd .snd .fst) in
           let mf ≔ fgauto_nfa_final_state S B (y .fst) (y .snd .fst) in
           let er ≔ fa .snd .snd .snd .snd .snd in
           let red ≔ transport (SignedWord S) (IsReducedWord S) (word_reduction S dec v) (fgauto_factor_letters S ps) er (word_reduction_reduced S dec v) in
           let bd ≔ fgauto_red_build S dec B ps (fa .snd .snd .snd .snd .fst) i0 i1 hD (inl. star.) (inl. (refl (inl. star. : FgautoOpt S))) star. red
             (y .fst) mf (fgauto_run_start S V E s (nth i1) (fgauto_factor_concat S ps) (y .fst) (inverse V (nth i1) s e1) (sp .snd .snd)) in
           let j ≔ bd .fst in
           let o' ≔ bd .snd .fst in
           let jf ≔ fgauto_nfa_pos S B (y .fst) mf in
           let ejf ≔ fgauto_nfa_nth_pos S B (y .fst) mf in
           let eu : Id (SignedWord S) (fgauto_factor_letters S ps) u
             ≔ concat (SignedWord S) (fgauto_factor_letters S ps) (word_reduction S dec v) u
                 (inverse (SignedWord S) (word_reduction S dec v) (fgauto_factor_letters S ps) er) (z .snd .snd) in
           mere TA' ((j, o'),
             (fgauto_filter_mem_intro RS (fgauto_rfinal_bool S dec B) (j, o') (fgauto_red_states S B)
                (fgauto_pair_list_mem (Fin k) (FgautoOpt S) (fgauto_fin_list k) (fgauto_opts S B) j o' (fgauto_fin_list_complete k j) (bd .snd .snd .fst))
                (fgauto_decision_bool_true (FgautoRFinal S dec B (j, o')) (fgauto_rfinal_decide S dec B (j, o'))
                  (jf, (fgauto_mem_transport V (y .fst) (nth jf) (B .nfinal) (inverse V (nth jf) (y .fst) ejf) (y .snd .fst), bd .snd .snd .snd .snd))),
              fgauto_run_word S RS (fgauto_red_edges S dec B) (i0, inl. star.) (fgauto_factor_letters S ps) u (j, o') eu (bd .snd .snd .snd .fst))))
         (z .snd .fst)) h,
     h ↦ mere_rec TA' (FgautoReductionImage S dec (FgautoNFAAccepts S B) u)
       (mere_isprop (Σ (SignedWord S) (v ↦ Product (FgautoNFAAccepts S B v) (Id (SignedWord S) (word_reduction S dec v) u))))
       (z ↦
         let q' ≔ z .fst in
         let fin ≔ fgauto_decision_bool_reflect (FgautoRFinal S dec B q') (fgauto_rfinal_decide S dec B q')
           (fgauto_filter_mem_elim RS (fgauto_rfinal_bool S dec B) q' (fgauto_red_states S B) (z .snd .fst)) in
         let lf ≔ fgauto_red_lift S dec B i0 (inl. star.) u q' (z .snd .snd) in
         let cp ≔ fgauto_red_compat S dec B i0 (inl. star.) u q' (z .snd .snd) in
         let dd ≔ fgauto_drel_sound S dec B (q' .fst) (fin .fst) (fin .snd .snd) in
         let w ≔ append L (lf .fst) (dd .fst) in
         mere (Σ (SignedWord S) (v ↦ Product (FgautoNFAAccepts S B v) (Id (SignedWord S) (word_reduction S dec v) u)))
           (w,
            (mere (TB w) (nth (fin .fst), (fin .snd .fst,
               fgauto_run_start S V E (nth i0) (B .ninit) w (nth (fin .fst)) ei
                 (fgauto_run_append S V E (nth i0) (lf .fst) (nth (q' .fst)) (dd .fst) (nth (fin .fst)) (lf .snd .fst) (dd .snd .fst)))),
             calc
               word_reduction S dec w = word_reduction S dec (lf .fst) by fgauto_red_drop_right S dec (lf .fst) (dd .fst) (dd .snd .snd)
               = word_reduction S dec u by lf .snd .snd
               = u by word_reduction_of_reduced S dec u (cp .snd) ∎))) h)

{` fggroups.tex:879: rho maps regular languages to regular languages. `}
def fgauto_reduction_regular (S : Type) (dec : DecidableEquality S) (L0 : SignedWord S → Type) (hL : FgautoRegular S L0)
  : FgautoRegular S (FgautoReductionImage S dec L0)
  ≔ mere_rec (Σ (FgautoNFA S) (B ↦ (w : SignedWord S) → FgautoIff (L0 w) (FgautoNFAAccepts S B w)))
      (FgautoRegular S (FgautoReductionImage S dec L0))
      (mere_isprop (Σ (FgautoNFA S) (A ↦ (w : SignedWord S) → FgautoIff (FgautoReductionImage S dec L0 w) (FgautoNFAAccepts S A w))))
      (z ↦
        let B ≔ z .fst in
        let hB ≔ z .snd in
        let T1 ≔ (u : SignedWord S) ↦ Σ (SignedWord S) (v ↦ Product (L0 v) (Id (SignedWord S) (word_reduction S dec v) u)) in
        let T2 ≔ (u : SignedWord S) ↦ Σ (SignedWord S) (v ↦ Product (FgautoNFAAccepts S B v) (Id (SignedWord S) (word_reduction S dec v) u)) in
        mere (Σ (FgautoNFA S) (A ↦ (w : SignedWord S) → FgautoIff (FgautoReductionImage S dec L0 w) (FgautoNFAAccepts S A w)))
          (fgauto_red_nfa S dec B,
           u ↦ (x ↦ fgauto_red_nfa_language S dec B u .fst
                  (mere_rec (T1 u) (Mere (T2 u)) (mere_isprop (T2 u)) (y ↦ mere (T2 u) (y .fst, (hB (y .fst) .fst (y .snd .fst), y .snd .snd))) x),
                y ↦ mere_rec (T2 u) (Mere (T1 u)) (mere_isprop (T1 u)) (y0 ↦ mere (T1 u) (y0 .fst, (hB (y0 .fst) .snd (y0 .snd .fst), y0 .snd .snd)))
                  (fgauto_red_nfa_language S dec B u .snd y)))) hL
