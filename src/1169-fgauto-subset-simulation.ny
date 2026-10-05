export "1163-fgauto-research-statements"

{` Chapter 11, automata part 20: tools for the direction "regular preimage
   => recognizable" of fggroups.tex:891 (module 1170).

   (1) Functional graphs: for a complete list U of vertices, a complete list
   L of letters and a step function st, the graph with edges f -x-> st f x
   (f in U, x in L); its runs compute st iterated along the word.
   (2) The subset simulation of a finite automaton B: the states of B are
   listed without repetitions as nth : Fin k → states (all states that occur
   in B), a set of states is a vector Fin k → Bool, fgauto_nfa_delta is one
   step of the subset construction and fgauto_nfa_sim runs it along a word.
   B accepts u iff the simulation from {init} meets the final states
   (fgauto_nfa_accepts_sim). `}

{` Functional graphs. `}
def fgauto_fun_edges_at (S V : Type) (st : V → SignedLetter S → V) (L : List (SignedLetter S)) (f : V) : List (FgautoEdge S V)
  ≔ fgauto_list_map (SignedLetter S) (FgautoEdge S V) (x ↦ (f, x, st f x)) L

def fgauto_fun_edges (S V : Type) (st : V → SignedLetter S → V) (U : List V) (L : List (SignedLetter S)) : List (FgautoEdge S V)
  ≔ fgauto_list_bind V (FgautoEdge S V) U (fgauto_fun_edges_at S V st L)

def fgauto_fun_edges_at_functional (S V : Type) (st : V → SignedLetter S → V) (L : List (SignedLetter S)) (f p : V)
  (x : SignedLetter S) (q : V) (s : FgautoStep S V (fgauto_fun_edges_at S V st L f) p x q) : Id V q (st p x)
  ≔ match L [
  | nil. ↦ match s []
  | cons. y L' ↦ match s [
    | inl. t ↦ concat V q (st f y) (st p x) (t .snd .snd)
        (refl ((u v ↦ st u v) : V → SignedLetter S → V) (inverse V p f (t .fst)) (inverse (SignedLetter S) x y (t .snd .fst)))
    | inr. s' ↦ fgauto_fun_edges_at_functional S V st L' f p x q s' ] ]

def fgauto_fun_iterate (S V : Type) (st : V → SignedLetter S → V) (p : V) (w : SignedWord S) : V
  ≔ match w [ nil. ↦ p | cons. x w' ↦ fgauto_fun_iterate S V st (st p x) w' ]

def fgauto_fun_run_value (S V : Type) (st : V → SignedLetter S → V) (U : List V) (L : List (SignedLetter S)) (p : V)
  (w : SignedWord S) (q : V) (r : FgautoRun S V (fgauto_fun_edges S V st U L) p w q) : Id V q (fgauto_fun_iterate S V st p w)
  ≔ match w [
  | nil. ↦ inverse V p q r
  | cons. x w' ↦ fgauto_fun_run_value S V st U L (st p x) w' q
      (fgauto_run_start S V (fgauto_fun_edges S V st U L) (r .fst) (st p x) w' q
        (fgauto_bind_edges_functional S V st U (fgauto_fun_edges_at S V st L) (fgauto_fun_edges_at_functional S V st L) p x (r .fst) (r .snd .fst))
        (r .snd .snd)) ]

def fgauto_fun_run_exists (S V : Type) (st : V → SignedLetter S → V) (U : List V) (cU : (v : V) → FgautoMem V v U)
  (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L) (p : V) (w : SignedWord S)
  : FgautoRun S V (fgauto_fun_edges S V st U L) p w (fgauto_fun_iterate S V st p w)
  ≔ match w [
  | nil. ↦ refl p
  | cons. x w' ↦ (st p x,
      (fgauto_mem_edge_step S V (fgauto_fun_edges S V st U L) (p, x, st p x)
         (fgauto_mem_bind V (FgautoEdge S V) U (fgauto_fun_edges_at S V st L) p (p, x, st p x) (cU p)
           (fgauto_mem_map (SignedLetter S) (FgautoEdge S V) (y ↦ (p, y, st p y)) x L (cL x))),
       fgauto_fun_run_exists S V st U cU L cL (st p x) w')) ]

{` Decidable equality of Bool-valued vectors and of pairs. `}
def fgauto_bool_decidable_equality : DecidableEquality Bool
  ≔ x y ↦ match x, y [
  | true., true. ↦ inl. (refl (true. : Bool))
  | false., false. ↦ inl. (refl (false. : Bool))
  | true., false. ↦ inr. (e ↦ bool_encode true. false. e)
  | false., true. ↦ inr. (e ↦ bool_encode false. true. e) ]

def fgauto_vec_decidable_equality (k : Nat) : DecidableEquality (Fin k → Bool)
  ≔ f g ↦ match fin_forall_decidable k (i ↦ Id Bool (f i) (g i)) (i ↦ fgauto_bool_decidable_equality (f i) (g i)) [
  | inl. h ↦ inl. (funext (Fin k) (_ ↦ Bool) f g h)
  | inr. no ↦ inr. (p ↦ no (happly (Fin k) (_ ↦ Bool) f g p)) ]

def fgauto_bool_list : List Bool ≔ cons. false. (cons. true. nil.)

def fgauto_bool_list_complete (b : Bool) : FgautoMem Bool b fgauto_bool_list
  ≔ match b [ false. ↦ inl. (refl (false. : Bool)) | true. ↦ inr. (inl. (refl (true. : Bool))) ]

def fgauto_vec_list (k : Nat) : List (Fin k → Bool) ≔ fgauto_fin_functions Bool fgauto_bool_list k

def fgauto_vec_list_complete (k : Nat) (f : Fin k → Bool) : FgautoMem (Fin k → Bool) f (fgauto_vec_list k)
  ≔ fgauto_fin_functions_complete Bool fgauto_bool_list fgauto_bool_list_complete k f

def fgauto_pair_decidable_equality (A B : Type) (dA : DecidableEquality A) (dB : DecidableEquality B) : DecidableEquality (Product A B)
  ≔ u v ↦ match dA (u .fst) (v .fst) [
  | inr. n ↦ inr. (e ↦ n (refl ((z ↦ z .fst) : Product A B → A) e))
  | inl. p ↦ match dB (u .snd) (v .snd) [
    | inr. n ↦ inr. (e ↦ n (refl ((z ↦ z .snd) : Product A B → B) e))
    | inl. q ↦ inl. (p, q) ] ]

def fgauto_pair_list (A B : Type) (la : List A) (lb : List B) : List (Product A B)
  ≔ fgauto_list_bind A (Product A B) la (a ↦ fgauto_list_map B (Product A B) (b ↦ (a, b)) lb)

def fgauto_pair_list_complete (A B : Type) (la : List A) (lb : List B) (ca : (a : A) → FgautoMem A a la)
  (cb : (b : B) → FgautoMem B b lb) (u : Product A B) : FgautoMem (Product A B) u (fgauto_pair_list A B la lb)
  ≔ fgauto_mem_bind A (Product A B) la (a ↦ fgauto_list_map B (Product A B) (b ↦ (a, b)) lb) (u .fst) u (ca (u .fst))
      (fgauto_mem_map B (Product A B) (b ↦ (u .fst, b)) (u .snd) lb (cb (u .snd)))

{` Deciding steps of a graph. `}
def fgauto_step_decide_cons (S V : Type) (p : V) (x : SignedLetter S) (q : V) (e : FgautoEdge S V) (R : Type)
  (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab))) (d3 : Decidable (Id V q (e .tgt)))
  (dr : Decidable R)
  : Decidable (Sum (Product (Id V p (e .src)) (Product (Id (SignedLetter S) x (e .lab)) (Id V q (e .tgt)))) R)
  ≔ match dr [
  | inl. r ↦ inl. (inr. r)
  | inr. nr ↦ match d1 [
    | inr. n1 ↦ inr. (k ↦ match k [ inl. t ↦ n1 (t .fst) | inr. r ↦ nr r ])
    | inl. a ↦ match d2 [
      | inr. n2 ↦ inr. (k ↦ match k [ inl. t ↦ n2 (t .snd .fst) | inr. r ↦ nr r ])
      | inl. b ↦ match d3 [
        | inr. n3 ↦ inr. (k ↦ match k [ inl. t ↦ n3 (t .snd .snd) | inr. r ↦ nr r ])
        | inl. c ↦ inl. (inl. (a, (b, c))) ] ] ] ]

def fgauto_step_decide (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V) (E : List (FgautoEdge S V))
  (p : V) (x : SignedLetter S) (q : V) : Decidable (FgautoStep S V E p x q)
  ≔ match E [
  | nil. ↦ inr. (s ↦ match s [])
  | cons. e E' ↦ fgauto_step_decide_cons S V p x q e (FgautoStep S V E' p x q)
      (dV p (e .src)) (signed_letter_decidable_equality S dec x (e .lab)) (dV q (e .tgt)) (fgauto_step_decide S V dec dV E' p x q) ]

{` The states of an automaton. `}
def fgauto_nfa_states (S : Type) (B : FgautoNFA S) : List (B .nstate)
  ≔ fgauto_dedup (B .nstate) (B .ndec)
      (cons. (B .ninit) (append (B .nstate) (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges))))

def fgauto_nfa_k (S : Type) (B : FgautoNFA S) : Nat ≔ length (B .nstate) (fgauto_nfa_states S B)

def fgauto_nfa_nth (S : Type) (B : FgautoNFA S) (j : Fin (fgauto_nfa_k S B)) : B .nstate
  ≔ fgauto_list_nth (B .nstate) (fgauto_nfa_states S B) j

def fgauto_nfa_pos (S : Type) (B : FgautoNFA S) (v : B .nstate) (m : FgautoMem (B .nstate) v (fgauto_nfa_states S B))
  : Fin (fgauto_nfa_k S B)
  ≔ fgauto_list_pos (B .nstate) (B .ndec) v (fgauto_nfa_states S B) m

def fgauto_nfa_nth_pos (S : Type) (B : FgautoNFA S) (v : B .nstate) (m : FgautoMem (B .nstate) v (fgauto_nfa_states S B))
  : Id (B .nstate) (fgauto_nfa_nth S B (fgauto_nfa_pos S B v m)) v
  ≔ fgauto_list_pos_nth (B .nstate) (B .ndec) v (fgauto_nfa_states S B) m

def fgauto_list_pos_irr_choose (V : Type) (v v' a : V) (t : List V) (e : Id V v v') (d : Decidable (Id V v a)) (d' : Decidable (Id V v' a))
  (rec1 : FgautoMem V v t → Fin (length V t)) (rec2 : FgautoMem V v' t → Fin (length V t))
  (ih : (k : FgautoMem V v t) (k' : FgautoMem V v' t) → Id (Fin (length V t)) (rec1 k) (rec2 k'))
  (m : FgautoMem V v (cons. a t)) (m' : FgautoMem V v' (cons. a t))
  : Id (Fin (length V (cons. a t))) (fgauto_list_pos_choose V v a t d rec1 m) (fgauto_list_pos_choose V v' a t d' rec2 m')
  ≔ match d [
  | inl. p ↦ match d' [
    | inl. _ ↦ refl (inr. star. : Fin (length V (cons. a t)))
    | inr. n' ↦ match n' (concat V v' v a (inverse V v v' e) p) [] ]
  | inr. n ↦ match d' [
    | inl. p' ↦ match n (concat V v v' a e p') []
    | inr. n' ↦ inl. (ih (fgauto_mem_tail V v a t n m) (fgauto_mem_tail V v' a t n' m')) ] ]

def fgauto_list_pos_irrelevant (V : Type) (dV : DecidableEquality V) (v v' : V) (l : List V) (e : Id V v v')
  (m : FgautoMem V v l) (m' : FgautoMem V v' l)
  : Id (Fin (length V l)) (fgauto_list_pos V dV v l m) (fgauto_list_pos V dV v' l m')
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ fgauto_list_pos_irr_choose V v v' a t e (dV v a) (dV v' a) (fgauto_list_pos V dV v t) (fgauto_list_pos V dV v' t)
      (k k' ↦ fgauto_list_pos_irrelevant V dV v v' t e k k') m m' ]

def fgauto_nfa_nth_injective (S : Type) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B))
  (e : Id (B .nstate) (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j)) : Id (Fin (fgauto_nfa_k S B)) i j
  ≔ let l ≔ fgauto_nfa_states S B in
    let nd ≔ fgauto_dedup_nodup (B .nstate) (B .ndec)
      (cons. (B .ninit) (append (B .nstate) (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges)))) in
    let mi ≔ fgauto_list_nth_mem (B .nstate) l i in
    let mj ≔ fgauto_list_nth_mem (B .nstate) l j in
    concat (Fin (fgauto_nfa_k S B)) i (fgauto_nfa_pos S B (fgauto_nfa_nth S B i) mi) j
      (inverse (Fin (fgauto_nfa_k S B)) (fgauto_nfa_pos S B (fgauto_nfa_nth S B i) mi) i (fgauto_list_nth_pos (B .nstate) (B .ndec) l nd i mi))
      (concat (Fin (fgauto_nfa_k S B)) (fgauto_nfa_pos S B (fgauto_nfa_nth S B i) mi) (fgauto_nfa_pos S B (fgauto_nfa_nth S B j) mj) j
        (fgauto_list_pos_irrelevant (B .nstate) (B .ndec) (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) l e mi mj)
        (fgauto_list_nth_pos (B .nstate) (B .ndec) l nd j mj))

def fgauto_nfa_endpoint_state (S : Type) (B : FgautoNFA S) (p : B .nstate) (x : SignedLetter S) (q : B .nstate)
  (s : FgautoStep S (B .nstate) (B .nedges) p x q) : FgautoMem (B .nstate) q (fgauto_nfa_states S B)
  ≔ fgauto_dedup_mem_intro (B .nstate) (B .ndec) q
      (cons. (B .ninit) (append (B .nstate) (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges))))
      (inr. (fgauto_mem_append_right (B .nstate) q (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges))
        (fgauto_endpoints_in S (B .nstate) (B .nedges) p x q s .snd)))

def fgauto_nfa_final_state (S : Type) (B : FgautoNFA S) (f : B .nstate) (m : FgautoMem (B .nstate) f (B .nfinal))
  : FgautoMem (B .nstate) f (fgauto_nfa_states S B)
  ≔ fgauto_dedup_mem_intro (B .nstate) (B .ndec) f
      (cons. (B .ninit) (append (B .nstate) (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges))))
      (inr. (fgauto_mem_append_left (B .nstate) f (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges)) m))

def fgauto_nfa_init_state (S : Type) (B : FgautoNFA S) : FgautoMem (B .nstate) (B .ninit) (fgauto_nfa_states S B)
  ≔ fgauto_dedup_mem_intro (B .nstate) (B .ndec) (B .ninit)
      (cons. (B .ninit) (append (B .nstate) (B .nfinal) (fgauto_endpoints S (B .nstate) (B .nedges)))) (inl. (refl (B .ninit)))

{` The subset simulation. `}
def FgautoNfaDeltaPred (S : Type) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool) (x : SignedLetter S)
  (j : Fin (fgauto_nfa_k S B)) (j' : Fin (fgauto_nfa_k S B)) : Type
  ≔ Product (Id Bool (P j') true.) (FgautoStep S (B .nstate) (B .nedges) (fgauto_nfa_nth S B j') x (fgauto_nfa_nth S B j))

def fgauto_nfa_delta_decide (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool)
  (x : SignedLetter S) (j : Fin (fgauto_nfa_k S B)) : Decidable (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaDeltaPred S B P x j))
  ≔ fin_sigma_decidable (fgauto_nfa_k S B) (FgautoNfaDeltaPred S B P x j)
      (j' ↦ match fgauto_bool_decide_true (P j') [
       | inr. n ↦ inr. (h ↦ n (h .fst))
       | inl. t ↦ match fgauto_step_decide S (B .nstate) dec (B .ndec) (B .nedges) (fgauto_nfa_nth S B j') x (fgauto_nfa_nth S B j) [
         | inl. s ↦ inl. (t, s)
         | inr. n ↦ inr. (h ↦ n (h .snd)) ] ])

def fgauto_nfa_delta (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool)
  (x : SignedLetter S) : Fin (fgauto_nfa_k S B) → Bool
  ≔ j ↦ fgauto_decision_bool (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaDeltaPred S B P x j)) (fgauto_nfa_delta_decide S dec B P x j)

def fgauto_nfa_sim (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool) (w : SignedWord S)
  : Fin (fgauto_nfa_k S B) → Bool
  ≔ fgauto_fun_iterate S (Fin (fgauto_nfa_k S B) → Bool) (fgauto_nfa_delta S dec B) P w

def fgauto_nfa_sim_sound (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool)
  (w : SignedWord S) (j : Fin (fgauto_nfa_k S B)) (t : Id Bool (fgauto_nfa_sim S dec B P w j) true.)
  : Σ (Fin (fgauto_nfa_k S B)) (j' ↦ Product (Id Bool (P j') true.)
      (FgautoRun S (B .nstate) (B .nedges) (fgauto_nfa_nth S B j') w (fgauto_nfa_nth S B j)))
  ≔ match w [
  | nil. ↦ (j, (t, refl (fgauto_nfa_nth S B j)))
  | cons. x w' ↦
    let z ≔ fgauto_nfa_sim_sound S dec B (fgauto_nfa_delta S dec B P x) w' j t in
    let y ≔ fgauto_decision_bool_reflect (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaDeltaPred S B P x (z .fst)))
      (fgauto_nfa_delta_decide S dec B P x (z .fst)) (z .snd .fst) in
    (y .fst, (y .snd .fst, (fgauto_nfa_nth S B (z .fst), (y .snd .snd, z .snd .snd)))) ]

def fgauto_nfa_sim_complete (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool)
  (j' : Fin (fgauto_nfa_k S B)) (hP : Id Bool (P j') true.) (w : SignedWord S) (j : Fin (fgauto_nfa_k S B))
  (r : FgautoRun S (B .nstate) (B .nedges) (fgauto_nfa_nth S B j') w (fgauto_nfa_nth S B j))
  : Id Bool (fgauto_nfa_sim S dec B P w j) true.
  ≔ match w [
  | nil. ↦ transport (Fin (fgauto_nfa_k S B)) (i ↦ Id Bool (P i) true.) j' j (fgauto_nfa_nth_injective S B j' j r) hP
  | cons. x w' ↦
    let mq ≔ fgauto_nfa_endpoint_state S B (fgauto_nfa_nth S B j') x (r .fst) (r .snd .fst) in
    let j1 ≔ fgauto_nfa_pos S B (r .fst) mq in
    let e1 ≔ fgauto_nfa_nth_pos S B (r .fst) mq in
    fgauto_nfa_sim_complete S dec B (fgauto_nfa_delta S dec B P x) j1
      (fgauto_decision_bool_true (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaDeltaPred S B P x j1)) (fgauto_nfa_delta_decide S dec B P x j1)
        (j', (hP, fgauto_step_transport S (B .nstate) (B .nedges) (fgauto_nfa_nth S B j') (fgauto_nfa_nth S B j') x x (r .fst)
          (fgauto_nfa_nth S B j1) (refl (fgauto_nfa_nth S B j')) (refl x) (inverse (B .nstate) (fgauto_nfa_nth S B j1) (r .fst) e1) (r .snd .fst))))
      w' j (fgauto_run_start S (B .nstate) (B .nedges) (r .fst) (fgauto_nfa_nth S B j1) w' (fgauto_nfa_nth S B j)
        (inverse (B .nstate) (fgauto_nfa_nth S B j1) (r .fst) e1) (r .snd .snd)) ]

{` Acceptance in terms of the simulation. `}
def fgauto_nfa_init_vec (S : Type) (B : FgautoNFA S) : Fin (fgauto_nfa_k S B) → Bool
  ≔ j ↦ fgauto_decision_bool (Id (B .nstate) (fgauto_nfa_nth S B j) (B .ninit)) (B .ndec (fgauto_nfa_nth S B j) (B .ninit))

def FgautoNfaMeetsPred (S : Type) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool) (j : Fin (fgauto_nfa_k S B)) : Type
  ≔ Product (Id Bool (P j) true.) (FgautoMem (B .nstate) (fgauto_nfa_nth S B j) (B .nfinal))

def fgauto_nfa_meets_decide (S : Type) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool)
  : Decidable (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaMeetsPred S B P))
  ≔ fin_sigma_decidable (fgauto_nfa_k S B) (FgautoNfaMeetsPred S B P)
      (j ↦ match fgauto_bool_decide_true (P j) [
       | inr. n ↦ inr. (h ↦ n (h .fst))
       | inl. t ↦ match fgauto_mem_decide (B .nstate) (B .ndec) (fgauto_nfa_nth S B j) (B .nfinal) [
         | inl. m ↦ inl. (t, m)
         | inr. n ↦ inr. (h ↦ n (h .snd)) ] ])

def fgauto_nfa_meets (S : Type) (B : FgautoNFA S) (P : Fin (fgauto_nfa_k S B) → Bool) : Bool
  ≔ fgauto_decision_bool (Σ (Fin (fgauto_nfa_k S B)) (FgautoNfaMeetsPred S B P)) (fgauto_nfa_meets_decide S B P)

def fgauto_nfa_accepts_sim (S : Type) (dec : DecidableEquality S) (B : FgautoNFA S) (w : SignedWord S)
  : FgautoIff (FgautoNFAAccepts S B w) (Id Bool (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B (fgauto_nfa_init_vec S B) w)) true.)
  ≔ let k ≔ fgauto_nfa_k S B in
    let I ≔ fgauto_nfa_init_vec S B in
    let mi ≔ fgauto_nfa_init_state S B in
    let ji ≔ fgauto_nfa_pos S B (B .ninit) mi in
    let ei ≔ fgauto_nfa_nth_pos S B (B .ninit) mi in
    (h ↦ mere_rec (Σ (B .nstate) (f ↦ Product (FgautoMem (B .nstate) f (B .nfinal)) (FgautoRun S (B .nstate) (B .nedges) (B .ninit) w f)))
       (Id Bool (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B I w)) true.)
       (bool_set (fgauto_nfa_meets S B (fgauto_nfa_sim S dec B I w)) true.)
       (z ↦
         let mf ≔ fgauto_nfa_final_state S B (z .fst) (z .snd .fst) in
         let jf ≔ fgauto_nfa_pos S B (z .fst) mf in
         let ef ≔ fgauto_nfa_nth_pos S B (z .fst) mf in
         fgauto_decision_bool_true (Σ (Fin k) (FgautoNfaMeetsPred S B (fgauto_nfa_sim S dec B I w)))
           (fgauto_nfa_meets_decide S B (fgauto_nfa_sim S dec B I w))
           (jf, (fgauto_nfa_sim_complete S dec B I ji
                   (fgauto_decision_bool_true (Id (B .nstate) (fgauto_nfa_nth S B ji) (B .ninit)) (B .ndec (fgauto_nfa_nth S B ji) (B .ninit)) ei)
                   w jf
                   (fgauto_run_end S (B .nstate) (B .nedges) (fgauto_nfa_nth S B ji) w (z .fst) (fgauto_nfa_nth S B jf)
                     (inverse (B .nstate) (fgauto_nfa_nth S B jf) (z .fst) ef)
                     (fgauto_run_start S (B .nstate) (B .nedges) (B .ninit) (fgauto_nfa_nth S B ji) w (z .fst)
                       (inverse (B .nstate) (fgauto_nfa_nth S B ji) (B .ninit) ei) (z .snd .snd))),
                 fgauto_mem_transport (B .nstate) (z .fst) (fgauto_nfa_nth S B jf) (B .nfinal)
                   (inverse (B .nstate) (fgauto_nfa_nth S B jf) (z .fst) ef) (z .snd .fst)))) h,
     t ↦
       let y ≔ fgauto_decision_bool_reflect (Σ (Fin k) (FgautoNfaMeetsPred S B (fgauto_nfa_sim S dec B I w)))
         (fgauto_nfa_meets_decide S B (fgauto_nfa_sim S dec B I w)) t in
       let z ≔ fgauto_nfa_sim_sound S dec B I w (y .fst) (y .snd .fst) in
       let e0 ≔ fgauto_decision_bool_reflect (Id (B .nstate) (fgauto_nfa_nth S B (z .fst)) (B .ninit))
         (B .ndec (fgauto_nfa_nth S B (z .fst)) (B .ninit)) (z .snd .fst) in
       mere (Σ (B .nstate) (f ↦ Product (FgautoMem (B .nstate) f (B .nfinal)) (FgautoRun S (B .nstate) (B .nedges) (B .ninit) w f)))
         (fgauto_nfa_nth S B (y .fst), (y .snd .snd,
           fgauto_run_start S (B .nstate) (B .nedges) (fgauto_nfa_nth S B (z .fst)) (B .ninit) w (fgauto_nfa_nth S B (y .fst)) e0 (z .snd .snd))))

def fgauto_fun_iterate_append (S V : Type) (st : V → SignedLetter S → V) (p : V) (u v : SignedWord S)
  : Id V (fgauto_fun_iterate S V st p (append (SignedLetter S) u v)) (fgauto_fun_iterate S V st (fgauto_fun_iterate S V st p u) v)
  ≔ match u [ nil. ↦ refl (fgauto_fun_iterate S V st p v) | cons. x u' ↦ fgauto_fun_iterate_append S V st (st p x) u' v ]
