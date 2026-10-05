export "1153-fgauto-stallings"

{` Chapter 11, automata part 6: reachability in finite graphs and
   generators of the loops at a vertex (spanning trees).

   For a graph E (edge list over a vertex type V with decidable equality)
   and a vertex i, fgauto_reach computes by a breadth-first closure a list
   of vertices reachable from i, each with a word labelling a run from i
   (a spanning tree with root i).  The closure adds one new vertex per
   round; since the listed vertices are distinct and occur among i and the
   endpoints of E, length(i :: endpoints E) rounds suffice, after which the
   list is closed under steps and so contains every vertex reachable from i
   (fgauto_reach_complete).

   For every edge p -x-> q with p reachable, t_p x t_q^-1 (t_v the tree
   word of v, t_i = eps) labels a closed walk at i; these words generate
   the reductions of all loops at i (fgauto_loop_gens_generate).  This is
   the generation half of the running-text claim at fggroups.tex:943 ("a
   basis for H from a spanning tree of S(H)"). `}

{` Generic lists: map, decidable membership, no repetitions. `}
def fgauto_list_map (A B : Type) (f : A → B) (l : List A) : List B
  ≔ match l [ nil. ↦ nil. | cons. a t ↦ cons. (f a) (fgauto_list_map A B f t) ]

def fgauto_mem_map (A B : Type) (f : A → B) (a : A) (l : List A) (m : FgautoMem A a l)
  : FgautoMem B (f a) (fgauto_list_map A B f l)
  ≔ match l [
  | nil. ↦ match m []
  | cons. b t ↦ match m [ inl. e ↦ inl. (refl f e) | inr. m' ↦ inr. (fgauto_mem_map A B f a t m') ] ]

def fgauto_mem_decide_cons (V : Type) (a b : V) (t : List V) (d : Decidable (Id V a b))
  (r : Decidable (FgautoMem V a t)) : Decidable (FgautoMem V a (cons. b t))
  ≔ match d [
  | inl. e ↦ inl. (inl. e)
  | inr. n ↦ match r [
    | inl. m ↦ inl. (inr. m)
    | inr. nm ↦ inr. (k ↦ match k [ inl. e ↦ n e | inr. m ↦ nm m ]) ] ]

def fgauto_mem_decide (V : Type) (dV : DecidableEquality V) (a : V) (l : List V) : Decidable (FgautoMem V a l)
  ≔ match l [
  | nil. ↦ inr. (k ↦ match k [])
  | cons. b t ↦ fgauto_mem_decide_cons V a b t (dV a b) (fgauto_mem_decide V dV a t) ]

def FgautoNoDup (V : Type) (l : List V) : Type
  ≔ match l [ nil. ↦ Unit | cons. a t ↦ Product (Not (FgautoMem V a t)) (FgautoNoDup V t) ]

{` A repetition-free list inside Vs is not longer than Vs. `}
def fgauto_nodup_length (V : Type) (dV : DecidableEquality V) (l Vs : List V) (nd : FgautoNoDup V l)
  (sub : (a : V) → FgautoMem V a l → FgautoMem V a Vs) : Le (length V l) (length V Vs)
  ≔ match l [
  | nil. ↦ star.
  | cons. a t ↦ le_trans (suc. (length V t)) (suc. (length V (fgauto_remove V dV a Vs))) (length V Vs)
      (fgauto_nodup_length V dV t (fgauto_remove V dV a Vs) (nd .snd)
        (b m ↦ fgauto_remove_mem V dV a b Vs
          (e ↦ nd .fst (fgauto_mem_transport V b a t e m)) (sub b (inr. m))))
      (fgauto_remove_lt V dV a Vs (sub a (inl. (refl a)))) ]

{` Searching the steps of a graph for a decidable property. `}
def fgauto_step_prop_transport (S V : Type) (P : V → SignedLetter S → V → Type) (p p' : V) (x x' : SignedLetter S)
  (q q' : V) (a : Id V p p') (b : Id (SignedLetter S) x x') (c : Id V q q') (h : P p x q) : P p' x' q'
  ≔ transport V (z ↦ P p' x' z) q q' c
      (transport (SignedLetter S) (z ↦ P p' z q) x x' b (transport V (z ↦ P z x q) p p' a h))

def FgautoFoundStep (S V : Type) (E : List (FgautoEdge S V)) (P : V → SignedLetter S → V → Type) : Type
  ≔ Σ V (p ↦ Σ (SignedLetter S) (x ↦ Σ V (q ↦ Product (FgautoStep S V E p x q) (P p x q))))

def fgauto_find_step_pick (S V : Type) (E : List (FgautoEdge S V)) (P : V → SignedLetter S → V → Type)
  (e : FgautoEdge S V) (L : List (FgautoEdge S V)) (i : FgautoStepIncl S V (cons. e L) E)
  (d : Decidable (P (e .src) (e .lab) (e .tgt)))
  (rest : Sum (FgautoFoundStep S V E P) ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V L p x q → Not (P p x q)))
  : Sum (FgautoFoundStep S V E P) ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V (cons. e L) p x q → Not (P p x q))
  ≔ match d [
  | inl. h ↦ inl. (e .src, (e .lab, (e .tgt, (i (e .src) (e .lab) (e .tgt) (fgauto_step_head S V e L), h))))
  | inr. n ↦ match rest [
    | inl. f ↦ inl. f
    | inr. g ↦ inr. (p x q s h ↦ match s [
      | inl. t ↦ n (fgauto_step_prop_transport S V P p (e .src) x (e .lab) q (e .tgt) (t .fst) (t .snd .fst) (t .snd .snd) h)
      | inr. s' ↦ g p x q s' h ]) ] ]

def fgauto_find_step_in (S V : Type) (E : List (FgautoEdge S V)) (P : V → SignedLetter S → V → Type)
  (dP : (p : V) (x : SignedLetter S) (q : V) → Decidable (P p x q)) (L : List (FgautoEdge S V))
  (i : FgautoStepIncl S V L E)
  : Sum (FgautoFoundStep S V E P) ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V L p x q → Not (P p x q))
  ≔ match L [
  | nil. ↦ inr. (p x q s ↦ match s [])
  | cons. e L' ↦ fgauto_find_step_pick S V E P e L' i (dP (e .src) (e .lab) (e .tgt))
      (fgauto_find_step_in S V E P dP L' (p0 x0 q0 s ↦ i p0 x0 q0 (inr. s))) ]

def fgauto_find_step (S V : Type) (E : List (FgautoEdge S V)) (P : V → SignedLetter S → V → Type)
  (dP : (p : V) (x : SignedLetter S) (q : V) → Decidable (P p x q))
  : Sum (FgautoFoundStep S V E P) ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Not (P p x q))
  ≔ fgauto_find_step_in S V E P dP E (p0 x0 q0 s ↦ s)

{` Reach lists: vertices with a run from i. `}
def FgautoReachEntry (S V : Type) (E : List (FgautoEdge S V)) (i : V) : Type
  ≔ Σ V (v ↦ Σ (SignedWord S) (w ↦ FgautoRun S V E i w v))

def fgauto_reach_vertices (S V : Type) (E : List (FgautoEdge S V)) (i : V) (R : List (FgautoReachEntry S V E i))
  : List V
  ≔ fgauto_list_map (FgautoReachEntry S V E i) V (z ↦ z .fst) R

def fgauto_reach_entry_of_mem (S V : Type) (E : List (FgautoEdge S V)) (i : V) (v : V)
  (R : List (FgautoReachEntry S V E i)) (m : FgautoMem V v (fgauto_reach_vertices S V E i R))
  : Σ (SignedWord S) (w ↦ FgautoRun S V E i w v)
  ≔ match R [
  | nil. ↦ match m []
  | cons. z R' ↦ match m [
    | inl. e ↦ (z .snd .fst, fgauto_run_end S V E i (z .snd .fst) (z .fst) v (inverse V v (z .fst) e) (z .snd .snd))
    | inr. m' ↦ fgauto_reach_entry_of_mem S V E i v R' m' ] ]

{` One round of the closure: find a step from a listed vertex to an
   unlisted one. `}
def FgautoBfsPred (S V : Type) (E : List (FgautoEdge S V)) (i : V) (R : List (FgautoReachEntry S V E i))
  (p : V) (x : SignedLetter S) (q : V) : Type
  ≔ Product (FgautoMem V p (fgauto_reach_vertices S V E i R)) (Not (FgautoMem V q (fgauto_reach_vertices S V E i R)))

def fgauto_bfs_pred_decide (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (R : List (FgautoReachEntry S V E i)) (p : V) (x : SignedLetter S) (q : V) : Decidable (FgautoBfsPred S V E i R p x q)
  ≔ match fgauto_mem_decide V dV p (fgauto_reach_vertices S V E i R) [
  | inr. n ↦ inr. (h ↦ n (h .fst))
  | inl. mp ↦ match fgauto_mem_decide V dV q (fgauto_reach_vertices S V E i R) [
    | inl. mq ↦ inr. (h ↦ h .snd mq)
    | inr. nq ↦ inl. (mp, nq) ] ]

def fgauto_bfs_new_entry (S V : Type) (E : List (FgautoEdge S V)) (i : V) (R : List (FgautoReachEntry S V E i))
  (f : FgautoFoundStep S V E (FgautoBfsPred S V E i R)) : FgautoReachEntry S V E i
  ≔ let p ≔ f .fst in
    let x ≔ f .snd .fst in
    let q ≔ f .snd .snd .fst in
    let z ≔ fgauto_reach_entry_of_mem S V E i p R (f .snd .snd .snd .snd .fst) in
    (q, (append (SignedLetter S) (z .fst) (cons. x nil.),
      fgauto_run_append S V E i (z .fst) p (cons. x nil.) q (z .snd)
        (fgauto_run_single S V E p x q (f .snd .snd .snd .fst))))

def fgauto_bfs_step (S V : Type) (E : List (FgautoEdge S V)) (i : V)
  (k : List (FgautoReachEntry S V E i) → List (FgautoReachEntry S V E i)) (R : List (FgautoReachEntry S V E i))
  (d : Sum (FgautoFoundStep S V E (FgautoBfsPred S V E i R))
         ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Not (FgautoBfsPred S V E i R p x q)))
  : List (FgautoReachEntry S V E i)
  ≔ match d [ inr. _ ↦ R | inl. f ↦ k (cons. (fgauto_bfs_new_entry S V E i R f) R) ]

def fgauto_bfs (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) (fuel : Nat)
  (R : List (FgautoReachEntry S V E i)) : List (FgautoReachEntry S V E i)
  ≔ match fuel [
  | zero. ↦ R
  | suc. f ↦ fgauto_bfs_step S V E i (fgauto_bfs S V dV E i f) R
      (fgauto_find_step S V E (FgautoBfsPred S V E i R) (fgauto_bfs_pred_decide S V dV E i R)) ]

{` Listed vertices stay listed. `}
def fgauto_bfs_mono_step (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) (f : Nat)
  (recur : (R1 : List (FgautoReachEntry S V E i)) (v : V) → FgautoMem V v (fgauto_reach_vertices S V E i R1)
    → FgautoMem V v (fgauto_reach_vertices S V E i (fgauto_bfs S V dV E i f R1)))
  (R : List (FgautoReachEntry S V E i)) (v : V) (m : FgautoMem V v (fgauto_reach_vertices S V E i R))
  (d : Sum (FgautoFoundStep S V E (FgautoBfsPred S V E i R))
         ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Not (FgautoBfsPred S V E i R p x q)))
  : FgautoMem V v (fgauto_reach_vertices S V E i (fgauto_bfs_step S V E i (fgauto_bfs S V dV E i f) R d))
  ≔ match d [ inr. _ ↦ m | inl. fs ↦ recur (cons. (fgauto_bfs_new_entry S V E i R fs) R) v (inr. m) ]

def fgauto_bfs_mono (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) (fuel : Nat)
  (R : List (FgautoReachEntry S V E i)) (v : V) (m : FgautoMem V v (fgauto_reach_vertices S V E i R))
  : FgautoMem V v (fgauto_reach_vertices S V E i (fgauto_bfs S V dV E i fuel R))
  ≔ match fuel [
  | zero. ↦ m
  | suc. f ↦ fgauto_bfs_mono_step S V dV E i f (fgauto_bfs_mono S V dV E i f) R v m
      (fgauto_find_step S V E (FgautoBfsPred S V E i R) (fgauto_bfs_pred_decide S V dV E i R)) ]

{` With enough fuel the result is closed under steps. `}
def FgautoStepClosed (S V : Type) (E : List (FgautoEdge S V)) (Vs : List V) : Type
  ≔ (p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → FgautoMem V p Vs → FgautoMem V q Vs

def fgauto_closed_of_none (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (R : List (FgautoReachEntry S V E i))
  (g : (p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Not (FgautoBfsPred S V E i R p x q))
  : FgautoStepClosed S V E (fgauto_reach_vertices S V E i R)
  ≔ p x q s mp ↦ match fgauto_mem_decide V dV q (fgauto_reach_vertices S V E i R) [
  | inl. mq ↦ mq
  | inr. nq ↦ match g p x q s (mp, nq) [] ]

def fgauto_reach_universe (S V : Type) (E : List (FgautoEdge S V)) (i : V) : List V
  ≔ cons. i (fgauto_endpoints S V E)

def FgautoBfsInv (S V : Type) (E : List (FgautoEdge S V)) (i : V) (fuel : Nat) (R : List (FgautoReachEntry S V E i)) : Type
  ≔ Product (FgautoNoDup V (fgauto_reach_vertices S V E i R))
      (Product ((v : V) → FgautoMem V v (fgauto_reach_vertices S V E i R) → FgautoMem V v (fgauto_reach_universe S V E i))
        (Le (suc. (length V (fgauto_reach_universe S V E i))) (add (length (FgautoReachEntry S V E i) R) fuel)))

def fgauto_reach_vertices_length (S V : Type) (E : List (FgautoEdge S V)) (i : V) (R : List (FgautoReachEntry S V E i))
  : Id Nat (length V (fgauto_reach_vertices S V E i R)) (length (FgautoReachEntry S V E i) R)
  ≔ match R [ nil. ↦ refl (zero. : Nat) | cons. z R' ↦ suc. (fgauto_reach_vertices_length S V E i R') ]

def fgauto_bfs_closed_step (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) (f : Nat)
  (recur : (R1 : List (FgautoReachEntry S V E i)) → FgautoBfsInv S V E i f R1
    → FgautoStepClosed S V E (fgauto_reach_vertices S V E i (fgauto_bfs S V dV E i f R1)))
  (R : List (FgautoReachEntry S V E i)) (h : FgautoBfsInv S V E i (suc. f) R)
  (d : Sum (FgautoFoundStep S V E (FgautoBfsPred S V E i R))
         ((p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Not (FgautoBfsPred S V E i R p x q)))
  : FgautoStepClosed S V E (fgauto_reach_vertices S V E i (fgauto_bfs_step S V E i (fgauto_bfs S V dV E i f) R d))
  ≔ match d [
  | inr. g ↦ fgauto_closed_of_none S V dV E i R g
  | inl. fs ↦
    let q ≔ fs .snd .snd .fst in
    let U ≔ fgauto_reach_universe S V E i in
    recur (cons. (fgauto_bfs_new_entry S V E i R fs) R)
      ((fs .snd .snd .snd .snd .snd, h .fst),
       (v m ↦ match m [
         | inl. e ↦ fgauto_mem_transport V q v U (inverse V v q e)
             (inr. (fgauto_endpoints_in S V E (fs .fst) (fs .snd .fst) q (fs .snd .snd .snd .fst) .snd))
         | inr. m' ↦ h .snd .fst v m' ],
        transport Nat (z ↦ Le (suc. (length V U)) z)
          (suc. (add (length (FgautoReachEntry S V E i) R) f))
          (add (suc. (length (FgautoReachEntry S V E i) R)) f)
          (inverse Nat (add (suc. (length (FgautoReachEntry S V E i) R)) f)
            (suc. (add (length (FgautoReachEntry S V E i) R) f))
            (add_suc_left (length (FgautoReachEntry S V E i) R) f))
          (h .snd .snd))) ]

def fgauto_bfs_closed (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) (fuel : Nat)
  (R : List (FgautoReachEntry S V E i)) (h : FgautoBfsInv S V E i fuel R)
  : FgautoStepClosed S V E (fgauto_reach_vertices S V E i (fgauto_bfs S V dV E i fuel R))
  ≔ match fuel [
  | zero. ↦
    let U ≔ fgauto_reach_universe S V E i in
    let n ≔ length (FgautoReachEntry S V E i) R in
    let bound : Le (length V (fgauto_reach_vertices S V E i R)) (length V U)
      ≔ fgauto_nodup_length V dV (fgauto_reach_vertices S V E i R) U (h .fst) (h .snd .fst) in
    match lt_irrefl (length V U)
      (le_trans (suc. (length V U)) n (length V U) (h .snd .snd)
        (transport Nat (z ↦ Le z (length V U)) (length V (fgauto_reach_vertices S V E i R)) n
          (fgauto_reach_vertices_length S V E i R) bound)) []
  | suc. f ↦ fgauto_bfs_closed_step S V dV E i f (fgauto_bfs_closed S V dV E i f) R h
      (fgauto_find_step S V E (FgautoBfsPred S V E i R) (fgauto_bfs_pred_decide S V dV E i R)) ]

{` The reachable vertices from i, with spanning-tree words. `}
def fgauto_reach_start (S V : Type) (E : List (FgautoEdge S V)) (i : V) : List (FgautoReachEntry S V E i)
  ≔ cons. (i, (nil., refl i)) nil.

def fgauto_reach (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  : List (FgautoReachEntry S V E i)
  ≔ fgauto_bfs S V dV E i (length V (fgauto_reach_universe S V E i)) (fgauto_reach_start S V E i)

def fgauto_reached (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) : List V
  ≔ fgauto_reach_vertices S V E i (fgauto_reach S V dV E i)

def fgauto_reach_closed (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  : FgautoStepClosed S V E (fgauto_reached S V dV E i)
  ≔ let U ≔ fgauto_reach_universe S V E i in
    fgauto_bfs_closed S V dV E i (length V U) (fgauto_reach_start S V E i)
      ((k ↦ match k [], star.),
       (v m ↦ match m [ inl. e ↦ inl. e | inr. k ↦ match k [] ],
        le_from_equal (suc. (length V U)) (add (suc. zero.) (length V U))
          (inverse Nat (add (suc. zero.) (length V U)) (suc. (length V U))
            (concat Nat (add (suc. zero.) (length V U)) (suc. (add zero. (length V U))) (suc. (length V U))
              (add_suc_left zero. (length V U)) (suc. (add_zero_left (length V U)))))))

def fgauto_reach_root (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  : FgautoMem V i (fgauto_reached S V dV E i)
  ≔ fgauto_bfs_mono S V dV E i (length V (fgauto_reach_universe S V E i)) (fgauto_reach_start S V E i) i
      (inl. (refl i))

def fgauto_closed_run (S V : Type) (E : List (FgautoEdge S V)) (Vs : List V) (h : FgautoStepClosed S V E Vs)
  (p : V) (w : SignedWord S) (q : V) (r : FgautoRun S V E p w q) (m : FgautoMem V p Vs) : FgautoMem V q Vs
  ≔ match w [
  | nil. ↦ fgauto_mem_transport V p q Vs r m
  | cons. x w' ↦ fgauto_closed_run S V E Vs h (r .fst) w' q (r .snd .snd) (h p x (r .fst) (r .snd .fst) m) ]

{` Completeness: every vertex reachable from i is listed. `}
def fgauto_reach_complete (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (w : SignedWord S) (v : V) (r : FgautoRun S V E i w v) : FgautoMem V v (fgauto_reached S V dV E i)
  ≔ fgauto_closed_run S V E (fgauto_reached S V dV E i) (fgauto_reach_closed S V dV E i) i w v r
      (fgauto_reach_root S V dV E i)

{` Spanning-tree words t_v (t_i = eps). `}
def fgauto_tree_word_choose (S V : Type) (E : List (FgautoEdge S V)) (i v : V) (R : List (FgautoReachEntry S V E i))
  (d1 : Decidable (Id V v i)) (d2 : Decidable (FgautoMem V v (fgauto_reach_vertices S V E i R))) : SignedWord S
  ≔ match d1 [
  | inl. _ ↦ nil.
  | inr. _ ↦ match d2 [ inl. m ↦ fgauto_reach_entry_of_mem S V E i v R m .fst | inr. _ ↦ nil. ] ]

def fgauto_tree_word (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i v : V) : SignedWord S
  ≔ fgauto_tree_word_choose S V E i v (fgauto_reach S V dV E i) (dV v i)
      (fgauto_mem_decide V dV v (fgauto_reached S V dV E i))

def fgauto_tree_word_choose_run (S V : Type) (E : List (FgautoEdge S V)) (i v : V) (R : List (FgautoReachEntry S V E i))
  (d1 : Decidable (Id V v i)) (d2 : Decidable (FgautoMem V v (fgauto_reach_vertices S V E i R)))
  (m : FgautoMem V v (fgauto_reach_vertices S V E i R))
  : FgautoRun S V E i (fgauto_tree_word_choose S V E i v R d1 d2) v
  ≔ match d1 [
  | inl. e ↦ inverse V v i e
  | inr. _ ↦ match d2 [
    | inl. m' ↦ fgauto_reach_entry_of_mem S V E i v R m' .snd
    | inr. n ↦ match n m [] ] ]

def fgauto_tree_word_run (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i v : V)
  (m : FgautoMem V v (fgauto_reached S V dV E i)) : FgautoRun S V E i (fgauto_tree_word S V dV E i v) v
  ≔ fgauto_tree_word_choose_run S V E i v (fgauto_reach S V dV E i) (dV v i)
      (fgauto_mem_decide V dV v (fgauto_reached S V dV E i)) m

def fgauto_tree_word_root_choose (S V : Type) (E : List (FgautoEdge S V)) (i : V) (R : List (FgautoReachEntry S V E i))
  (d1 : Decidable (Id V i i)) (d2 : Decidable (FgautoMem V i (fgauto_reach_vertices S V E i R)))
  : Id (SignedWord S) (fgauto_tree_word_choose S V E i i R d1 d2) nil.
  ≔ match d1 [ inl. _ ↦ refl (nil. : SignedWord S) | inr. n ↦ match n (refl i) [] ]

def fgauto_tree_word_root (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  : Id (SignedWord S) (fgauto_tree_word S V dV E i i) nil.
  ≔ fgauto_tree_word_root_choose S V E i (fgauto_reach S V dV E i) (dV i i)
      (fgauto_mem_decide V dV i (fgauto_reached S V dV E i))

{` The loop generators t_p x t_q^-1 of the edges with reachable source. `}
def fgauto_edge_loop_word (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (p : V) (x : SignedLetter S) (q : V) : SignedWord S
  ≔ append (SignedLetter S) (fgauto_tree_word S V dV E i p) (cons. x (word_inverse S (fgauto_tree_word S V dV E i q)))

def fgauto_loop_gens_pick (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (e : FgautoEdge S V) (d : Decidable (FgautoMem V (e .src) (fgauto_reached S V dV E i))) (rest : List (SignedWord S))
  : List (SignedWord S)
  ≔ match d [ inl. _ ↦ cons. (fgauto_edge_loop_word S V dV E i (e .src) (e .lab) (e .tgt)) rest | inr. _ ↦ rest ]

def fgauto_loop_gens_in (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (L : List (FgautoEdge S V)) : List (SignedWord S)
  ≔ match L [
  | nil. ↦ nil.
  | cons. e L' ↦ fgauto_loop_gens_pick S V dV E i e (fgauto_mem_decide V dV (e .src) (fgauto_reached S V dV E i))
      (fgauto_loop_gens_in S V dV E i L') ]

def fgauto_loop_gens (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V) : List (SignedWord S)
  ≔ fgauto_loop_gens_in S V dV E i E

{` Every step from a reachable vertex contributes its loop word. `}
def fgauto_loop_gens_pick_mem (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (e : FgautoEdge S V) (rest : List (SignedWord S)) (p : V) (x : SignedLetter S) (q : V)
  (t : Product (Id V p (e .src)) (Product (Id (SignedLetter S) x (e .lab)) (Id V q (e .tgt))))
  (mp : FgautoMem V p (fgauto_reached S V dV E i)) (d : Decidable (FgautoMem V (e .src) (fgauto_reached S V dV E i)))
  : FgautoMem (SignedWord S) (fgauto_edge_loop_word S V dV E i p x q) (fgauto_loop_gens_pick S V dV E i e d rest)
  ≔ match d [
  | inl. _ ↦ inl. (refl ((a b c ↦ fgauto_edge_loop_word S V dV E i a b c) : V → SignedLetter S → V → SignedWord S)
      (t .fst) (t .snd .fst) (t .snd .snd))
  | inr. n ↦ match n (fgauto_mem_transport V p (e .src) (fgauto_reached S V dV E i) (t .fst) mp) [] ]

def fgauto_loop_gens_pick_rest (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (e : FgautoEdge S V) (rest : List (SignedWord S)) (g : SignedWord S) (m : FgautoMem (SignedWord S) g rest)
  (d : Decidable (FgautoMem V (e .src) (fgauto_reached S V dV E i)))
  : FgautoMem (SignedWord S) g (fgauto_loop_gens_pick S V dV E i e d rest)
  ≔ match d [ inl. _ ↦ inr. m | inr. _ ↦ m ]

def fgauto_loop_gens_in_mem (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (L : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) (s : FgautoStep S V L p x q)
  (mp : FgautoMem V p (fgauto_reached S V dV E i))
  : FgautoMem (SignedWord S) (fgauto_edge_loop_word S V dV E i p x q) (fgauto_loop_gens_in S V dV E i L)
  ≔ match L [
  | nil. ↦ match s []
  | cons. e L' ↦ match s [
    | inl. t ↦ fgauto_loop_gens_pick_mem S V dV E i e (fgauto_loop_gens_in S V dV E i L') p x q t mp
        (fgauto_mem_decide V dV (e .src) (fgauto_reached S V dV E i))
    | inr. s' ↦ fgauto_loop_gens_pick_rest S V dV E i e (fgauto_loop_gens_in S V dV E i L')
        (fgauto_edge_loop_word S V dV E i p x q) (fgauto_loop_gens_in_mem S V dV E i L' p x q s' mp)
        (fgauto_mem_decide V dV (e .src) (fgauto_reached S V dV E i)) ] ]

{` Generation: for a run p -w-> q from a reachable p, H t_p w = H t_q where
   H is generated by the loop words. `}
def fgauto_loop_gens_run (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V) (E : List (FgautoEdge S V))
  (i : V) (p : V) (w : SignedWord S) (q : V) (r : FgautoRun S V E p w q) (mp : FgautoMem V p (fgauto_reached S V dV E i))
  : FgautoSameCoset S dec (fgauto_loop_gens S V dV E i)
      (append (SignedLetter S) (fgauto_tree_word S V dV E i p) w) (fgauto_tree_word S V dV E i q)
  ≔ let gens ≔ fgauto_loop_gens S V dV E i in
    let t ≔ fgauto_tree_word S V dV E i in
    match w [
    | nil. ↦ fgauto_same_coset_transport S dec gens (t p) (append (SignedLetter S) (t p) nil.) (t p) (t q)
        (fgauto_wsym S (append (SignedLetter S) (t p) nil.) (t p) (append_nil (SignedLetter S) (t p)))
        (refl t r) (fgauto_same_coset_refl S dec gens (t p))
    | cons. x w' ↦
      let rr ≔ r .fst in
      fgauto_same_coset_trans S dec gens (append (SignedLetter S) (t p) (cons. x w'))
        (append (SignedLetter S) (t rr) w') (t q)
        (fgauto_same_coset_transport S dec gens
          (append (SignedLetter S) (append (SignedLetter S) (t p) (cons. x nil.)) w') (append (SignedLetter S) (t p) (cons. x w'))
          (append (SignedLetter S) (t rr) w') (append (SignedLetter S) (t rr) w')
          (append_assoc (SignedLetter S) (t p) (cons. x nil.) w') (refl (append (SignedLetter S) (t rr) w'))
          (fgauto_same_coset_mul_right S dec gens (append (SignedLetter S) (t p) (cons. x nil.)) (t rr) w'
            (fgauto_in_subgroup_red S dec gens (fgauto_edge_loop_word S V dV E i p x rr)
              (append (SignedLetter S) (append (SignedLetter S) (t p) (cons. x nil.)) (word_inverse S (t rr)))
              (refl (word_reduction S dec)
                (fgauto_wsym S (append (SignedLetter S) (append (SignedLetter S) (t p) (cons. x nil.)) (word_inverse S (t rr)))
                  (fgauto_edge_loop_word S V dV E i p x rr)
                  (append_assoc (SignedLetter S) (t p) (cons. x nil.) (word_inverse S (t rr)))))
              (fgauto_in_subgroup_generator S dec gens (fgauto_edge_loop_word S V dV E i p x rr)
                (fgauto_loop_gens_in_mem S V dV E i E p x rr (r .snd .fst) mp)))))
        (fgauto_loop_gens_run S V dec dV E i rr w' q (r .snd .snd)
          (fgauto_reach_closed S V dV E i p x rr (r .snd .fst) mp)) ]

{` Every loop at i lies in the subgroup generated by the loop words, and
   every run i -w-> q gives H w = H t_q. `}
def fgauto_loop_gens_coset (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (i : V) (w : SignedWord S) (q : V) (r : FgautoRun S V E i w q)
  : FgautoSameCoset S dec (fgauto_loop_gens S V dV E i) w (fgauto_tree_word S V dV E i q)
  ≔ fgauto_same_coset_transport S dec (fgauto_loop_gens S V dV E i)
      (append (SignedLetter S) (fgauto_tree_word S V dV E i i) w) w
      (fgauto_tree_word S V dV E i q) (fgauto_tree_word S V dV E i q)
      (refl ((z ↦ append (SignedLetter S) z w) : SignedWord S → SignedWord S) (fgauto_tree_word_root S V dV E i))
      (refl (fgauto_tree_word S V dV E i q))
      (fgauto_loop_gens_run S V dec dV E i i w q r (fgauto_reach_root S V dV E i))

def fgauto_loop_gens_generate (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (i : V) (w : SignedWord S) (r : FgautoRun S V E i w i)
  : FgautoInSubgroup S dec (fgauto_loop_gens S V dV E i) w
  ≔ fgauto_same_coset_unit_member S dec (fgauto_loop_gens S V dV E i) w
      (fgauto_same_coset_transport S dec (fgauto_loop_gens S V dV E i) w w (fgauto_tree_word S V dV E i i) nil.
        (refl w) (fgauto_tree_word_root S V dV E i) (fgauto_loop_gens_coset S V dec dV E i w i r))

{` Conversely each loop word labels a closed walk at i (inverse graphs). `}
def fgauto_loop_gens_pick_loop (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (hs : FgautoSymmetric S V E) (e : FgautoEdge S V) (se : FgautoStep S V E (e .src) (e .lab) (e .tgt))
  (rest : List (SignedWord S))
  (ih : (g : SignedWord S) → FgautoMem (SignedWord S) g rest → FgautoRun S V E i g i)
  (d : Decidable (FgautoMem V (e .src) (fgauto_reached S V dV E i)))
  (g : SignedWord S) (m : FgautoMem (SignedWord S) g (fgauto_loop_gens_pick S V dV E i e d rest))
  : FgautoRun S V E i g i
  ≔ match d [
  | inr. _ ↦ ih g m
  | inl. ms ↦ match m [
    | inr. m' ↦ ih g m'
    | inl. eg ↦
      let t ≔ fgauto_tree_word S V dV E i in
      let mt ≔ fgauto_reach_closed S V dV E i (e .src) (e .lab) (e .tgt) se ms in
      fgauto_run_word S V E i (fgauto_edge_loop_word S V dV E i (e .src) (e .lab) (e .tgt)) g i
        (fgauto_wsym S g (fgauto_edge_loop_word S V dV E i (e .src) (e .lab) (e .tgt)) eg)
        (fgauto_run_append S V E i (t (e .src)) (e .src) (cons. (e .lab) (word_inverse S (t (e .tgt)))) i
          (fgauto_tree_word_run S V dV E i (e .src) ms)
          (e .tgt, (se, fgauto_run_inverse S V E hs i (t (e .tgt)) (e .tgt) (fgauto_tree_word_run S V dV E i (e .tgt) mt)))) ] ]

def fgauto_loop_gens_in_loop (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (hs : FgautoSymmetric S V E) (L : List (FgautoEdge S V)) (incl : FgautoStepIncl S V L E)
  (g : SignedWord S) (m : FgautoMem (SignedWord S) g (fgauto_loop_gens_in S V dV E i L)) : FgautoRun S V E i g i
  ≔ match L [
  | nil. ↦ match m []
  | cons. e L' ↦ fgauto_loop_gens_pick_loop S V dV E i hs e (incl (e .src) (e .lab) (e .tgt) (fgauto_step_head S V e L'))
      (fgauto_loop_gens_in S V dV E i L')
      (fgauto_loop_gens_in_loop S V dV E i hs L' (p0 x0 q0 s ↦ incl p0 x0 q0 (inr. s)))
      (fgauto_mem_decide V dV (e .src) (fgauto_reached S V dV E i)) g m ]

def fgauto_loop_gens_loop (S V : Type) (dV : DecidableEquality V) (E : List (FgautoEdge S V)) (i : V)
  (hs : FgautoSymmetric S V E) (g : SignedWord S) (m : FgautoMem (SignedWord S) g (fgauto_loop_gens S V dV E i))
  : FgautoRun S V E i g i
  ≔ fgauto_loop_gens_in_loop S V dV E i hs E (p0 x0 q0 s ↦ s) g m

{` Words in the loop generators label closed walks at i. `}
def fgauto_gen_eval_run_at (S V : Type) (gens : List (SignedWord S)) (E : List (FgautoEdge S V)) (i : V)
  (hs : FgautoSymmetric S V E) (hl : (g : SignedWord S) → FgautoMem (SignedWord S) g gens → FgautoRun S V E i g i)
  (h : SignedWord (FgautoGen S gens)) : FgautoRun S V E i (fgauto_gen_eval S gens h) i
  ≔ match h [
  | nil. ↦ refl i
  | cons. x t ↦ fgauto_run_append S V E i (fgauto_gen_letter_eval S gens x) i (fgauto_gen_eval S gens t) i
      (match x [
       | inl. g ↦ hl (g .fst) (g .snd)
       | inr. g ↦ fgauto_run_inverse S V E hs i (g .fst) i (hl (g .fst) (g .snd)) ])
      (fgauto_gen_eval_run_at S V gens E i hs hl t) ]
