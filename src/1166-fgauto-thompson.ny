export "1162-fgauto-rational-subgroups"

{` Chapter 11, automata part 17: from rational expressions to automata
   (Thompson's construction), for an arbitrary monoid M with its laws.

   An automaton over M has edges labelled by inl m (m in M; the inr
   letters are not used), states List Nat, one start and one end state.
   The value of a path is the product of its labels (fgauto_path_eval).
   fgauto_thompson r builds the usual automaton: two states and one edge per
   element for a finite set; for union, product and star the
   sub-automata are tagged by the heads 0 and 1 of their states and joined
   by edges labelled by the unit (the book's empty transitions).

   This module provides the construction and the generic "region" lemmas:
   a run that starts inside the copy of a sub-automaton either stays there
   or leaves it through one of the joining edges (fgauto_region_exit), and
   a run inside a region is a run of the sub-automaton
   (fgauto_region_stay).  Module 1167 proves that the values of the
   accepting runs are exactly the elements of the rational subset. `}

def FgautoMonoidLaws (M : FgautoMonoid) : Type ≔ sig (
  ml_unit_left : (m : M .mcarrier) → Id (M .mcarrier) (M .mmul (M .munit) m) m,
  ml_unit_right : (m : M .mcarrier) → Id (M .mcarrier) (M .mmul m (M .munit)) m,
  ml_assoc : (a b c : M .mcarrier) → Id (M .mcarrier) (M .mmul a (M .mmul b c)) (M .mmul (M .mmul a b) c))

def fgauto_group_monoid_laws (G : AbstractGroup) : FgautoMonoidLaws (fgauto_group_monoid G)
  ≔ (G .laws .unit_left, G .laws .unit_right, G .laws .assoc)

def fgauto_label_eval (M : FgautoMonoid) (x : SignedLetter (M .mcarrier)) : M .mcarrier
  ≔ match x [ inl. m ↦ m | inr. m ↦ m ]

def fgauto_path_eval (M : FgautoMonoid) (w : SignedWord (M .mcarrier)) : M .mcarrier
  ≔ match w [ nil. ↦ M .munit | cons. x t ↦ M .mmul (fgauto_label_eval M x) (fgauto_path_eval M t) ]

def fgauto_path_eval_append (M : FgautoMonoid) (L : FgautoMonoidLaws M) (u v : SignedWord (M .mcarrier))
  : Id (M .mcarrier) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) u v))
      (M .mmul (fgauto_path_eval M u) (fgauto_path_eval M v))
  ≔ match u [
  | nil. ↦ inverse (M .mcarrier) (M .mmul (M .munit) (fgauto_path_eval M v)) (fgauto_path_eval M v) (L .ml_unit_left (fgauto_path_eval M v))
  | cons. x t ↦ concat (M .mcarrier)
      (M .mmul (fgauto_label_eval M x) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) t v)))
      (M .mmul (fgauto_label_eval M x) (M .mmul (fgauto_path_eval M t) (fgauto_path_eval M v)))
      (M .mmul (M .mmul (fgauto_label_eval M x) (fgauto_path_eval M t)) (fgauto_path_eval M v))
      (refl (M .mmul (fgauto_label_eval M x)) (fgauto_path_eval_append M L t v))
      (L .ml_assoc (fgauto_label_eval M x) (fgauto_path_eval M t) (fgauto_path_eval M v)) ]

{` States and tags. `}
def fgauto_n1 : Nat ≔ suc. zero.
def fgauto_n2 : Nat ≔ suc. (suc. zero.)
def fgauto_n3 : Nat ≔ suc. (suc. (suc. zero.))

def fgauto_tstate_dec : DecidableEquality (List Nat) ≔ fw_list_decidable_equality Nat nat_dec_eq

def fgauto_tag_clash (k j : Nat) (p q : List Nat) (e : Id (List Nat) (cons. k p) (cons. j q)) : NatCode k j
  ≔ nat_encode k j (list_encode Nat (cons. k p) (cons. j q) e .fst)

def fgauto_tag_tail (k : Nat) (p q : List Nat) (e : Id (List Nat) (cons. k p) (cons. k q)) : Id (List Nat) p q
  ≔ list_encode Nat (cons. k p) (cons. k q) e .snd

def FgautoThompsonAut (M : FgautoMonoid) : Type ≔ sig (
  tedges : List (FgautoEdge (M .mcarrier) (List Nat)),
  tstart : List Nat,
  tend : List Nat)

def fgauto_tpre (M : FgautoMonoid) (k : Nat) (E : List (FgautoEdge (M .mcarrier) (List Nat)))
  : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ fgauto_map_edges (M .mcarrier) (List Nat) (List Nat) (v ↦ cons. k v) E

def fgauto_teps (M : FgautoMonoid) : SignedLetter (M .mcarrier) ≔ inl. (M .munit)

def fgauto_tfin_edges (M : FgautoMonoid) (l : List (M .mcarrier)) : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ fgauto_list_map (M .mcarrier) (FgautoEdge (M .mcarrier) (List Nat)) (m ↦ (cons. zero. nil., inl. m, cons. fgauto_n1 nil.)) l

def fgauto_union_glue (M : FgautoMonoid) (A B : FgautoThompsonAut M) : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ cons. (cons. fgauto_n2 nil., fgauto_teps M, cons. zero. (A .tstart))
      (cons. (cons. fgauto_n2 nil., fgauto_teps M, cons. fgauto_n1 (B .tstart))
        (cons. (cons. zero. (A .tend), fgauto_teps M, cons. fgauto_n3 nil.)
          (cons. (cons. fgauto_n1 (B .tend), fgauto_teps M, cons. fgauto_n3 nil.) nil.)))

def fgauto_prod_glue (M : FgautoMonoid) (A B : FgautoThompsonAut M) : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ cons. (cons. zero. (A .tend), fgauto_teps M, cons. fgauto_n1 (B .tstart)) nil.

def fgauto_star_glue (M : FgautoMonoid) (A : FgautoThompsonAut M) : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ cons. (cons. fgauto_n2 nil., fgauto_teps M, cons. zero. (A .tstart))
      (cons. (cons. zero. (A .tend), fgauto_teps M, cons. fgauto_n2 nil.) nil.)

def fgauto_join2 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M zero. (A .tedges))
      (append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) glue)

def fgauto_join1 (M : FgautoMonoid) (A : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : List (FgautoEdge (M .mcarrier) (List Nat))
  ≔ append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M zero. (A .tedges)) glue

def fgauto_thompson (M : FgautoMonoid) (r : FgautoRatExpr (M .mcarrier)) : FgautoThompsonAut M
  ≔ match r [
  | rat_fin. l ↦ (fgauto_tfin_edges M l, cons. zero. nil., cons. fgauto_n1 nil.)
  | rat_union. r1 r2 ↦
    let A ≔ fgauto_thompson M r1 in
    let B ≔ fgauto_thompson M r2 in
    (fgauto_join2 M A B (fgauto_union_glue M A B), cons. fgauto_n2 nil., cons. fgauto_n3 nil.)
  | rat_prod. r1 r2 ↦
    let A ≔ fgauto_thompson M r1 in
    let B ≔ fgauto_thompson M r2 in
    (fgauto_join2 M A B (fgauto_prod_glue M A B), cons. zero. (A .tstart), cons. fgauto_n1 (B .tend))
  | rat_star. r1 ↦
    let A ≔ fgauto_thompson M r1 in
    (fgauto_join1 M A (fgauto_star_glue M A), cons. fgauto_n2 nil., cons. fgauto_n2 nil.) ]

def FgautoThompsonLang (M : FgautoMonoid) (A : FgautoThompsonAut M) (m : M .mcarrier) : Type
  ≔ Mere (Σ (SignedWord (M .mcarrier)) (w ↦ Product (FgautoRun (M .mcarrier) (List Nat) (A .tedges) (A .tstart) w (A .tend))
       (Id (M .mcarrier) (fgauto_path_eval M w) m)))

{` Regions. `}
def FgautoRegionClassify (M : FgautoMonoid) (G E R : List (FgautoEdge (M .mcarrier) (List Nat))) (k : Nat) : Type
  ≔ (p : List Nat) (x : SignedLetter (M .mcarrier)) (z : List Nat) → FgautoStep (M .mcarrier) (List Nat) G (cons. k p) x z
    → Sum (Σ (List Nat) (p' ↦ Product (FgautoStep (M .mcarrier) (List Nat) E p x p') (Id (List Nat) z (cons. k p'))))
        (FgautoStep (M .mcarrier) (List Nat) R (cons. k p) x z)

def fgauto_tpre_step (M : FgautoMonoid) (k : Nat) (E : List (FgautoEdge (M .mcarrier) (List Nat))) (p : List Nat)
  (x : SignedLetter (M .mcarrier)) (z : List Nat) (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_tpre M k E) (cons. k p) x z)
  : Σ (List Nat) (p' ↦ Product (FgautoStep (M .mcarrier) (List Nat) E p x p') (Id (List Nat) z (cons. k p')))
  ≔ let y ≔ fgauto_step_map_preimage (M .mcarrier) (List Nat) (List Nat) (v ↦ cons. k v) E (cons. k p) x z s in
    (y .snd .fst,
     (fgauto_step_transport (M .mcarrier) (List Nat) E (y .fst) p x x (y .snd .fst) (y .snd .fst)
        (inverse (List Nat) p (y .fst) (fgauto_tag_tail k p (y .fst) (y .snd .snd .snd .fst))) (refl x) (refl (y .snd .fst))
        (y .snd .snd .fst),
      y .snd .snd .snd .snd))

def fgauto_tpre_step_other (M : FgautoMonoid) (k j : Nat) (n : NatCode k j → Empty) (E : List (FgautoEdge (M .mcarrier) (List Nat)))
  (p : List Nat) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_tpre M j E) (cons. k p) x z) : Empty
  ≔ let y ≔ fgauto_step_map_preimage (M .mcarrier) (List Nat) (List Nat) (v ↦ cons. j v) E (cons. k p) x z s in
    n (fgauto_tag_clash k j p (y .fst) (y .snd .snd .snd .fst))

def fgauto_tpre_embed (M : FgautoMonoid) (k : Nat) (E : List (FgautoEdge (M .mcarrier) (List Nat))) (p : List Nat)
  (w : SignedWord (M .mcarrier)) (q : List Nat) (r : FgautoRun (M .mcarrier) (List Nat) E p w q)
  : FgautoRun (M .mcarrier) (List Nat) (fgauto_tpre M k E) (cons. k p) w (cons. k q)
  ≔ fgauto_run_map (M .mcarrier) (List Nat) (List Nat) (v ↦ cons. k v) E p w q r

{` Leaving a region. `}
def FgautoRegionExit (M : FgautoMonoid) (G E R : List (FgautoEdge (M .mcarrier) (List Nat))) (k : Nat) (p : List Nat)
  (w : SignedWord (M .mcarrier)) (q : List Nat) : Type
  ≔ Σ (SignedWord (M .mcarrier)) (w1 ↦ Σ (SignedLetter (M .mcarrier)) (y ↦ Σ (SignedWord (M .mcarrier)) (w2 ↦
      Σ (List Nat) (pe ↦ Σ (List Nat) (z ↦
        Product (Id (SignedWord (M .mcarrier)) w (append (SignedLetter (M .mcarrier)) w1 (cons. y w2)))
          (Product (FgautoRun (M .mcarrier) (List Nat) E p w1 pe)
            (Product (FgautoStep (M .mcarrier) (List Nat) R (cons. k pe) y z)
              (FgautoRun (M .mcarrier) (List Nat) G z w2 q))))))))

def fgauto_region_exit (M : FgautoMonoid) (G E R : List (FgautoEdge (M .mcarrier) (List Nat))) (k : Nat)
  (hc : FgautoRegionClassify M G E R k) (p : List Nat) (w : SignedWord (M .mcarrier)) (q : List Nat)
  (nq : (q' : List Nat) → Not (Id (List Nat) q (cons. k q')))
  (r : FgautoRun (M .mcarrier) (List Nat) G (cons. k p) w q) : FgautoRegionExit M G E R k p w q
  ≔ let L ≔ SignedLetter (M .mcarrier) in
    match w [
    | nil. ↦ match nq p (inverse (List Nat) (cons. k p) q r) []
    | cons. x w' ↦ match hc p x (r .fst) (r .snd .fst) [
      | inr. sR ↦ (nil., (x, (w', (p, (r .fst, (refl (cons. x w' : SignedWord (M .mcarrier)), (refl p, (sR, r .snd .snd))))))))
      | inl. internal ↦
        let p' ≔ internal .fst in
        let ex ≔ fgauto_region_exit M G E R k hc p' w' q nq
          (fgauto_run_start (M .mcarrier) (List Nat) G (r .fst) (cons. k p') w' q (internal .snd .snd) (r .snd .snd)) in
        (cons. x (ex .fst), (ex .snd .fst, (ex .snd .snd .fst, (ex .snd .snd .snd .fst, (ex .snd .snd .snd .snd .fst,
          (cons. (refl x) (ex .snd .snd .snd .snd .snd .fst),
           ((p', (internal .snd .fst, ex .snd .snd .snd .snd .snd .snd .fst)),
            ex .snd .snd .snd .snd .snd .snd .snd))))))) ] ]

{` Staying in a region without exits. `}
def fgauto_region_stay (M : FgautoMonoid) (G E R : List (FgautoEdge (M .mcarrier) (List Nat))) (k : Nat)
  (hc : FgautoRegionClassify M G E R k)
  (noexit : (p : List Nat) (x : SignedLetter (M .mcarrier)) (z : List Nat) → Not (FgautoStep (M .mcarrier) (List Nat) R (cons. k p) x z))
  (p : List Nat) (w : SignedWord (M .mcarrier)) (q : List Nat)
  (r : FgautoRun (M .mcarrier) (List Nat) G (cons. k p) w (cons. k q)) : FgautoRun (M .mcarrier) (List Nat) E p w q
  ≔ match w [
  | nil. ↦ fgauto_tag_tail k p q r
  | cons. x w' ↦ match hc p x (r .fst) (r .snd .fst) [
    | inr. sR ↦ match noexit p x (r .fst) sR []
    | inl. internal ↦ (internal .fst, (internal .snd .fst,
        fgauto_region_stay M G E R k hc noexit (internal .fst) w' q
          (fgauto_run_start (M .mcarrier) (List Nat) G (r .fst) (cons. k (internal .fst)) w' (cons. k q) (internal .snd .snd) (r .snd .snd)))) ] ]

{` Classification for the joined graphs. `}
def fgauto_join2_classify0 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoRegionClassify M (fgauto_join2 M A B glue) (A .tedges) glue zero.
  ≔ p x z s ↦
    let E1 ≔ fgauto_tpre M zero. (A .tedges) in
    let E2 ≔ fgauto_tpre M fgauto_n1 (B .tedges) in
    match fgauto_step_append_split (M .mcarrier) (List Nat) E1 (append (FgautoEdge (M .mcarrier) (List Nat)) E2 glue) (cons. zero. p) x z s [
    | inl. s1 ↦ inl. (fgauto_tpre_step M zero. (A .tedges) p x z s1)
    | inr. s2 ↦ match fgauto_step_append_split (M .mcarrier) (List Nat) E2 glue (cons. zero. p) x z s2 [
      | inl. s3 ↦ match fgauto_tpre_step_other M zero. fgauto_n1 (e ↦ e) (B .tedges) p x z s3 []
      | inr. s4 ↦ inr. s4 ] ]

def fgauto_join2_classify1 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoRegionClassify M (fgauto_join2 M A B glue) (B .tedges) glue fgauto_n1
  ≔ p x z s ↦
    let E1 ≔ fgauto_tpre M zero. (A .tedges) in
    let E2 ≔ fgauto_tpre M fgauto_n1 (B .tedges) in
    match fgauto_step_append_split (M .mcarrier) (List Nat) E1 (append (FgautoEdge (M .mcarrier) (List Nat)) E2 glue) (cons. fgauto_n1 p) x z s [
    | inl. s1 ↦ match fgauto_tpre_step_other M fgauto_n1 zero. (e ↦ e) (A .tedges) p x z s1 []
    | inr. s2 ↦ match fgauto_step_append_split (M .mcarrier) (List Nat) E2 glue (cons. fgauto_n1 p) x z s2 [
      | inl. s3 ↦ inl. (fgauto_tpre_step M fgauto_n1 (B .tedges) p x z s3)
      | inr. s4 ↦ inr. s4 ] ]

def fgauto_join1_classify0 (M : FgautoMonoid) (A : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoRegionClassify M (fgauto_join1 M A glue) (A .tedges) glue zero.
  ≔ p x z s ↦ match fgauto_step_append_split (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) glue (cons. zero. p) x z s [
  | inl. s1 ↦ inl. (fgauto_tpre_step M zero. (A .tedges) p x z s1)
  | inr. s2 ↦ inr. s2 ]

{` Embeddings of the components and glue into the joined graphs. `}
def fgauto_join2_left (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStepIncl (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) (fgauto_join2 M A B glue)
  ≔ fgauto_step_append_left (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges))
      (append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) glue)

def fgauto_join2_right (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStepIncl (M .mcarrier) (List Nat) (fgauto_tpre M fgauto_n1 (B .tedges)) (fgauto_join2 M A B glue)
  ≔ p x q s ↦ fgauto_step_append_right (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges))
      (append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) glue) p x q
      (fgauto_step_append_left (M .mcarrier) (List Nat) (fgauto_tpre M fgauto_n1 (B .tedges)) glue p x q s)

def fgauto_join2_glue (M : FgautoMonoid) (A B : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStepIncl (M .mcarrier) (List Nat) glue (fgauto_join2 M A B glue)
  ≔ p x q s ↦ fgauto_step_append_right (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges))
      (append (FgautoEdge (M .mcarrier) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) glue) p x q
      (fgauto_step_append_right (M .mcarrier) (List Nat) (fgauto_tpre M fgauto_n1 (B .tedges)) glue p x q s)

def fgauto_join1_left (M : FgautoMonoid) (A : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStepIncl (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) (fgauto_join1 M A glue)
  ≔ fgauto_step_append_left (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) glue

def fgauto_join1_glue (M : FgautoMonoid) (A : FgautoThompsonAut M) (glue : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStepIncl (M .mcarrier) (List Nat) glue (fgauto_join1 M A glue)
  ≔ fgauto_step_append_right (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) glue
