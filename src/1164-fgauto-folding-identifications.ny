export "1156-fgauto-cosets-automata"

{` Chapter 11, automata part 15: the running-text claim at
   fggroups.tex:919-922, "Two vertices p, q get identified in the Stallings
   graph/automaton iff there is a run from p to q with a word w whose
   reduction is 1."

   Vertices of the bouquet are identified when folding sends them to the
   same vertex of S(H).  Folding does not depend on the tracked vertex
   (fgauto_fold_edges_indep), so the image of a vertex v is
   fgauto_fold_image v = (fold of the bouquet tracking v).snd.  We prove:
   images agree iff the bouquet has a run from v to w whose label reduces
   to the empty word (fgauto_identified_iff_dyck_run).  "<=": the run maps
   to a run of S(H), which is deterministic and inverse, so its reduced
   label eps runs from the image of v to the image of w.  "=>": an
   invariant of folding, carried for all pairs of vertices: steps of the
   folded graph lift to the bouquet, and vertices with the same image are
   joined by such a run; a fold of the conflict s -x-> t1, s -x-> t2 joins
   a vertex over t2 to one over t1 by a run of shape D x-bar D x D. `}

def fgauto_fold_edges_indep_step (S : Type) (dec : DecidableEquality S) (f : Nat)
  (recur : (E1 : List (FgautoEdge S (SignedWord S))) (b1 b1' : SignedWord S)
    → Id (List (FgautoEdge S (SignedWord S))) (fgauto_fold S dec f E1 b1 .fst) (fgauto_fold S dec f E1 b1' .fst))
  (E : List (FgautoEdge S (SignedWord S))) (b b' : SignedWord S)
  (d : Sum (FgautoConflict S (SignedWord S) E) (FgautoDeterministic S (SignedWord S) E))
  : Id (List (FgautoEdge S (SignedWord S))) (fgauto_fold_step S dec (fgauto_fold S dec f) E b d .fst)
      (fgauto_fold_step S dec (fgauto_fold S dec f) E b' d .fst)
  ≔ match d [
  | inr. _ ↦ refl E
  | inl. c ↦ recur (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b) (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b') ]

def fgauto_fold_edges_indep (S : Type) (dec : DecidableEquality S) (fuel : Nat) (E : List (FgautoEdge S (SignedWord S)))
  (b b' : SignedWord S)
  : Id (List (FgautoEdge S (SignedWord S))) (fgauto_fold S dec fuel E b .fst) (fgauto_fold S dec fuel E b' .fst)
  ≔ match fuel [
  | zero. ↦ refl E
  | suc. f ↦ fgauto_fold_edges_indep_step S dec f (fgauto_fold_edges_indep S dec f) E b b'
      (fgauto_conflict_search S (SignedWord S) dec (signed_word_decidable_equality S dec) E) ]

{` Folding with a vertex map tracked: P E phi preserved by the folds gives
   P for the folded graph and v |-> image of phi v. `}
def fgauto_fold_ind_fun_step (S : Type) (dec : DecidableEquality S)
  (P : List (FgautoEdge S (SignedWord S)) → (SignedWord S → SignedWord S) → Type)
  (hP : (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S) (c : FgautoConflict S (SignedWord S) E)
    → P E phi
    → P (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
        (v ↦ fgauto_merge S dec (c .ctgt1) (c .ctgt2) (phi v)))
  (f : Nat)
  (recur : (E1 : List (FgautoEdge S (SignedWord S))) (e1 : SignedWord S) (phi1 : SignedWord S → SignedWord S) → P E1 phi1
    → P (fgauto_fold S dec f E1 e1 .fst) (v ↦ fgauto_fold S dec f E1 (phi1 v) .snd))
  (E : List (FgautoEdge S (SignedWord S))) (e0 : SignedWord S) (phi : SignedWord S → SignedWord S) (h : P E phi)
  (d : Sum (FgautoConflict S (SignedWord S) E) (FgautoDeterministic S (SignedWord S) E))
  : P (fgauto_fold_step S dec (fgauto_fold S dec f) E e0 d .fst) (v ↦ fgauto_fold_step S dec (fgauto_fold S dec f) E (phi v) d .snd)
  ≔ match d [
  | inr. _ ↦ h
  | inl. c ↦ recur (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) e0) (v ↦ fgauto_merge S dec (c .ctgt1) (c .ctgt2) (phi v)) (hP E phi c h) ]

def fgauto_fold_ind_fun (S : Type) (dec : DecidableEquality S)
  (P : List (FgautoEdge S (SignedWord S)) → (SignedWord S → SignedWord S) → Type)
  (hP : (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S) (c : FgautoConflict S (SignedWord S) E)
    → P E phi
    → P (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
        (v ↦ fgauto_merge S dec (c .ctgt1) (c .ctgt2) (phi v)))
  (fuel : Nat) (E : List (FgautoEdge S (SignedWord S))) (e0 : SignedWord S) (phi : SignedWord S → SignedWord S) (h : P E phi)
  : P (fgauto_fold S dec fuel E e0 .fst) (v ↦ fgauto_fold S dec fuel E (phi v) .snd)
  ≔ match fuel [
  | zero. ↦ h
  | suc. f ↦ fgauto_fold_ind_fun_step S dec P hP f (fgauto_fold_ind_fun S dec P hP f) E e0 phi h
      (fgauto_conflict_search S (SignedWord S) dec (signed_word_decidable_equality S dec) E) ]

{` The image of a bouquet vertex in S(H). `}
def fgauto_fold_image (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (v : SignedWord S) : SignedWord S
  ≔ fgauto_fold S dec (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) v .snd

def fgauto_fold_image_base (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : Id (SignedWord S) (fgauto_fold_image S dec gens nil.) (fgauto_stallings_base S dec gens)
  ≔ refl (fgauto_stallings_base S dec gens)

def FgautoDyckRun (S : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S (SignedWord S))) (v w : SignedWord S) : Type
  ≔ Σ (SignedWord S) (d ↦ Product (FgautoRun S (SignedWord S) E v d w) (Id (SignedWord S) (word_reduction S dec d) nil.))

{` "<=". `}
def fgauto_dyck_run_identified (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (v w : SignedWord S)
  (h : FgautoDyckRun S dec (fgauto_bouquet S gens) v w)
  : Id (SignedWord S) (fgauto_fold_image S dec gens v) (fgauto_fold_image S dec gens w)
  ≔ let E0 ≔ fgauto_bouquet S gens in
    let n ≔ fgauto_stallings_fuel S gens in
    let E ≔ fgauto_stallings_edges S dec gens in
    let r1 : FgautoRun S (SignedWord S) (fgauto_fold S dec n E0 v .fst) (fgauto_fold_image S dec gens v) (h .fst)
        (fgauto_fold_image S dec gens w)
      ≔ fgauto_fold_ind2 S dec (E1 b b' ↦ FgautoRun S (SignedWord S) E1 b (h .fst) b')
          (E1 b b' c r ↦ fgauto_run_map S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E1 b (h .fst) b' r)
          n E0 v w (h .snd .fst) in
    let r2 : FgautoRun S (SignedWord S) E (fgauto_fold_image S dec gens v) (h .fst) (fgauto_fold_image S dec gens w)
      ≔ transport (List (FgautoEdge S (SignedWord S)))
          (E1 ↦ FgautoRun S (SignedWord S) E1 (fgauto_fold_image S dec gens v) (h .fst) (fgauto_fold_image S dec gens w))
          (fgauto_fold S dec n E0 v .fst) E (fgauto_fold_edges_indep S dec n E0 v nil.) r1 in
    fgauto_run_word S (SignedWord S) E (fgauto_fold_image S dec gens v) (word_reduction S dec (h .fst)) nil.
      (fgauto_fold_image S dec gens w) (h .snd .snd)
      (fgauto_run_reduction S (SignedWord S) dec E (fgauto_stallings_symmetric S dec gens) (fgauto_stallings_deterministic S dec gens)
        (fgauto_fold_image S dec gens v) (h .fst) (fgauto_fold_image S dec gens w) r2)

{` "=>": the invariant. `}
def FgautoLiftInv (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S)))
  (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S) : Type
  ≔ Product
      ((p' : SignedWord S) (x : SignedLetter S) (q' : SignedWord S) → FgautoStep S (SignedWord S) E p' x q'
        → Σ (SignedWord S) (p ↦ Σ (SignedWord S) (q ↦ Product (FgautoStep S (SignedWord S) E0 p x q)
            (Product (Id (SignedWord S) p' (phi p)) (Id (SignedWord S) q' (phi q))))))
      ((v w : SignedWord S) → Id (SignedWord S) (phi v) (phi w) → FgautoDyckRun S dec E0 v w)

def fgauto_dyck_run_compose (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S))) (u v w : SignedWord S)
  (a : FgautoDyckRun S dec E0 u v) (b : FgautoDyckRun S dec E0 v w) : FgautoDyckRun S dec E0 u w
  ≔ (append (SignedLetter S) (a .fst) (b .fst),
     (fgauto_run_append S (SignedWord S) E0 u (a .fst) v (b .fst) w (a .snd .fst) (b .snd .fst),
      fgauto_wtrans S (word_reduction S dec (append (SignedLetter S) (a .fst) (b .fst)))
        (word_reduction S dec (b .fst)) nil.
        (fgauto_red_drop_left S dec (a .fst) (b .fst) (a .snd .snd)) (b .snd .snd)))

def fgauto_dyck_run_inverse (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S)))
  (hs : FgautoSymmetric S (SignedWord S) E0) (v w : SignedWord S) (a : FgautoDyckRun S dec E0 v w) : FgautoDyckRun S dec E0 w v
  ≔ (word_inverse S (a .fst),
     (fgauto_run_inverse S (SignedWord S) E0 hs v (a .fst) w (a .snd .fst),
      fgauto_red_inverse_congr S dec (a .fst) nil. (a .snd .snd)))

{` x-bar D x reduces to eps when D does. `}
def fgauto_dyck_conjugate (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (d : SignedWord S)
  (h : Id (SignedWord S) (word_reduction S dec d) nil.)
  : Id (SignedWord S) (word_reduction S dec (cons. (letter_complement S x) (append (SignedLetter S) d (cons. x nil.)))) nil.
  ≔ fgauto_wtrans S (word_reduction S dec (cons. (letter_complement S x) (append (SignedLetter S) d (cons. x nil.))))
      (word_letter_reduce S dec (letter_complement S x) (word_reduction S dec (cons. x nil.))) nil.
      (refl (word_letter_reduce S dec (letter_complement S x)) (fgauto_red_drop_left S dec d (cons. x nil.) h))
      (fgauto_wtrans S (word_letter_reduce S dec (letter_complement S x) (cons. x nil.))
        (word_letter_reduce S dec (letter_complement S x) (cons. (letter_complement S (letter_complement S x)) nil.)) nil.
        (refl ((y ↦ word_letter_reduce S dec (letter_complement S x) (cons. y nil.)) : SignedLetter S → SignedWord S)
          (inverse (SignedLetter S) (letter_complement S (letter_complement S x)) x (letter_complement_involutive S x)))
        (word_letter_reduce_drop S dec (letter_complement S x) nil.))

{` A step lifted along phi: the pieces needed for a merge. `}
def fgauto_merge_join (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S)))
  (hs : FgautoSymmetric S (SignedWord S) E0) (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S)
  (h : FgautoLiftInv S dec E0 E phi) (c : FgautoConflict S (SignedWord S) E) (v w : SignedWord S)
  (ev : Id (SignedWord S) (phi v) (c .ctgt2)) (ew : Id (SignedWord S) (phi w) (c .ctgt1)) : FgautoDyckRun S dec E0 v w
  ≔ let l1 ≔ h .fst (c .csrc) (c .clab) (c .ctgt1) (c .cstep1) in
    let l2 ≔ h .fst (c .csrc) (c .clab) (c .ctgt2) (c .cstep2) in
    let p1 ≔ l1 .fst in let q1 ≔ l1 .snd .fst in
    let p2 ≔ l2 .fst in let q2 ≔ l2 .snd .fst in
    let x ≔ c .clab in
    let d1 ≔ h .snd v q2 (fgauto_wtrans S (phi v) (c .ctgt2) (phi q2) ev (l2 .snd .snd .snd .snd)) in
    let d2 ≔ h .snd p2 p1 (fgauto_wtrans S (phi p2) (c .csrc) (phi p1)
      (fgauto_wsym S (c .csrc) (phi p2) (l2 .snd .snd .snd .fst)) (l1 .snd .snd .snd .fst)) in
    let d3 ≔ h .snd q1 w (fgauto_wtrans S (phi q1) (c .ctgt1) (phi w)
      (fgauto_wsym S (c .ctgt1) (phi q1) (l1 .snd .snd .snd .snd)) (fgauto_wsym S (phi w) (c .ctgt1) ew)) in
    let mid : FgautoDyckRun S dec E0 q2 q1
      ≔ (cons. (letter_complement S x) (append (SignedLetter S) (d2 .fst) (cons. x nil.)),
         ((p2, (hs p2 x q2 (l2 .snd .snd .fst),
           fgauto_run_append S (SignedWord S) E0 p2 (d2 .fst) p1 (cons. x nil.) q1 (d2 .snd .fst)
             (fgauto_run_single S (SignedWord S) E0 p1 x q1 (l1 .snd .snd .fst)))),
          fgauto_dyck_conjugate S dec x (d2 .fst) (d2 .snd .snd))) in
    fgauto_dyck_run_compose S dec E0 v q2 w d1 (fgauto_dyck_run_compose S dec E0 q2 q1 w mid d3)

def fgauto_lift_inv_merge_pairs (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S)))
  (hs : FgautoSymmetric S (SignedWord S) E0) (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S)
  (h : FgautoLiftInv S dec E0 E phi) (c : FgautoConflict S (SignedWord S) E) (v w : SignedWord S)
  (dv : Decidable (Id (SignedWord S) (phi v) (c .ctgt2))) (dw : Decidable (Id (SignedWord S) (phi w) (c .ctgt2)))
  (e : Id (SignedWord S) (fgauto_merge_choose S (c .ctgt1) (c .ctgt2) (phi v) dv) (fgauto_merge_choose S (c .ctgt1) (c .ctgt2) (phi w) dw))
  : FgautoDyckRun S dec E0 v w
  ≔ match dv [
  | inl. av ↦ match dw [
    | inl. aw ↦ h .snd v w (fgauto_wtrans S (phi v) (c .ctgt2) (phi w) av (fgauto_wsym S (phi w) (c .ctgt2) aw))
    | inr. _ ↦ fgauto_merge_join S dec E0 hs E phi h c v w av (fgauto_wsym S (c .ctgt1) (phi w) e) ]
  | inr. _ ↦ match dw [
    | inl. aw ↦ fgauto_dyck_run_inverse S dec E0 hs w v (fgauto_merge_join S dec E0 hs E phi h c w v aw e)
    | inr. _ ↦ h .snd v w e ] ]

def fgauto_lift_inv_merge (S : Type) (dec : DecidableEquality S) (E0 : List (FgautoEdge S (SignedWord S)))
  (hs : FgautoSymmetric S (SignedWord S) E0) (E : List (FgautoEdge S (SignedWord S))) (phi : SignedWord S → SignedWord S)
  (c : FgautoConflict S (SignedWord S) E) (h : FgautoLiftInv S dec E0 E phi)
  : FgautoLiftInv S dec E0 (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (v ↦ fgauto_merge S dec (c .ctgt1) (c .ctgt2) (phi v))
  ≔ let f ≔ fgauto_merge S dec (c .ctgt1) (c .ctgt2) in
    (p' x q' s ↦
       let z ≔ fgauto_step_map_preimage S (SignedWord S) (SignedWord S) f E p' x q' s in
       let l ≔ h .fst (z .fst) x (z .snd .fst) (z .snd .snd .fst) in
       (l .fst, (l .snd .fst, (l .snd .snd .fst,
         (fgauto_wtrans S p' (f (z .fst)) (f (phi (l .fst))) (z .snd .snd .snd .fst) (refl f (l .snd .snd .snd .fst)),
          fgauto_wtrans S q' (f (z .snd .fst)) (f (phi (l .snd .fst))) (z .snd .snd .snd .snd) (refl f (l .snd .snd .snd .snd)))))),
     v w e ↦ fgauto_lift_inv_merge_pairs S dec E0 hs E phi h c v w
       (signed_word_decidable_equality S dec (phi v) (c .ctgt2)) (signed_word_decidable_equality S dec (phi w) (c .ctgt2)) e)

def fgauto_identified_dyck_run (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (v w : SignedWord S)
  (e : Id (SignedWord S) (fgauto_fold_image S dec gens v) (fgauto_fold_image S dec gens w))
  : FgautoDyckRun S dec (fgauto_bouquet S gens) v w
  ≔ let E0 ≔ fgauto_bouquet S gens in
    let hs ≔ fgauto_symmetrize_symmetric S (SignedWord S) (fgauto_petals S gens) in
    fgauto_fold_ind_fun S dec (FgautoLiftInv S dec E0) (E phi c h ↦ fgauto_lift_inv_merge S dec E0 hs E phi c h)
      (fgauto_stallings_fuel S gens) E0 nil. (y ↦ y)
      ((p' x q' s ↦ (p', (q', (s, (refl p', refl q'))))),
       (v0 w0 e0 ↦ (nil., (e0, refl (nil. : SignedWord S)))))
      .snd v w e

{` fggroups.tex:919-922. `}
def fgauto_identified_iff_dyck_run (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (v w : SignedWord S)
  : Product (Id (SignedWord S) (fgauto_fold_image S dec gens v) (fgauto_fold_image S dec gens w)
        → FgautoDyckRun S dec (fgauto_bouquet S gens) v w)
      (FgautoDyckRun S dec (fgauto_bouquet S gens) v w
        → Id (SignedWord S) (fgauto_fold_image S dec gens v) (fgauto_fold_image S dec gens w))
  ≔ (fgauto_identified_dyck_run S dec gens v w, fgauto_dyck_run_identified S dec gens v w)
