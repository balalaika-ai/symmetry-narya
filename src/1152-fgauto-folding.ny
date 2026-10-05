export "1151-fgauto-graphs"

{` Chapter 11, automata part 3: Stallings folding (fggroups.tex:837, the
   footnote cites Stallings 1991; the book never defines the automaton).

   The bouquet of a finite list gens of words has one petal per generator
   g = x1 ... xm: the path eps -x1-> [x1] -x2-> [x1 x2] ... -xm-> eps whose
   inner vertices are named by the proper prefixes of g (so the vertex type
   is SignedWord S and the base vertex is eps; generators with a common
   prefix share the corresponding vertices, which is one of the folds
   anyway).  The bouquet is made inverse by adding all reversed edges.

   A conflict is a pair of steps p -x-> q, p -x-> q' with q /= q'; folding
   it renames q' to q everywhere (fgauto_merge).  fgauto_fold repeats this
   at most `fuel` times, choosing the first conflict found by the decision
   procedure fgauto_conflict_search; with fuel = the number of endpoint
   occurrences of the bouquet the result is deterministic
   (fgauto_fold_deterministic: every fold removes a vertex).  The Stallings
   automaton S(H) of H = <gens> is the folded bouquet with its base vertex
   (fgauto_stallings).

   The key invariant (FgautoEdgeInv): every step p -x-> q satisfies
   H p x = H q (right cosets); it holds for the bouquet, is preserved by
   folding because folded vertices lie in the same coset, and implies that
   the label of every run p -w-> q satisfies H p w = H q. `}

{` Coset calculus. `}
def fgauto_same_coset_transport (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (p p' q q' : SignedWord S) (a : Id (SignedWord S) p p') (b : Id (SignedWord S) q q')
  (h : FgautoSameCoset S dec gens p q) : FgautoSameCoset S dec gens p' q'
  ≔ fgauto_in_subgroup_red S dec gens (append (SignedLetter S) p (word_inverse S q))
      (append (SignedLetter S) p' (word_inverse S q'))
      (refl ((u v ↦ word_reduction S dec (append (SignedLetter S) u (word_inverse S v)))
        : SignedWord S → SignedWord S → SignedWord S) a b) h

def fgauto_same_coset_mul_right (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (a b c : SignedWord S) (h : FgautoSameCoset S dec gens a b)
  : FgautoSameCoset S dec gens (append (SignedLetter S) a c) (append (SignedLetter S) b c)
  ≔ let ic ≔ word_inverse S c in
    let ib ≔ word_inverse S b in
    fgauto_in_subgroup_red S dec gens (append (SignedLetter S) a ib)
      (append (SignedLetter S) (append (SignedLetter S) a c) (word_inverse S (append (SignedLetter S) b c)))
      (calc
        word_reduction S dec (append (SignedLetter S) a ib)
        = word_reduction S dec (append (SignedLetter S) a (append (SignedLetter S) (append (SignedLetter S) c ic) ib))
          by fgauto_red_congr_right S dec a ib (append (SignedLetter S) (append (SignedLetter S) c ic) ib)
               (fgauto_wsym S (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) c ic) ib))
                 (word_reduction S dec ib)
                 (fgauto_red_drop_left S dec (append (SignedLetter S) c ic) ib (fgauto_red_inverse_right S dec c)))
        = word_reduction S dec (append (SignedLetter S) a (append (SignedLetter S) c (append (SignedLetter S) ic ib)))
          by refl ((z ↦ word_reduction S dec (append (SignedLetter S) a z)) : SignedWord S → SignedWord S)
               (append_assoc (SignedLetter S) c ic ib)
        = word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) a c) (append (SignedLetter S) ic ib))
          by fgauto_wsym S
               (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) a c) (append (SignedLetter S) ic ib)))
               (word_reduction S dec (append (SignedLetter S) a (append (SignedLetter S) c (append (SignedLetter S) ic ib))))
               (fgauto_red_assoc S dec a c (append (SignedLetter S) ic ib))
        = word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) a c) (word_inverse S (append (SignedLetter S) b c)))
          by refl ((z ↦ word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) a c) z)) : SignedWord S → SignedWord S)
               (fgauto_wsym S (word_inverse S (append (SignedLetter S) b c)) (append (SignedLetter S) ic ib)
                 (fgauto_word_inverse_append S b c)) ∎)
      h

{` H p x = H q implies H q x-bar = H p. `}
def fgauto_same_coset_flip (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (p : SignedWord S) (x : SignedLetter S) (q : SignedWord S)
  (h : FgautoSameCoset S dec gens (append (SignedLetter S) p (cons. x nil.)) q)
  : FgautoSameCoset S dec gens (append (SignedLetter S) q (cons. (letter_complement S x) nil.)) p
  ≔ let c : SignedWord S ≔ cons. (letter_complement S x) nil. in
    let ip ≔ word_inverse S p in
    fgauto_in_subgroup_red S dec gens
      (word_inverse S (append (SignedLetter S) (append (SignedLetter S) p (cons. x nil.)) (word_inverse S q)))
      (append (SignedLetter S) (append (SignedLetter S) q c) ip)
      (refl (word_reduction S dec)
        (calc
          word_inverse S (append (SignedLetter S) (append (SignedLetter S) p (cons. x nil.)) (word_inverse S q))
          = append (SignedLetter S) (word_inverse S (word_inverse S q)) (word_inverse S (append (SignedLetter S) p (cons. x nil.)))
            by fgauto_word_inverse_append S (append (SignedLetter S) p (cons. x nil.)) (word_inverse S q)
          = append (SignedLetter S) q (append (SignedLetter S) c ip)
            by refl ((u v ↦ append (SignedLetter S) u v) : SignedWord S → SignedWord S → SignedWord S)
                 (fgauto_word_inverse_involutive S q) (fgauto_word_inverse_append S p (cons. x nil.))
          = append (SignedLetter S) (append (SignedLetter S) q c) ip
            by fgauto_wsym S (append (SignedLetter S) (append (SignedLetter S) q c) ip)
                 (append (SignedLetter S) q (append (SignedLetter S) c ip)) (append_assoc (SignedLetter S) q c ip) ∎))
      (fgauto_in_subgroup_inv S dec gens
        (append (SignedLetter S) (append (SignedLetter S) p (cons. x nil.)) (word_inverse S q)) h)

{` The edge invariant and its consequence for runs. `}
def FgautoEdgeInv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) : Type
  ≔ (p : SignedWord S) (x : SignedLetter S) (q : SignedWord S) → FgautoStep S (SignedWord S) E p x q
    → FgautoSameCoset S dec gens (append (SignedLetter S) p (cons. x nil.)) q

def fgauto_run_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (h : FgautoEdgeInv S dec gens E)
  (p : SignedWord S) (w : SignedWord S) (q : SignedWord S) (r : FgautoRun S (SignedWord S) E p w q)
  : FgautoSameCoset S dec gens (append (SignedLetter S) p w) q
  ≔ match w [
  | nil. ↦ fgauto_same_coset_transport S dec gens p (append (SignedLetter S) p nil.) p q
      (fgauto_wsym S (append (SignedLetter S) p nil.) p (append_nil (SignedLetter S) p)) r
      (fgauto_same_coset_refl S dec gens p)
  | cons. x w' ↦ fgauto_same_coset_trans S dec gens (append (SignedLetter S) p (cons. x w'))
      (append (SignedLetter S) (r .fst) w') q
      (fgauto_same_coset_transport S dec gens
        (append (SignedLetter S) (append (SignedLetter S) p (cons. x nil.)) w') (append (SignedLetter S) p (cons. x w'))
        (append (SignedLetter S) (r .fst) w') (append (SignedLetter S) (r .fst) w')
        (append_assoc (SignedLetter S) p (cons. x nil.) w') (refl (append (SignedLetter S) (r .fst) w'))
        (fgauto_same_coset_mul_right S dec gens (append (SignedLetter S) p (cons. x nil.)) (r .fst) w'
          (h p x (r .fst) (r .snd .fst))))
      (fgauto_run_coset S dec gens E h (r .fst) w' q (r .snd .snd)) ]

{` If the base b lies in H and b -u-> b is a run, then u represents an
   element of H. `}
def fgauto_run_loop_member (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (h : FgautoEdgeInv S dec gens E) (b : SignedWord S)
  (hb : FgautoSameCoset S dec gens b nil.) (u : SignedWord S) (r : FgautoRun S (SignedWord S) E b u b)
  : FgautoInSubgroup S dec gens u
  ≔ let ib ≔ word_inverse S b in
    let bu ≔ append (SignedLetter S) b u in
    fgauto_in_subgroup_red S dec gens (append (SignedLetter S) ib bu) u
      (fgauto_wtrans S (word_reduction S dec (append (SignedLetter S) ib bu))
        (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) ib b) u)) (word_reduction S dec u)
        (fgauto_wsym S (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) ib b) u))
          (word_reduction S dec (append (SignedLetter S) ib bu)) (fgauto_red_assoc S dec ib b u))
        (fgauto_red_drop_left S dec (append (SignedLetter S) ib b) u (fgauto_red_inverse_left S dec b)))
      (fgauto_in_subgroup_mul S dec gens ib bu
        (fgauto_in_subgroup_inv S dec gens b (fgauto_same_coset_unit_member S dec gens b hb))
        (fgauto_same_coset_unit_member S dec gens bu
          (fgauto_same_coset_trans S dec gens bu b nil. (fgauto_run_coset S dec gens E h b u b r) hb)))

{` The bouquet of the generators. `}
def fgauto_petal (S : Type) (p : SignedWord S) (w : SignedWord S) : List (FgautoEdge S (SignedWord S))
  ≔ match w [
  | nil. ↦ nil.
  | cons. x t ↦ match t [
    | nil. ↦ cons. (p, x, nil.) nil.
    | cons. y t' ↦ cons. (p, x, append (SignedLetter S) p (cons. x nil.))
        (fgauto_petal S (append (SignedLetter S) p (cons. x nil.)) (cons. y t')) ] ]

def fgauto_petals (S : Type) (gens : List (SignedWord S)) : List (FgautoEdge S (SignedWord S))
  ≔ match gens [ nil. ↦ nil. | cons. g gs ↦ append (FgautoEdge S (SignedWord S)) (fgauto_petal S nil. g) (fgauto_petals S gs) ]

def fgauto_bouquet (S : Type) (gens : List (SignedWord S)) : List (FgautoEdge S (SignedWord S))
  ≔ fgauto_symmetrize S (SignedWord S) (fgauto_petals S gens)

{` Each petal reads its generator from the base back to the base. `}
def fgauto_petal_run (S : Type) (p : SignedWord S) (x : SignedLetter S) (t : SignedWord S)
  : FgautoRun S (SignedWord S) (fgauto_petal S p (cons. x t)) p (cons. x t) nil.
  ≔ match t [
  | nil. ↦ (nil., (fgauto_step_head S (SignedWord S) (p, x, nil.) nil., refl (nil. : SignedWord S)))
  | cons. y t' ↦
    let P ≔ append (SignedLetter S) p (cons. x nil.) in
    (P, (fgauto_step_head S (SignedWord S) (p, x, P) (fgauto_petal S P (cons. y t')),
      fgauto_run_mono S (SignedWord S) (fgauto_petal S P (cons. y t'))
        (cons. (p, x, P) (fgauto_petal S P (cons. y t'))) (p0 x0 q0 s ↦ inr. s) P (cons. y t') nil.
        (fgauto_petal_run S P y t'))) ]

def fgauto_petal_loop (S : Type) (g : SignedWord S)
  : FgautoRun S (SignedWord S) (fgauto_petal S nil. g) nil. g nil.
  ≔ match g [ nil. ↦ refl (nil. : SignedWord S) | cons. x t ↦ fgauto_petal_run S nil. x t ]

def fgauto_petals_loop (S : Type) (gens : List (SignedWord S)) (g : SignedWord S)
  (m : FgautoMem (SignedWord S) g gens) : FgautoRun S (SignedWord S) (fgauto_petals S gens) nil. g nil.
  ≔ match gens [
  | nil. ↦ match m []
  | cons. g0 gs ↦ match m [
    | inl. e ↦ fgauto_run_mono S (SignedWord S) (fgauto_petal S nil. g0) (fgauto_petals S (cons. g0 gs))
        (fgauto_step_append_left S (SignedWord S) (fgauto_petal S nil. g0) (fgauto_petals S gs)) nil. g nil.
        (fgauto_run_word S (SignedWord S) (fgauto_petal S nil. g0) nil. g0 g nil.
          (fgauto_wsym S g g0 e) (fgauto_petal_loop S g0))
    | inr. m' ↦ fgauto_run_mono S (SignedWord S) (fgauto_petals S gs) (fgauto_petals S (cons. g0 gs))
        (fgauto_step_append_right S (SignedWord S) (fgauto_petal S nil. g0) (fgauto_petals S gs)) nil. g nil.
        (fgauto_petals_loop S gs g m') ] ]

def fgauto_bouquet_loop (S : Type) (gens : List (SignedWord S)) (g : SignedWord S)
  (m : FgautoMem (SignedWord S) g gens) : FgautoRun S (SignedWord S) (fgauto_bouquet S gens) nil. g nil.
  ≔ fgauto_run_mono S (SignedWord S) (fgauto_petals S gens) (fgauto_bouquet S gens)
      (fgauto_step_append_left S (SignedWord S) (fgauto_petals S gens) (fgauto_reverse_edges S (SignedWord S) (fgauto_petals S gens)))
      nil. g nil. (fgauto_petals_loop S gens g m)

{` The edge invariant for the bouquet. `}
def fgauto_petal_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (p : SignedWord S) (x : SignedLetter S) (t : SignedWord S)
  (hg : FgautoInSubgroup S dec gens (append (SignedLetter S) p (cons. x t)))
  : FgautoEdgeInv S dec gens (fgauto_petal S p (cons. x t))
  ≔ p0 x0 q0 s ↦ match t [
  | nil. ↦ match s [
    | inl. e ↦ fgauto_same_coset_transport S dec gens (append (SignedLetter S) p (cons. x nil.))
        (append (SignedLetter S) p0 (cons. x0 nil.)) nil. q0
        (refl ((u v ↦ append (SignedLetter S) u (cons. v nil.)) : SignedWord S → SignedLetter S → SignedWord S)
          (fgauto_wsym S p0 p (e .fst)) (inverse (SignedLetter S) x0 x (e .snd .fst)))
        (fgauto_wsym S q0 nil. (e .snd .snd))
        (fgauto_member_same_coset_unit S dec gens (append (SignedLetter S) p (cons. x nil.)) hg)
    | inr. s' ↦ match s' [] ]
  | cons. y t' ↦
    let P ≔ append (SignedLetter S) p (cons. x nil.) in
    match s [
    | inl. e ↦ fgauto_same_coset_transport S dec gens P (append (SignedLetter S) p0 (cons. x0 nil.)) P q0
        (refl ((u v ↦ append (SignedLetter S) u (cons. v nil.)) : SignedWord S → SignedLetter S → SignedWord S)
          (fgauto_wsym S p0 p (e .fst)) (inverse (SignedLetter S) x0 x (e .snd .fst)))
        (fgauto_wsym S q0 P (e .snd .snd))
        (fgauto_same_coset_refl S dec gens P)
    | inr. s' ↦ fgauto_petal_inv S dec gens P y t'
        (fgauto_in_subgroup_red S dec gens (append (SignedLetter S) p (cons. x (cons. y t')))
          (append (SignedLetter S) P (cons. y t'))
          (refl (word_reduction S dec)
            (fgauto_wsym S (append (SignedLetter S) P (cons. y t')) (append (SignedLetter S) p (cons. x (cons. y t')))
              (append_assoc (SignedLetter S) p (cons. x nil.) (cons. y t'))))
          hg) p0 x0 q0 s' ] ]

def fgauto_petals_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (L : List (SignedWord S)) (hL : (g : SignedWord S) → FgautoMem (SignedWord S) g L → FgautoInSubgroup S dec gens g)
  : FgautoEdgeInv S dec gens (fgauto_petals S L)
  ≔ p0 x0 q0 s ↦ match L [
  | nil. ↦ match s []
  | cons. g gs ↦ match fgauto_step_append_split S (SignedWord S) (fgauto_petal S nil. g) (fgauto_petals S gs) p0 x0 q0 s [
    | inl. k ↦ match g [
      | nil. ↦ match k []
      | cons. x t ↦ fgauto_petal_inv S dec gens nil. x t (hL (cons. x t) (inl. (refl (cons. x t : SignedWord S)))) p0 x0 q0 k ]
    | inr. k ↦ fgauto_petals_inv S dec gens gs (g' m ↦ hL g' (inr. m)) p0 x0 q0 k ] ]

def fgauto_symmetrize_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (h : FgautoEdgeInv S dec gens E)
  : FgautoEdgeInv S dec gens (fgauto_symmetrize S (SignedWord S) E)
  ≔ p x q s ↦ match fgauto_step_append_split S (SignedWord S) E (fgauto_reverse_edges S (SignedWord S) E) p x q s [
  | inl. k ↦ h p x q k
  | inr. k ↦ fgauto_same_coset_transport S dec gens
      (append (SignedLetter S) p (cons. (letter_complement S (letter_complement S x)) nil.))
      (append (SignedLetter S) p (cons. x nil.)) q q
      (refl ((v ↦ append (SignedLetter S) p (cons. v nil.)) : SignedLetter S → SignedWord S)
        (letter_complement_involutive S x)) (refl q)
      (fgauto_same_coset_flip S dec gens q (letter_complement S x) p
        (h q (letter_complement S x) p (fgauto_step_unreverse S (SignedWord S) E p x q k))) ]

def fgauto_bouquet_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoEdgeInv S dec gens (fgauto_bouquet S gens)
  ≔ fgauto_symmetrize_inv S dec gens (fgauto_petals S gens)
      (fgauto_petals_inv S dec gens gens (fgauto_in_subgroup_generator S dec gens))

{` Folding one conflict: merge b into a. `}
def fgauto_merge_choose (S : Type) (a b v : SignedWord S) (d : Decidable (Id (SignedWord S) v b)) : SignedWord S
  ≔ match d [ inl. _ ↦ a | inr. _ ↦ v ]

def fgauto_merge (S : Type) (dec : DecidableEquality S) (a b : SignedWord S) (v : SignedWord S) : SignedWord S
  ≔ fgauto_merge_choose S a b v (signed_word_decidable_equality S dec v b)

def fgauto_merge_choose_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (a b v : SignedWord S) (hab : FgautoSameCoset S dec gens a b) (d : Decidable (Id (SignedWord S) v b))
  : FgautoSameCoset S dec gens (fgauto_merge_choose S a b v d) v
  ≔ match d [
  | inl. e ↦ fgauto_same_coset_transport S dec gens a a b v (refl a) (fgauto_wsym S v b e) hab
  | inr. _ ↦ fgauto_same_coset_refl S dec gens v ]

def fgauto_merge_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (a b v : SignedWord S) (hab : FgautoSameCoset S dec gens a b)
  : FgautoSameCoset S dec gens (fgauto_merge S dec a b v) v
  ≔ fgauto_merge_choose_coset S dec gens a b v hab (signed_word_decidable_equality S dec v b)

def fgauto_merge_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (h : FgautoEdgeInv S dec gens E) (a b : SignedWord S)
  (hab : FgautoSameCoset S dec gens a b)
  : FgautoEdgeInv S dec gens (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec a b) E)
  ≔ p' x q' s ↦
    let f ≔ fgauto_merge S dec a b in
    let z ≔ fgauto_step_map_preimage S (SignedWord S) (SignedWord S) f E p' x q' s in
    let p ≔ z .fst in
    let q ≔ z .snd .fst in
    fgauto_same_coset_transport S dec gens (append (SignedLetter S) (f p) (cons. x nil.))
      (append (SignedLetter S) p' (cons. x nil.)) (f q) q'
      (refl ((u ↦ append (SignedLetter S) u (cons. x nil.)) : SignedWord S → SignedWord S)
        (fgauto_wsym S p' (f p) (z .snd .snd .snd .fst)))
      (fgauto_wsym S q' (f q) (z .snd .snd .snd .snd))
      (fgauto_same_coset_trans S dec gens (append (SignedLetter S) (f p) (cons. x nil.))
        (append (SignedLetter S) p (cons. x nil.)) (f q)
        (fgauto_same_coset_mul_right S dec gens (f p) p (cons. x nil.) (fgauto_merge_coset S dec gens a b p hab))
        (fgauto_same_coset_trans S dec gens (append (SignedLetter S) p (cons. x nil.)) q (f q)
          (h p x q (z .snd .snd .fst))
          (fgauto_same_coset_sym S dec gens (f q) q (fgauto_merge_coset S dec gens a b q hab))))

{` The two targets of a conflict lie in the same coset. `}
def fgauto_conflict_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (h : FgautoEdgeInv S dec gens E) (c : FgautoConflict S (SignedWord S) E)
  : FgautoSameCoset S dec gens (c .ctgt1) (c .ctgt2)
  ≔ let px ≔ append (SignedLetter S) (c .csrc) (cons. (c .clab) nil.) in
    fgauto_same_coset_trans S dec gens (c .ctgt1) px (c .ctgt2)
      (fgauto_same_coset_sym S dec gens px (c .ctgt1) (h (c .csrc) (c .clab) (c .ctgt1) (c .cstep1)))
      (h (c .csrc) (c .clab) (c .ctgt2) (c .cstep2))

{` The folding procedure. `}
def FgautoPointedGraph (S : Type) : Type ≔ Product (List (FgautoEdge S (SignedWord S))) (SignedWord S)

def fgauto_fold_step (S : Type) (dec : DecidableEquality S)
  (k : List (FgautoEdge S (SignedWord S)) → SignedWord S → FgautoPointedGraph S)
  (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S)
  (d : Sum (FgautoConflict S (SignedWord S) E) (FgautoDeterministic S (SignedWord S) E)) : FgautoPointedGraph S
  ≔ match d [
  | inr. _ ↦ (E, b)
  | inl. c ↦ k (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b) ]

def fgauto_fold (S : Type) (dec : DecidableEquality S) (fuel : Nat) (E : List (FgautoEdge S (SignedWord S)))
  (b : SignedWord S) : FgautoPointedGraph S
  ≔ match fuel [
  | zero. ↦ (E, b)
  | suc. f ↦ fgauto_fold_step S dec (fgauto_fold S dec f) E b
      (fgauto_conflict_search S (SignedWord S) dec (signed_word_decidable_equality S dec) E) ]

{` Induction principle for properties preserved by every fold. `}
def fgauto_fold_ind_step (S : Type) (dec : DecidableEquality S)
  (P : List (FgautoEdge S (SignedWord S)) → SignedWord S → Type)
  (hP : (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (c : FgautoConflict S (SignedWord S) E) → P E b
    → P (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
        (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b))
  (f : Nat)
  (recur : (E1 : List (FgautoEdge S (SignedWord S))) (b1 : SignedWord S) → P E1 b1
    → P (fgauto_fold S dec f E1 b1 .fst) (fgauto_fold S dec f E1 b1 .snd))
  (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (h : P E b)
  (d : Sum (FgautoConflict S (SignedWord S) E) (FgautoDeterministic S (SignedWord S) E))
  : P (fgauto_fold_step S dec (fgauto_fold S dec f) E b d .fst) (fgauto_fold_step S dec (fgauto_fold S dec f) E b d .snd)
  ≔ match d [
  | inr. _ ↦ h
  | inl. c ↦ recur (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b) (hP E b c h) ]

def fgauto_fold_ind (S : Type) (dec : DecidableEquality S)
  (P : List (FgautoEdge S (SignedWord S)) → SignedWord S → Type)
  (hP : (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (c : FgautoConflict S (SignedWord S) E) → P E b
    → P (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
        (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b))
  (fuel : Nat) (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (h : P E b)
  : P (fgauto_fold S dec fuel E b .fst) (fgauto_fold S dec fuel E b .snd)
  ≔ match fuel [
  | zero. ↦ h
  | suc. f ↦ fgauto_fold_ind_step S dec P hP f (fgauto_fold_ind S dec P hP f) E b h
      (fgauto_conflict_search S (SignedWord S) dec (signed_word_decidable_equality S dec) E) ]
