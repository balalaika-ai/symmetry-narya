export "1150-fgauto-subgroups"

{` Chapter 11, automata part 2: labelled graphs (automata over the signed
   alphabet S~ = S + S) given by finite lists of edges, their runs, inverse
   (symmetric) and deterministic graphs, and the deterministic transition
   function obtained by running the automaton.

   A graph with vertex type V is a list E of edges (src, lab, tgt).  A step
   p -x-> q is a position in E of an edge with these data (FgautoStep, by
   recursion on the list), and a run p -w-> q reads the word w letter by
   letter (FgautoRun, by recursion on w).  The graph is inverse (the book's
   "there's an edge (p,a,q) iff there's one (q,A,p)", fggroups.tex:914-918)
   when every step p -x-> q has a reverse step q -x-bar-> p, and
   deterministic when steps from p with the same letter have the same
   target.  For a deterministic inverse graph a run of x x-bar w can be
   shortened to a run of w, hence every run of w gives a run of rho(w)
   (fgauto_run_reduction). `}

def FgautoEdge (S V : Type) : Type ≔ sig (src : V, lab : SignedLetter S, tgt : V)

def FgautoStep (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) : Type
  ≔ match E [
  | nil. ↦ Empty
  | cons. e E' ↦ Sum (Product (Id V p (e .src)) (Product (Id (SignedLetter S) x (e .lab)) (Id V q (e .tgt))))
      (FgautoStep S V E' p x q) ]

def FgautoRun (S V : Type) (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q : V) : Type
  ≔ match w [
  | nil. ↦ Id V p q
  | cons. x w' ↦ Σ V (r ↦ Product (FgautoStep S V E p x r) (FgautoRun S V E r w' q)) ]

{` The step of the head edge. `}
def fgauto_step_head (S V : Type) (e : FgautoEdge S V) (E : List (FgautoEdge S V))
  : FgautoStep S V (cons. e E) (e .src) (e .lab) (e .tgt)
  ≔ inl. (refl (e .src), (refl (e .lab), refl (e .tgt)))

{` Transport of steps and runs along identifications of the endpoints. `}
def fgauto_step_transport (S V : Type) (E : List (FgautoEdge S V)) (p p' : V) (x x' : SignedLetter S) (q q' : V)
  (a : Id V p p') (b : Id (SignedLetter S) x x') (c : Id V q q') (s : FgautoStep S V E p x q)
  : FgautoStep S V E p' x' q'
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ inl. (concat V p' p (e .src) (inverse V p p' a) (t .fst),
        (concat (SignedLetter S) x' x (e .lab) (inverse (SignedLetter S) x x' b) (t .snd .fst),
         concat V q' q (e .tgt) (inverse V q q' c) (t .snd .snd)))
    | inr. s' ↦ inr. (fgauto_step_transport S V E' p p' x x' q q' a b c s') ] ]

def fgauto_run_end (S V : Type) (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q q' : V)
  (c : Id V q q') (r : FgautoRun S V E p w q) : FgautoRun S V E p w q'
  ≔ match w [
  | nil. ↦ concat V p q q' r c
  | cons. x w' ↦ (r .fst, (r .snd .fst, fgauto_run_end S V E (r .fst) w' q q' c (r .snd .snd))) ]

def fgauto_run_start (S V : Type) (E : List (FgautoEdge S V)) (p p' : V) (w : SignedWord S) (q : V)
  (c : Id V p p') (r : FgautoRun S V E p w q) : FgautoRun S V E p' w q
  ≔ match w [
  | nil. ↦ concat V p' p q (inverse V p p' c) r
  | cons. x w' ↦ (r .fst, (fgauto_step_transport S V E p p' x x (r .fst) (r .fst) c (refl x) (refl (r .fst)) (r .snd .fst),
      r .snd .snd)) ]

def fgauto_run_word (S V : Type) (E : List (FgautoEdge S V)) (p : V) (w w' : SignedWord S) (q : V)
  (c : Id (SignedWord S) w w') (r : FgautoRun S V E p w q) : FgautoRun S V E p w' q
  ≔ transport (SignedWord S) (z ↦ FgautoRun S V E p z q) w w' c r

def fgauto_run_single (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V E p x q) : FgautoRun S V E p (cons. x nil.) q
  ≔ (q, (s, refl q))

{` Runs compose along concatenation and split along it. `}
def fgauto_run_append (S V : Type) (E : List (FgautoEdge S V)) (p : V) (u : SignedWord S) (r : V)
  (v : SignedWord S) (q : V) (a : FgautoRun S V E p u r) (b : FgautoRun S V E r v q)
  : FgautoRun S V E p (append (SignedLetter S) u v) q
  ≔ match u [
  | nil. ↦ fgauto_run_start S V E r p v q (inverse V p r a) b
  | cons. x u' ↦ (a .fst, (a .snd .fst, fgauto_run_append S V E (a .fst) u' r v q (a .snd .snd) b)) ]

def fgauto_run_split (S V : Type) (E : List (FgautoEdge S V)) (p : V) (u v : SignedWord S) (q : V)
  (a : FgautoRun S V E p (append (SignedLetter S) u v) q)
  : Σ V (r ↦ Product (FgautoRun S V E p u r) (FgautoRun S V E r v q))
  ≔ match u [
  | nil. ↦ (p, (refl p, a))
  | cons. x u' ↦
    let t ≔ fgauto_run_split S V E (a .fst) u' v q (a .snd .snd) in
    (t .fst, ((a .fst, (a .snd .fst, t .snd .fst)), t .snd .snd)) ]

{` Edge lists: inclusion, concatenation, images under vertex maps. `}
def FgautoStepIncl (S V : Type) (E E' : List (FgautoEdge S V)) : Type
  ≔ (p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → FgautoStep S V E' p x q

def fgauto_run_mono (S V : Type) (E E' : List (FgautoEdge S V)) (i : FgautoStepIncl S V E E')
  (p : V) (w : SignedWord S) (q : V) (r : FgautoRun S V E p w q) : FgautoRun S V E' p w q
  ≔ match w [
  | nil. ↦ r
  | cons. x w' ↦ (r .fst, (i p x (r .fst) (r .snd .fst), fgauto_run_mono S V E E' i (r .fst) w' q (r .snd .snd))) ]

def fgauto_step_append_left (S V : Type) (E E' : List (FgautoEdge S V)) : FgautoStepIncl S V E (append (FgautoEdge S V) E E')
  ≔ p x q s ↦ match E [
  | nil. ↦ match s []
  | cons. e E0 ↦ match s [ inl. t ↦ inl. t | inr. s' ↦ inr. (fgauto_step_append_left S V E0 E' p x q s') ] ]

def fgauto_step_append_right (S V : Type) (E E' : List (FgautoEdge S V)) : FgautoStepIncl S V E' (append (FgautoEdge S V) E E')
  ≔ p x q s ↦ match E [ nil. ↦ s | cons. e E0 ↦ inr. (fgauto_step_append_right S V E0 E' p x q s) ]

def fgauto_step_append_split (S V : Type) (E E' : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V (append (FgautoEdge S V) E E') p x q) : Sum (FgautoStep S V E p x q) (FgautoStep S V E' p x q)
  ≔ match E [
  | nil. ↦ inr. s
  | cons. e E0 ↦ match s [
    | inl. t ↦ inl. (inl. t)
    | inr. s' ↦ match fgauto_step_append_split S V E0 E' p x q s' [ inl. k ↦ inl. (inr. k) | inr. k ↦ inr. k ] ] ]

def fgauto_map_edges (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) : List (FgautoEdge S W)
  ≔ match E [ nil. ↦ nil. | cons. e E' ↦ cons. (f (e .src), e .lab, f (e .tgt)) (fgauto_map_edges S V W f E') ]

def fgauto_step_map (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V E p x q) : FgautoStep S W (fgauto_map_edges S V W f E) (f p) x (f q)
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ inl. (refl f (t .fst), (t .snd .fst, refl f (t .snd .snd)))
    | inr. s' ↦ inr. (fgauto_step_map S V W f E' p x q s') ] ]

def fgauto_run_map (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q : V)
  (r : FgautoRun S V E p w q) : FgautoRun S W (fgauto_map_edges S V W f E) (f p) w (f q)
  ≔ match w [
  | nil. ↦ refl f r
  | cons. x w' ↦ (f (r .fst), (fgauto_step_map S V W f E p x (r .fst) (r .snd .fst),
      fgauto_run_map S V W f E (r .fst) w' q (r .snd .snd))) ]

{` A step of an image graph comes from a step of the original graph. `}
def FgautoStepPreimage (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) (p' : W) (x : SignedLetter S) (q' : W)
  : Type
  ≔ Σ V (p ↦ Σ V (q ↦ Product (FgautoStep S V E p x q) (Product (Id W p' (f p)) (Id W q' (f q)))))

def fgauto_step_map_preimage (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) (p' : W) (x : SignedLetter S)
  (q' : W) (s : FgautoStep S W (fgauto_map_edges S V W f E) p' x q') : FgautoStepPreimage S V W f E p' x q'
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ (e .src, (e .tgt, (inl. (refl (e .src), (t .snd .fst, refl (e .tgt))), (t .fst, t .snd .snd))))
    | inr. s' ↦
      let z ≔ fgauto_step_map_preimage S V W f E' p' x q' s' in
      (z .fst, (z .snd .fst, (inr. (z .snd .snd .fst), z .snd .snd .snd))) ] ]

{` Inverse graphs: the reversed edge list and symmetric edge lists. `}
def fgauto_reverse_edges (S V : Type) (E : List (FgautoEdge S V)) : List (FgautoEdge S V)
  ≔ match E [ nil. ↦ nil. | cons. e E' ↦ cons. (e .tgt, letter_complement S (e .lab), e .src) (fgauto_reverse_edges S V E') ]

def fgauto_step_reverse (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V E p x q) : FgautoStep S V (fgauto_reverse_edges S V E) q (letter_complement S x) p
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ inl. (t .snd .snd, (refl (letter_complement S) (t .snd .fst), t .fst))
    | inr. s' ↦ inr. (fgauto_step_reverse S V E' p x q s') ] ]

def fgauto_step_unreverse (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V (fgauto_reverse_edges S V E) p x q) : FgautoStep S V E q (letter_complement S x) p
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ inl. (t .snd .snd,
        (concat (SignedLetter S) (letter_complement S x) (letter_complement S (letter_complement S (e .lab))) (e .lab)
          (refl (letter_complement S) (t .snd .fst)) (letter_complement_involutive S (e .lab)), t .fst))
    | inr. s' ↦ inr. (fgauto_step_unreverse S V E' p x q s') ] ]

def FgautoSymmetric (S V : Type) (E : List (FgautoEdge S V)) : Type
  ≔ (p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → FgautoStep S V E q (letter_complement S x) p

{` The symmetric closure E ++ reverse(E) is symmetric. `}
def fgauto_symmetrize (S V : Type) (E : List (FgautoEdge S V)) : List (FgautoEdge S V)
  ≔ append (FgautoEdge S V) E (fgauto_reverse_edges S V E)

def fgauto_symmetrize_symmetric (S V : Type) (E : List (FgautoEdge S V)) : FgautoSymmetric S V (fgauto_symmetrize S V E)
  ≔ p x q s ↦ match fgauto_step_append_split S V E (fgauto_reverse_edges S V E) p x q s [
  | inl. k ↦ fgauto_step_append_right S V E (fgauto_reverse_edges S V E) q (letter_complement S x) p
      (fgauto_step_reverse S V E p x q k)
  | inr. k ↦ fgauto_step_append_left S V E (fgauto_reverse_edges S V E) q (letter_complement S x) p
      (fgauto_step_unreverse S V E p x q k) ]

{` Symmetry is preserved by images. `}
def fgauto_map_symmetric (S V W : Type) (f : V → W) (E : List (FgautoEdge S V)) (h : FgautoSymmetric S V E)
  : FgautoSymmetric S W (fgauto_map_edges S V W f E)
  ≔ p' x q' s ↦
    let z ≔ fgauto_step_map_preimage S V W f E p' x q' s in
    fgauto_step_transport S W (fgauto_map_edges S V W f E) (f (z .snd .fst)) q' (letter_complement S x)
      (letter_complement S x) (f (z .fst)) p'
      (inverse W q' (f (z .snd .fst)) (z .snd .snd .snd .snd)) (refl (letter_complement S x))
      (inverse W p' (f (z .fst)) (z .snd .snd .snd .fst))
      (fgauto_step_map S V W f E (z .snd .fst) (letter_complement S x) (z .fst)
        (h (z .fst) x (z .snd .fst) (z .snd .snd .fst)))

{` In a symmetric graph runs can be reversed: a run p -w-> q gives a run
   q -w^-1-> p. `}
def fgauto_run_inverse (S V : Type) (E : List (FgautoEdge S V)) (h : FgautoSymmetric S V E)
  (p : V) (w : SignedWord S) (q : V) (r : FgautoRun S V E p w q) : FgautoRun S V E q (word_inverse S w) p
  ≔ match w [
  | nil. ↦ inverse V p q r
  | cons. x w' ↦ fgauto_run_append S V E q (word_inverse S w') (r .fst) (cons. (letter_complement S x) nil.) p
      (fgauto_run_inverse S V E h (r .fst) w' q (r .snd .snd))
      (fgauto_run_single S V E (r .fst) (letter_complement S x) p (h p x (r .fst) (r .snd .fst))) ]

{` Deterministic graphs. `}
def FgautoDeterministic (S V : Type) (E : List (FgautoEdge S V)) : Type
  ≔ (p : V) (x : SignedLetter S) (q q' : V) → FgautoStep S V E p x q → FgautoStep S V E p x q' → Id V q q'

{` In a deterministic symmetric graph, p -x-> r -x-bar-> t forces t = p. `}
def fgauto_det_cancel_vertex (S V : Type) (E : List (FgautoEdge S V)) (hs : FgautoSymmetric S V E)
  (hd : FgautoDeterministic S V E) (p : V) (x : SignedLetter S) (r t : V)
  (a : FgautoStep S V E p x r) (b : FgautoStep S V E r (letter_complement S x) t) : Id V p t
  ≔ hd r (letter_complement S x) p t (hs p x r a) b

def fgauto_run_cancel_pair (S V : Type) (E : List (FgautoEdge S V)) (hs : FgautoSymmetric S V E)
  (hd : FgautoDeterministic S V E) (p : V) (x y : SignedLetter S) (v : SignedWord S) (q : V)
  (c : Id (SignedLetter S) y (letter_complement S x)) (r : FgautoRun S V E p (cons. x (cons. y v)) q)
  : FgautoRun S V E p v q
  ≔ let r1 ≔ r .fst in
    let r2 ≔ r .snd .snd .fst in
    fgauto_run_start S V E r2 p v q
      (inverse V p r2 (fgauto_det_cancel_vertex S V E hs hd p x r1 r2 (r .snd .fst)
        (fgauto_step_transport S V E r1 r1 y (letter_complement S x) r2 r2 (refl r1) c (refl r2)
          (r .snd .snd .snd .fst))))
      (r .snd .snd .snd .snd)

def fgauto_run_letter_reduce_step (S V : Type) (E : List (FgautoEdge S V)) (hs : FgautoSymmetric S V E)
  (hd : FgautoDeterministic S V E) (p : V) (x y : SignedLetter S) (v : SignedWord S) (q : V)
  (d : Decidable (Id (SignedLetter S) y (letter_complement S x))) (r : FgautoRun S V E p (cons. x (cons. y v)) q)
  : FgautoRun S V E p (fw_cancel_or_cons S x y v d) q
  ≔ match d [ inl. c ↦ fgauto_run_cancel_pair S V E hs hd p x y v q c r | inr. _ ↦ r ]

def fgauto_run_letter_reduce (S V : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S V))
  (hs : FgautoSymmetric S V E) (hd : FgautoDeterministic S V E) (p : V) (x : SignedLetter S) (v : SignedWord S)
  (q : V) (r : FgautoRun S V E p (cons. x v) q) : FgautoRun S V E p (word_letter_reduce S dec x v) q
  ≔ match v [
  | nil. ↦ r
  | cons. y v' ↦ fgauto_run_letter_reduce_step S V E hs hd p x y v' q
      (signed_letter_decidable_equality S dec y (letter_complement S x)) r ]

{` Every run of w in a deterministic inverse graph gives a run of rho(w). `}
def fgauto_run_reduction (S V : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S V))
  (hs : FgautoSymmetric S V E) (hd : FgautoDeterministic S V E) (p : V) (w : SignedWord S) (q : V)
  (r : FgautoRun S V E p w q) : FgautoRun S V E p (word_reduction S dec w) q
  ≔ match w [
  | nil. ↦ r
  | cons. x w' ↦ fgauto_run_letter_reduce S V dec E hs hd p x (word_reduction S dec w') q
      (r .fst, (r .snd .fst, fgauto_run_reduction S V dec E hs hd (r .fst) w' q (r .snd .snd))) ]

{` Running a deterministic automaton: the partial transition function
   (first matching edge; inl star = undefined) and its extension to words. `}
def fgauto_lookup_pick (S V : Type) (p : V) (x : SignedLetter S) (e : FgautoEdge S V)
  (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab))) (rest : Sum Unit V) : Sum Unit V
  ≔ match d1 [ inl. _ ↦ match d2 [ inl. _ ↦ inr. (e .tgt) | inr. _ ↦ rest ] | inr. _ ↦ rest ]

def fgauto_lookup (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V) (E : List (FgautoEdge S V))
  (p : V) (x : SignedLetter S) : Sum Unit V
  ≔ match E [
  | nil. ↦ inl. star.
  | cons. e E' ↦ fgauto_lookup_pick S V p x e (dV p (e .src)) (signed_letter_decidable_equality S dec x (e .lab))
      (fgauto_lookup S V dec dV E' p x) ]

def fgauto_bind (V : Type) (o : Sum Unit V) (k : V → Sum Unit V) : Sum Unit V
  ≔ match o [ inl. _ ↦ inl. star. | inr. r ↦ k r ]

def fgauto_delta (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V) (E : List (FgautoEdge S V))
  (p : V) (w : SignedWord S) : Sum Unit V
  ≔ match w [
  | nil. ↦ inr. p
  | cons. x w' ↦ fgauto_bind V (fgauto_lookup S V dec dV E p x) (r ↦ fgauto_delta S V dec dV E r w') ]

{` Soundness: a defined transition is a step, a defined run is a run. `}
def fgauto_lookup_pick_sound (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S)
  (e : FgautoEdge S V) (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab)))
  (rest : Sum Unit V) (q : V) (ih : Id (Sum Unit V) rest (inr. q) → FgautoStep S V E p x q)
  (h : Id (Sum Unit V) (fgauto_lookup_pick S V p x e d1 d2 rest) (inr. q)) : FgautoStep S V (cons. e E) p x q
  ≔ match d1 [
  | inl. a ↦ match d2 [
    | inl. b ↦ inl. (a, (b, inverse V (e .tgt) q (sum_encode Unit V (inr. (e .tgt)) (inr. q) h)))
    | inr. _ ↦ inr. (ih h) ]
  | inr. _ ↦ inr. (ih h) ]

def fgauto_lookup_sound (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (h : Id (Sum Unit V) (fgauto_lookup S V dec dV E p x) (inr. q)) : FgautoStep S V E p x q
  ≔ match E [
  | nil. ↦ match sum_encode Unit V (inl. star.) (inr. q) h []
  | cons. e E' ↦ fgauto_lookup_pick_sound S V E' p x e (dV p (e .src))
      (signed_letter_decidable_equality S dec x (e .lab)) (fgauto_lookup S V dec dV E' p x) q
      (fgauto_lookup_sound S V dec dV E' p x q) h ]

def fgauto_bind_inr (V : Type) (o : Sum Unit V) (k : V → Sum Unit V) (q : V)
  (h : Id (Sum Unit V) (fgauto_bind V o k) (inr. q))
  : Σ V (r ↦ Product (Id (Sum Unit V) o (inr. r)) (Id (Sum Unit V) (k r) (inr. q)))
  ≔ match o [
  | inl. u ↦ match sum_encode Unit V (inl. star.) (inr. q) h []
  | inr. r ↦ (r, (refl (inr. r : Sum Unit V), h)) ]

def fgauto_delta_sound (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q : V)
  (h : Id (Sum Unit V) (fgauto_delta S V dec dV E p w) (inr. q)) : FgautoRun S V E p w q
  ≔ match w [
  | nil. ↦ sum_encode Unit V (inr. p) (inr. q) h
  | cons. x w' ↦
    let z ≔ fgauto_bind_inr V (fgauto_lookup S V dec dV E p x) (r ↦ fgauto_delta S V dec dV E r w') q h in
    (z .fst, (fgauto_lookup_sound S V dec dV E p x (z .fst) (z .snd .fst),
      fgauto_delta_sound S V dec dV E (z .fst) w' q (z .snd .snd))) ]

{` Completeness: if there is a step, the transition is defined. `}
def fgauto_lookup_pick_complete_here (S V : Type) (p : V) (x : SignedLetter S) (e : FgautoEdge S V)
  (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab))) (rest : Sum Unit V)
  (a : Id V p (e .src)) (b : Id (SignedLetter S) x (e .lab))
  : Σ V (q ↦ Id (Sum Unit V) (fgauto_lookup_pick S V p x e d1 d2 rest) (inr. q))
  ≔ match d1 [
  | inl. _ ↦ match d2 [
    | inl. _ ↦ (e .tgt, refl (inr. (e .tgt) : Sum Unit V))
    | inr. n ↦ match n b [] ]
  | inr. n ↦ match n a [] ]

def fgauto_lookup_pick_complete_rest (S V : Type) (p : V) (x : SignedLetter S) (e : FgautoEdge S V)
  (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab))) (rest : Sum Unit V)
  (q : V) (h : Id (Sum Unit V) rest (inr. q))
  : Σ V (q' ↦ Id (Sum Unit V) (fgauto_lookup_pick S V p x e d1 d2 rest) (inr. q'))
  ≔ match d1 [
  | inl. _ ↦ match d2 [ inl. _ ↦ (e .tgt, refl (inr. (e .tgt) : Sum Unit V)) | inr. _ ↦ (q, h) ]
  | inr. _ ↦ (q, h) ]

def fgauto_lookup_complete (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) (s : FgautoStep S V E p x q)
  : Σ V (q' ↦ Id (Sum Unit V) (fgauto_lookup S V dec dV E p x) (inr. q'))
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ fgauto_lookup_pick_complete_here S V p x e (dV p (e .src))
        (signed_letter_decidable_equality S dec x (e .lab)) (fgauto_lookup S V dec dV E' p x) (t .fst) (t .snd .fst)
    | inr. s' ↦
      let z ≔ fgauto_lookup_complete S V dec dV E' p x q s' in
      fgauto_lookup_pick_complete_rest S V p x e (dV p (e .src))
        (signed_letter_decidable_equality S dec x (e .lab)) (fgauto_lookup S V dec dV E' p x) (z .fst) (z .snd) ] ]

{` For deterministic graphs the transition function computes the run. `}
def fgauto_lookup_det (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (hd : FgautoDeterministic S V E) (p : V) (x : SignedLetter S) (q : V)
  (s : FgautoStep S V E p x q) : Id (Sum Unit V) (fgauto_lookup S V dec dV E p x) (inr. q)
  ≔ let z ≔ fgauto_lookup_complete S V dec dV E p x q s in
    concat (Sum Unit V) (fgauto_lookup S V dec dV E p x) (inr. (z .fst)) (inr. q) (z .snd)
      (inr. (hd p x (z .fst) q (fgauto_lookup_sound S V dec dV E p x (z .fst) (z .snd)) s))

def fgauto_delta_det (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (hd : FgautoDeterministic S V E) (p : V) (w : SignedWord S) (q : V)
  (r : FgautoRun S V E p w q) : Id (Sum Unit V) (fgauto_delta S V dec dV E p w) (inr. q)
  ≔ match w [
  | nil. ↦ inr. r
  | cons. x w' ↦ concat (Sum Unit V)
      (fgauto_bind V (fgauto_lookup S V dec dV E p x) (t ↦ fgauto_delta S V dec dV E t w'))
      (fgauto_delta S V dec dV E (r .fst) w') (inr. q)
      (refl ((o ↦ fgauto_bind V o (t ↦ fgauto_delta S V dec dV E t w')) : Sum Unit V → Sum Unit V)
        (fgauto_lookup_det S V dec dV E hd p x (r .fst) (r .snd .fst)))
      (fgauto_delta_det S V dec dV E hd (r .fst) w' q (r .snd .snd)) ]

{` Deciding determinism: either two steps with the same source and letter
   and distinct targets (a conflict, to be folded), or determinism. `}
def FgautoConflict (S V : Type) (E : List (FgautoEdge S V)) : Type ≔ sig (
  csrc : V,
  clab : SignedLetter S,
  ctgt1 : V,
  ctgt2 : V,
  cstep1 : FgautoStep S V E csrc clab ctgt1,
  cstep2 : FgautoStep S V E csrc clab ctgt2,
  cdistinct : Not (Id V ctgt1 ctgt2))

def FgautoNoPartner (S V : Type) (L : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) : Type
  ≔ (p' : V) (x' : SignedLetter S) (q' : V) → Id V p' p → Id (SignedLetter S) x' x → FgautoStep S V L p' x' q'
    → Id V q q'

def FgautoPartner (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) : Type
  ≔ Σ V (q' ↦ Product (FgautoStep S V E p x q') (Not (Id V q q')))

def fgauto_partner_skip (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (e : FgautoEdge S V) (L : List (FgautoEdge S V))
  (k : Sum (Not (Id V p (e .src))) (Sum (Not (Id (SignedLetter S) x (e .lab))) (Id V q (e .tgt))))
  (rest : Sum (FgautoPartner S V E p x q) (FgautoNoPartner S V L p x q))
  : Sum (FgautoPartner S V E p x q) (FgautoNoPartner S V (cons. e L) p x q)
  ≔ match rest [
  | inl. y ↦ inl. y
  | inr. f ↦ inr. (p' x' q' a b s ↦ match s [
    | inl. t ↦ match k [
      | inl. n1 ↦ match n1 (concat V p p' (e .src) (inverse V p' p a) (t .fst)) []
      | inr. (inl. n2) ↦ match n2 (concat (SignedLetter S) x x' (e .lab) (inverse (SignedLetter S) x' x b) (t .snd .fst)) []
      | inr. (inr. c) ↦ concat V q (e .tgt) q' c (inverse V q' (e .tgt) (t .snd .snd)) ]
    | inr. s' ↦ f p' x' q' a b s' ]) ]

def fgauto_partner_pick (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V)
  (e : FgautoEdge S V) (L : List (FgautoEdge S V)) (i : FgautoStepIncl S V (cons. e L) E)
  (d1 : Decidable (Id V p (e .src))) (d2 : Decidable (Id (SignedLetter S) x (e .lab)))
  (d3 : Decidable (Id V q (e .tgt)))
  (rest : Sum (FgautoPartner S V E p x q) (FgautoNoPartner S V L p x q))
  : Sum (FgautoPartner S V E p x q) (FgautoNoPartner S V (cons. e L) p x q)
  ≔ match d1 [
  | inr. n1 ↦ fgauto_partner_skip S V E p x q e L (inl. n1) rest
  | inl. a ↦ match d2 [
    | inr. n2 ↦ fgauto_partner_skip S V E p x q e L (inr. (inl. n2)) rest
    | inl. b ↦ match d3 [
      | inl. c ↦ fgauto_partner_skip S V E p x q e L (inr. (inr. c)) rest
      | inr. nc ↦ inl. (e .tgt, (i p x (e .tgt) (inl. (a, (b, refl (e .tgt)))), nc)) ] ] ]

def fgauto_partner_search (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) (L : List (FgautoEdge S V))
  (i : FgautoStepIncl S V L E) : Sum (FgautoPartner S V E p x q) (FgautoNoPartner S V L p x q)
  ≔ match L [
  | nil. ↦ inr. (p' x' q' a b s ↦ match s [])
  | cons. e L' ↦ fgauto_partner_pick S V E p x q e L' i (dV p (e .src))
      (signed_letter_decidable_equality S dec x (e .lab)) (dV q (e .tgt))
      (fgauto_partner_search S V dec dV E p x q L' (p0 x0 q0 s ↦ i p0 x0 q0 (inr. s))) ]

def FgautoDetRel (S V : Type) (L E : List (FgautoEdge S V)) : Type
  ≔ (p : V) (x : SignedLetter S) (q q' : V) → FgautoStep S V L p x q → FgautoStep S V E p x q' → Id V q q'

def fgauto_conflict_pick (S V : Type) (E : List (FgautoEdge S V)) (e : FgautoEdge S V) (L : List (FgautoEdge S V))
  (i : FgautoStepIncl S V (cons. e L) E)
  (ps : Sum (FgautoPartner S V E (e .src) (e .lab) (e .tgt)) (FgautoNoPartner S V E (e .src) (e .lab) (e .tgt)))
  (rest : Sum (FgautoConflict S V E) (FgautoDetRel S V L E))
  : Sum (FgautoConflict S V E) (FgautoDetRel S V (cons. e L) E)
  ≔ match ps [
  | inl. y ↦ inl. (e .src, e .lab, e .tgt, y .fst, i (e .src) (e .lab) (e .tgt) (fgauto_step_head S V e L),
      y .snd .fst, y .snd .snd)
  | inr. f ↦ match rest [
    | inl. c ↦ inl. c
    | inr. g ↦ inr. (p x q q' s s' ↦ match s [
      | inl. t ↦ concat V q (e .tgt) q' (t .snd .snd) (f p x q' (t .fst) (t .snd .fst) s')
      | inr. s0 ↦ g p x q q' s0 s' ]) ] ]

def fgauto_conflict_search_in (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) (L : List (FgautoEdge S V)) (i : FgautoStepIncl S V L E)
  : Sum (FgautoConflict S V E) (FgautoDetRel S V L E)
  ≔ match L [
  | nil. ↦ inr. (p x q q' s s' ↦ match s [])
  | cons. e L' ↦ fgauto_conflict_pick S V E e L' i
      (fgauto_partner_search S V dec dV E (e .src) (e .lab) (e .tgt) E (p0 x0 q0 s ↦ s))
      (fgauto_conflict_search_in S V dec dV E L' (p0 x0 q0 s ↦ i p0 x0 q0 (inr. s))) ]

{` Determinism is decidable (with a conflict as the negative witness). `}
def fgauto_conflict_search (S V : Type) (dec : DecidableEquality S) (dV : DecidableEquality V)
  (E : List (FgautoEdge S V)) : Sum (FgautoConflict S V E) (FgautoDeterministic S V E)
  ≔ fgauto_conflict_search_in S V dec dV E E (p0 x0 q0 s ↦ s)

def fgauto_conflict_not_deterministic (S V : Type) (E : List (FgautoEdge S V)) (c : FgautoConflict S V E)
  (hd : FgautoDeterministic S V E) : Empty
  ≔ c .cdistinct (hd (c .csrc) (c .clab) (c .ctgt1) (c .ctgt2) (c .cstep1) (c .cstep2))
