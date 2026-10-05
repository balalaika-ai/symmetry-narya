export "1177-fgauto-word-expressions"
export "1156-fgauto-cosets-automata"

{` Chapter 11, automata part 29: the theorem of Benois (fggroups.tex:874),
   direction "X rational => iota(X) regular".

   For a rational expression r over F(S), the expression fgauto_lift_expr r
   over S~* has only atoms of length <= 1, so its Thompson automaton has
   edges labelled by single letters or by the empty word; reading those as
   letter edges and empty edges gives an automaton with empty transitions
   (fgauto_short_enfa) accepting exactly the words of the subset of
   fgauto_lift_expr r.  Removing the empty transitions (module 1176) and
   reducing (rho maps regular languages to regular languages, module 1175)
   shows that iota(X) = {rho(w) | w in lift(r)} is regular. `}

def FgautoShortWord (S : Type) (w : SignedWord S) : Type
  ≔ match w [ nil. ↦ Unit | cons. x t ↦ match t [ nil. ↦ Unit | cons. _ _ ↦ Empty ] ]

def FgautoShortExpr (S : Type) (r : FgautoRatExpr (SignedWord S)) : Type
  ≔ match r [
  | rat_fin. l ↦ FgautoAllIn (SignedWord S) (FgautoShortWord S) l
  | rat_union. r1 r2 ↦ Product (FgautoShortExpr S r1) (FgautoShortExpr S r2)
  | rat_prod. r1 r2 ↦ Product (FgautoShortExpr S r1) (FgautoShortExpr S r2)
  | rat_star. r1 ↦ FgautoShortExpr S r1 ]

def fgauto_word_expr_short (S : Type) (w : SignedWord S) : FgautoShortExpr S (fgauto_word_expr S w)
  ≔ match w [ nil. ↦ star. | cons. x t ↦ ((star., star.), fgauto_word_expr_short S t) ]

def fgauto_words_expr_short (S : Type) (l : List (SignedWord S)) : FgautoShortExpr S (fgauto_words_expr S l)
  ≔ match l [ nil. ↦ star. | cons. g t ↦ (fgauto_word_expr_short S g, fgauto_words_expr_short S t) ]

def fgauto_lift_expr_short (S : Type) (r : FgautoRatExpr (ReducedWord S)) : FgautoShortExpr S (fgauto_lift_expr S r)
  ≔ match r [
  | rat_fin. l ↦ fgauto_words_expr_short S (fgauto_list_map (ReducedWord S) (SignedWord S) (g ↦ g .fst) l)
  | rat_union. r1 r2 ↦ (fgauto_lift_expr_short S r1, fgauto_lift_expr_short S r2)
  | rat_prod. r1 r2 ↦ (fgauto_lift_expr_short S r1, fgauto_lift_expr_short S r2)
  | rat_star. r1 ↦ fgauto_lift_expr_short S r1 ]

{` Labels of Thompson automata of short expressions. `}
def FgautoShortLabel (S : Type) (y : SignedLetter (SignedWord S)) : Type
  ≔ Σ (SignedWord S) (w ↦ Product (Id (SignedLetter (SignedWord S)) y (inl. w)) (FgautoShortWord S w))

def FgautoShortLabels (S : Type) (E : List (FgautoEdge (SignedWord S) (List Nat))) : Type
  ≔ (p : List Nat) (y : SignedLetter (SignedWord S)) (q : List Nat) → FgautoStep (SignedWord S) (List Nat) E p y q → FgautoShortLabel S y

def fgauto_eps_short (S : Type) : FgautoShortLabel S (fgauto_teps (fgauto_free_monoid S))
  ≔ (nil., (refl (fgauto_teps (fgauto_free_monoid S)), star.))

def fgauto_short_append (S : Type) (E E' : List (FgautoEdge (SignedWord S) (List Nat))) (h : FgautoShortLabels S E)
  (h' : FgautoShortLabels S E') : FgautoShortLabels S (append (FgautoEdge (SignedWord S) (List Nat)) E E')
  ≔ p y q s ↦ match fgauto_step_append_split (SignedWord S) (List Nat) E E' p y q s [ inl. k ↦ h p y q k | inr. k ↦ h' p y q k ]

def fgauto_short_tpre (S : Type) (k : Nat) (E : List (FgautoEdge (SignedWord S) (List Nat))) (h : FgautoShortLabels S E)
  : FgautoShortLabels S (fgauto_tpre (fgauto_free_monoid S) k E)
  ≔ p y q s ↦
    let z ≔ fgauto_step_map_preimage (SignedWord S) (List Nat) (List Nat) (v ↦ cons. k v) E p y q s in
    h (z .fst) y (z .snd .fst) (z .snd .snd .fst)

def fgauto_short_eps_list (S : Type) (E : List (FgautoEdge (SignedWord S) (List Nat)))
  (h : FgautoAllIn (FgautoEdge (SignedWord S) (List Nat)) (e ↦ Id (SignedLetter (SignedWord S)) (e .lab) (fgauto_teps (fgauto_free_monoid S))) E)
  : FgautoShortLabels S E
  ≔ p y q s ↦ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ (nil., (concat (SignedLetter (SignedWord S)) y (e .lab) (inl. nil.) (t .snd .fst) (h .fst), star.))
    | inr. s' ↦ fgauto_short_eps_list S E' (h .snd) p y q s' ] ]

def fgauto_allin_mem (A : Type) (P : A → Type) (l : List A) (a : A) (h : FgautoAllIn A P l) (m : FgautoMem A a l) : P a
  ≔ match l [
  | nil. ↦ match m []
  | cons. b t ↦ match m [ inl. e ↦ transport A P b a (inverse A a b e) (h .fst) | inr. m' ↦ fgauto_allin_mem A P t a (h .snd) m' ] ]

def fgauto_thompson_short (S : Type) (r : FgautoRatExpr (SignedWord S)) (hr : FgautoShortExpr S r)
  : FgautoShortLabels S (fgauto_thompson (fgauto_free_monoid S) r .tedges)
  ≔ let M ≔ fgauto_free_monoid S in
    let ep ≔ refl (fgauto_teps M) in
    match r [
    | rat_fin. l ↦ p y q s ↦
      let z ≔ fgauto_tfin_step M l p y q s in
      (z .fst, (z .snd .snd .snd .fst, fgauto_allin_mem (SignedWord S) (FgautoShortWord S) l (z .fst) hr (z .snd .fst)))
    | rat_union. r1 r2 ↦
      let A ≔ fgauto_thompson M r1 in
      let B ≔ fgauto_thompson M r2 in
      fgauto_short_append S (fgauto_tpre M zero. (A .tedges)) (append (FgautoEdge (SignedWord S) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) (fgauto_union_glue M A B))
        (fgauto_short_tpre S zero. (A .tedges) (fgauto_thompson_short S r1 (hr .fst)))
        (fgauto_short_append S (fgauto_tpre M fgauto_n1 (B .tedges)) (fgauto_union_glue M A B)
          (fgauto_short_tpre S fgauto_n1 (B .tedges) (fgauto_thompson_short S r2 (hr .snd)))
          (fgauto_short_eps_list S (fgauto_union_glue M A B) (ep, (ep, (ep, (ep, star.))))))
    | rat_prod. r1 r2 ↦
      let A ≔ fgauto_thompson M r1 in
      let B ≔ fgauto_thompson M r2 in
      fgauto_short_append S (fgauto_tpre M zero. (A .tedges)) (append (FgautoEdge (SignedWord S) (List Nat)) (fgauto_tpre M fgauto_n1 (B .tedges)) (fgauto_prod_glue M A B))
        (fgauto_short_tpre S zero. (A .tedges) (fgauto_thompson_short S r1 (hr .fst)))
        (fgauto_short_append S (fgauto_tpre M fgauto_n1 (B .tedges)) (fgauto_prod_glue M A B)
          (fgauto_short_tpre S fgauto_n1 (B .tedges) (fgauto_thompson_short S r2 (hr .snd)))
          (fgauto_short_eps_list S (fgauto_prod_glue M A B) (ep, star.)))
    | rat_star. r1 ↦
      let A ≔ fgauto_thompson M r1 in
      fgauto_short_append S (fgauto_tpre M zero. (A .tedges)) (fgauto_star_glue M A)
        (fgauto_short_tpre S zero. (A .tedges) (fgauto_thompson_short S r1 hr))
        (fgauto_short_eps_list S (fgauto_star_glue M A) (ep, (ep, star.))) ]

{` The automaton with empty transitions. `}
def fgauto_letter_pick (S : Type) (src tgt : List Nat) (y : SignedLetter (SignedWord S)) : List (FgautoEdge S (List Nat))
  ≔ match y [
  | inl. w ↦ match w [ nil. ↦ nil. | cons. x t ↦ match t [ nil. ↦ cons. (src, x, tgt) nil. | cons. _ _ ↦ nil. ] ]
  | inr. _ ↦ nil. ]

def fgauto_eps_pick (S : Type) (src tgt : List Nat) (y : SignedLetter (SignedWord S)) : List (FgautoEdge Unit (List Nat))
  ≔ match y [
  | inl. w ↦ match w [ nil. ↦ cons. (src, inl. star., tgt) nil. | cons. _ _ ↦ nil. ]
  | inr. _ ↦ nil. ]

def fgauto_short_enfa (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) : FgautoENFA S
  ≔ (List Nat, fgauto_tstate_dec,
     fgauto_list_bind (FgautoEdge (SignedWord S) (List Nat)) (FgautoEdge S (List Nat)) (T .tedges) (e ↦ fgauto_letter_pick S (e .src) (e .tgt) (e .lab)),
     fgauto_list_bind (FgautoEdge (SignedWord S) (List Nat)) (FgautoEdge Unit (List Nat)) (T .tedges) (e ↦ fgauto_eps_pick S (e .src) (e .tgt) (e .lab)),
     T .tstart, cons. (T .tend) nil.)

def fgauto_letter_pick_step (S : Type) (src tgt : List Nat) (y : SignedLetter (SignedWord S)) (p : List Nat) (x : SignedLetter S) (q : List Nat)
  (s : FgautoStep S (List Nat) (fgauto_letter_pick S src tgt y) p x q)
  : Product (Id (List Nat) p src) (Product (Id (List Nat) q tgt) (Id (SignedLetter (SignedWord S)) y (inl. (cons. x nil.))))
  ≔ match y [
  | inr. _ ↦ match s []
  | inl. w ↦ match w [
    | nil. ↦ match s []
    | cons. z t ↦ match t [
      | cons. _ _ ↦ match s []
      | nil. ↦ match s [
        | inl. e ↦ (e .fst, (e .snd .snd, inl. (cons. (inverse (SignedLetter S) x z (e .snd .fst)) (refl (nil. : SignedWord S)))))
        | inr. s' ↦ match s' [] ] ] ] ]

def fgauto_eps_pick_step (S : Type) (src tgt : List Nat) (y : SignedLetter (SignedWord S)) (p : List Nat) (u : SignedLetter Unit) (q : List Nat)
  (s : FgautoStep Unit (List Nat) (fgauto_eps_pick S src tgt y) p u q)
  : Product (Id (List Nat) p src) (Product (Id (List Nat) q tgt) (Id (SignedLetter (SignedWord S)) y (inl. nil.)))
  ≔ match y [
  | inr. _ ↦ match s []
  | inl. w ↦ match w [
    | cons. _ _ ↦ match s []
    | nil. ↦ match s [ inl. e ↦ (e .fst, (e .snd .snd, refl (inl. nil. : SignedLetter (SignedWord S)))) | inr. s' ↦ match s' [] ] ] ]

def fgauto_short_letter_step_elim (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p : List Nat) (x : SignedLetter S) (q : List Nat)
  (s : FgautoStep S (List Nat) (fgauto_short_enfa S T .eletters) p x q)
  : FgautoStep (SignedWord S) (List Nat) (T .tedges) p (inl. (cons. x nil.)) q
  ≔ let Ed ≔ FgautoEdge (SignedWord S) (List Nat) in
    let z ≔ fgauto_bind_step S (List Nat) Ed (T .tedges) (e ↦ fgauto_letter_pick S (e .src) (e .tgt) (e .lab)) p x q s in
    let e ≔ z .fst in
    let c ≔ fgauto_letter_pick_step S (e .src) (e .tgt) (e .lab) p x q (z .snd .snd) in
    fgauto_step_transport (SignedWord S) (List Nat) (T .tedges) (e .src) p (e .lab) (inl. (cons. x nil.)) (e .tgt) q
      (inverse (List Nat) p (e .src) (c .fst)) (c .snd .snd) (inverse (List Nat) q (e .tgt) (c .snd .fst))
      (fgauto_mem_edge_step (SignedWord S) (List Nat) (T .tedges) e (z .snd .fst))

def fgauto_short_eps_step_elim (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p : List Nat) (u : SignedLetter Unit) (q : List Nat)
  (s : FgautoStep Unit (List Nat) (fgauto_short_enfa S T .eeps) p u q)
  : FgautoStep (SignedWord S) (List Nat) (T .tedges) p (inl. nil.) q
  ≔ let Ed ≔ FgautoEdge (SignedWord S) (List Nat) in
    let z ≔ fgauto_bind_step Unit (List Nat) Ed (T .tedges) (e ↦ fgauto_eps_pick S (e .src) (e .tgt) (e .lab)) p u q s in
    let e ≔ z .fst in
    let c ≔ fgauto_eps_pick_step S (e .src) (e .tgt) (e .lab) p u q (z .snd .snd) in
    fgauto_step_transport (SignedWord S) (List Nat) (T .tedges) (e .src) p (e .lab) (inl. nil.) (e .tgt) q
      (inverse (List Nat) p (e .src) (c .fst)) (c .snd .snd) (inverse (List Nat) q (e .tgt) (c .snd .fst))
      (fgauto_mem_edge_step (SignedWord S) (List Nat) (T .tedges) e (z .snd .fst))

def fgauto_short_letter_step_intro (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p : List Nat) (x : SignedLetter S) (q : List Nat)
  (s : FgautoStep (SignedWord S) (List Nat) (T .tedges) p (inl. (cons. x nil.)) q)
  : FgautoStep S (List Nat) (fgauto_short_enfa S T .eletters) p x q
  ≔ let Ed ≔ FgautoEdge (SignedWord S) (List Nat) in
    let z ≔ fgauto_step_mem_edge (SignedWord S) (List Nat) (T .tedges) p (inl. (cons. x nil.)) q s in
    let e ≔ z .fst in
    fgauto_step_transport S (List Nat) (fgauto_short_enfa S T .eletters) (e .src) p x x (e .tgt) q
      (inverse (List Nat) p (e .src) (z .snd .snd .fst)) (refl x) (inverse (List Nat) q (e .tgt) (z .snd .snd .snd .snd))
      (fgauto_mem_edge_step S (List Nat) (fgauto_short_enfa S T .eletters) (e .src, x, e .tgt)
        (fgauto_mem_bind Ed (FgautoEdge S (List Nat)) (T .tedges) (e0 ↦ fgauto_letter_pick S (e0 .src) (e0 .tgt) (e0 .lab)) e (e .src, x, e .tgt)
          (z .snd .fst)
          (transport (SignedLetter (SignedWord S)) (y ↦ FgautoMem (FgautoEdge S (List Nat)) (e .src, x, e .tgt) (fgauto_letter_pick S (e .src) (e .tgt) y))
            (inl. (cons. x nil.)) (e .lab) (z .snd .snd .snd .fst) (inl. (refl ((e .src, x, e .tgt) : FgautoEdge S (List Nat)))))))

def fgauto_short_eps_step_intro (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p q : List Nat)
  (s : FgautoStep (SignedWord S) (List Nat) (T .tedges) p (inl. nil.) q)
  : FgautoStep Unit (List Nat) (fgauto_short_enfa S T .eeps) p (inl. star.) q
  ≔ let Ed ≔ FgautoEdge (SignedWord S) (List Nat) in
    let z ≔ fgauto_step_mem_edge (SignedWord S) (List Nat) (T .tedges) p (inl. nil.) q s in
    let e ≔ z .fst in
    fgauto_step_transport Unit (List Nat) (fgauto_short_enfa S T .eeps) (e .src) p (inl. star.) (inl. star.) (e .tgt) q
      (inverse (List Nat) p (e .src) (z .snd .snd .fst)) (refl (inl. star. : SignedLetter Unit)) (inverse (List Nat) q (e .tgt) (z .snd .snd .snd .snd))
      (fgauto_mem_edge_step Unit (List Nat) (fgauto_short_enfa S T .eeps) (e .src, inl. star., e .tgt)
        (fgauto_mem_bind Ed (FgautoEdge Unit (List Nat)) (T .tedges) (e0 ↦ fgauto_eps_pick S (e0 .src) (e0 .tgt) (e0 .lab)) e (e .src, inl. star., e .tgt)
          (z .snd .fst)
          (transport (SignedLetter (SignedWord S)) (y ↦ FgautoMem (FgautoEdge Unit (List Nat)) (e .src, inl. star., e .tgt) (fgauto_eps_pick S (e .src) (e .tgt) y))
            (inl. nil.) (e .lab) (z .snd .snd .snd .fst) (inl. (refl ((e .src, inl. star., e .tgt) : FgautoEdge Unit (List Nat)))))))

{` Runs: Thompson runs <-> runs with empty transitions. `}
def fgauto_eprepend (S : Type) (A : FgautoENFA S) (p r : A .estate) (u : SignedLetter Unit) (s : FgautoStep Unit (A .estate) (A .eeps) p u r)
  (w : SignedWord S) (q : A .estate) (h : FgautoERun S A r w q) : FgautoERun S A p w q
  ≔ match w [
  | nil. ↦ (cons. u (h .fst), (r, (s, h .snd)))
  | cons. x w' ↦ (h .fst, ((cons. u (h .snd .fst .fst), (r, (s, h .snd .fst .snd))), h .snd .snd)) ]

def fgauto_short_to_erun_case (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p r q : List Nat) (w : SignedWord S)
  (hw : FgautoShortWord S w) (rest : SignedWord S) (st : FgautoStep (SignedWord S) (List Nat) (T .tedges) p (inl. w) r)
  (ih : FgautoERun S (fgauto_short_enfa S T) r rest q) (y : SignedLetter (SignedWord S)) (ey : Id (SignedLetter (SignedWord S)) y (inl. w))
  : FgautoERun S (fgauto_short_enfa S T) p (append (SignedLetter S) (fgauto_label_eval (fgauto_free_monoid S) y) rest) q
  ≔ let A ≔ fgauto_short_enfa S T in
    transport (SignedLetter (SignedWord S)) (z ↦ FgautoERun S A p (append (SignedLetter S) (fgauto_label_eval (fgauto_free_monoid S) z) rest) q)
      (inl. w) y (inverse (SignedLetter (SignedWord S)) y (inl. w) ey)
      (match w [
       | nil. ↦ fgauto_eprepend S A p r (inl. star.) (fgauto_short_eps_step_intro S T p r st) rest q ih
       | cons. x t ↦ match t [
         | cons. _ _ ↦ match hw []
         | nil. ↦ (p, ((nil., refl p), (r, (fgauto_short_letter_step_intro S T p x r st, ih)))) ] ])

def fgauto_thompson_to_erun (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (hs : FgautoShortLabels S (T .tedges))
  (p : List Nat) (W : SignedWord (SignedWord S)) (q : List Nat) (r : FgautoRun (SignedWord S) (List Nat) (T .tedges) p W q)
  : FgautoERun S (fgauto_short_enfa S T) p (fgauto_path_eval (fgauto_free_monoid S) W) q
  ≔ let A ≔ fgauto_short_enfa S T in
    match W [
    | nil. ↦ (nil., r)
    | cons. y W' ↦
      let sh ≔ hs p y (r .fst) (r .snd .fst) in
      let st ≔ fgauto_step_transport (SignedWord S) (List Nat) (T .tedges) p p y (inl. (sh .fst)) (r .fst) (r .fst) (refl p) (sh .snd .fst) (refl (r .fst)) (r .snd .fst) in
      let ih ≔ fgauto_thompson_to_erun S T hs (r .fst) W' q (r .snd .snd) in
      fgauto_short_to_erun_case S T p (r .fst) q (sh .fst) (sh .snd .snd) (fgauto_path_eval (fgauto_free_monoid S) W') st ih y (sh .snd .fst) ]

def fgauto_ereach_to_thompson (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p : List Nat) (e : SignedWord Unit) (q : List Nat)
  (r : FgautoRun Unit (List Nat) (fgauto_short_enfa S T .eeps) p e q)
  : Σ (SignedWord (SignedWord S)) (W ↦ Product (FgautoRun (SignedWord S) (List Nat) (T .tedges) p W q)
      (Id (SignedWord S) (fgauto_path_eval (fgauto_free_monoid S) W) nil.))
  ≔ match e [
  | nil. ↦ (nil., (r, refl (nil. : SignedWord S)))
  | cons. u e' ↦
    let ih ≔ fgauto_ereach_to_thompson S T (r .fst) e' q (r .snd .snd) in
    (cons. (inl. nil.) (ih .fst), ((r .fst, (fgauto_short_eps_step_elim S T p u (r .fst) (r .snd .fst), ih .snd .fst)), ih .snd .snd)) ]

def fgauto_erun_to_thompson (S : Type) (T : FgautoThompsonAut (fgauto_free_monoid S)) (p : List Nat) (w : SignedWord S) (q : List Nat)
  (r : FgautoERun S (fgauto_short_enfa S T) p w q)
  : Σ (SignedWord (SignedWord S)) (W ↦ Product (FgautoRun (SignedWord S) (List Nat) (T .tedges) p W q)
      (Id (SignedWord S) (fgauto_path_eval (fgauto_free_monoid S) W) w))
  ≔ let M ≔ fgauto_free_monoid S in
    let L ≔ SignedLetter (SignedWord S) in
    match w [
    | nil. ↦ fgauto_ereach_to_thompson S T p (r .fst) q (r .snd)
    | cons. x w' ↦
      let a ≔ fgauto_ereach_to_thompson S T p (r .snd .fst .fst) (r .fst) (r .snd .fst .snd) in
      let r1 ≔ r .snd .snd .fst in
      let b ≔ fgauto_erun_to_thompson S T r1 w' q (r .snd .snd .snd .snd) in
      let W2 : SignedWord (SignedWord S) ≔ cons. (inl. (cons. x nil.)) (b .fst) in
      (append L (a .fst) W2,
       (fgauto_run_append (SignedWord S) (List Nat) (T .tedges) p (a .fst) (r .fst) W2 q (a .snd .fst)
          (r1, (fgauto_short_letter_step_elim S T (r .fst) x r1 (r .snd .snd .snd .fst), b .snd .fst)),
        concat (SignedWord S) (fgauto_path_eval M (append L (a .fst) W2))
          (append (SignedLetter S) (fgauto_path_eval M (a .fst)) (fgauto_path_eval M W2)) (cons. x w')
          (fgauto_path_eval_append M (fgauto_free_monoid_laws S) (a .fst) W2)
          (refl ((u v ↦ append (SignedLetter S) u (cons. x v)) : SignedWord S → SignedWord S → SignedWord S) (a .snd .snd) (b .snd .snd)))) ]

{` The words of a short expression form a regular language. `}
def fgauto_short_expr_enfa (S : Type) (r : FgautoRatExpr (SignedWord S)) (hr : FgautoShortExpr S r) (w : SignedWord S)
  : FgautoIff (fgauto_rat_mem (fgauto_free_monoid S) r w) (FgautoEAccepts S (fgauto_short_enfa S (fgauto_thompson (fgauto_free_monoid S) r)) w)
  ≔ let M ≔ fgauto_free_monoid S in
    let T ≔ fgauto_thompson M r in
    let A ≔ fgauto_short_enfa S T in
    let hs ≔ fgauto_thompson_short S r hr in
    let TL ≔ Σ (SignedWord (SignedWord S)) (W ↦ Product (FgautoRun (SignedWord S) (List Nat) (T .tedges) (T .tstart) W (T .tend))
       (Id (SignedWord S) (fgauto_path_eval M W) w)) in
    let TE ≔ Σ (List Nat) (f ↦ Product (FgautoMem (List Nat) f (A .efinal)) (FgautoERun S A (A .einit) w f)) in
    (h ↦ mere_rec TL (FgautoEAccepts S A w) (mere_isprop TE)
       (z ↦ mere TE (T .tend, (inl. (refl (T .tend)),
         transport (SignedWord S) (u ↦ FgautoERun S A (T .tstart) u (T .tend)) (fgauto_path_eval M (z .fst)) w (z .snd .snd)
           (fgauto_thompson_to_erun S T hs (T .tstart) (z .fst) (T .tend) (z .snd .fst)))))
       (fgauto_thompson_correct M (fgauto_free_monoid_laws S) r w .fst h),
     h ↦ fgauto_thompson_correct M (fgauto_free_monoid_laws S) r w .snd
       (mere_rec TE (Mere TL) (mere_isprop TL)
         (z ↦ match z .snd .fst [
           | inr. k ↦ match k []
           | inl. ef ↦ mere TL (fgauto_erun_to_thompson S T (T .tstart) w (T .tend)
               (transport (List Nat) (f ↦ FgautoERun S A (A .einit) w f) (z .fst) (T .tend) ef (z .snd .snd))) ]) h))

{` fggroups.tex:874, "=>". `}
def fgauto_iota_image_prop (S : Type) (dec : DecidableEquality S) (X : FgautoFreeSubset S) (u : SignedWord S)
  : isProp (FgautoIotaImage S (m ↦ X m .fst) u)
  ≔ sigma_prop (IsReducedWord S u) (h ↦ X (u, h) .fst) (is_reduced_word_prop S u) (h ↦ X (u, h) .snd)

def fgauto_benois_rational_regular (S : Type) (dec : DecidableEquality S) (X : FgautoFreeSubset S)
  (hX : FgautoRational (fgauto_free_group_monoid S dec) (m ↦ X m .fst)) : FgautoRegular S (FgautoIotaImage S (m ↦ X m .fst))
  ≔ let MF ≔ fgauto_free_group_monoid S dec in
    let Mw ≔ fgauto_free_monoid S in
    let RW ≔ ReducedWord S in
    let W ≔ SignedWord S in
    mere_rec (Σ (FgautoRatExpr RW) (r ↦ (m : RW) → FgautoIff (X m .fst) (fgauto_rat_mem MF r m)))
      (FgautoRegular S (FgautoIotaImage S (m ↦ X m .fst)))
      (mere_isprop (Σ (FgautoNFA S) (B ↦ (w : W) → FgautoIff (FgautoIotaImage S (m ↦ X m .fst) w) (FgautoNFAAccepts S B w))))
      (z ↦
        let r ≔ z .fst in
        let A ≔ fgauto_short_enfa S (fgauto_thompson Mw (fgauto_lift_expr S r)) in
        let L0 ≔ FgautoEAccepts S A in
        let eq ≔ fgauto_short_expr_enfa S (fgauto_lift_expr S r) (fgauto_lift_expr_short S r) in
        let reg ≔ fgauto_reduction_regular S dec L0 (fgauto_enfa_regular S A) in
        let T1 ≔ (u : W) ↦ Σ W (v ↦ Product (L0 v) (Id W (word_reduction S dec v) u)) in
        let iota_prop ≔ (u : W) ↦ fgauto_iota_image_prop S dec X u in
        mere_rec (Σ (FgautoNFA S) (B ↦ (w : W) → FgautoIff (FgautoReductionImage S dec L0 w) (FgautoNFAAccepts S B w)))
          (FgautoRegular S (FgautoIotaImage S (m ↦ X m .fst)))
          (mere_isprop (Σ (FgautoNFA S) (B ↦ (w : W) → FgautoIff (FgautoIotaImage S (m ↦ X m .fst) w) (FgautoNFAAccepts S B w))))
          (y ↦ mere (Σ (FgautoNFA S) (B ↦ (w : W) → FgautoIff (FgautoIotaImage S (m ↦ X m .fst) w) (FgautoNFAAccepts S B w)))
            (y .fst, u ↦
              (iu ↦ y .snd u .fst
                 (mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r) w) (Id W (word_reduction S dec w) u)))
                   (Mere (T1 u)) (mere_isprop (T1 u))
                   (zz ↦ mere (T1 u) (zz .fst, (eq (zz .fst) .fst (zz .snd .fst), zz .snd .snd)))
                   (fgauto_lift_expr_correct S dec r (u, iu .fst) .fst (z .snd (u, iu .fst) .fst (iu .snd)))),
               ab ↦ mere_rec (T1 u) (FgautoIotaImage S (m ↦ X m .fst) u) (iota_prop u)
                 (zz ↦
                   let v ≔ zz .fst in
                   let hr ≔ transport W (IsReducedWord S) (word_reduction S dec v) u (zz .snd .snd) (word_reduction_reduced S dec v) in
                   (hr, z .snd (u, hr) .snd (fgauto_lift_expr_correct S dec r (u, hr) .snd
                     (mere (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r) w) (Id W (word_reduction S dec w) u)))
                       (v, (eq v .snd (zz .snd .fst), zz .snd .snd))))))
                 (y .snd u .snd ab))))
          reg) hX
