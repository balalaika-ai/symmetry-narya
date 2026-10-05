export "1175-fgauto-reduction-regular"

{` Chapter 11, automata part 27: automata with empty transitions and their
   removal (used for the theorem of Benois, fggroups.tex:874).

   An epsilon-automaton has letter edges and empty edges (edges over the
   one-letter alphabet Unit whose letters are ignored); a run reads a word
   letter by letter, with arbitrarily many empty edges before each letter
   and at the end.  The usual construction (edge p -x-> r whenever some
   state reachable from p by empty edges has an x-edge to r; p final when a
   final state is reachable from p by empty edges) gives an ordinary
   automaton with the same language (fgauto_enfa_regular). `}

def FgautoENFA (S : Type) : Type ≔ sig (
  estate : Type,
  edec : DecidableEquality estate,
  eletters : List (FgautoEdge S estate),
  eeps : List (FgautoEdge Unit estate),
  einit : estate,
  efinal : List estate)

def FgautoEReach (S : Type) (A : FgautoENFA S) (p q : A .estate) : Type
  ≔ Σ (SignedWord Unit) (e ↦ FgautoRun Unit (A .estate) (A .eeps) p e q)

def FgautoERun (S : Type) (A : FgautoENFA S) (p : A .estate) (w : SignedWord S) (q : A .estate) : Type
  ≔ match w [
  | nil. ↦ FgautoEReach S A p q
  | cons. x w' ↦ Σ (A .estate) (p' ↦ Product (FgautoEReach S A p p')
      (Σ (A .estate) (r ↦ Product (FgautoStep S (A .estate) (A .eletters) p' x r) (FgautoERun S A r w' q)))) ]

def FgautoEAccepts (S : Type) (A : FgautoENFA S) (w : SignedWord S) : Type
  ≔ Mere (Σ (A .estate) (f ↦ Product (FgautoMem (A .estate) f (A .efinal)) (FgautoERun S A (A .einit) w f)))

{` Empty closures by breadth-first search. `}
def fgauto_eclosure (S : Type) (A : FgautoENFA S) (p : A .estate) : List (A .estate)
  ≔ fgauto_reached Unit (A .estate) (A .edec) (A .eeps) p

def fgauto_eclosure_complete (S : Type) (A : FgautoENFA S) (p q : A .estate) (h : FgautoEReach S A p q)
  : FgautoMem (A .estate) q (fgauto_eclosure S A p)
  ≔ fgauto_reach_complete Unit (A .estate) (A .edec) (A .eeps) p (h .fst) q (h .snd)

def fgauto_eclosure_sound (S : Type) (A : FgautoENFA S) (p q : A .estate) (m : FgautoMem (A .estate) q (fgauto_eclosure S A p))
  : FgautoEReach S A p q
  ≔ (fgauto_tree_word Unit (A .estate) (A .edec) (A .eeps) p q, fgauto_tree_word_run Unit (A .estate) (A .edec) (A .eeps) p q m)

{` Positional steps come from list members. `}
def fgauto_step_mem_edge (S V : Type) (E : List (FgautoEdge S V)) (p : V) (x : SignedLetter S) (q : V) (s : FgautoStep S V E p x q)
  : Σ (FgautoEdge S V) (e ↦ Product (FgautoMem (FgautoEdge S V) e E)
      (Product (Id V p (e .src)) (Product (Id (SignedLetter S) x (e .lab)) (Id V q (e .tgt)))))
  ≔ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ (e, (inl. (refl e), t))
    | inr. s' ↦ let z ≔ fgauto_step_mem_edge S V E' p x q s' in (z .fst, (inr. (z .snd .fst), z .snd .snd)) ] ]

def fgauto_list_exists_decide (A : Type) (P : A → Type) (dP : (a : A) → Decidable (P a)) (l : List A)
  : Decidable (Σ A (a ↦ Product (FgautoMem A a l) (P a)))
  ≔ match l [
  | nil. ↦ inr. (z ↦ match z .snd .fst [])
  | cons. b t ↦ match dP b [
    | inl. pb ↦ inl. (b, (inl. (refl b), pb))
    | inr. nb ↦ match fgauto_list_exists_decide A P dP t [
      | inl. z ↦ inl. (z .fst, (inr. (z .snd .fst), z .snd .snd))
      | inr. nz ↦ inr. (z ↦ match z .snd .fst [
          | inl. e ↦ nb (transport A P (z .fst) b e (z .snd .snd))
          | inr. m ↦ nz (z .fst, (m, z .snd .snd)) ]) ] ] ]

{` The states and the automaton without empty edges. `}
def fgauto_enfa_states (S : Type) (A : FgautoENFA S) : List (A .estate)
  ≔ cons. (A .einit) (append (A .estate) (A .efinal) (append (A .estate) (fgauto_endpoints S (A .estate) (A .eletters))
      (fgauto_endpoints Unit (A .estate) (A .eeps))))

def fgauto_enfa_pick (S : Type) (A : FgautoENFA S) (p : A .estate) (e : FgautoEdge S (A .estate))
  (d : Decidable (FgautoMem (A .estate) (e .src) (fgauto_eclosure S A p))) : List (FgautoEdge S (A .estate))
  ≔ match d [ inl. _ ↦ cons. (p, e .lab, e .tgt) nil. | inr. _ ↦ nil. ]

def fgauto_enfa_edges_at (S : Type) (A : FgautoENFA S) (p : A .estate) : List (FgautoEdge S (A .estate))
  ≔ fgauto_list_bind (FgautoEdge S (A .estate)) (FgautoEdge S (A .estate)) (A .eletters)
      (e ↦ fgauto_enfa_pick S A p e (fgauto_mem_decide (A .estate) (A .edec) (e .src) (fgauto_eclosure S A p)))

def fgauto_enfa_edges (S : Type) (A : FgautoENFA S) : List (FgautoEdge S (A .estate))
  ≔ fgauto_list_bind (A .estate) (FgautoEdge S (A .estate)) (fgauto_enfa_states S A) (fgauto_enfa_edges_at S A)

def FgautoEFinalAt (S : Type) (A : FgautoENFA S) (p : A .estate) : Type
  ≔ Σ (A .estate) (f ↦ Product (FgautoMem (A .estate) f (A .efinal)) (FgautoMem (A .estate) f (fgauto_eclosure S A p)))

def fgauto_efinal_bool (S : Type) (A : FgautoENFA S) (p : A .estate) : Bool
  ≔ fgauto_decision_bool (FgautoEFinalAt S A p)
      (fgauto_list_exists_decide (A .estate) (f ↦ FgautoMem (A .estate) f (fgauto_eclosure S A p))
        (f ↦ fgauto_mem_decide (A .estate) (A .edec) f (fgauto_eclosure S A p)) (A .efinal))

def fgauto_enfa_nfa (S : Type) (A : FgautoENFA S) : FgautoNFA S
  ≔ (A .estate, A .edec, fgauto_enfa_edges S A, A .einit,
     fgauto_list_filter (A .estate) (fgauto_efinal_bool S A) (fgauto_enfa_states S A))

{` Steps of the new automaton. `}
def fgauto_enfa_pick_step (S : Type) (A : FgautoENFA S) (p : A .estate) (e : FgautoEdge S (A .estate))
  (d : Decidable (FgautoMem (A .estate) (e .src) (fgauto_eclosure S A p))) (p0 : A .estate) (x : SignedLetter S) (q : A .estate)
  (s : FgautoStep S (A .estate) (fgauto_enfa_pick S A p e d) p0 x q)
  : Product (FgautoMem (A .estate) (e .src) (fgauto_eclosure S A p))
      (Product (Id (A .estate) p0 p) (Product (Id (SignedLetter S) x (e .lab)) (Id (A .estate) q (e .tgt))))
  ≔ match d [ inr. _ ↦ match s [] | inl. m ↦ match s [ inl. t ↦ (m, t) | inr. s' ↦ match s' [] ] ]

def fgauto_enfa_step_elim (S : Type) (A : FgautoENFA S) (p0 : A .estate) (x : SignedLetter S) (q : A .estate)
  (s : FgautoStep S (A .estate) (fgauto_enfa_edges S A) p0 x q)
  : Σ (A .estate) (p' ↦ Product (FgautoEReach S A p0 p') (FgautoStep S (A .estate) (A .eletters) p' x q))
  ≔ let V ≔ A .estate in
    let z1 ≔ fgauto_bind_step S V V (fgauto_enfa_states S A) (fgauto_enfa_edges_at S A) p0 x q s in
    let p ≔ z1 .fst in
    let z2 ≔ fgauto_bind_step S V (FgautoEdge S V) (A .eletters)
      (e ↦ fgauto_enfa_pick S A p e (fgauto_mem_decide V (A .edec) (e .src) (fgauto_eclosure S A p))) p0 x q (z1 .snd .snd) in
    let e ≔ z2 .fst in
    let c ≔ fgauto_enfa_pick_step S A p e (fgauto_mem_decide V (A .edec) (e .src) (fgauto_eclosure S A p)) p0 x q (z2 .snd .snd) in
    let r ≔ fgauto_eclosure_sound S A p (e .src) (c .fst) in
    (e .src,
     ((r .fst, fgauto_run_start Unit V (A .eeps) p p0 (r .fst) (e .src) (inverse V p0 p (c .snd .fst)) (r .snd)),
      fgauto_step_transport S V (A .eletters) (e .src) (e .src) (e .lab) x (e .tgt) q (refl (e .src))
        (inverse (SignedLetter S) x (e .lab) (c .snd .snd .fst)) (inverse V q (e .tgt) (c .snd .snd .snd))
        (fgauto_mem_edge_step S V (A .eletters) e (z2 .snd .fst))))

def fgauto_enfa_pick_mem (S : Type) (A : FgautoENFA S) (p : A .estate) (e : FgautoEdge S (A .estate))
  (me : FgautoMem (A .estate) (e .src) (fgauto_eclosure S A p)) (d : Decidable (FgautoMem (A .estate) (e .src) (fgauto_eclosure S A p)))
  : FgautoMem (FgautoEdge S (A .estate)) (p, e .lab, e .tgt) (fgauto_enfa_pick S A p e d)
  ≔ match d [ inl. _ ↦ inl. (refl ((p, e .lab, e .tgt) : FgautoEdge S (A .estate))) | inr. n ↦ match n me [] ]

def fgauto_enfa_step_intro (S : Type) (A : FgautoENFA S) (p : A .estate) (mp : FgautoMem (A .estate) p (fgauto_enfa_states S A))
  (p' : A .estate) (h : FgautoEReach S A p p') (x : SignedLetter S) (q : A .estate)
  (s : FgautoStep S (A .estate) (A .eletters) p' x q) : FgautoStep S (A .estate) (fgauto_enfa_edges S A) p x q
  ≔ let V ≔ A .estate in
    let z ≔ fgauto_step_mem_edge S V (A .eletters) p' x q s in
    let e ≔ z .fst in
    let me ≔ fgauto_mem_transport V p' (e .src) (fgauto_eclosure S A p) (z .snd .snd .fst) (fgauto_eclosure_complete S A p p' h) in
    fgauto_step_transport S V (fgauto_enfa_edges S A) p p (e .lab) x (e .tgt) q (refl p)
      (inverse (SignedLetter S) x (e .lab) (z .snd .snd .snd .fst)) (inverse V q (e .tgt) (z .snd .snd .snd .snd))
      (fgauto_mem_edge_step S V (fgauto_enfa_edges S A) (p, e .lab, e .tgt)
        (fgauto_mem_bind V (FgautoEdge S V) (fgauto_enfa_states S A) (fgauto_enfa_edges_at S A) p (p, e .lab, e .tgt) mp
          (fgauto_mem_bind (FgautoEdge S V) (FgautoEdge S V) (A .eletters)
            (e0 ↦ fgauto_enfa_pick S A p e0 (fgauto_mem_decide V (A .edec) (e0 .src) (fgauto_eclosure S A p))) e (p, e .lab, e .tgt)
            (z .snd .fst) (fgauto_enfa_pick_mem S A p e me (fgauto_mem_decide V (A .edec) (e .src) (fgauto_eclosure S A p))))))

{` The languages agree. `}
def fgauto_enfa_to_nfa_run (S : Type) (A : FgautoENFA S) (p : A .estate) (mp : FgautoMem (A .estate) p (fgauto_enfa_states S A))
  (w : SignedWord S) (f : A .estate) (mf : FgautoMem (A .estate) f (A .efinal)) (r : FgautoERun S A p w f)
  : Σ (A .estate) (q ↦ Product (FgautoMem (A .estate) q (fgauto_enfa_nfa S A .nfinal)) (FgautoRun S (A .estate) (fgauto_enfa_edges S A) p w q))
  ≔ let V ≔ A .estate in
    match w [
    | nil. ↦ (p, (fgauto_filter_mem_intro V (fgauto_efinal_bool S A) p (fgauto_enfa_states S A) mp
          (fgauto_decision_bool_true (FgautoEFinalAt S A p)
            (fgauto_list_exists_decide V (f0 ↦ FgautoMem V f0 (fgauto_eclosure S A p)) (f0 ↦ fgauto_mem_decide V (A .edec) f0 (fgauto_eclosure S A p)) (A .efinal))
            (f, (mf, fgauto_eclosure_complete S A p f r))),
        refl p))
    | cons. x w' ↦
      let p' ≔ r .fst in
      let q1 ≔ r .snd .snd .fst in
      let mq1 : FgautoMem V q1 (fgauto_enfa_states S A)
        ≔ inr. (fgauto_mem_append_right V q1 (A .efinal) (append V (fgauto_endpoints S V (A .eletters)) (fgauto_endpoints Unit V (A .eeps)))
            (fgauto_mem_append_left V q1 (fgauto_endpoints S V (A .eletters)) (fgauto_endpoints Unit V (A .eeps))
              (fgauto_endpoints_in S V (A .eletters) p' x q1 (r .snd .snd .snd .fst) .snd))) in
      let ih ≔ fgauto_enfa_to_nfa_run S A q1 mq1 w' f mf (r .snd .snd .snd .snd) in
      (ih .fst, (ih .snd .fst, (q1, (fgauto_enfa_step_intro S A p mp p' (r .snd .fst) x q1 (r .snd .snd .snd .fst), ih .snd .snd)))) ]

def fgauto_nfa_to_enfa_run (S : Type) (A : FgautoENFA S) (p : A .estate) (w : SignedWord S) (q : A .estate)
  (mq : FgautoMem (A .estate) q (fgauto_enfa_nfa S A .nfinal)) (r : FgautoRun S (A .estate) (fgauto_enfa_edges S A) p w q)
  : Σ (A .estate) (f ↦ Product (FgautoMem (A .estate) f (A .efinal)) (FgautoERun S A p w f))
  ≔ let V ≔ A .estate in
    match w [
    | nil. ↦
      let fz ≔ fgauto_decision_bool_reflect (FgautoEFinalAt S A q)
        (fgauto_list_exists_decide V (f0 ↦ FgautoMem V f0 (fgauto_eclosure S A q)) (f0 ↦ fgauto_mem_decide V (A .edec) f0 (fgauto_eclosure S A q)) (A .efinal))
        (fgauto_filter_mem_elim V (fgauto_efinal_bool S A) q (fgauto_enfa_states S A) mq) in
      let rr ≔ fgauto_eclosure_sound S A q (fz .fst) (fz .snd .snd) in
      (fz .fst, (fz .snd .fst, (rr .fst, fgauto_run_start Unit V (A .eeps) q p (rr .fst) (fz .fst) (inverse V p q r) (rr .snd))))
    | cons. x w' ↦
      let se ≔ fgauto_enfa_step_elim S A p x (r .fst) (r .snd .fst) in
      let ih ≔ fgauto_nfa_to_enfa_run S A (r .fst) w' q mq (r .snd .snd) in
      (ih .fst, (ih .snd .fst, (se .fst, (se .snd .fst, (r .fst, (se .snd .snd, ih .snd .snd)))))) ]

def fgauto_enfa_nfa_language (S : Type) (A : FgautoENFA S) (w : SignedWord S)
  : FgautoIff (FgautoEAccepts S A w) (FgautoNFAAccepts S (fgauto_enfa_nfa S A) w)
  ≔ let V ≔ A .estate in
    let N ≔ fgauto_enfa_nfa S A in
    (h ↦ mere_rec (Σ V (f ↦ Product (FgautoMem V f (A .efinal)) (FgautoERun S A (A .einit) w f))) (FgautoNFAAccepts S N w)
       (mere_isprop (Σ V (q ↦ Product (FgautoMem V q (N .nfinal)) (FgautoRun S V (N .nedges) (A .einit) w q))))
       (z ↦ mere (Σ V (q ↦ Product (FgautoMem V q (N .nfinal)) (FgautoRun S V (N .nedges) (A .einit) w q)))
         (fgauto_enfa_to_nfa_run S A (A .einit) (inl. (refl (A .einit))) w (z .fst) (z .snd .fst) (z .snd .snd))) h,
     h ↦ mere_rec (Σ V (q ↦ Product (FgautoMem V q (N .nfinal)) (FgautoRun S V (N .nedges) (A .einit) w q))) (FgautoEAccepts S A w)
       (mere_isprop (Σ V (f ↦ Product (FgautoMem V f (A .efinal)) (FgautoERun S A (A .einit) w f))))
       (z ↦ mere (Σ V (f ↦ Product (FgautoMem V f (A .efinal)) (FgautoERun S A (A .einit) w f)))
         (fgauto_nfa_to_enfa_run S A (A .einit) w (z .fst) (z .snd .fst) (z .snd .snd))) h)

def fgauto_enfa_regular (S : Type) (A : FgautoENFA S) : FgautoRegular S (FgautoEAccepts S A)
  ≔ mere (Σ (FgautoNFA S) (B ↦ (w : SignedWord S) → FgautoIff (FgautoEAccepts S A w) (FgautoNFAAccepts S B w)))
      (fgauto_enfa_nfa S A, fgauto_enfa_nfa_language S A)
