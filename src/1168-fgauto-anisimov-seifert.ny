export "1167-fgauto-thompson-correct"

{` Chapter 11, automata part 19: the theorem at fggroups.tex:956
   (Anisimov and Seifert): a subgroup H of a group G is rational iff it is
   finitely generated.  "<=" is module 1162; here "=>".

   If H is the rational subset of r, it is the set of values of the
   accepting runs of the automaton A = fgauto_thompson r (module 1167).
   For every state p reachable from the start choose a word u_p leading to
   it (spanning tree, module 1155) and put c_p = value(u_p); for every
   state q from which the end is reachable choose a word v_q from q to the
   end.  The finitely many elements c_p x c_q^-1, for the edges p -x-> q
   with p reachable and q co-reachable, together with c_end, lie in H
   (each is a quotient of values of accepting runs) and generate H: along
   an accepting run s = p0 -x1-> p1 ... -> pn = t the value telescopes,
   value = prod_k (c_(p_(k-1)) x_k c_(p_k)^-1) . c_t. `}

{` Group algebra. `}
def fgauto_tri (G : AbstractGroup) (a x b : G .carrier) : G .carrier ≔ G .mul (G .mul a x) (G .inv b)

def fgauto_tri_mul (G : AbstractGroup) (a x b y c : G .carrier)
  : Id (G .carrier) (G .mul (fgauto_tri G a x b) (fgauto_tri G b y c)) (fgauto_tri G a (G .mul x y) c)
  ≔ let C ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let Lw ≔ G .laws in
    calc
      m (m (m a x) (i b)) (m (m b y) (i c))
      = m (m a x) (m (i b) (m (m b y) (i c))) by inverse C (m (m a x) (m (i b) (m (m b y) (i c)))) (m (m (m a x) (i b)) (m (m b y) (i c)))
          (Lw .assoc (m a x) (i b) (m (m b y) (i c)))
      = m (m a x) (m (i b) (m b (m y (i c)))) by refl ((z ↦ m (m a x) (m (i b) z)) : C → C)
          (inverse C (m b (m y (i c))) (m (m b y) (i c)) (Lw .assoc b y (i c)))
      = m (m a x) (m y (i c)) by refl (m (m a x)) (ag_mul_inv_cancel_left G b (m y (i c)))
      = m (m (m a x) y) (i c) by Lw .assoc (m a x) y (i c)
      = m (m a (m x y)) (i c) by refl ((z ↦ m z (i c)) : C → C) (inverse C (m a (m x y)) (m (m a x) y) (Lw .assoc a x y)) ∎

def fgauto_tri_unit (G : AbstractGroup) (a : G .carrier) : Id (G .carrier) (fgauto_tri G a (G .unit) a) (G .unit)
  ≔ concat (G .carrier) (G .mul (G .mul a (G .unit)) (G .inv a)) (G .mul a (G .inv a)) (G .unit)
      (refl ((z ↦ G .mul z (G .inv a)) : G .carrier → G .carrier) (G .laws .unit_right a)) (G .laws .inv_right a)

def fgauto_tri_quotient (G : AbstractGroup) (a x b d : G .carrier)
  : Id (G .carrier) (G .mul (G .mul (G .mul a x) d) (G .inv (G .mul b d))) (fgauto_tri G a x b)
  ≔ let C ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let Lw ≔ G .laws in
    calc
      m (m (m a x) d) (i (m b d))
      = m (m (m a x) d) (m (i d) (i b)) by refl (m (m (m a x) d)) (ag_inv_mul G b d)
      = m (m (m (m a x) d) (i d)) (i b) by Lw .assoc (m (m a x) d) (i d) (i b)
      = m (m a x) (i b) by refl ((z ↦ m z (i b)) : C → C) (ag_mul_inv_cancel_right G (m a x) d) ∎

def fgauto_tri_unit_left (G : AbstractGroup) (x c : G .carrier)
  : Id (G .carrier) (G .mul (fgauto_tri G (G .unit) x c) c) x
  ≔ concat (G .carrier) (G .mul (G .mul (G .mul (G .unit) x) (G .inv c)) c) (G .mul (G .unit) x) x
      (ag_mul_cancel_inv_right G (G .mul (G .unit) x) c) (G .laws .unit_left x)

{` Runs of the reversed graph. `}
def fgauto_reverse_run (S V : Type) (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q : V)
  (r : FgautoRun S V (fgauto_reverse_edges S V E) p w q) : FgautoRun S V E q (word_inverse S w) p
  ≔ match w [
  | nil. ↦ inverse V p q r
  | cons. x w' ↦ fgauto_run_append S V E q (word_inverse S w') (r .fst) (cons. (letter_complement S x) nil.) p
      (fgauto_reverse_run S V E (r .fst) w' q (r .snd .snd))
      (fgauto_run_single S V E (r .fst) (letter_complement S x) p (fgauto_step_unreverse S V E p x (r .fst) (r .snd .fst))) ]

def fgauto_run_to_reverse (S V : Type) (E : List (FgautoEdge S V)) (p : V) (w : SignedWord S) (q : V)
  (r : FgautoRun S V E p w q) : FgautoRun S V (fgauto_reverse_edges S V E) q (word_inverse S w) p
  ≔ match w [
  | nil. ↦ inverse V p q r
  | cons. x w' ↦ fgauto_run_append S V (fgauto_reverse_edges S V E) q (word_inverse S w') (r .fst) (cons. (letter_complement S x) nil.) p
      (fgauto_run_to_reverse S V E (r .fst) w' q (r .snd .snd))
      (fgauto_run_single S V (fgauto_reverse_edges S V E) (r .fst) (letter_complement S x) p (fgauto_step_reverse S V E p x (r .fst) (r .snd .fst))) ]

{` The data of an automaton over G. `}
def fgauto_as_monoid (G : AbstractGroup) : FgautoMonoid ≔ fgauto_group_monoid G

def fgauto_as_val (G : AbstractGroup) (w : SignedWord (G .carrier)) : G .carrier ≔ fgauto_path_eval (fgauto_group_monoid G) w

def fgauto_as_val_append (G : AbstractGroup) (u v : SignedWord (G .carrier))
  : Id (G .carrier) (fgauto_as_val G (append (SignedLetter (G .carrier)) u v)) (G .mul (fgauto_as_val G u) (fgauto_as_val G v))
  ≔ fgauto_path_eval_append (fgauto_group_monoid G) (fgauto_group_monoid_laws G) u v

def fgauto_as_fwd (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) : List (List Nat)
  ≔ fgauto_reached (G .carrier) (List Nat) fgauto_tstate_dec (A .tedges) (A .tstart)

def fgauto_as_bwd (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) : List (List Nat)
  ≔ fgauto_reached (G .carrier) (List Nat) fgauto_tstate_dec (fgauto_reverse_edges (G .carrier) (List Nat) (A .tedges)) (A .tend)

def fgauto_as_u (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (p : List Nat) : SignedWord (G .carrier)
  ≔ fgauto_tree_word (G .carrier) (List Nat) fgauto_tstate_dec (A .tedges) (A .tstart) p

def fgauto_as_v (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (q : List Nat) : SignedWord (G .carrier)
  ≔ word_inverse (G .carrier) (fgauto_tree_word (G .carrier) (List Nat) fgauto_tstate_dec
      (fgauto_reverse_edges (G .carrier) (List Nat) (A .tedges)) (A .tend) q)

def fgauto_as_c (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (p : List Nat) : G .carrier
  ≔ fgauto_as_val G (fgauto_as_u G A p)

def fgauto_as_u_run (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (p : List Nat)
  (m : FgautoMem (List Nat) p (fgauto_as_fwd G A))
  : FgautoRun (G .carrier) (List Nat) (A .tedges) (A .tstart) (fgauto_as_u G A p) p
  ≔ fgauto_tree_word_run (G .carrier) (List Nat) fgauto_tstate_dec (A .tedges) (A .tstart) p m

def fgauto_as_v_run (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (q : List Nat)
  (m : FgautoMem (List Nat) q (fgauto_as_bwd G A))
  : FgautoRun (G .carrier) (List Nat) (A .tedges) q (fgauto_as_v G A q) (A .tend)
  ≔ fgauto_reverse_run (G .carrier) (List Nat) (A .tedges) (A .tend)
      (fgauto_tree_word (G .carrier) (List Nat) fgauto_tstate_dec (fgauto_reverse_edges (G .carrier) (List Nat) (A .tedges)) (A .tend) q) q
      (fgauto_tree_word_run (G .carrier) (List Nat) fgauto_tstate_dec (fgauto_reverse_edges (G .carrier) (List Nat) (A .tedges)) (A .tend) q m)

def fgauto_as_bwd_complete (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (q : List Nat)
  (w : SignedWord (G .carrier)) (r : FgautoRun (G .carrier) (List Nat) (A .tedges) q w (A .tend))
  : FgautoMem (List Nat) q (fgauto_as_bwd G A)
  ≔ fgauto_reach_complete (G .carrier) (List Nat) fgauto_tstate_dec (fgauto_reverse_edges (G .carrier) (List Nat) (A .tedges)) (A .tend)
      (word_inverse (G .carrier) w) q (fgauto_run_to_reverse (G .carrier) (List Nat) (A .tedges) q w (A .tend) r)

{` The generators. `}
def fgauto_as_edge_gen (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (p : List Nat)
  (x : SignedLetter (G .carrier)) (q : List Nat) : G .carrier
  ≔ fgauto_tri G (fgauto_as_c G A p) (fgauto_label_eval (fgauto_group_monoid G) x) (fgauto_as_c G A q)

def fgauto_as_gens_pick (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (e : FgautoEdge (G .carrier) (List Nat))
  (d1 : Decidable (FgautoMem (List Nat) (e .src) (fgauto_as_fwd G A))) (d2 : Decidable (FgautoMem (List Nat) (e .tgt) (fgauto_as_bwd G A)))
  (rest : List (G .carrier)) : List (G .carrier)
  ≔ match d1 [
  | inl. _ ↦ match d2 [ inl. _ ↦ cons. (fgauto_as_edge_gen G A (e .src) (e .lab) (e .tgt)) rest | inr. _ ↦ rest ]
  | inr. _ ↦ rest ]

def fgauto_as_gens_in (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (L : List (FgautoEdge (G .carrier) (List Nat)))
  : List (G .carrier)
  ≔ match L [
  | nil. ↦ nil.
  | cons. e L' ↦ fgauto_as_gens_pick G A e (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .src) (fgauto_as_fwd G A))
      (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .tgt) (fgauto_as_bwd G A)) (fgauto_as_gens_in G A L') ]

def fgauto_as_gens (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) : List (G .carrier)
  ≔ cons. (fgauto_as_c G A (A .tend)) (fgauto_as_gens_in G A (A .tedges))

{` Every step between a reachable and a co-reachable state contributes. `}
def fgauto_as_gens_pick_mem (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (e : FgautoEdge (G .carrier) (List Nat))
  (rest : List (G .carrier)) (p : List Nat) (x : SignedLetter (G .carrier)) (q : List Nat)
  (t : Product (Id (List Nat) p (e .src)) (Product (Id (SignedLetter (G .carrier)) x (e .lab)) (Id (List Nat) q (e .tgt))))
  (mp : FgautoMem (List Nat) p (fgauto_as_fwd G A)) (mq : FgautoMem (List Nat) q (fgauto_as_bwd G A))
  (d1 : Decidable (FgautoMem (List Nat) (e .src) (fgauto_as_fwd G A))) (d2 : Decidable (FgautoMem (List Nat) (e .tgt) (fgauto_as_bwd G A)))
  : FgautoMem (G .carrier) (fgauto_as_edge_gen G A p x q) (fgauto_as_gens_pick G A e d1 d2 rest)
  ≔ match d1 [
  | inl. _ ↦ match d2 [
    | inl. _ ↦ inl. (refl ((a b c ↦ fgauto_as_edge_gen G A a b c) : List Nat → SignedLetter (G .carrier) → List Nat → G .carrier)
        (t .fst) (t .snd .fst) (t .snd .snd))
    | inr. n ↦ match n (fgauto_mem_transport (List Nat) q (e .tgt) (fgauto_as_bwd G A) (t .snd .snd) mq) [] ]
  | inr. n ↦ match n (fgauto_mem_transport (List Nat) p (e .src) (fgauto_as_fwd G A) (t .fst) mp) [] ]

def fgauto_as_gens_pick_rest (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (e : FgautoEdge (G .carrier) (List Nat))
  (rest : List (G .carrier)) (g : G .carrier) (m : FgautoMem (G .carrier) g rest)
  (d1 : Decidable (FgautoMem (List Nat) (e .src) (fgauto_as_fwd G A))) (d2 : Decidable (FgautoMem (List Nat) (e .tgt) (fgauto_as_bwd G A)))
  : FgautoMem (G .carrier) g (fgauto_as_gens_pick G A e d1 d2 rest)
  ≔ match d1 [ inl. _ ↦ match d2 [ inl. _ ↦ inr. m | inr. _ ↦ m ] | inr. _ ↦ m ]

def fgauto_as_gens_in_mem (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (L : List (FgautoEdge (G .carrier) (List Nat)))
  (p : List Nat) (x : SignedLetter (G .carrier)) (q : List Nat) (s : FgautoStep (G .carrier) (List Nat) L p x q)
  (mp : FgautoMem (List Nat) p (fgauto_as_fwd G A)) (mq : FgautoMem (List Nat) q (fgauto_as_bwd G A))
  : FgautoMem (G .carrier) (fgauto_as_edge_gen G A p x q) (fgauto_as_gens_in G A L)
  ≔ match L [
  | nil. ↦ match s []
  | cons. e L' ↦ match s [
    | inl. t ↦ fgauto_as_gens_pick_mem G A e (fgauto_as_gens_in G A L') p x q t mp mq
        (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .src) (fgauto_as_fwd G A))
        (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .tgt) (fgauto_as_bwd G A))
    | inr. s' ↦ fgauto_as_gens_pick_rest G A e (fgauto_as_gens_in G A L') (fgauto_as_edge_gen G A p x q)
        (fgauto_as_gens_in_mem G A L' p x q s' mp mq)
        (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .src) (fgauto_as_fwd G A))
        (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .tgt) (fgauto_as_bwd G A)) ] ]

{` Telescoping along a run to the end state. `}
def fgauto_as_telescope (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (p : List Nat) (w : SignedWord (G .carrier))
  (r : FgautoRun (G .carrier) (List Nat) (A .tedges) p w (A .tend)) (mp : FgautoMem (List Nat) p (fgauto_as_fwd G A))
  : FgautoGenerated G (fgauto_as_gens G A) (fgauto_tri G (fgauto_as_c G A p) (fgauto_as_val G w) (fgauto_as_c G A (A .tend)))
  ≔ let gs ≔ fgauto_as_gens G A in
    let sub ≔ fgauto_generated_subgroup G gs in
    let C ≔ G .carrier in
    match w [
    | nil. ↦ fgauto_group_subset_transport G (fgauto_generated_subset G gs) (G .unit)
        (fgauto_tri G (fgauto_as_c G A p) (G .unit) (fgauto_as_c G A (A .tend)))
        (concat C (G .unit) (fgauto_tri G (fgauto_as_c G A p) (G .unit) (fgauto_as_c G A p))
          (fgauto_tri G (fgauto_as_c G A p) (G .unit) (fgauto_as_c G A (A .tend)))
          (inverse C (fgauto_tri G (fgauto_as_c G A p) (G .unit) (fgauto_as_c G A p)) (G .unit) (fgauto_tri_unit G (fgauto_as_c G A p)))
          (refl ((z ↦ fgauto_tri G (fgauto_as_c G A p) (G .unit) (fgauto_as_c G A z)) : List Nat → C) r))
        (sub .fst)
    | cons. x w' ↦
      let q ≔ r .fst in
      let mq ≔ fgauto_reach_closed C (List Nat) fgauto_tstate_dec (A .tedges) (A .tstart) p x q (r .snd .fst) mp in
      let bq ≔ fgauto_as_bwd_complete G A q w' (r .snd .snd) in
      let gen ≔ fgauto_generated_contains G gs (fgauto_as_edge_gen G A p x q)
        (inr. (fgauto_as_gens_in_mem G A (A .tedges) p x q (r .snd .fst) mp bq)) in
      fgauto_group_subset_transport G (fgauto_generated_subset G gs)
        (G .mul (fgauto_as_edge_gen G A p x q) (fgauto_tri G (fgauto_as_c G A q) (fgauto_as_val G w') (fgauto_as_c G A (A .tend))))
        (fgauto_tri G (fgauto_as_c G A p) (fgauto_as_val G (cons. x w')) (fgauto_as_c G A (A .tend)))
        (fgauto_tri_mul G (fgauto_as_c G A p) (fgauto_label_eval (fgauto_group_monoid G) x) (fgauto_as_c G A q) (fgauto_as_val G w')
          (fgauto_as_c G A (A .tend)))
        (sub .snd .fst (fgauto_as_edge_gen G A p x q) (fgauto_tri G (fgauto_as_c G A q) (fgauto_as_val G w') (fgauto_as_c G A (A .tend)))
          gen (fgauto_as_telescope G A q w' (r .snd .snd) mq)) ]

{` The theorem. `}
def fgauto_as_lang (G : AbstractGroup) (A : FgautoThompsonAut (fgauto_group_monoid G)) (w : SignedWord (G .carrier))
  (r : FgautoRun (G .carrier) (List Nat) (A .tedges) (A .tstart) w (A .tend)) : FgautoThompsonLang (fgauto_group_monoid G) A (fgauto_as_val G w)
  ≔ mere (Σ (SignedWord (G .carrier)) (w0 ↦ Product (FgautoRun (G .carrier) (List Nat) (A .tedges) (A .tstart) w0 (A .tend))
       (Id (G .carrier) (fgauto_path_eval (fgauto_group_monoid G) w0) (fgauto_as_val G w)))) (w, (r, refl (fgauto_as_val G w)))

def fgauto_as_gens_pick_H (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (r : FgautoRatExpr (G .carrier)) (hr : (g : G .carrier) → FgautoIff (H g .fst) (fgauto_rat_mem (fgauto_group_monoid G) r g))
  (e : FgautoEdge (G .carrier) (List Nat))
  (se : FgautoStep (G .carrier) (List Nat) (fgauto_thompson (fgauto_group_monoid G) r .tedges) (e .src) (e .lab) (e .tgt))
  (d1 : Decidable (FgautoMem (List Nat) (e .src) (fgauto_as_fwd G (fgauto_thompson (fgauto_group_monoid G) r))))
  (d2 : Decidable (FgautoMem (List Nat) (e .tgt) (fgauto_as_bwd G (fgauto_thompson (fgauto_group_monoid G) r))))
  (rest : List (G .carrier)) (ih : (g : G .carrier) → FgautoMem (G .carrier) g rest → H g .fst)
  (g : G .carrier) (mg : FgautoMem (G .carrier) g (fgauto_as_gens_pick G (fgauto_thompson (fgauto_group_monoid G) r) e d1 d2 rest))
  : H g .fst
  ≔ let M ≔ fgauto_group_monoid G in
    let Lw ≔ fgauto_group_monoid_laws G in
    let A ≔ fgauto_thompson M r in
    let C ≔ G .carrier in
    let inH : (g0 : C) → FgautoThompsonLang M A g0 → H g0 .fst ≔ g0 l ↦ hr g0 .snd (fgauto_thompson_correct M Lw r g0 .snd l) in
    match d1 [
    | inr. _ ↦ ih g mg
    | inl. m1 ↦ match d2 [
      | inr. _ ↦ ih g mg
      | inl. m2 ↦ match mg [
        | inr. mg' ↦ ih g mg'
        | inl. eg ↦
          let p ≔ e .src in
          let q ≔ e .tgt in
          let mq ≔ fgauto_reach_closed C (List Nat) fgauto_tstate_dec (A .tedges) (A .tstart) p (e .lab) q se m1 in
          let up ≔ fgauto_as_u G A p in
          let uq ≔ fgauto_as_u G A q in
          let vq ≔ fgauto_as_v G A q in
          let w1 ≔ append (SignedLetter C) up (cons. (e .lab) vq) in
          let w2 ≔ append (SignedLetter C) uq vq in
          let h1 ≔ inH (fgauto_as_val G w1) (fgauto_as_lang G A w1
            (fgauto_run_append C (List Nat) (A .tedges) (A .tstart) up p (cons. (e .lab) vq) (A .tend) (fgauto_as_u_run G A p m1)
              (q, (se, fgauto_as_v_run G A q m2)))) in
          let h2 ≔ inH (fgauto_as_val G w2) (fgauto_as_lang G A w2
            (fgauto_run_append C (List Nat) (A .tedges) (A .tstart) uq q vq (A .tend) (fgauto_as_u_run G A q mq) (fgauto_as_v_run G A q m2))) in
          let ev1 : Id C (fgauto_as_val G w1) (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq))
            ≔ concat C (fgauto_as_val G w1) (G .mul (fgauto_as_c G A p) (G .mul (fgauto_label_eval M (e .lab)) (fgauto_as_val G vq)))
                (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq))
                (fgauto_as_val_append G up (cons. (e .lab) vq))
                (G .laws .assoc (fgauto_as_c G A p) (fgauto_label_eval M (e .lab)) (fgauto_as_val G vq)) in
          let ev2 : Id C (fgauto_as_val G w2) (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq)) ≔ fgauto_as_val_append G uq vq in
          fgauto_group_subset_transport G H
            (G .mul (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq))
              (G .inv (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq))))
            g
            (concat C (G .mul (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq))
                (G .inv (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq))))
              (fgauto_as_edge_gen G A p (e .lab) q) g
              (fgauto_tri_quotient G (fgauto_as_c G A p) (fgauto_label_eval M (e .lab)) (fgauto_as_c G A q) (fgauto_as_val G vq))
              (inverse C g (fgauto_as_edge_gen G A p (e .lab) q) eg))
            (hH .snd .fst (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq))
              (G .inv (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq)))
              (fgauto_group_subset_transport G H (fgauto_as_val G w1)
                (G .mul (G .mul (fgauto_as_c G A p) (fgauto_label_eval M (e .lab))) (fgauto_as_val G vq)) ev1 h1)
              (hH .snd .snd (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq))
                (fgauto_group_subset_transport G H (fgauto_as_val G w2) (G .mul (fgauto_as_c G A q) (fgauto_as_val G vq)) ev2 h2))) ] ] ]

def fgauto_as_gens_in_H_at (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (r : FgautoRatExpr (G .carrier)) (hr : (g : G .carrier) → FgautoIff (H g .fst) (fgauto_rat_mem (fgauto_group_monoid G) r g))
  (L : List (FgautoEdge (G .carrier) (List Nat)))
  (incl : FgautoStepIncl (G .carrier) (List Nat) L (fgauto_thompson (fgauto_group_monoid G) r .tedges))
  (g : G .carrier) (mg : FgautoMem (G .carrier) g (fgauto_as_gens_in G (fgauto_thompson (fgauto_group_monoid G) r) L))
  : H g .fst
  ≔ match L [
  | nil. ↦ match mg []
  | cons. e L' ↦ fgauto_as_gens_pick_H G H hH r hr e (incl (e .src) (e .lab) (e .tgt) (fgauto_step_head (G .carrier) (List Nat) e L'))
      (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .src) (fgauto_as_fwd G (fgauto_thompson (fgauto_group_monoid G) r)))
      (fgauto_mem_decide (List Nat) fgauto_tstate_dec (e .tgt) (fgauto_as_bwd G (fgauto_thompson (fgauto_group_monoid G) r)))
      (fgauto_as_gens_in G (fgauto_thompson (fgauto_group_monoid G) r) L')
      (fgauto_as_gens_in_H_at G H hH r hr L' (p0 x0 q0 s ↦ incl p0 x0 q0 (inr. s))) g mg ]

def fgauto_as_gens_in_H (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (r : FgautoRatExpr (G .carrier)) (hr : (g : G .carrier) → FgautoIff (H g .fst) (fgauto_rat_mem (fgauto_group_monoid G) r g))
  (g : G .carrier) (mg : FgautoMem (G .carrier) g (fgauto_as_gens_in G (fgauto_thompson (fgauto_group_monoid G) r)
      (fgauto_thompson (fgauto_group_monoid G) r .tedges)))
  : H g .fst
  ≔ fgauto_as_gens_in_H_at G H hH r hr (fgauto_thompson (fgauto_group_monoid G) r .tedges) (p x q s ↦ s) g mg

def fgauto_rational_subgroup_fg_at (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (r : FgautoRatExpr (G .carrier)) (hr : (g : G .carrier) → FgautoIff (H g .fst) (fgauto_rat_mem (fgauto_group_monoid G) r g))
  : (g : G .carrier) → FgautoIff (H g .fst) (FgautoGenerated G (fgauto_as_gens G (fgauto_thompson (fgauto_group_monoid G) r)) g)
  ≔ let M ≔ fgauto_group_monoid G in
    let Lw ≔ fgauto_group_monoid_laws G in
    let A ≔ fgauto_thompson M r in
    let C ≔ G .carrier in
    let E ≔ A .tedges in
    let gs ≔ fgauto_as_gens G A in
    let inH : (g : C) → FgautoThompsonLang M A g → H g .fst ≔ g l ↦ hr g .snd (fgauto_thompson_correct M Lw r g .snd l) in
    let langH : (g : C) → H g .fst → FgautoThompsonLang M A g ≔ g h ↦ fgauto_thompson_correct M Lw r g .fst (hr g .fst h) in
    let R ≔ (g : C) ↦ Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) E (A .tstart) w (A .tend)) (Id C (fgauto_path_eval M w) g)) in
    let ne : Mere (R (G .unit)) ≔ langH (G .unit) (hH .fst) in
    let gensH : (g : C) → FgautoMem C g gs → H g .fst
      ≔ g mg ↦ mere_rec (R (G .unit)) (H g .fst) (H g .snd)
          (z0 ↦
            let mt ≔ fgauto_reach_complete C (List Nat) fgauto_tstate_dec E (A .tstart) (z0 .fst) (A .tend) (z0 .snd .fst) in
            match mg [
            | inl. eg ↦ fgauto_group_subset_transport G H (fgauto_as_c G A (A .tend)) g (inverse C g (fgauto_as_c G A (A .tend)) eg)
                (inH (fgauto_as_c G A (A .tend)) (fgauto_as_lang G A (fgauto_as_u G A (A .tend)) (fgauto_as_u_run G A (A .tend) mt)))
            | inr. mg' ↦ fgauto_as_gens_in_H G H hH r hr g mg' ]) ne in
    g ↦ (h ↦ mere_rec (R g) (FgautoGenerated G gs g) (mere_isprop (Σ (List C) (l ↦ Product (FgautoAllIn C (x ↦ Mere (FgautoMem C x (fgauto_sym_gens G gs))) l)
              (Id C g (fgauto_list_product M l)))))
           (z ↦
             let ms ≔ fgauto_reach_root C (List Nat) fgauto_tstate_dec E (A .tstart) in
             let mt ≔ fgauto_reach_complete C (List Nat) fgauto_tstate_dec E (A .tstart) (z .fst) (A .tend) (z .snd .fst) in
             let tel ≔ fgauto_as_telescope G A (A .tstart) (z .fst) (z .snd .fst) ms in
             let cs : Id C (fgauto_as_c G A (A .tstart)) (G .unit)
               ≔ refl (fgauto_as_val G) (fgauto_tree_word_root C (List Nat) fgauto_tstate_dec E (A .tstart)) in
             let sub ≔ fgauto_generated_subgroup G gs in
             fgauto_group_subset_transport G (fgauto_generated_subset G gs)
               (G .mul (fgauto_tri G (G .unit) (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend))) (fgauto_as_c G A (A .tend))) g
               (concat C (G .mul (fgauto_tri G (G .unit) (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend))) (fgauto_as_c G A (A .tend)))
                  (fgauto_as_val G (z .fst)) g
                  (fgauto_tri_unit_left G (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend))) (z .snd .snd))
               (sub .snd .fst (fgauto_tri G (G .unit) (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend))) (fgauto_as_c G A (A .tend))
                 (fgauto_group_subset_transport G (fgauto_generated_subset G gs)
                   (fgauto_tri G (fgauto_as_c G A (A .tstart)) (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend)))
                   (fgauto_tri G (G .unit) (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend)))
                   (refl ((y ↦ fgauto_tri G y (fgauto_as_val G (z .fst)) (fgauto_as_c G A (A .tend))) : C → C) cs) tel)
                 (fgauto_generated_contains G gs (fgauto_as_c G A (A .tend)) (inl. (refl (fgauto_as_c G A (A .tend)))))))
           (langH g h),
         m ↦ fgauto_generated_least G gs H hH gensH g m)

{` fggroups.tex:956, "=>": rational subgroups are finitely generated. `}
def fgauto_rational_subgroup_finitely_generated (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (hr : FgautoRational (fgauto_group_monoid G) (g ↦ H g .fst)) : FgautoFinitelyGeneratedSubgroup G (g ↦ H g .fst)
  ≔ mere_rec (Σ (FgautoRatExpr (G .carrier)) (r ↦ (m : G .carrier) → FgautoIff (H m .fst) (fgauto_rat_mem (fgauto_group_monoid G) r m)))
      (FgautoFinitelyGeneratedSubgroup G (g ↦ H g .fst))
      (mere_isprop (Σ (List (G .carrier)) (gs ↦ (g : G .carrier) → FgautoIff (H g .fst) (FgautoGenerated G gs g))))
      (z ↦ mere (Σ (List (G .carrier)) (gs ↦ (g : G .carrier) → FgautoIff (H g .fst) (FgautoGenerated G gs g)))
        (fgauto_as_gens G (fgauto_thompson (fgauto_group_monoid G) (z .fst)), fgauto_rational_subgroup_fg_at G H hH (z .fst) (z .snd))) hr

def fgauto_anisimov_seifert (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  : FgautoIff (FgautoRational (fgauto_group_monoid G) (g ↦ H g .fst)) (FgautoFinitelyGeneratedSubgroup G (g ↦ H g .fst))
  ≔ (fgauto_rational_subgroup_finitely_generated G H hH, fgauto_finitely_generated_rational G (g ↦ H g .fst))
