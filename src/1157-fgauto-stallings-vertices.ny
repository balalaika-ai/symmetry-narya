export "1155-fgauto-reachability"

{` Chapter 11, automata part 8: the vertices of the Stallings automaton.

   The vertex list of S(H) is the base followed by all endpoints of edges,
   without repetitions (fgauto_stallings_vertices, module 1153).  Here: every
   vertex of S(H) is reachable from the base (an invariant of folding, true
   for the bouquet because petal vertices are prefixes of generators), and a
   repetition-free list l gives a finite set {v | v in l} with exactly
   length(l) elements (fgauto_list_set_fin_equiv). `}

{` Reachability of all sources from the base, an invariant of folding. `}
def FgautoSourcesReachable (S : Type) (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) : Type
  ≔ (p : SignedWord S) (x : SignedLetter S) (q : SignedWord S) → FgautoStep S (SignedWord S) E p x q
    → Σ (SignedWord S) (w ↦ FgautoRun S (SignedWord S) E b w p)

def fgauto_merge_sources_reachable (S : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S (SignedWord S)))
  (b : SignedWord S) (c : FgautoConflict S (SignedWord S) E) (h : FgautoSourcesReachable S E b)
  : FgautoSourcesReachable S (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b)
  ≔ p' x q' s ↦
    let f ≔ fgauto_merge S dec (c .ctgt1) (c .ctgt2) in
    let z ≔ fgauto_step_map_preimage S (SignedWord S) (SignedWord S) f E p' x q' s in
    let r ≔ h (z .fst) x (z .snd .fst) (z .snd .snd .fst) in
    (r .fst, fgauto_run_end S (SignedWord S) (fgauto_map_edges S (SignedWord S) (SignedWord S) f E) (f b) (r .fst)
      (f (z .fst)) p' (fgauto_wsym S p' (f (z .fst)) (z .snd .snd .snd .fst))
      (fgauto_run_map S (SignedWord S) (SignedWord S) f E b (r .fst) (z .fst) (r .snd)))

{` Petal vertices are reachable from the start of the petal. `}
def FgautoEndsReachable (S : Type) (E E' : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) : Type
  ≔ (p : SignedWord S) (x : SignedLetter S) (q : SignedWord S) → FgautoStep S (SignedWord S) E p x q
    → Product (Σ (SignedWord S) (w ↦ FgautoRun S (SignedWord S) E' b w p))
        (Σ (SignedWord S) (w ↦ FgautoRun S (SignedWord S) E' b w q))

def fgauto_petal_reachable (S : Type) (p0 : SignedWord S) (x : SignedLetter S) (t : SignedWord S)
  : FgautoEndsReachable S (fgauto_petal S p0 (cons. x t)) (fgauto_petal S p0 (cons. x t)) p0
  ≔ p y q s ↦ match t [
  | nil. ↦ match s [
    | inl. e ↦ ((nil., fgauto_wsym S p p0 (e .fst)),
        (cons. x nil., fgauto_run_end S (SignedWord S) (fgauto_petal S p0 (cons. x nil.)) p0 (cons. x nil.) nil. q
          (fgauto_wsym S q nil. (e .snd .snd)) (fgauto_petal_run S p0 x nil.)))
    | inr. s' ↦ match s' [] ]
  | cons. y0 t' ↦
    let P ≔ append (SignedLetter S) p0 (cons. x nil.) in
    let E : List (FgautoEdge S (SignedWord S)) ≔ cons. (p0, x, P) (fgauto_petal S P (cons. y0 t')) in
    match s [
    | inl. e ↦ ((nil., fgauto_wsym S p p0 (e .fst)),
        (cons. x nil., (P, (fgauto_step_head S (SignedWord S) (p0, x, P) (fgauto_petal S P (cons. y0 t')),
          fgauto_wsym S q P (e .snd .snd)))))
    | inr. s' ↦
      let ih ≔ fgauto_petal_reachable S P y0 t' p y q s' in
      let lift ≔ fgauto_run_mono S (SignedWord S) (fgauto_petal S P (cons. y0 t')) E (p1 x1 q1 k ↦ inr. k) in
      ((cons. x (ih .fst .fst), (P, (fgauto_step_head S (SignedWord S) (p0, x, P) (fgauto_petal S P (cons. y0 t')),
          lift P (ih .fst .fst) p (ih .fst .snd)))),
       (cons. x (ih .snd .fst), (P, (fgauto_step_head S (SignedWord S) (p0, x, P) (fgauto_petal S P (cons. y0 t')),
          lift P (ih .snd .fst) q (ih .snd .snd))))) ] ]

def fgauto_petals_reachable (S : Type) (gens : List (SignedWord S))
  : FgautoEndsReachable S (fgauto_petals S gens) (fgauto_petals S gens) nil.
  ≔ p y q s ↦ match gens [
  | nil. ↦ match s []
  | cons. g gs ↦
    let E1 ≔ fgauto_petal S nil. g in
    let E2 ≔ fgauto_petals S gs in
    match fgauto_step_append_split S (SignedWord S) E1 E2 p y q s [
    | inl. k ↦ match g [
      | nil. ↦ match k []
      | cons. x t ↦
        let r ≔ fgauto_petal_reachable S nil. x t p y q k in
        let lift ≔ fgauto_run_mono S (SignedWord S) (fgauto_petal S nil. (cons. x t)) (append (FgautoEdge S (SignedWord S))
          (fgauto_petal S nil. (cons. x t)) E2)
          (fgauto_step_append_left S (SignedWord S) (fgauto_petal S nil. (cons. x t)) E2) nil. in
        ((r .fst .fst, lift (r .fst .fst) p (r .fst .snd)), (r .snd .fst, lift (r .snd .fst) q (r .snd .snd))) ]
    | inr. k ↦
      let r ≔ fgauto_petals_reachable S gs p y q k in
      let lift ≔ fgauto_run_mono S (SignedWord S) E2 (append (FgautoEdge S (SignedWord S)) E1 E2)
        (fgauto_step_append_right S (SignedWord S) E1 E2) nil. in
      ((r .fst .fst, lift (r .fst .fst) p (r .fst .snd)), (r .snd .fst, lift (r .snd .fst) q (r .snd .snd))) ] ]

def fgauto_bouquet_sources_reachable (S : Type) (gens : List (SignedWord S))
  : FgautoSourcesReachable S (fgauto_bouquet S gens) nil.
  ≔ p x q s ↦
    let E ≔ fgauto_petals S gens in
    let lift ≔ fgauto_run_mono S (SignedWord S) E (fgauto_bouquet S gens)
      (fgauto_step_append_left S (SignedWord S) E (fgauto_reverse_edges S (SignedWord S) E)) nil. in
    match fgauto_step_append_split S (SignedWord S) E (fgauto_reverse_edges S (SignedWord S) E) p x q s [
    | inl. k ↦
      let r ≔ fgauto_petals_reachable S gens p x q k .fst in
      (r .fst, lift (r .fst) p (r .snd))
    | inr. k ↦
      let r ≔ fgauto_petals_reachable S gens q (letter_complement S x) p
        (fgauto_step_unreverse S (SignedWord S) E p x q k) .snd in
      (r .fst, lift (r .fst) p (r .snd)) ]

def fgauto_stallings_sources_reachable (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoSourcesReachable S (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens)
  ≔ fgauto_fold_ind S dec (FgautoSourcesReachable S) (E b c h ↦ fgauto_merge_sources_reachable S dec E b c h)
      (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil. (fgauto_bouquet_sources_reachable S gens)

{` Removal and repetition-free lists. `}
def fgauto_remove_choose_mem_elim (V : Type) (a b v : V) (d : Decidable (Id V b a)) (rest t : List V)
  (ih : FgautoMem V v rest → FgautoMem V v t) (m : FgautoMem V v (fgauto_remove_choose V a b d rest))
  : FgautoMem V v (cons. b t)
  ≔ match d [ inl. _ ↦ inr. (ih m) | inr. _ ↦ match m [ inl. e ↦ inl. e | inr. m' ↦ inr. (ih m') ] ]

def fgauto_remove_mem_elim (V : Type) (dV : DecidableEquality V) (a v : V) (l : List V)
  (m : FgautoMem V v (fgauto_remove V dV a l)) : FgautoMem V v l
  ≔ match l [
  | nil. ↦ match m []
  | cons. b t ↦ fgauto_remove_choose_mem_elim V a b v (dV b a) (fgauto_remove V dV a t) t
      (fgauto_remove_mem_elim V dV a v t) m ]

def fgauto_remove_choose_not_mem (V : Type) (a b : V) (d : Decidable (Id V b a)) (rest : List V)
  (ih : Not (FgautoMem V a rest)) : Not (FgautoMem V a (fgauto_remove_choose V a b d rest))
  ≔ match d [
  | inl. _ ↦ ih
  | inr. n ↦ m ↦ match m [ inl. e ↦ n (inverse V a b e) | inr. m' ↦ ih m' ] ]

def fgauto_remove_not_mem (V : Type) (dV : DecidableEquality V) (a : V) (l : List V)
  : Not (FgautoMem V a (fgauto_remove V dV a l))
  ≔ match l [
  | nil. ↦ m ↦ match m []
  | cons. b t ↦ fgauto_remove_choose_not_mem V a b (dV b a) (fgauto_remove V dV a t) (fgauto_remove_not_mem V dV a t) ]

def fgauto_remove_choose_nodup (V : Type) (dV : DecidableEquality V) (a b : V) (d : Decidable (Id V b a))
  (t : List V) (hb : Not (FgautoMem V b t)) (ih : FgautoNoDup V (fgauto_remove V dV a t))
  : FgautoNoDup V (fgauto_remove_choose V a b d (fgauto_remove V dV a t))
  ≔ match d [
  | inl. _ ↦ ih
  | inr. _ ↦ (m ↦ hb (fgauto_remove_mem_elim V dV a b t m), ih) ]

def fgauto_remove_nodup (V : Type) (dV : DecidableEquality V) (a : V) (l : List V) (h : FgautoNoDup V l)
  : FgautoNoDup V (fgauto_remove V dV a l)
  ≔ match l [
  | nil. ↦ star.
  | cons. b t ↦ fgauto_remove_choose_nodup V dV a b (dV b a) t (h .fst) (fgauto_remove_nodup V dV a t (h .snd)) ]

def fgauto_dedup_nodup (V : Type) (dV : DecidableEquality V) (l : List V) : FgautoNoDup V (fgauto_dedup V dV l)
  ≔ match l [
  | nil. ↦ star.
  | cons. a t ↦ (fgauto_remove_not_mem V dV a (fgauto_dedup V dV t),
      fgauto_remove_nodup V dV a (fgauto_dedup V dV t) (fgauto_dedup_nodup V dV t)) ]

def fgauto_dedup_mem_intro (V : Type) (dV : DecidableEquality V) (v : V) (l : List V) (m : FgautoMem V v l)
  : FgautoMem V v (fgauto_dedup V dV l)
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ match m [
    | inl. e ↦ inl. e
    | inr. m' ↦ match dV v a [
      | inl. e ↦ inl. e
      | inr. n ↦ inr. (fgauto_remove_mem V dV a v (fgauto_dedup V dV t) n (fgauto_dedup_mem_intro V dV v t m')) ] ] ]

def fgauto_dedup_mem_elim (V : Type) (dV : DecidableEquality V) (v : V) (l : List V)
  (m : FgautoMem V v (fgauto_dedup V dV l)) : FgautoMem V v l
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ match m [
    | inl. e ↦ inl. e
    | inr. m' ↦ inr. (fgauto_dedup_mem_elim V dV v t (fgauto_remove_mem_elim V dV a v (fgauto_dedup V dV t) m')) ] ]

{` The finite set of elements of a list. `}
def FgautoListSet (V : Type) (l : List V) : Type ≔ Σ V (v ↦ Mere (FgautoMem V v l))

def fgauto_list_set_path (V : Type) (l : List V) (u w : FgautoListSet V l) (p : Id V (u .fst) (w .fst))
  : Id (FgautoListSet V l) u w
  ≔ subtype_equal V (v ↦ Mere (FgautoMem V v l)) (v ↦ mere_isprop (FgautoMem V v l)) u w p

def fgauto_list_nth (V : Type) (l : List V) (i : Fin (length V l)) : V
  ≔ match l [
  | nil. ↦ match i []
  | cons. a t ↦ match i [ inl. j ↦ fgauto_list_nth V t j | inr. _ ↦ a ] ]

def fgauto_list_nth_mem (V : Type) (l : List V) (i : Fin (length V l)) : FgautoMem V (fgauto_list_nth V l i) l
  ≔ match l [
  | nil. ↦ match i []
  | cons. a t ↦ match i [ inl. j ↦ inr. (fgauto_list_nth_mem V t j) | inr. _ ↦ inl. (refl a) ] ]

def fgauto_mem_tail (V : Type) (v a : V) (t : List V) (n : Not (Id V v a)) (m : FgautoMem V v (cons. a t))
  : FgautoMem V v t
  ≔ match m [ inl. e ↦ absurd (FgautoMem V v t) (n e) | inr. m' ↦ m' ]

def fgauto_list_pos_choose (V : Type) (v a : V) (t : List V) (d : Decidable (Id V v a))
  (recur : FgautoMem V v t → Fin (length V t)) (m : FgautoMem V v (cons. a t)) : Fin (length V (cons. a t))
  ≔ match d [
  | inl. _ ↦ inr. star.
  | inr. n ↦ inl. (recur (fgauto_mem_tail V v a t n m)) ]

def fgauto_list_pos (V : Type) (dV : DecidableEquality V) (v : V) (l : List V) (m : FgautoMem V v l) : Fin (length V l)
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ fgauto_list_pos_choose V v a t (dV v a) (fgauto_list_pos V dV v t) m ]

def fgauto_list_pos_choose_nth (V : Type) (v a : V) (t : List V) (d : Decidable (Id V v a))
  (recur : FgautoMem V v t → Fin (length V t))
  (ih : (m : FgautoMem V v t) → Id V (fgauto_list_nth V t (recur m)) v) (m : FgautoMem V v (cons. a t))
  : Id V (fgauto_list_nth V (cons. a t) (fgauto_list_pos_choose V v a t d recur m)) v
  ≔ match d [
  | inl. e ↦ inverse V v a e
  | inr. n ↦ ih (fgauto_mem_tail V v a t n m) ]

def fgauto_list_pos_nth (V : Type) (dV : DecidableEquality V) (v : V) (l : List V) (m : FgautoMem V v l)
  : Id V (fgauto_list_nth V l (fgauto_list_pos V dV v l m)) v
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ fgauto_list_pos_choose_nth V v a t (dV v a) (fgauto_list_pos V dV v t) (fgauto_list_pos_nth V dV v t) m ]

def fgauto_list_nth_pos_choose (V : Type) (a : V) (t : List V) (j : Fin (length V t)) (d : Decidable (Id V (fgauto_list_nth V t j) a))
  (recur : FgautoMem V (fgauto_list_nth V t j) t → Fin (length V t))
  (ih : (m : FgautoMem V (fgauto_list_nth V t j) t) → Id (Fin (length V t)) (recur m) j)
  (ha : Not (FgautoMem V a t)) (m : FgautoMem V (fgauto_list_nth V t j) (cons. a t))
  : Id (Fin (length V (cons. a t))) (fgauto_list_pos_choose V (fgauto_list_nth V t j) a t d recur m) (inl. j)
  ≔ match d [
  | inl. e ↦ match ha (fgauto_mem_transport V (fgauto_list_nth V t j) a t e (fgauto_list_nth_mem V t j)) []
  | inr. n ↦ inl. (ih (fgauto_mem_tail V (fgauto_list_nth V t j) a t n m)) ]

def fgauto_list_nth_pos_head (V : Type) (a : V) (t : List V) (d : Decidable (Id V a a))
  (recur : FgautoMem V a t → Fin (length V t)) (m : FgautoMem V a (cons. a t))
  : Id (Fin (length V (cons. a t))) (fgauto_list_pos_choose V a a t d recur m) (inr. star.)
  ≔ match d [ inl. _ ↦ refl (inr. star. : Fin (length V (cons. a t))) | inr. n ↦ match n (refl a) [] ]

def fgauto_list_nth_pos (V : Type) (dV : DecidableEquality V) (l : List V) (h : FgautoNoDup V l) (i : Fin (length V l))
  (m : FgautoMem V (fgauto_list_nth V l i) l) : Id (Fin (length V l)) (fgauto_list_pos V dV (fgauto_list_nth V l i) l m) i
  ≔ match l [
  | nil. ↦ match i []
  | cons. a t ↦ match i [
    | inl. j ↦ fgauto_list_nth_pos_choose V a t j (dV (fgauto_list_nth V t j) a) (fgauto_list_pos V dV (fgauto_list_nth V t j) t)
        (fgauto_list_nth_pos V dV t (h .snd) j) (h .fst) m
    | inr. u ↦ match u [ star. ↦ fgauto_list_nth_pos_head V a t (dV a a) (fgauto_list_pos V dV a t) m ] ] ]

{` {v | v in l} has exactly length(l) elements when l has no repetitions. `}
def fgauto_list_set_fin_equiv (V : Type) (dV : DecidableEquality V) (l : List V) (h : FgautoNoDup V l)
  : Equiv (FgautoListSet V l) (Fin (length V l))
  ≔ let pick ≔ (u : FgautoListSet V l) ↦ decidable_pick (FgautoMem V (u .fst) l) (fgauto_mem_decide V dV (u .fst) l) (u .snd) in
    quasi_inverse_equiv (FgautoListSet V l) (Fin (length V l))
      (u ↦ fgauto_list_pos V dV (u .fst) l (pick u))
      (i ↦ (fgauto_list_nth V l i, mere (FgautoMem V (fgauto_list_nth V l i) l) (fgauto_list_nth_mem V l i)))
      (u ↦ fgauto_list_set_path V l
        (fgauto_list_nth V l (fgauto_list_pos V dV (u .fst) l (pick u)),
         mere (FgautoMem V (fgauto_list_nth V l (fgauto_list_pos V dV (u .fst) l (pick u))) l)
           (fgauto_list_nth_mem V l (fgauto_list_pos V dV (u .fst) l (pick u))))
        u (fgauto_list_pos_nth V dV (u .fst) l (pick u)))
      (i ↦ fgauto_list_nth_pos V dV l h i
        (decidable_pick (FgautoMem V (fgauto_list_nth V l i) l) (fgauto_mem_decide V dV (fgauto_list_nth V l i) l)
          (mere (FgautoMem V (fgauto_list_nth V l i) l) (fgauto_list_nth_mem V l i))))

def fgauto_list_set_decidable_equality (V : Type) (dV : DecidableEquality V) (l : List V)
  : DecidableEquality (FgautoListSet V l)
  ≔ u w ↦ match dV (u .fst) (w .fst) [
  | inl. p ↦ inl. (fgauto_list_set_path V l u w p)
  | inr. n ↦ inr. (q ↦ n (refl ((z ↦ z .fst) : FgautoListSet V l → V) q)) ]

{` The vertices of S(H): every one is reachable from the base. `}
def FgautoStallingsVertex (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : Type
  ≔ FgautoListSet (SignedWord S) (fgauto_stallings_vertices S dec gens)

def fgauto_stallings_vertices_nodup (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoNoDup (SignedWord S) (fgauto_stallings_vertices S dec gens)
  ≔ fgauto_dedup_nodup (SignedWord S) (signed_word_decidable_equality S dec)
      (cons. (fgauto_stallings_base S dec gens) (fgauto_endpoints S (SignedWord S) (fgauto_stallings_edges S dec gens)))

def fgauto_stallings_vertex_count_equiv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : Equiv (FgautoStallingsVertex S dec gens) (Fin (fgauto_stallings_vertex_count S dec gens))
  ≔ fgauto_list_set_fin_equiv (SignedWord S) (signed_word_decidable_equality S dec) (fgauto_stallings_vertices S dec gens)
      (fgauto_stallings_vertices_nodup S dec gens)

def fgauto_endpoints_mem_step (S V : Type) (E : List (FgautoEdge S V)) (v : V) (m : FgautoMem V v (fgauto_endpoints S V E))
  : Σ V (p ↦ Σ (SignedLetter S) (x ↦ Σ V (q ↦ Product (FgautoStep S V E p x q) (Sum (Id V v p) (Id V v q)))))
  ≔ match E [
  | nil. ↦ match m []
  | cons. e E' ↦ match m [
    | inl. a ↦ (e .src, (e .lab, (e .tgt, (fgauto_step_head S V e E', inl. a))))
    | inr. m' ↦ match m' [
      | inl. a ↦ (e .src, (e .lab, (e .tgt, (fgauto_step_head S V e E', inr. a))))
      | inr. m'' ↦
        let z ≔ fgauto_endpoints_mem_step S V E' v m'' in
        (z .fst, (z .snd .fst, (z .snd .snd .fst, (inr. (z .snd .snd .snd .fst), z .snd .snd .snd .snd)))) ] ] ]

def fgauto_stallings_vertex_reachable (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (v : SignedWord S) (m : FgautoMem (SignedWord S) v (fgauto_stallings_vertices S dec gens))
  : Σ (SignedWord S) (w ↦ FgautoRun S (SignedWord S) (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens) w v)
  ≔ let E ≔ fgauto_stallings_edges S dec gens in
    let b ≔ fgauto_stallings_base S dec gens in
    let hr ≔ fgauto_stallings_sources_reachable S dec gens in
    match fgauto_dedup_mem_elim (SignedWord S) (signed_word_decidable_equality S dec) v
      (cons. b (fgauto_endpoints S (SignedWord S) E)) m [
    | inl. e ↦ (nil., fgauto_wsym S v b e)
    | inr. m' ↦
      let z ≔ fgauto_endpoints_mem_step S (SignedWord S) E v m' in
      let p ≔ z .fst in
      let x ≔ z .snd .fst in
      let q ≔ z .snd .snd .fst in
      let s ≔ z .snd .snd .snd .fst in
      match z .snd .snd .snd .snd [
      | inl. e ↦ let r ≔ hr p x q s in (r .fst, fgauto_run_end S (SignedWord S) E b (r .fst) p v (fgauto_wsym S v p e) (r .snd))
      | inr. e ↦
        let r ≔ hr q (letter_complement S x) p (fgauto_stallings_symmetric S dec gens p x q s) in
        (r .fst, fgauto_run_end S (SignedWord S) E b (r .fst) q v (fgauto_wsym S v q e) (r .snd)) ] ]

{` Endpoints of S(H) are vertices. `}
def fgauto_stallings_endpoint_vertex (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (p : SignedWord S) (x : SignedLetter S) (q : SignedWord S)
  (s : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) p x q)
  : Product (FgautoMem (SignedWord S) p (fgauto_stallings_vertices S dec gens))
      (FgautoMem (SignedWord S) q (fgauto_stallings_vertices S dec gens))
  ≔ let E ≔ fgauto_stallings_edges S dec gens in
    let l : List (SignedWord S) ≔ cons. (fgauto_stallings_base S dec gens) (fgauto_endpoints S (SignedWord S) E) in
    let ends ≔ fgauto_endpoints_in S (SignedWord S) E p x q s in
    (fgauto_dedup_mem_intro (SignedWord S) (signed_word_decidable_equality S dec) p l (inr. (ends .fst)),
     fgauto_dedup_mem_intro (SignedWord S) (signed_word_decidable_equality S dec) q l (inr. (ends .snd)))

def fgauto_stallings_base_vertex (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoMem (SignedWord S) (fgauto_stallings_base S dec gens) (fgauto_stallings_vertices S dec gens)
  ≔ fgauto_dedup_mem_intro (SignedWord S) (signed_word_decidable_equality S dec) (fgauto_stallings_base S dec gens)
      (cons. (fgauto_stallings_base S dec gens) (fgauto_endpoints S (SignedWord S) (fgauto_stallings_edges S dec gens)))
      (inl. (refl (fgauto_stallings_base S dec gens)))
