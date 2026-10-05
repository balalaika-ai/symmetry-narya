export "1152-fgauto-folding"

{` Chapter 11, automata part 4: the Stallings automaton S(H) and the
   theorem at fggroups.tex:839, the generalized word problem
   (corollary at fggroups.tex:932) and the claims at fggroups.tex:914-922.

   Termination of folding: the endpoints of the bouquet, listed with
   repetitions, give a list Vs containing every endpoint; folding the
   conflict p -x-> q, p -x-> q' (q /= q') replaces Vs by Vs without q', which
   is strictly shorter and still contains every endpoint.  Hence with fuel
   length(Vs) the folded graph has no conflict, i.e. it is deterministic
   (fgauto_stallings_deterministic). `}

{` Endpoints and removal from a list. `}
def fgauto_endpoints (S V : Type) (E : List (FgautoEdge S V)) : List V
  ≔ match E [ nil. ↦ nil. | cons. e E' ↦ cons. (e .src) (cons. (e .tgt) (fgauto_endpoints S V E')) ]

def FgautoEndpointsIn (S V : Type) (E : List (FgautoEdge S V)) (Vs : List V) : Type
  ≔ (p : V) (x : SignedLetter S) (q : V) → FgautoStep S V E p x q → Product (FgautoMem V p Vs) (FgautoMem V q Vs)

def fgauto_endpoints_in (S V : Type) (E : List (FgautoEdge S V)) : FgautoEndpointsIn S V E (fgauto_endpoints S V E)
  ≔ p x q s ↦ match E [
  | nil. ↦ match s []
  | cons. e E' ↦ match s [
    | inl. t ↦ (inl. (t .fst), inr. (inl. (t .snd .snd)))
    | inr. s' ↦
      let z ≔ fgauto_endpoints_in S V E' p x q s' in
      (inr. (inr. (z .fst)), inr. (inr. (z .snd))) ] ]

def fgauto_mem_transport (V : Type) (a a' : V) (l : List V) (e : Id V a a') (m : FgautoMem V a l) : FgautoMem V a' l
  ≔ transport V (z ↦ FgautoMem V z l) a a' e m

def fgauto_remove_choose (V : Type) (a b : V) (d : Decidable (Id V b a)) (rest : List V) : List V
  ≔ match d [ inl. _ ↦ rest | inr. _ ↦ cons. b rest ]

def fgauto_remove (V : Type) (dV : DecidableEquality V) (a : V) (l : List V) : List V
  ≔ match l [ nil. ↦ nil. | cons. b t ↦ fgauto_remove_choose V a b (dV b a) (fgauto_remove V dV a t) ]

def fgauto_remove_choose_mem (V : Type) (a b v : V) (d : Decidable (Id V b a)) (rest t : List V)
  (ih : FgautoMem V v t → FgautoMem V v rest) (na : Not (Id V v a)) (m : FgautoMem V v (cons. b t))
  : FgautoMem V v (fgauto_remove_choose V a b d rest)
  ≔ match d [
  | inl. e ↦ match m [
    | inl. vb ↦ match na (concat V v b a vb e) []
    | inr. m' ↦ ih m' ]
  | inr. _ ↦ match m [ inl. vb ↦ inl. vb | inr. m' ↦ inr. (ih m') ] ]

def fgauto_remove_mem (V : Type) (dV : DecidableEquality V) (a v : V) (l : List V) (na : Not (Id V v a))
  (m : FgautoMem V v l) : FgautoMem V v (fgauto_remove V dV a l)
  ≔ match l [
  | nil. ↦ match m []
  | cons. b t ↦ fgauto_remove_choose_mem V a b v (dV b a) (fgauto_remove V dV a t) t
      (fgauto_remove_mem V dV a v t na) na m ]

def fgauto_remove_choose_le (V : Type) (a b : V) (d : Decidable (Id V b a)) (rest : List V) (t : List V)
  (ih : Le (length V rest) (length V t)) : Le (length V (fgauto_remove_choose V a b d rest)) (suc. (length V t))
  ≔ match d [ inl. _ ↦ le_step (length V rest) (length V t) ih | inr. _ ↦ ih ]

def fgauto_remove_le (V : Type) (dV : DecidableEquality V) (a : V) (l : List V)
  : Le (length V (fgauto_remove V dV a l)) (length V l)
  ≔ match l [
  | nil. ↦ star.
  | cons. b t ↦ fgauto_remove_choose_le V a b (dV b a) (fgauto_remove V dV a t) t (fgauto_remove_le V dV a t) ]

def fgauto_remove_choose_lt (V : Type) (a b : V) (d : Decidable (Id V b a)) (rest t : List V)
  (le : Le (length V rest) (length V t)) (ih : FgautoMem V a t → Lt (length V rest) (length V t))
  (m : FgautoMem V a (cons. b t)) : Lt (length V (fgauto_remove_choose V a b d rest)) (suc. (length V t))
  ≔ match d [
  | inl. _ ↦ le
  | inr. n ↦ match m [
    | inl. ab ↦ match n (inverse V a b ab) []
    | inr. m' ↦ ih m' ] ]

def fgauto_remove_lt (V : Type) (dV : DecidableEquality V) (a : V) (l : List V) (m : FgautoMem V a l)
  : Lt (length V (fgauto_remove V dV a l)) (length V l)
  ≔ match l [
  | nil. ↦ match m []
  | cons. b t ↦ fgauto_remove_choose_lt V a b (dV b a) (fgauto_remove V dV a t) t (fgauto_remove_le V dV a t)
      (fgauto_remove_lt V dV a t) m ]

{` Merging keeps endpoints inside the shortened vertex list. `}
def fgauto_merge_choose_mem (S : Type) (a b v : SignedWord S) (Vs : List (SignedWord S))
  (rem : List (SignedWord S))
  (ha : FgautoMem (SignedWord S) a rem) (hv : Not (Id (SignedWord S) v b) → FgautoMem (SignedWord S) v rem)
  (d : Decidable (Id (SignedWord S) v b)) : FgautoMem (SignedWord S) (fgauto_merge_choose S a b v d) rem
  ≔ match d [ inl. _ ↦ ha | inr. n ↦ hv n ]

def fgauto_merge_mem (S : Type) (dec : DecidableEquality S) (a b v : SignedWord S) (Vs : List (SignedWord S))
  (nab : Not (Id (SignedWord S) a b)) (ha : FgautoMem (SignedWord S) a Vs) (hv : FgautoMem (SignedWord S) v Vs)
  : FgautoMem (SignedWord S) (fgauto_merge S dec a b v) (fgauto_remove (SignedWord S) (signed_word_decidable_equality S dec) b Vs)
  ≔ fgauto_merge_choose_mem S a b v Vs (fgauto_remove (SignedWord S) (signed_word_decidable_equality S dec) b Vs)
      (fgauto_remove_mem (SignedWord S) (signed_word_decidable_equality S dec) b a Vs nab ha)
      (n ↦ fgauto_remove_mem (SignedWord S) (signed_word_decidable_equality S dec) b v Vs n hv)
      (signed_word_decidable_equality S dec v b)

def fgauto_merge_endpoints (S : Type) (dec : DecidableEquality S) (E : List (FgautoEdge S (SignedWord S)))
  (Vs : List (SignedWord S)) (hV : FgautoEndpointsIn S (SignedWord S) E Vs) (c : FgautoConflict S (SignedWord S) E)
  : FgautoEndpointsIn S (SignedWord S)
      (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_remove (SignedWord S) (signed_word_decidable_equality S dec) (c .ctgt2) Vs)
  ≔ p' x q' s ↦
    let f ≔ fgauto_merge S dec (c .ctgt1) (c .ctgt2) in
    let rem ≔ fgauto_remove (SignedWord S) (signed_word_decidable_equality S dec) (c .ctgt2) Vs in
    let z ≔ fgauto_step_map_preimage S (SignedWord S) (SignedWord S) f E p' x q' s in
    let ends ≔ hV (z .fst) x (z .snd .fst) (z .snd .snd .fst) in
    let ha ≔ hV (c .csrc) (c .clab) (c .ctgt1) (c .cstep1) .snd in
    (fgauto_mem_transport (SignedWord S) (f (z .fst)) p' rem (fgauto_wsym S p' (f (z .fst)) (z .snd .snd .snd .fst))
       (fgauto_merge_mem S dec (c .ctgt1) (c .ctgt2) (z .fst) Vs (c .cdistinct) ha (ends .fst)),
     fgauto_mem_transport (SignedWord S) (f (z .snd .fst)) q' rem
       (fgauto_wsym S q' (f (z .snd .fst)) (z .snd .snd .snd .snd))
       (fgauto_merge_mem S dec (c .ctgt1) (c .ctgt2) (z .snd .fst) Vs (c .cdistinct) ha (ends .snd)))

{` Enough fuel makes the folded graph deterministic. `}
def fgauto_mem_length_zero (V : Type) (Vs : List V) (p : V) (hl : Le (length V Vs) zero.) (m : FgautoMem V p Vs)
  : Empty
  ≔ match Vs [ nil. ↦ match m [] | cons. _ _ ↦ match hl [] ]

def fgauto_fold_det_step (S : Type) (dec : DecidableEquality S) (f : Nat)
  (recur : (E1 : List (FgautoEdge S (SignedWord S))) (b1 : SignedWord S) (Vs1 : List (SignedWord S))
    → FgautoEndpointsIn S (SignedWord S) E1 Vs1 → Le (length (SignedWord S) Vs1) f
    → FgautoDeterministic S (SignedWord S) (fgauto_fold S dec f E1 b1 .fst))
  (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (Vs : List (SignedWord S))
  (hV : FgautoEndpointsIn S (SignedWord S) E Vs) (hl : Le (length (SignedWord S) Vs) (suc. f))
  (d : Sum (FgautoConflict S (SignedWord S) E) (FgautoDeterministic S (SignedWord S) E))
  : FgautoDeterministic S (SignedWord S) (fgauto_fold_step S dec (fgauto_fold S dec f) E b d .fst)
  ≔ match d [
  | inr. hd ↦ hd
  | inl. c ↦
    let rem ≔ fgauto_remove (SignedWord S) (signed_word_decidable_equality S dec) (c .ctgt2) Vs in
    recur (fgauto_map_edges S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E)
      (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b) rem
      (fgauto_merge_endpoints S dec E Vs hV c)
      (le_trans (suc. (length (SignedWord S) rem)) (length (SignedWord S) Vs) (suc. f)
        (fgauto_remove_lt (SignedWord S) (signed_word_decidable_equality S dec) (c .ctgt2) Vs
          (hV (c .csrc) (c .clab) (c .ctgt2) (c .cstep2) .snd))
        hl) ]

def fgauto_fold_deterministic (S : Type) (dec : DecidableEquality S) (fuel : Nat)
  (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) (Vs : List (SignedWord S))
  (hV : FgautoEndpointsIn S (SignedWord S) E Vs) (hl : Le (length (SignedWord S) Vs) fuel)
  : FgautoDeterministic S (SignedWord S) (fgauto_fold S dec fuel E b .fst)
  ≔ match fuel [
  | zero. ↦ p x q q' s s' ↦ match fgauto_mem_length_zero (SignedWord S) Vs p hl (hV p x q s .fst) []
  | suc. f ↦ fgauto_fold_det_step S dec f (fgauto_fold_deterministic S dec f) E b Vs hV hl
      (fgauto_conflict_search S (SignedWord S) dec (signed_word_decidable_equality S dec) E) ]

{` The Stallings automaton S(H) of H = <gens>: edges and base vertex. `}
def fgauto_stallings_fuel (S : Type) (gens : List (SignedWord S)) : Nat
  ≔ length (SignedWord S) (fgauto_endpoints S (SignedWord S) (fgauto_bouquet S gens))

def fgauto_stallings (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : FgautoPointedGraph S
  ≔ fgauto_fold S dec (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil.

def fgauto_stallings_edges (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : List (FgautoEdge S (SignedWord S))
  ≔ fgauto_stallings S dec gens .fst

def fgauto_stallings_base (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : SignedWord S
  ≔ fgauto_stallings S dec gens .snd

{` S(H) is deterministic, inverse, satisfies the coset invariant, and
   reads every generator as a loop at the base. `}
def fgauto_stallings_deterministic (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoDeterministic S (SignedWord S) (fgauto_stallings_edges S dec gens)
  ≔ fgauto_fold_deterministic S dec (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil.
      (fgauto_endpoints S (SignedWord S) (fgauto_bouquet S gens))
      (fgauto_endpoints_in S (SignedWord S) (fgauto_bouquet S gens))
      (le_refl (fgauto_stallings_fuel S gens))

def fgauto_stallings_symmetric (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoSymmetric S (SignedWord S) (fgauto_stallings_edges S dec gens)
  ≔ fgauto_fold_ind S dec (E b ↦ FgautoSymmetric S (SignedWord S) E)
      (E b c h ↦ fgauto_map_symmetric S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E h)
      (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil.
      (fgauto_symmetrize_symmetric S (SignedWord S) (fgauto_petals S gens))

def FgautoCosetInv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (E : List (FgautoEdge S (SignedWord S))) (b : SignedWord S) : Type
  ≔ Product (FgautoEdgeInv S dec gens E) (FgautoSameCoset S dec gens b nil.)

def fgauto_stallings_coset_inv (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoCosetInv S dec gens (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens)
  ≔ fgauto_fold_ind S dec (FgautoCosetInv S dec gens)
      (E b c h ↦ (fgauto_merge_inv S dec gens E (h .fst) (c .ctgt1) (c .ctgt2) (fgauto_conflict_coset S dec gens E (h .fst) c),
        fgauto_same_coset_trans S dec gens (fgauto_merge S dec (c .ctgt1) (c .ctgt2) b) b nil.
          (fgauto_merge_coset S dec gens (c .ctgt1) (c .ctgt2) b (fgauto_conflict_coset S dec gens E (h .fst) c))
          (h .snd)))
      (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil.
      (fgauto_bouquet_inv S dec gens, fgauto_same_coset_refl S dec gens nil.)

def FgautoGeneratorLoops (S : Type) (gens : List (SignedWord S)) (E : List (FgautoEdge S (SignedWord S)))
  (b : SignedWord S) : Type
  ≔ (g : SignedWord S) → FgautoMem (SignedWord S) g gens → FgautoRun S (SignedWord S) E b g b

def fgauto_stallings_loops (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoGeneratorLoops S gens (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens)
  ≔ fgauto_fold_ind S dec (FgautoGeneratorLoops S gens)
      (E b c h g m ↦ fgauto_run_map S (SignedWord S) (SignedWord S) (fgauto_merge S dec (c .ctgt1) (c .ctgt2)) E b g b (h g m))
      (fgauto_stallings_fuel S gens) (fgauto_bouquet S gens) nil. (fgauto_bouquet_loop S gens)

{` Words in the generators label loops at the base. `}
def fgauto_gen_eval_run (S : Type) (gens : List (SignedWord S)) (E : List (FgautoEdge S (SignedWord S)))
  (b : SignedWord S) (hs : FgautoSymmetric S (SignedWord S) E) (hl : FgautoGeneratorLoops S gens E b)
  (h : SignedWord (FgautoGen S gens)) : FgautoRun S (SignedWord S) E b (fgauto_gen_eval S gens h) b
  ≔ match h [
  | nil. ↦ refl b
  | cons. x t ↦ fgauto_run_append S (SignedWord S) E b (fgauto_gen_letter_eval S gens x) b (fgauto_gen_eval S gens t) b
      (match x [
       | inl. g ↦ hl (g .fst) (g .snd)
       | inr. g ↦ fgauto_run_inverse S (SignedWord S) E hs b (g .fst) b (hl (g .fst) (g .snd)) ])
      (fgauto_gen_eval_run S gens E b hs hl t) ]

{` Acceptance by the (deterministic) Stallings automaton: running it from
   the base on w ends at the base. `}
def fgauto_vertex_option_decidable_equality (S : Type) (dec : DecidableEquality S)
  : DecidableEquality (Sum Unit (SignedWord S))
  ≔ sum_decidable_equality Unit (SignedWord S) (x y ↦ inl. (unit_prop x y)) (signed_word_decidable_equality S dec)

def fgauto_vertex_option_set (S : Type) (dec : DecidableEquality S) : isSet (Sum Unit (SignedWord S))
  ≔ sum_set Unit (SignedWord S) unit_set (signed_word_set S dec)

def fgauto_stallings_run (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S)
  : Sum Unit (SignedWord S)
  ≔ fgauto_delta S (SignedWord S) dec (signed_word_decidable_equality S dec) (fgauto_stallings_edges S dec gens)
      (fgauto_stallings_base S dec gens) w

def FgautoStallingsAccepts (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S) : Type
  ≔ Id (Sum Unit (SignedWord S)) (fgauto_stallings_run S dec gens w) (inr. (fgauto_stallings_base S dec gens))

def fgauto_stallings_accepts_prop (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S)
  : isProp (FgautoStallingsAccepts S dec gens w)
  ≔ fgauto_vertex_option_set S dec (fgauto_stallings_run S dec gens w) (inr. (fgauto_stallings_base S dec gens))

{` "Recognized" in the sense of a run labelled w from the base to the base;
   for S(H) this is equivalent to acceptance (determinism). `}
def FgautoStallingsRecognizes (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S)
  : Type
  ≔ FgautoRun S (SignedWord S) (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens) w
      (fgauto_stallings_base S dec gens)

def fgauto_stallings_accepts_recognizes (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (w : SignedWord S)
  : Product (FgautoStallingsAccepts S dec gens w → FgautoStallingsRecognizes S dec gens w)
      (FgautoStallingsRecognizes S dec gens w → FgautoStallingsAccepts S dec gens w)
  ≔ (fgauto_delta_sound S (SignedWord S) dec (signed_word_decidable_equality S dec) (fgauto_stallings_edges S dec gens)
       (fgauto_stallings_base S dec gens) w (fgauto_stallings_base S dec gens),
     fgauto_delta_det S (SignedWord S) dec (signed_word_decidable_equality S dec) (fgauto_stallings_edges S dec gens)
       (fgauto_stallings_deterministic S dec gens) (fgauto_stallings_base S dec gens) w (fgauto_stallings_base S dec gens))

{` fggroups.tex:839.  Let H be the subgroup of F(S) generated by gens and
   u a reduced word.  Then u represents an element of H iff u is
   recognized (accepted) by the Stallings automaton S(H). `}
def fgauto_recognized_member (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (u : SignedWord S)
  (r : FgautoStallingsRecognizes S dec gens u) : FgautoInSubgroup S dec gens u
  ≔ fgauto_run_loop_member S dec gens (fgauto_stallings_edges S dec gens) (fgauto_stallings_coset_inv S dec gens .fst)
      (fgauto_stallings_base S dec gens) (fgauto_stallings_coset_inv S dec gens .snd) u r

def fgauto_member_accepted (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (u : SignedWord S)
  (hu : IsReducedWord S u) (m : FgautoInSubgroup S dec gens u) : FgautoStallingsAccepts S dec gens u
  ≔ let E ≔ fgauto_stallings_edges S dec gens in
    let b ≔ fgauto_stallings_base S dec gens in
    let hs ≔ fgauto_stallings_symmetric S dec gens in
    let hd ≔ fgauto_stallings_deterministic S dec gens in
    mere_rec (Σ (SignedWord (FgautoGen S gens)) (h ↦
       Id (SignedWord S) (word_reduction S dec (fgauto_gen_eval S gens h)) (word_reduction S dec u)))
      (FgautoStallingsAccepts S dec gens u) (fgauto_stallings_accepts_prop S dec gens u)
      (z ↦ fgauto_stallings_accepts_recognizes S dec gens u .snd
        (fgauto_run_word S (SignedWord S) E b (word_reduction S dec (fgauto_gen_eval S gens (z .fst))) u b
          (fgauto_wtrans S (word_reduction S dec (fgauto_gen_eval S gens (z .fst))) (word_reduction S dec u) u
            (z .snd) (word_reduction_of_reduced S dec u hu))
          (fgauto_run_reduction S (SignedWord S) dec E hs hd b (fgauto_gen_eval S gens (z .fst)) b
            (fgauto_gen_eval_run S gens E b hs (fgauto_stallings_loops S dec gens) (z .fst))))) m

def fgauto_stallings_recognizes_subgroup (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (u : SignedWord S) (hu : IsReducedWord S u)
  : Product (FgautoInSubgroup S dec gens u → FgautoStallingsRecognizes S dec gens u)
      (FgautoStallingsRecognizes S dec gens u → FgautoInSubgroup S dec gens u)
  ≔ (m ↦ fgauto_stallings_accepts_recognizes S dec gens u .fst (fgauto_member_accepted S dec gens u hu m),
     fgauto_recognized_member S dec gens u)

def fgauto_stallings_accepts_iff_member (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (u : SignedWord S) (hu : IsReducedWord S u)
  : Equiv (FgautoInSubgroup S dec gens u) (FgautoStallingsAccepts S dec gens u)
  ≔ iff_equiv (FgautoInSubgroup S dec gens u) (FgautoStallingsAccepts S dec gens u)
      (fgauto_in_subgroup_prop S dec gens u) (fgauto_stallings_accepts_prop S dec gens u)
      (fgauto_member_accepted S dec gens u hu)
      (a ↦ fgauto_recognized_member S dec gens u (fgauto_stallings_accepts_recognizes S dec gens u .fst a))

{` fggroups.tex:932 (generalized word problem): membership of an arbitrary
   word in a finitely generated subgroup is decidable, by running S(H) on
   the reduction of the word (marginnote 937-941). `}
def fgauto_member_decide_with (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S)
  (d : Decidable (FgautoStallingsAccepts S dec gens (word_reduction S dec w))) : Decidable (FgautoInSubgroup S dec gens w)
  ≔ let rw ≔ word_reduction S dec w in
    match d [
    | inl. a ↦ inl. (fgauto_in_subgroup_red S dec gens rw w (word_reduction_idempotent S dec w)
        (fgauto_recognized_member S dec gens rw (fgauto_stallings_accepts_recognizes S dec gens rw .fst a)))
    | inr. n ↦ inr. (m ↦ n (fgauto_member_accepted S dec gens rw (word_reduction_reduced S dec w)
        (fgauto_in_subgroup_red S dec gens w rw
          (fgauto_wsym S (word_reduction S dec rw) (word_reduction S dec w) (word_reduction_idempotent S dec w)) m))) ]

def fgauto_generalized_word_problem (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (w : SignedWord S) : Decidable (FgautoInSubgroup S dec gens w)
  ≔ fgauto_member_decide_with S dec gens w
      (fgauto_vertex_option_decidable_equality S dec (fgauto_stallings_run S dec gens (word_reduction S dec w))
        (inr. (fgauto_stallings_base S dec gens)))

def fgauto_decision_bool (A : Type) (d : Decidable A) : Bool ≔ match d [ inl. _ ↦ true. | inr. _ ↦ false. ]

def fgauto_decision_bool_true (A : Type) (d : Decidable A) (a : A) : Id Bool (fgauto_decision_bool A d) true.
  ≔ match d [ inl. _ ↦ refl (true. : Bool) | inr. n ↦ match n a [] ]

def fgauto_decision_bool_reflect (A : Type) (d : Decidable A) (t : Id Bool (fgauto_decision_bool A d) true.) : A
  ≔ match d [ inl. a ↦ a | inr. n ↦ match bool_encode false. true. t [] ]

def fgauto_member_bool (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (w : SignedWord S) : Bool
  ≔ fgauto_decision_bool (FgautoInSubgroup S dec gens w) (fgauto_generalized_word_problem S dec gens w)

{` fggroups.tex:914-918: S(H) is an inverse automaton, deterministic in
   both directions (a reverse step q -x-bar-> p is a step of S(H)). `}
def fgauto_stallings_codeterministic (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (q : SignedWord S) (x : SignedLetter S) (p p' : SignedWord S)
  (s : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) p x q)
  (s' : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) p' x q) : Id (SignedWord S) p p'
  ≔ fgauto_stallings_deterministic S dec gens q (letter_complement S x) p p'
      (fgauto_stallings_symmetric S dec gens p x q s) (fgauto_stallings_symmetric S dec gens p' x q s')

{` Vertices of S(H): the base and all endpoints, without repetitions. `}
def fgauto_dedup (V : Type) (dV : DecidableEquality V) (l : List V) : List V
  ≔ match l [ nil. ↦ nil. | cons. x t ↦ cons. x (fgauto_remove V dV x (fgauto_dedup V dV t)) ]

def fgauto_stallings_vertices (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : List (SignedWord S)
  ≔ fgauto_dedup (SignedWord S) (signed_word_decidable_equality S dec)
      (cons. (fgauto_stallings_base S dec gens) (fgauto_endpoints S (SignedWord S) (fgauto_stallings_edges S dec gens)))

def fgauto_stallings_vertex_count (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : Nat
  ≔ length (SignedWord S) (fgauto_stallings_vertices S dec gens)

{` Litmus checks over S = Bool (a = inl false, b = inl true, A, B inverses). `}
def fgauto_w1 (x : SignedLetter Bool) : SignedWord Bool ≔ cons. x nil.
def fgauto_w2 (x y : SignedLetter Bool) : SignedWord Bool ≔ cons. x (cons. y nil.)
def fgauto_w3 (x y z : SignedLetter Bool) : SignedWord Bool ≔ cons. x (cons. y (cons. z nil.))

def fgauto_gens_a : List (SignedWord Bool) ≔ cons. (fgauto_w1 fw_letter_a) nil.
def fgauto_gens_aa_b : List (SignedWord Bool)
  ≔ cons. (fgauto_w2 fw_letter_a fw_letter_a) (cons. (fgauto_w1 fw_letter_b) nil.)
def fgauto_gens_abA_aa : List (SignedWord Bool)
  ≔ cons. (fgauto_w3 fw_letter_a fw_letter_b fw_letter_A) (cons. (fgauto_w2 fw_letter_a fw_letter_a) nil.)

{` a b A is not in <a>; a a is in <a a, b>; b a is not in <a a, b>. `}
def fgauto_litmus_abA_not_in_a
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_a
      (fgauto_w3 fw_letter_a fw_letter_b fw_letter_A)) false.
  ≔ refl (false. : Bool)

def fgauto_litmus_aa_in_aa_b
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_aa_b (fgauto_w2 fw_letter_a fw_letter_a)) true.
  ≔ refl (true. : Bool)

def fgauto_litmus_ba_not_in_aa_b
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_aa_b (fgauto_w2 fw_letter_b fw_letter_a)) false.
  ≔ refl (false. : Bool)

{` A A b a a is in <a a, b> although it is not a product of generators
   letter by letter; the unreduced a b B A a a also is. `}
def fgauto_litmus_AAbaa_in_aa_b
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_aa_b
      (cons. fw_letter_A (cons. fw_letter_A (cons. fw_letter_b (cons. fw_letter_a (cons. fw_letter_a nil.)))))) true.
  ≔ refl (true. : Bool)

{` S(<a a, b>) has two vertices; S(<a>) has one; S(<a b A, a a>) needs a
   fold (the vertices [a b] and [a] are identified) and has two vertices. `}
def fgauto_litmus_vertices_aa_b
  : Id Nat (fgauto_stallings_vertex_count Bool fw_bool_decidable_equality fgauto_gens_aa_b) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)

def fgauto_litmus_vertices_a
  : Id Nat (fgauto_stallings_vertex_count Bool fw_bool_decidable_equality fgauto_gens_a) (suc. zero.)
  ≔ refl (suc. zero. : Nat)

def fgauto_litmus_vertices_abA_aa
  : Id Nat (fgauto_stallings_vertex_count Bool fw_bool_decidable_equality fgauto_gens_abA_aa) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)

{` a b b A = (a b A)(a b A) is in <a b A, a a>, b is not. `}
def fgauto_litmus_abbA_in
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_abA_aa
      (cons. fw_letter_a (cons. fw_letter_b (cons. fw_letter_b (cons. fw_letter_A nil.))))) true.
  ≔ refl (true. : Bool)

def fgauto_litmus_b_not_in
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_abA_aa (fgauto_w1 fw_letter_b)) false.
  ≔ refl (false. : Bool)
