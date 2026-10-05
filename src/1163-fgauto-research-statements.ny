export "1162-fgauto-rational-subgroups"
export "1158-fgauto-finite-index"

{` Chapter 11, automata part 14: exact statements of the research-level
   theorems of the section (Sénizergues 885, Chomsky–Schützenberger 896,
   Muller–Schupp 907), with all notions defined, and the parts proved here.

   885 (Sénizergues): "A rational subset of F(S) is either disjunctive or
   recognizable."  Disjunctive: the syntactic congruence (u ≡ v iff
   p u q in X <=> p v q in X for all p, q) is equality.  Stated as
   FgautoSenizerguesStatement (the "or" as a mere disjunction).  Proved
   here: the two cases exclude each other when S is nonempty
   (fgauto_disjunctive_not_recognizable: a finite action identifies two
   distinct powers a^i, a^j).  The dichotomy itself is not proved.

   896 (Chomsky–Schützenberger): as printed "h : T* → S~*" cannot be applied
   to R ∩ D_S ⊆ S~*; the homomorphism must go S~* → T*.  Context-free
   languages are defined by grammars (finitely many nonterminals Fin k, a
   finite list of rules, a derivation step rewrites any occurrence of a
   nonterminal by the right-hand side of one of its rules), D_S is the 2-sided Dyck language
   (rho(w) = eps).  Stated as FgautoChomskySchutzenbergerStatement; not
   proved.

   907 (Muller–Schupp): G is virtually free if it has a normal subgroup of
   finite index which is free (on a finite basis b : T → G: every element of
   the subgroup is the image of exactly one reduced word over T).  Stated as
   FgautoMullerSchuppStatement for f.g. G with surjective matched
   homomorphism alpha~ : S~* → G and ker alpha~ = {w | alpha~(w) = 1}; not
   proved. `}

{` 885. `}
def FgautoSyntacticEquivalent (M : FgautoMonoid) (X : M .mcarrier → Type) (u v : M .mcarrier) : Type
  ≔ (p q : M .mcarrier) → FgautoIff (X (M .mmul (M .mmul p u) q)) (X (M .mmul (M .mmul p v) q))

def FgautoDisjunctive (M : FgautoMonoid) (X : M .mcarrier → Type) : Type
  ≔ (u v : M .mcarrier) → FgautoSyntacticEquivalent M X u v → Id (M .mcarrier) u v

def FgautoSenizerguesStatement (S : Type) (dec : DecidableEquality S) : Type
  ≔ (X : ReducedWord S → Type) → FgautoRational (fgauto_free_group_monoid S dec) X
    → Mere (Sum (FgautoDisjunctive (fgauto_free_group_monoid S dec) X) (FgautoRecognizable (fgauto_free_group_monoid S dec) X))

def fgauto_power_length (S : Type) (x : SignedLetter S) (n : Nat) : Id Nat (length (SignedLetter S) (fgauto_power S x n)) n
  ≔ match n [ zero. ↦ refl (zero. : Nat) | suc. k ↦ suc. (fgauto_power_length S x k) ]

def fgauto_reduced_power (S : Type) (x : SignedLetter S) (n : Nat) : ReducedWord S
  ≔ (fgauto_power S x n, fgauto_power_reduced S x n)

{` Same action => syntactically equivalent. `}
def fgauto_same_action_syntactic (M : FgautoMonoid) (X : M .mcarrier → Type) (A : FgautoFiniteAction M)
  (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool) (hr : FgautoRecognizes M A q0 F X) (u v : M .mcarrier)
  (h : Id (Fin (A .asize) → Fin (A .asize)) (q ↦ A .aact q u) (q ↦ A .aact q v)) : FgautoSyntacticEquivalent M X u v
  ≔ p q ↦
    let N ≔ A .asize in
    let e : Id (Fin N) (A .aact q0 (M .mmul (M .mmul p u) q)) (A .aact q0 (M .mmul (M .mmul p v) q))
      ≔ calc
          A .aact q0 (M .mmul (M .mmul p u) q) = A .aact (A .aact q0 (M .mmul p u)) q by A .amul q0 (M .mmul p u) q
          = A .aact (A .aact (A .aact q0 p) u) q by refl ((y ↦ A .aact y q) : Fin N → Fin N) (A .amul q0 p u)
          = A .aact (A .aact (A .aact q0 p) v) q
            by refl ((y ↦ A .aact y q) : Fin N → Fin N) (happly (Fin N) (_ ↦ Fin N) (y ↦ A .aact y u) (y ↦ A .aact y v) h (A .aact q0 p))
          = A .aact (A .aact q0 (M .mmul p v)) q
            by refl ((y ↦ A .aact y q) : Fin N → Fin N) (inverse (Fin N) (A .aact q0 (M .mmul p v)) (A .aact (A .aact q0 p) v) (A .amul q0 p v))
          = A .aact q0 (M .mmul (M .mmul p v) q)
            by inverse (Fin N) (A .aact q0 (M .mmul (M .mmul p v) q)) (A .aact (A .aact q0 (M .mmul p v)) q) (A .amul q0 (M .mmul p v) q) ∎ in
    (x ↦ hr (M .mmul (M .mmul p v) q) .snd
       (transport (Fin N) (z ↦ Id Bool (F z) true.) (A .aact q0 (M .mmul (M .mmul p u) q)) (A .aact q0 (M .mmul (M .mmul p v) q)) e
         (hr (M .mmul (M .mmul p u) q) .fst x)),
     y ↦ hr (M .mmul (M .mmul p u) q) .snd
       (transport (Fin N) (z ↦ Id Bool (F z) true.) (A .aact q0 (M .mmul (M .mmul p v) q)) (A .aact q0 (M .mmul (M .mmul p u) q))
         (inverse (Fin N) (A .aact q0 (M .mmul (M .mmul p u) q)) (A .aact q0 (M .mmul (M .mmul p v) q)) e)
         (hr (M .mmul (M .mmul p v) q) .fst y)))

def fgauto_power_action (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (A : FgautoFiniteAction (fgauto_free_group_monoid S dec)) (i : Nat) : Fin (A .asize) → Fin (A .asize)
  ≔ q ↦ A .aact q (fgauto_reduced_power S x i)

def fgauto_power_action_mem (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (A : FgautoFiniteAction (fgauto_free_group_monoid S dec)) (i : Nat)
  : FgautoMem (Fin (A .asize) → Fin (A .asize)) (fgauto_power_action S dec x A i)
      (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize))
  ≔ fgauto_fin_functions_complete (Fin (A .asize)) (fgauto_fin_list (A .asize)) (fgauto_fin_list_complete (A .asize)) (A .asize)
      (fgauto_power_action S dec x A i)

def fgauto_power_action_pos (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (A : FgautoFiniteAction (fgauto_free_group_monoid S dec)) (i : Nat)
  : Fin (length (Fin (A .asize) → Fin (A .asize)) (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize)))
  ≔ fgauto_list_pos (Fin (A .asize) → Fin (A .asize)) (fgauto_fin_fun_decidable_equality (A .asize) (A .asize))
      (fgauto_power_action S dec x A i) (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize))
      (fgauto_power_action_mem S dec x A i)

def fgauto_power_action_pos_eq (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (A : FgautoFiniteAction (fgauto_free_group_monoid S dec)) (i j : Nat)
  (e : Id (Fin (length (Fin (A .asize) → Fin (A .asize)) (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize))))
         (fgauto_power_action_pos S dec x A i) (fgauto_power_action_pos S dec x A j))
  : Id (Fin (A .asize) → Fin (A .asize)) (fgauto_power_action S dec x A i) (fgauto_power_action S dec x A j)
  ≔ let V ≔ Fin (A .asize) → Fin (A .asize) in
    let Fs ≔ fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize) in
    let dV ≔ fgauto_fin_fun_decidable_equality (A .asize) (A .asize) in
    concat V (fgauto_power_action S dec x A i) (fgauto_list_nth V Fs (fgauto_power_action_pos S dec x A i)) (fgauto_power_action S dec x A j)
      (inverse V (fgauto_list_nth V Fs (fgauto_power_action_pos S dec x A i)) (fgauto_power_action S dec x A i)
        (fgauto_list_pos_nth V dV (fgauto_power_action S dec x A i) Fs (fgauto_power_action_mem S dec x A i)))
      (concat V (fgauto_list_nth V Fs (fgauto_power_action_pos S dec x A i)) (fgauto_list_nth V Fs (fgauto_power_action_pos S dec x A j))
        (fgauto_power_action S dec x A j)
        (refl (fgauto_list_nth V Fs) e)
        (fgauto_list_pos_nth V dV (fgauto_power_action S dec x A j) Fs (fgauto_power_action_mem S dec x A j)))

def fgauto_powers_equal (S : Type) (x : SignedLetter S) (i j : Nat)
  (e : Id (ReducedWord S) (fgauto_reduced_power S x i) (fgauto_reduced_power S x j)) : Id Nat i j
  ≔ concat Nat i (length (SignedLetter S) (fgauto_power S x i)) j
      (inverse Nat (length (SignedLetter S) (fgauto_power S x i)) i (fgauto_power_length S x i))
      (concat Nat (length (SignedLetter S) (fgauto_power S x i)) (length (SignedLetter S) (fgauto_power S x j)) j
        (refl ((r ↦ length (SignedLetter S) (r .fst)) : ReducedWord S → Nat) e) (fgauto_power_length S x j))

def fgauto_disjunctive_not_recognizable_at (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (X : ReducedWord S → Type)
  (hd : FgautoDisjunctive (fgauto_free_group_monoid S dec) X) (A : FgautoFiniteAction (fgauto_free_group_monoid S dec))
  (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool) (hr : FgautoRecognizes (fgauto_free_group_monoid S dec) A q0 F X) : Empty
  ≔ let K ≔ length (Fin (A .asize) → Fin (A .asize)) (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize)) in
    let col ≔ fin_pigeonhole K (i ↦ fgauto_power_action_pos S dec x A (fin_index (suc. K) i)) in
    let il ≔ fin_index (suc. K) (col .left) in
    let ir ≔ fin_index (suc. K) (col .right) in
    col .distinct (fin_index_injective (suc. K) (col .left) (col .right)
      (fgauto_powers_equal S x il ir
        (hd (fgauto_reduced_power S x il) (fgauto_reduced_power S x ir)
          (fgauto_same_action_syntactic (fgauto_free_group_monoid S dec) X A q0 F hr
            (fgauto_reduced_power S x il) (fgauto_reduced_power S x ir)
            (fgauto_power_action_pos_eq S dec x A il ir (col .same))))))

{` 885, the provable part: no subset of F(S) (S nonempty) is both
   disjunctive and recognizable. `}
def fgauto_disjunctive_not_recognizable (S : Type) (dec : DecidableEquality S) (s0 : S) (X : ReducedWord S → Type)
  (hd : FgautoDisjunctive (fgauto_free_group_monoid S dec) X) (hr : FgautoRecognizable (fgauto_free_group_monoid S dec) X) : Empty
  ≔ let M ≔ fgauto_free_group_monoid S dec in
    mere_rec (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦ FgautoRecognizes M A q0 F X))))
      Empty empty_prop
      (z ↦ fgauto_disjunctive_not_recognizable_at S dec (inl. s0) X hd (z .fst) (z .snd .fst) (z .snd .snd .fst) (z .snd .snd .snd))
      hr

{` 896: context-free grammars and languages. `}
def FgautoGrammar (T : Type) : Type ≔ sig (
  gnonterm : Nat,
  gstart : Fin gnonterm,
  grules : List (Σ (Fin gnonterm) (_ ↦ List (Sum (Fin gnonterm) T))))

def FgautoSentential (T : Type) (Gr : FgautoGrammar T) : Type ≔ List (Sum (Fin (Gr .gnonterm)) T)

def FgautoRewriteStep (T : Type) (Gr : FgautoGrammar T) (a b : FgautoSentential T Gr) : Type
  ≔ Σ (FgautoSentential T Gr) (u ↦ Σ (FgautoSentential T Gr) (v ↦ Σ (Σ (Fin (Gr .gnonterm)) (_ ↦ FgautoSentential T Gr)) (r ↦
      Product (FgautoMem (Σ (Fin (Gr .gnonterm)) (_ ↦ FgautoSentential T Gr)) r (Gr .grules))
        (Product (Id (FgautoSentential T Gr) a (append (Sum (Fin (Gr .gnonterm)) T) u (cons. (inl. (r .fst)) v)))
          (Id (FgautoSentential T Gr) b (append (Sum (Fin (Gr .gnonterm)) T) u (append (Sum (Fin (Gr .gnonterm)) T) (r .snd) v)))))))

def FgautoRewrites (T : Type) (Gr : FgautoGrammar T) (n : Nat) (a b : FgautoSentential T Gr) : Type
  ≔ match n [
  | zero. ↦ Id (FgautoSentential T Gr) a b
  | suc. k ↦ Σ (FgautoSentential T Gr) (c ↦ Product (FgautoRewriteStep T Gr a c) (FgautoRewrites T Gr k c b)) ]

def FgautoGrammarLanguage (T : Type) (Gr : FgautoGrammar T) (w : List T) : Type
  ≔ Mere (Σ Nat (n ↦ FgautoRewrites T Gr n (cons. (inl. (Gr .gstart)) nil.)
       (fgauto_list_map T (Sum (Fin (Gr .gnonterm)) T) (t ↦ inr. t) w)))

def FgautoContextFree (T : Type) (L : List T → Type) : Type
  ≔ Mere (Σ (FgautoGrammar T) (Gr ↦ (w : List T) → FgautoIff (L w) (FgautoGrammarLanguage T Gr w)))

{` Regular languages and homomorphic images over an arbitrary alphabet are
   needed for the statement; regular languages over S~ (module 1160). `}
def fgauto_word_hom (S T : Type) (h : SignedLetter S → List T) (w : SignedWord S) : List T
  ≔ match w [ nil. ↦ nil. | cons. x t ↦ append T (h x) (fgauto_word_hom S T h t) ]

def FgautoDyck (S : Type) (dec : DecidableEquality S) (w : SignedWord S) : Type
  ≔ Id (SignedWord S) (word_reduction S dec w) nil.

def FgautoChomskySchutzenbergerStatement (T : Type) : Type
  ≔ (L : List T → Type) → FgautoIff (FgautoContextFree T L)
      (Mere (Σ Nat (n ↦ Σ (SignedLetter (Fin n) → List T) (h ↦ Σ (SignedWord (Fin n) → Type) (R ↦
         Product (FgautoRegular (Fin n) R)
           ((w : List T) → FgautoIff (L w)
             (Mere (Σ (SignedWord (Fin n)) (v ↦ Product (Product (R v) (FgautoDyck (Fin n) (fin_decidable_equality n) v))
               (Id (List T) (fgauto_word_hom (Fin n) T h v) w))))))))))

{` 907: virtually free groups. `}
def FgautoFreeSubgroupOn (G : AbstractGroup) (N : G .carrier → Type) (T : Type) (b : T → G .carrier) : Type
  ≔ (g : G .carrier) → FgautoIff (N g)
      (isContr (Σ (ReducedWord T) (r ↦ Id (G .carrier) (fgauto_matched_hom T G b (r .fst)) g)))

def FgautoNormalSubset (G : AbstractGroup) (N : G .carrier → Type) : Type
  ≔ (g n : G .carrier) → N n → N (G .mul (G .mul g n) (G .inv g))

def FgautoVirtuallyFree (G : AbstractGroup) : Type
  ≔ Mere (Σ (Subtypes (G .carrier)) (N ↦ Σ (FgautoAbstractSubgroup G N) (hN ↦
       Product (FgautoNormalSubset G (g ↦ N g .fst))
         (Product (FgautoGroupFiniteIndex G N hN)
           (Σ Nat (k ↦ Σ (Fin k → G .carrier) (b ↦ FgautoFreeSubgroupOn G (g ↦ N g .fst) (Fin k) b)))))))

def FgautoMullerSchuppStatement (S : Type) : Type
  ≔ (G : AbstractGroup) (a : S → G .carrier) → FgautoGeneratesGroup S G a
    → FgautoIff (FgautoVirtuallyFree G)
        (FgautoContextFree (SignedLetter S) (w ↦ Id (G .carrier) (fgauto_matched_hom S G a w) (G .unit)))
