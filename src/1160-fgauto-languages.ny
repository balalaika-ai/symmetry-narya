export "1153-fgauto-stallings"
export "403-abstract-groups"

{` Chapter 11, automata part 11: the language-theoretic notions of the
   section "Connections with automata (*)" (fggroups.tex:866-961), which the
   book uses without definitions.

   - Finite automata over the signed alphabet S~ (FgautoNFA: a finite edge
     list over some state type with decidable equality, an initial state and
     a finite list of final states); the language of a word w is "some run from the initial state to
     a final state reads w".  A language L ⊆ S~* is regular if it is the
     language of a finite automaton (FgautoRegular).
   - Rational subsets of a monoid M (FgautoRational): denotations of
     rational expressions, built from finite subsets by union, product and
     star (FgautoRatExpr).
   - Recognizable subsets of a monoid M (FgautoRecognizable): X = {m |
     q0 . m in F} for a finite right M-set Fin n, a point q0 and a decidable
     subset F (Bool-valued).  For a group G this is "recognisable by a finite
     G-action" (891).
   - The monoids used: the free monoid S~* (words, concatenation), F(S) as
     the reduced words with product rho(u v) (module 866 identifies this
     with USym F(S)), and the monoid underlying an abstract group.
   - Matched homomorphisms (fggroups.tex:889-890): for a map a : S → G into
     a group, alpha~ : S~* → G sends a to a(a) and A to a(a)^-1 (the book
     starts from a monoid hom alpha : S* → G, which is the same as a map on
     letters). `}

def FgautoIff (A B : Type) : Type ≔ Product (A → B) (B → A)

{` Monoids (operations only; laws are added where needed). `}
def FgautoMonoid : Type ≔ sig (mcarrier : Type, munit : mcarrier, mmul : mcarrier → mcarrier → mcarrier)

def fgauto_free_monoid (S : Type) : FgautoMonoid ≔ (SignedWord S, nil., append (SignedLetter S))

def fgauto_reduced_mul (S : Type) (dec : DecidableEquality S) (u v : ReducedWord S) : ReducedWord S
  ≔ (word_reduction S dec (append (SignedLetter S) (u .fst) (v .fst)),
     word_reduction_reduced S dec (append (SignedLetter S) (u .fst) (v .fst)))

def fgauto_free_group_monoid (S : Type) (dec : DecidableEquality S) : FgautoMonoid
  ≔ (ReducedWord S, reduced_word_empty S, fgauto_reduced_mul S dec)

def fgauto_group_monoid (G : AbstractGroup) : FgautoMonoid ≔ (G .carrier, G .unit, G .mul)

def fgauto_list_product (M : FgautoMonoid) (l : List (M .mcarrier)) : M .mcarrier
  ≔ match l [ nil. ↦ M .munit | cons. a t ↦ M .mmul a (fgauto_list_product M t) ]

def FgautoAllIn (A : Type) (P : A → Type) (l : List A) : Type
  ≔ match l [ nil. ↦ Unit | cons. a t ↦ Product (P a) (FgautoAllIn A P t) ]

{` Rational expressions and rational subsets. `}
def FgautoRatExpr (M : Type) : Type ≔ data [
| rat_fin. (_ : List M)
| rat_union. (_ : FgautoRatExpr M) (_ : FgautoRatExpr M)
| rat_prod. (_ : FgautoRatExpr M) (_ : FgautoRatExpr M)
| rat_star. (_ : FgautoRatExpr M) ]

def fgauto_rat_mem (M : FgautoMonoid) (r : FgautoRatExpr (M .mcarrier)) (m : M .mcarrier) : Type
  ≔ match r [
  | rat_fin. l ↦ Mere (FgautoMem (M .mcarrier) m l)
  | rat_union. r1 r2 ↦ Mere (Sum (fgauto_rat_mem M r1 m) (fgauto_rat_mem M r2 m))
  | rat_prod. r1 r2 ↦ Mere (Σ (M .mcarrier) (a ↦ Σ (M .mcarrier) (b ↦
      Product (fgauto_rat_mem M r1 a) (Product (fgauto_rat_mem M r2 b) (Id (M .mcarrier) m (M .mmul a b))))))
  | rat_star. r1 ↦ Mere (Σ (List (M .mcarrier)) (l ↦
      Product (FgautoAllIn (M .mcarrier) (fgauto_rat_mem M r1) l) (Id (M .mcarrier) m (fgauto_list_product M l)))) ]

def fgauto_rat_mem_prop (M : FgautoMonoid) (r : FgautoRatExpr (M .mcarrier)) (m : M .mcarrier)
  : isProp (fgauto_rat_mem M r m)
  ≔ match r [
  | rat_fin. l ↦ mere_isprop (FgautoMem (M .mcarrier) m l)
  | rat_union. r1 r2 ↦ mere_isprop (Sum (fgauto_rat_mem M r1 m) (fgauto_rat_mem M r2 m))
  | rat_prod. r1 r2 ↦ mere_isprop (Σ (M .mcarrier) (a ↦ Σ (M .mcarrier) (b ↦
      Product (fgauto_rat_mem M r1 a) (Product (fgauto_rat_mem M r2 b) (Id (M .mcarrier) m (M .mmul a b))))))
  | rat_star. r1 ↦ mere_isprop (Σ (List (M .mcarrier)) (l ↦
      Product (FgautoAllIn (M .mcarrier) (fgauto_rat_mem M r1) l) (Id (M .mcarrier) m (fgauto_list_product M l)))) ]

def FgautoRational (M : FgautoMonoid) (X : M .mcarrier → Type) : Type
  ≔ Mere (Σ (FgautoRatExpr (M .mcarrier)) (r ↦ (m : M .mcarrier) → FgautoIff (X m) (fgauto_rat_mem M r m)))

{` Recognizable subsets: finite right actions. `}
def FgautoFiniteAction (M : FgautoMonoid) : Type ≔ sig (
  asize : Nat,
  aact : Fin asize → M .mcarrier → Fin asize,
  aunit : (q : Fin asize) → Id (Fin asize) (aact q (M .munit)) q,
  amul : (q : Fin asize) (m m' : M .mcarrier) → Id (Fin asize) (aact q (M .mmul m m')) (aact (aact q m) m'))

def FgautoRecognizes (M : FgautoMonoid) (A : FgautoFiniteAction M) (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool)
  (X : M .mcarrier → Type) : Type
  ≔ (m : M .mcarrier) → FgautoIff (X m) (Id Bool (F (A .aact q0 m)) true.)

def FgautoRecognizable (M : FgautoMonoid) (X : M .mcarrier → Type) : Type
  ≔ Mere (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦
       FgautoRecognizes M A q0 F X))))

{` Finite automata over S~ and regular languages. `}
def FgautoNFA (S : Type) : Type ≔ sig (
  nstate : Type,
  ndec : DecidableEquality nstate,
  nedges : List (FgautoEdge S nstate),
  ninit : nstate,
  nfinal : List nstate)

def FgautoNFAAccepts (S : Type) (A : FgautoNFA S) (w : SignedWord S) : Type
  ≔ Mere (Σ (A .nstate) (f ↦ Product (FgautoMem (A .nstate) f (A .nfinal)) (FgautoRun S (A .nstate) (A .nedges) (A .ninit) w f)))

def FgautoRegular (S : Type) (L : SignedWord S → Type) : Type
  ≔ Mere (Σ (FgautoNFA S) (A ↦ (w : SignedWord S) → FgautoIff (L w) (FgautoNFAAccepts S A w)))

{` The image rho(L) and the language iota(X) of reduced words of X ⊆ F(S). `}
def FgautoReductionImage (S : Type) (dec : DecidableEquality S) (L : SignedWord S → Type) (w : SignedWord S) : Type
  ≔ Mere (Σ (SignedWord S) (v ↦ Product (L v) (Id (SignedWord S) (word_reduction S dec v) w)))

def FgautoIotaImage (S : Type) (X : ReducedWord S → Type) (w : SignedWord S) : Type
  ≔ Σ (IsReducedWord S w) (h ↦ X (w, h))

{` Matched homomorphisms. `}
def fgauto_matched_letter (S : Type) (G : AbstractGroup) (a : S → G .carrier) (x : SignedLetter S) : G .carrier
  ≔ match x [ inl. s ↦ a s | inr. s ↦ G .inv (a s) ]

def fgauto_matched_hom (S : Type) (G : AbstractGroup) (a : S → G .carrier) (w : SignedWord S) : G .carrier
  ≔ match w [ nil. ↦ G .unit | cons. x t ↦ G .mul (fgauto_matched_letter S G a x) (fgauto_matched_hom S G a t) ]

def FgautoGeneratesGroup (S : Type) (G : AbstractGroup) (a : S → G .carrier) : Type
  ≔ (g : G .carrier) → Mere (Σ (SignedWord S) (w ↦ Id (G .carrier) (fgauto_matched_hom S G a w) g))

def FgautoPreimage (S : Type) (G : AbstractGroup) (a : S → G .carrier) (X : G .carrier → Type) (w : SignedWord S) : Type
  ≔ X (fgauto_matched_hom S G a w)

{` Litmus checks: a star expression contains a a; the one-state automaton
   with an a-loop accepts a a and rejects b; the matched homomorphism into
   the integers-free example is checked in later modules. `}
def fgauto_litmus_star_aa
  : fgauto_rat_mem (fgauto_free_monoid Bool) (rat_star. (rat_fin. (cons. (fgauto_w1 fw_letter_a) nil.)))
      (fgauto_w2 fw_letter_a fw_letter_a)
  ≔ let M ≔ fgauto_free_monoid Bool in
    let r1 : FgautoRatExpr (SignedWord Bool) ≔ rat_fin. (cons. (fgauto_w1 fw_letter_a) nil.) in
    let ma : fgauto_rat_mem M r1 (fgauto_w1 fw_letter_a)
      ≔ mere (FgautoMem (SignedWord Bool) (fgauto_w1 fw_letter_a) (cons. (fgauto_w1 fw_letter_a) nil.))
          (inl. (refl (fgauto_w1 fw_letter_a))) in
    mere (Σ (List (SignedWord Bool)) (l ↦
        Product (FgautoAllIn (SignedWord Bool) (fgauto_rat_mem M r1) l)
          (Id (SignedWord Bool) (fgauto_w2 fw_letter_a fw_letter_a) (fgauto_list_product M l))))
      (cons. (fgauto_w1 fw_letter_a) (cons. (fgauto_w1 fw_letter_a) nil.), ((ma, (ma, star.)), refl (fgauto_w2 fw_letter_a fw_letter_a)))

def fgauto_litmus_nfa_a : FgautoNFA Bool ≔ (Unit, (x y ↦ inl. (unit_prop x y)), cons. (star., fw_letter_a, star.) nil., star., cons. star. nil.)

def fgauto_litmus_nfa_accepts_aa : FgautoNFAAccepts Bool fgauto_litmus_nfa_a (fgauto_w2 fw_letter_a fw_letter_a)
  ≔ mere (Σ Unit (f ↦ Product (FgautoMem Unit f (cons. star. nil.))
        (FgautoRun Bool Unit (cons. (star., fw_letter_a, star.) nil.) star. (fgauto_w2 fw_letter_a fw_letter_a) f)))
      (star., (inl. (refl star.),
        (star., (fgauto_step_head Bool Unit (star., fw_letter_a, star.) nil.,
          (star., (fgauto_step_head Bool Unit (star., fw_letter_a, star.) nil., refl star.))))))

def fgauto_litmus_nfa_rejects_b : Not (FgautoNFAAccepts Bool fgauto_litmus_nfa_a (fgauto_w1 fw_letter_b))
  ≔ h ↦ mere_rec (Σ Unit (f ↦ Product (FgautoMem Unit f (cons. star. nil.))
        (FgautoRun Bool Unit (cons. (star., fw_letter_a, star.) nil.) star. (fgauto_w1 fw_letter_b) f)))
      Empty empty_prop
      (z ↦ match z .snd .snd .snd .fst [
       | inl. t ↦ bool_encode true. false. (sum_encode Bool Bool (inl. true.) (inl. false.) (t .snd .fst))
       | inr. k ↦ match k [] ]) h
