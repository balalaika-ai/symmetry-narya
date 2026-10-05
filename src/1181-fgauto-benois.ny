export "1180-fgauto-kleene-correct"

{` Chapter 11, automata part 32: the theorem of Benois (fggroups.tex:874):
   a subset X of F(S) is rational iff iota(X) (its elements as reduced
   words) is a regular language.  "=>" is module 1178; "<=" uses the
   McNaughton–Yamada expressions (modules 1179-1180) in the monoid F(S)
   with the valuation x |-> [x]: the values of the words accepted by an
   automaton for iota(X) are exactly the elements of X. `}

def FgautoImageVal (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (m : M .mcarrier) : Type
  ≔ Mere (Σ (SignedWord S) (w ↦ Product (FgautoNFAAccepts S B w) (Id (M .mcarrier) (fgauto_val_word S M val w) m)))

def fgauto_image_val_prop (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (m : M .mcarrier)
  : isProp (FgautoImageVal S M val B m)
  ≔ mere_isprop (Σ (SignedWord S) (w ↦ Product (FgautoNFAAccepts S B w) (Id (M .mcarrier) (fgauto_val_word S M val w) m)))

{` Restricted runs at level k between listed states are runs. `}
def fgauto_ky_lang_runs (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (f : B .nstate) (mf : FgautoMem (B .nstate) f (fgauto_nfa_states S B)) (m : M .mcarrier)
  : FgautoIff (FgautoKyLang S M val B (fgauto_nfa_k S B) (fgauto_nfa_nth S B (fgauto_nfa_pos S B (B .ninit) (fgauto_nfa_init_state S B)))
        (fgauto_nfa_nth S B (fgauto_nfa_pos S B f mf)) m)
      (Mere (Σ (SignedWord S) (w ↦ Product (FgautoRun S (B .nstate) (B .nedges) (B .ninit) w f) (Id (M .mcarrier) (fgauto_val_word S M val w) m))))
  ≔ let V ≔ B .nstate in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let k ≔ fgauto_nfa_k S B in
    let p0 ≔ fgauto_nfa_nth S B (fgauto_nfa_pos S B (B .ninit) (fgauto_nfa_init_state S B)) in
    let q0 ≔ fgauto_nfa_nth S B (fgauto_nfa_pos S B f mf) in
    let ei ≔ fgauto_nfa_nth_pos S B (B .ninit) (fgauto_nfa_init_state S B) in
    let ef ≔ fgauto_nfa_nth_pos S B f mf in
    let T ≔ Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m)) in
    (h ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B k p0 w q0) (Id C (fgauto_val_word S M val w) m))) (Mere T) (mere_isprop T)
       (z ↦ mere T (z .fst, (fgauto_run_start S V (B .nedges) p0 (B .ninit) (z .fst) f ei
          (fgauto_run_end S V (B .nedges) p0 (z .fst) q0 f ef (fgauto_irun_run S B k p0 (z .fst) q0 (z .snd .fst))), z .snd .snd))) h,
     h ↦ mere_rec T (FgautoKyLang S M val B k p0 q0 m) (fgauto_ky_lang_prop S M val B k p0 q0 m)
       (z ↦ fgauto_ky_lang_intro S M val B k p0 q0 m (z .fst)
         (fgauto_run_irun_all S B p0 (z .fst) q0
           (fgauto_run_start S V (B .nedges) (B .ninit) p0 (z .fst) q0 (inverse V p0 (B .ninit) ei)
             (fgauto_run_end S V (B .nedges) (B .ninit) (z .fst) f q0 (inverse V q0 f ef) (z .snd .fst))))
         (z .snd .snd)) h)

{` The union over the final states. `}
def fgauto_ky_final_expr (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (Fl : List (B .nstate))
  (incl : (f : B .nstate) → FgautoMem (B .nstate) f Fl → FgautoMem (B .nstate) f (B .nfinal)) : FgautoRatExpr (M .mcarrier)
  ≔ match Fl [
  | nil. ↦ rat_fin. nil.
  | cons. f t ↦ rat_union.
      (fgauto_ky_expr S M val B (fgauto_nfa_k S B) (fgauto_nfa_pos S B (B .ninit) (fgauto_nfa_init_state S B))
        (fgauto_nfa_pos S B f (fgauto_nfa_final_state S B f (incl f (inl. (refl f))))))
      (fgauto_ky_final_expr S M val B t (f0 m0 ↦ incl f0 (inr. m0))) ]

def FgautoFinalRuns (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (Fl : List (B .nstate)) (m : M .mcarrier)
  : Type
  ≔ Mere (Σ (B .nstate) (f ↦ Product (FgautoMem (B .nstate) f Fl)
       (Σ (SignedWord S) (w ↦ Product (FgautoRun S (B .nstate) (B .nedges) (B .ninit) w f) (Id (M .mcarrier) (fgauto_val_word S M val w) m)))))

def fgauto_ky_final_correct (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (Fl : List (B .nstate)) (incl : (f : B .nstate) → FgautoMem (B .nstate) f Fl → FgautoMem (B .nstate) f (B .nfinal)) (m : M .mcarrier)
  : FgautoIff (fgauto_rat_mem M (fgauto_ky_final_expr S M val B Fl incl) m) (FgautoFinalRuns S M val B Fl m)
  ≔ let V ≔ B .nstate in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let T ≔ (Fl0 : List V) ↦ Σ V (f ↦ Product (FgautoMem V f Fl0) (Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m)))) in
    match Fl [
    | nil. ↦ (h ↦ mere_rec (FgautoMem C m nil.) (Mere (T nil.)) (mere_isprop (T nil.)) (k0 ↦ match k0 []) h,
        h ↦ mere_rec (T nil.) (Mere (FgautoMem C m nil.)) (mere_isprop (FgautoMem C m nil.)) (z ↦ match z .snd .fst []) h)
    | cons. f t ↦
      let mf ≔ fgauto_nfa_final_state S B f (incl f (inl. (refl f))) in
      let i0 ≔ fgauto_nfa_pos S B (B .ninit) (fgauto_nfa_init_state S B) in
      let e1 ≔ fgauto_ky_correct S M L val B (fgauto_nfa_k S B) i0 (fgauto_nfa_pos S B f mf) m in
      let e2 ≔ fgauto_ky_lang_runs S M val B f mf m in
      let rest ≔ fgauto_ky_final_correct S M L val B t (f0 m0 ↦ incl f0 (inr. m0)) m in
      let R1 ≔ Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m)) in
      (h ↦ mere_rec (Sum (fgauto_rat_mem M (fgauto_ky_expr S M val B (fgauto_nfa_k S B) i0 (fgauto_nfa_pos S B f mf)) m)
            (fgauto_rat_mem M (fgauto_ky_final_expr S M val B t (f0 m0 ↦ incl f0 (inr. m0))) m))
          (Mere (T (cons. f t))) (mere_isprop (T (cons. f t)))
          (s ↦ match s [
            | inl. a ↦ mere_rec R1 (Mere (T (cons. f t))) (mere_isprop (T (cons. f t)))
                (z ↦ mere (T (cons. f t)) (f, (inl. (refl f), z))) (e2 .fst (e1 .fst a))
            | inr. b ↦ mere_rec (T t) (Mere (T (cons. f t))) (mere_isprop (T (cons. f t)))
                (z ↦ mere (T (cons. f t)) (z .fst, (inr. (z .snd .fst), z .snd .snd))) (rest .fst b) ]) h,
       h ↦ mere_rec (T (cons. f t)) (fgauto_rat_mem M (fgauto_ky_final_expr S M val B (cons. f t) incl) m)
          (fgauto_rat_mem_prop M (fgauto_ky_final_expr S M val B (cons. f t) incl) m)
          (z ↦ match z .snd .fst [
            | inl. e ↦ mere (Sum (fgauto_rat_mem M (fgauto_ky_expr S M val B (fgauto_nfa_k S B) i0 (fgauto_nfa_pos S B f mf)) m)
                  (fgauto_rat_mem M (fgauto_ky_final_expr S M val B t (f0 m0 ↦ incl f0 (inr. m0))) m))
                (inl. (e1 .snd (e2 .snd (mere R1 (z .snd .snd .fst,
                  (fgauto_run_end S V (B .nedges) (B .ninit) (z .snd .snd .fst) (z .fst) f e (z .snd .snd .snd .fst), z .snd .snd .snd .snd))))))
            | inr. mt ↦ mere (Sum (fgauto_rat_mem M (fgauto_ky_expr S M val B (fgauto_nfa_k S B) i0 (fgauto_nfa_pos S B f mf)) m)
                  (fgauto_rat_mem M (fgauto_ky_final_expr S M val B t (f0 m0 ↦ incl f0 (inr. m0))) m))
                (inr. (rest .snd (mere (T t) (z .fst, (mt, z .snd .snd))))) ]) h) ]

{` The image of a regular language under a valuation is rational. `}
def fgauto_automaton_image_rational (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier)
  (B : FgautoNFA S) : FgautoRational M (FgautoImageVal S M val B)
  ≔ let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let V ≔ B .nstate in
    let ex ≔ fgauto_ky_final_expr S M val B (B .nfinal) (f m0 ↦ m0) in
    mere (Σ (FgautoRatExpr C) (r ↦ (m : C) → FgautoIff (FgautoImageVal S M val B m) (fgauto_rat_mem M r m)))
      (ex, m ↦
        let cc ≔ fgauto_ky_final_correct S M L val B (B .nfinal) (f m0 ↦ m0) m in
        (h ↦ cc .snd (mere_rec (Σ W (w ↦ Product (FgautoNFAAccepts S B w) (Id C (fgauto_val_word S M val w) m)))
             (FgautoFinalRuns S M val B (B .nfinal) m)
             (mere_isprop (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m))))))
             (z ↦ mere_rec (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (FgautoRun S V (B .nedges) (B .ninit) (z .fst) f)))
                (FgautoFinalRuns S M val B (B .nfinal) m)
                (mere_isprop (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m))))))
                (y ↦ mere (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m)))))
                  (y .fst, (y .snd .fst, (z .fst, (y .snd .snd, z .snd .snd))))) (z .snd .fst)) h),
         r ↦ mere_rec (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (Σ W (w ↦ Product (FgautoRun S V (B .nedges) (B .ninit) w f) (Id C (fgauto_val_word S M val w) m)))))
           (FgautoImageVal S M val B m) (fgauto_image_val_prop S M val B m)
           (z ↦ mere (Σ W (w ↦ Product (FgautoNFAAccepts S B w) (Id C (fgauto_val_word S M val w) m)))
             (z .snd .snd .fst, (mere (Σ V (f ↦ Product (FgautoMem V f (B .nfinal)) (FgautoRun S V (B .nedges) (B .ninit) (z .snd .snd .fst) f)))
                 (z .fst, (z .snd .fst, z .snd .snd .snd .fst)), z .snd .snd .snd .snd)))
           (cc .fst r)))

{` The valuation of F(S): a word is sent to its reduction. `}
def fgauto_free_val (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) : ReducedWord S
  ≔ fgauto_reduce_word S dec (cons. x nil.)

def fgauto_free_val_word (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : Id (ReducedWord S) (fgauto_val_word S (fgauto_free_group_monoid S dec) (fgauto_free_val S dec) w) (fgauto_reduce_word S dec w)
  ≔ let L ≔ SignedLetter S in
    let MF ≔ fgauto_free_group_monoid S dec in
    match w [
    | nil. ↦ refl (reduced_word_empty S)
    | cons. x t ↦ reduced_word_path S (fgauto_val_word S MF (fgauto_free_val S dec) (cons. x t)) (fgauto_reduce_word S dec (cons. x t))
        (fgauto_wtrans S (word_reduction S dec (append L (word_reduction S dec (cons. x nil.)) (fgauto_val_word S MF (fgauto_free_val S dec) t .fst)))
          (word_reduction S dec (append L (word_reduction S dec (cons. x nil.)) (word_reduction S dec t)))
          (word_reduction S dec (cons. x t))
          (refl ((z ↦ word_reduction S dec (append L (word_reduction S dec (cons. x nil.)) z)) : SignedWord S → SignedWord S)
            (refl ((g ↦ g .fst) : ReducedWord S → SignedWord S) (fgauto_free_val_word S dec t)))
          (fgauto_wsym S (word_reduction S dec (append L (cons. x nil.) t))
            (word_reduction S dec (append L (word_reduction S dec (cons. x nil.)) (word_reduction S dec t)))
            (word_reduction_append S dec (cons. x nil.) t))) ]

{` fggroups.tex:874, "<=". `}
def fgauto_benois_regular_rational (S : Type) (dec : DecidableEquality S) (X : FgautoFreeSubset S)
  (hX : FgautoRegular S (FgautoIotaImage S (m ↦ X m .fst))) : FgautoRational (fgauto_free_group_monoid S dec) (m ↦ X m .fst)
  ≔ let MF ≔ fgauto_free_group_monoid S dec in
    let RW ≔ ReducedWord S in
    let W ≔ SignedWord S in
    let val ≔ fgauto_free_val S dec in
    mere_rec (Σ (FgautoNFA S) (B ↦ (w : W) → FgautoIff (FgautoIotaImage S (m ↦ X m .fst) w) (FgautoNFAAccepts S B w)))
      (FgautoRational MF (m ↦ X m .fst))
      (mere_isprop (Σ (FgautoRatExpr RW) (r ↦ (m : RW) → FgautoIff (X m .fst) (fgauto_rat_mem MF r m))))
      (z ↦
        let B ≔ z .fst in
        let hB ≔ z .snd in
        mere_rec (Σ (FgautoRatExpr RW) (r ↦ (m : RW) → FgautoIff (FgautoImageVal S MF val B m) (fgauto_rat_mem MF r m)))
          (FgautoRational MF (m ↦ X m .fst))
          (mere_isprop (Σ (FgautoRatExpr RW) (r ↦ (m : RW) → FgautoIff (X m .fst) (fgauto_rat_mem MF r m))))
          (y ↦ mere (Σ (FgautoRatExpr RW) (r ↦ (m : RW) → FgautoIff (X m .fst) (fgauto_rat_mem MF r m)))
            (y .fst, m ↦
              (x ↦ y .snd m .fst
                 (mere (Σ W (w ↦ Product (FgautoNFAAccepts S B w) (Id RW (fgauto_val_word S MF val w) m)))
                   (m .fst, (hB (m .fst) .fst (m .snd, x),
                     concat RW (fgauto_val_word S MF val (m .fst)) (fgauto_reduce_word S dec (m .fst)) m (fgauto_free_val_word S dec (m .fst))
                       (reduced_word_path S (fgauto_reduce_word S dec (m .fst)) m (word_reduction_of_reduced S dec (m .fst) (m .snd)))))),
               r ↦ mere_rec (Σ W (w ↦ Product (FgautoNFAAccepts S B w) (Id RW (fgauto_val_word S MF val w) m))) (X m .fst) (X m .snd)
                 (yy ↦
                   let w ≔ yy .fst in
                   let io ≔ hB w .snd (yy .snd .fst) in
                   transport RW (g ↦ X g .fst) (w, io .fst) m
                     (concat RW (w, io .fst) (fgauto_reduce_word S dec w) m
                       (reduced_word_path S (w, io .fst) (fgauto_reduce_word S dec w)
                         (inverse W (word_reduction S dec w) w (word_reduction_of_reduced S dec w (io .fst))))
                       (concat RW (fgauto_reduce_word S dec w) (fgauto_val_word S MF val w) m
                         (inverse RW (fgauto_val_word S MF val w) (fgauto_reduce_word S dec w) (fgauto_free_val_word S dec w)) (yy .snd .snd)))
                     (io .snd))
                 (y .snd m .snd r))))
          (fgauto_automaton_image_rational S MF (fgauto_free_group_monoid_laws S dec) val B)) hX

{` fggroups.tex:874 (Benois). `}
def fgauto_benois (S : Type) (dec : DecidableEquality S) (X : FgautoFreeSubset S)
  : FgautoIff (FgautoRational (fgauto_free_group_monoid S dec) (m ↦ X m .fst)) (FgautoRegular S (FgautoIotaImage S (m ↦ X m .fst)))
  ≔ (fgauto_benois_rational_regular S dec X, fgauto_benois_regular_rational S dec X)
