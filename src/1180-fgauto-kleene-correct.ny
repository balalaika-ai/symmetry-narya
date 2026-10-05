export "1179-fgauto-kleene"

{` Chapter 11, automata part 31: the McNaughton–Yamada expressions and
   their correctness (fgauto_ky_correct), and the consequence: the image of
   the language of a finite automaton under the valuation of words is a
   rational subset (fgauto_automaton_image_rational). `}

def fgauto_ky_pick (M : FgautoMonoid) (P : Type) (d : Decidable P) (m : M .mcarrier) : List (M .mcarrier)
  ≔ match d [ inl. _ ↦ cons. m nil. | inr. _ ↦ nil. ]

def FgautoKyEdgeAt (S : Type) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B)) (e : FgautoEdge S (B .nstate)) : Type
  ≔ Product (Id (B .nstate) (e .src) (fgauto_nfa_nth S B i)) (Id (B .nstate) (e .tgt) (fgauto_nfa_nth S B j))

def fgauto_ky_vals (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (i j : Fin (fgauto_nfa_k S B))
  : List (M .mcarrier)
  ≔ fgauto_list_bind (FgautoEdge S (B .nstate)) (M .mcarrier) (B .nedges)
      (e ↦ fgauto_ky_pick M (FgautoKyEdgeAt S B i j e)
        (fgauto_and_decide (Id (B .nstate) (e .src) (fgauto_nfa_nth S B i)) (Id (B .nstate) (e .tgt) (fgauto_nfa_nth S B j))
          (B .ndec (e .src) (fgauto_nfa_nth S B i)) (B .ndec (e .tgt) (fgauto_nfa_nth S B j))) (val (e .lab)))

def fgauto_ky_diag (M : FgautoMonoid) (k : Nat) (i j : Fin k) : List (M .mcarrier)
  ≔ fgauto_ky_pick M (Id (Fin k) i j) (fin_decidable_equality k i j) (M .munit)

def fgauto_ky_step (S : Type) (M : FgautoMonoid) (B : FgautoNFA S)
  (R : Fin (fgauto_nfa_k S B) → Fin (fgauto_nfa_k S B) → FgautoRatExpr (M .mcarrier)) (n : Nat) (i j : Fin (fgauto_nfa_k S B))
  (d : Decidable (Lt n (fgauto_nfa_k S B))) : FgautoRatExpr (M .mcarrier)
  ≔ match d [
  | inl. h ↦
    let c ≔ fgauto_fin_at (fgauto_nfa_k S B) n h in
    rat_union. (R i j) (rat_prod. (R i c) (rat_prod. (rat_star. (R c c)) (R c j)))
  | inr. _ ↦ R i j ]

def fgauto_ky_expr (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (n : Nat)
  (i j : Fin (fgauto_nfa_k S B)) : FgautoRatExpr (M .mcarrier)
  ≔ match n [
  | zero. ↦ rat_union. (rat_fin. (fgauto_ky_vals S M val B i j)) (rat_fin. (fgauto_ky_diag M (fgauto_nfa_k S B) i j))
  | suc. n0 ↦ fgauto_ky_step S M B (fgauto_ky_expr S M val B n0) n0 i j (lt_decidable n0 (fgauto_nfa_k S B)) ]

def FgautoKyLang (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (n : Nat)
  (p q : B .nstate) (m : M .mcarrier) : Type
  ≔ Mere (Σ (SignedWord S) (w ↦ Product (FgautoIRun S B n p w q) (Id (M .mcarrier) (fgauto_val_word S M val w) m)))

def fgauto_ky_lang_prop (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (n : Nat)
  (p q : B .nstate) (m : M .mcarrier) : isProp (FgautoKyLang S M val B n p q m)
  ≔ mere_isprop (Σ (SignedWord S) (w ↦ Product (FgautoIRun S B n p w q) (Id (M .mcarrier) (fgauto_val_word S M val w) m)))

def fgauto_ky_lang_intro (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S) (n : Nat)
  (p q : B .nstate) (m : M .mcarrier) (w : SignedWord S) (r : FgautoIRun S B n p w q) (e : Id (M .mcarrier) (fgauto_val_word S M val w) m)
  : FgautoKyLang S M val B n p q m
  ≔ mere (Σ (SignedWord S) (w0 ↦ Product (FgautoIRun S B n p w0 q) (Id (M .mcarrier) (fgauto_val_word S M val w0) m))) (w, (r, e))

{` Level 0. `}
def fgauto_ky_pick_mem (M : FgautoMonoid) (P : Type) (d : Decidable P) (m x : M .mcarrier) (h : FgautoMem (M .mcarrier) x (fgauto_ky_pick M P d m))
  : Product P (Id (M .mcarrier) x m)
  ≔ match d [ inr. _ ↦ match h [] | inl. p ↦ match h [ inl. e ↦ (p, e) | inr. h' ↦ match h' [] ] ]

def fgauto_ky_pick_intro (M : FgautoMonoid) (P : Type) (d : Decidable P) (m : M .mcarrier) (p : P)
  : FgautoMem (M .mcarrier) m (fgauto_ky_pick M P d m)
  ≔ match d [ inl. _ ↦ inl. (refl m) | inr. n ↦ match n p [] ]

def fgauto_irunfrom_zero (S : Type) (B : FgautoNFA S) (r : B .nstate) (w : SignedWord S) (q : B .nstate)
  (t : FgautoIRunFrom S B zero. r w q) : Product (Id (SignedWord S) w nil.) (Id (B .nstate) r q)
  ≔ match w [ nil. ↦ (refl (nil. : SignedWord S), t) | cons. y w2 ↦ match t .fst .snd .fst [] ]

def fgauto_mem_bind_elim (A B : Type) (l : List A) (k : A → List B) (b : B) (m : FgautoMem B b (fgauto_list_bind A B l k))
  : Σ A (a ↦ Product (FgautoMem A a l) (FgautoMem B b (k a)))
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ match fgauto_mem_append_split B b (k a) (fgauto_list_bind A B t k) m [
    | inl. h ↦ (a, (inl. (refl a), h))
    | inr. h ↦ let z ≔ fgauto_mem_bind_elim A B t k b h in (z .fst, (inr. (z .snd .fst), z .snd .snd)) ] ]

def fgauto_ky_zero_run (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier) (w : SignedWord S)
  (r : FgautoIRun S B zero. (fgauto_nfa_nth S B i) w (fgauto_nfa_nth S B j)) (e : Id (M .mcarrier) (fgauto_val_word S M val w) m)
  : fgauto_rat_mem M (fgauto_ky_expr S M val B zero. i j) m
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let C ≔ M .mcarrier in
    let Ed ≔ FgautoEdge S V in
    let pickd ≔ (e0 : Ed) ↦ fgauto_and_decide (Id V (e0 .src) (nth i)) (Id V (e0 .tgt) (nth j)) (B .ndec (e0 .src) (nth i)) (B .ndec (e0 .tgt) (nth j)) in
    let U ≔ Sum (Mere (FgautoMem C m (fgauto_ky_vals S M val B i j))) (Mere (FgautoMem C m (fgauto_ky_diag M k i j))) in
    match w [
    | nil. ↦ mere U (inr. (mere (FgautoMem C m (fgauto_ky_diag M k i j))
        (fgauto_mem_transport C (M .munit) m (fgauto_ky_diag M k i j) e
          (fgauto_ky_pick_intro M (Id (Fin k) i j) (fin_decidable_equality k i j) (M .munit) (fgauto_nfa_nth_injective S B i j r)))))
    | cons. x w1 ↦ match w1 [
      | cons. y w2 ↦ match (r .snd .snd) .fst .snd .fst []
      | nil. ↦
        let z ≔ fgauto_step_mem_edge S V (B .nedges) (nth i) x (r .fst) (r .snd .fst) in
        let ed ≔ z .fst in
        let at : FgautoKyEdgeAt S B i j ed
          ≔ (inverse V (nth i) (ed .src) (z .snd .snd .fst),
             concat V (ed .tgt) (r .fst) (nth j) (inverse V (r .fst) (ed .tgt) (z .snd .snd .snd .snd)) (r .snd .snd)) in
        mere U (inl. (mere (FgautoMem C m (fgauto_ky_vals S M val B i j))
          (fgauto_mem_bind Ed C (B .nedges) (e0 ↦ fgauto_ky_pick M (FgautoKyEdgeAt S B i j e0) (pickd e0) (val (e0 .lab))) ed m (z .snd .fst)
            (fgauto_mem_transport C (val (ed .lab)) m (fgauto_ky_pick M (FgautoKyEdgeAt S B i j ed) (pickd ed) (val (ed .lab)))
              (concat C (val (ed .lab)) (val x) m (refl val (inverse (SignedLetter S) x (ed .lab) (z .snd .snd .snd .fst)))
                (concat C (val x) (M .mmul (val x) (M .munit)) m (inverse C (M .mmul (val x) (M .munit)) (val x) (L .ml_unit_right (val x))) e))
              (fgauto_ky_pick_intro M (FgautoKyEdgeAt S B i j ed) (pickd ed) (val (ed .lab)) at))))) ] ]

def fgauto_ky_zero (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier)
  : FgautoIff (fgauto_rat_mem M (fgauto_ky_expr S M val B zero. i j) m) (FgautoKyLang S M val B zero. (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m)
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let V ≔ B .nstate in
    let C ≔ M .mcarrier in
    let Ed ≔ FgautoEdge S V in
    let goalR ≔ fgauto_rat_mem M (fgauto_ky_expr S M val B zero. i j) m in
    let pickd ≔ (e : Ed) ↦ fgauto_and_decide (Id V (e .src) (nth i)) (Id V (e .tgt) (nth j)) (B .ndec (e .src) (nth i)) (B .ndec (e .tgt) (nth j)) in
    (h ↦ mere_rec (Sum (Mere (FgautoMem C m (fgauto_ky_vals S M val B i j))) (Mere (FgautoMem C m (fgauto_ky_diag M k i j))))
       (FgautoKyLang S M val B zero. (nth i) (nth j) m) (fgauto_ky_lang_prop S M val B zero. (nth i) (nth j) m)
       (s ↦ match s [
         | inl. a ↦ mere_rec (FgautoMem C m (fgauto_ky_vals S M val B i j)) (FgautoKyLang S M val B zero. (nth i) (nth j) m)
             (fgauto_ky_lang_prop S M val B zero. (nth i) (nth j) m)
             (mm ↦
               let z ≔ fgauto_mem_bind_elim Ed C (B .nedges) (e0 ↦ fgauto_ky_pick M (FgautoKyEdgeAt S B i j e0) (pickd e0) (val (e0 .lab))) m mm in
               let e ≔ z .fst in
               let pm ≔ fgauto_ky_pick_mem M (FgautoKyEdgeAt S B i j e) (pickd e) (val (e .lab)) m (z .snd .snd) in
               fgauto_ky_lang_intro S M val B zero. (nth i) (nth j) m (cons. (e .lab) nil.)
                 (nth j, (fgauto_step_transport S V (B .nedges) (e .src) (nth i) (e .lab) (e .lab) (e .tgt) (nth j)
                    (pm .fst .fst) (refl (e .lab)) (pm .fst .snd) (fgauto_mem_edge_step S V (B .nedges) e (z .snd .fst)), refl (nth j)))
                 (concat C (M .mmul (val (e .lab)) (M .munit)) (val (e .lab)) m (L .ml_unit_right (val (e .lab)))
                   (inverse C m (val (e .lab)) (pm .snd))))
             a
         | inr. b ↦ mere_rec (FgautoMem C m (fgauto_ky_diag M k i j)) (FgautoKyLang S M val B zero. (nth i) (nth j) m)
             (fgauto_ky_lang_prop S M val B zero. (nth i) (nth j) m)
             (mm ↦
               let pm ≔ fgauto_ky_pick_mem M (Id (Fin k) i j) (fin_decidable_equality k i j) (M .munit) m mm in
               fgauto_ky_lang_intro S M val B zero. (nth i) (nth j) m nil. (refl nth (pm .fst)) (inverse C m (M .munit) (pm .snd)))
             b ]) h,
     h ↦ mere_rec (Σ (SignedWord S) (w ↦ Product (FgautoIRun S B zero. (nth i) w (nth j)) (Id C (fgauto_val_word S M val w) m)))
       goalR (fgauto_rat_mem_prop M (fgauto_ky_expr S M val B zero. i j) m)
       (z ↦ fgauto_ky_zero_run S M L val B i j m (z .fst) (z .snd .fst) (z .snd .snd)) h)


{` Decomposition into loops at c. `}
def fgauto_concat_words (S : Type) (ls : List (SignedWord S)) : SignedWord S
  ≔ match ls [ nil. ↦ nil. | cons. l t ↦ append (SignedLetter S) l (fgauto_concat_words S t) ]

def fgauto_length_suffix2 (A : Type) (u v : List A) : Le (length A v) (length A (append A u v))
  ≔ match u [ nil. ↦ le_refl (length A v) | cons. a t ↦ le_step (length A v) (length A (append A t v)) (fgauto_length_suffix2 A t v) ]

def FgautoLoops (S : Type) (B : FgautoNFA S) (n : Nat) (c : B .nstate) (v : SignedWord S) (q : B .nstate) : Type
  ≔ Σ (List (SignedWord S)) (ls ↦ Σ (SignedWord S) (last ↦
      Product (Id (SignedWord S) v (append (SignedLetter S) (fgauto_concat_words S ls) last))
        (Product (FgautoAllIn (SignedWord S) (l ↦ FgautoIRun S B n c l c) ls) (FgautoIRun S B n c last q))))

def fgauto_loops (S : Type) (B : FgautoNFA S) (n : Nat) (h : Lt n (fgauto_nfa_k S B)) (f : Nat) (v : SignedWord S)
  (hl : Le (length (SignedLetter S) v) f) (q : B .nstate)
  (r : FgautoIRun S B (fgauto_succ n) (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) v q)
  : FgautoLoops S B n (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) v q
  ≔ let c ≔ fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h) in
    let L ≔ SignedLetter S in
    let W ≔ SignedWord S in
    match v [
    | nil. ↦ (nil., (nil., (refl (nil. : W), (star., r))))
    | cons. x v1 ↦ match f [
      | zero. ↦ match hl []
      | suc. f1 ↦ match fgauto_irunfrom_first_visit S B n h (r .fst) v1 q (r .snd .snd) [
        | inl. t2 ↦ (nil., (cons. x v1, (refl (cons. x v1 : W), (star., (r .fst, (r .snd .fst, t2))))))
        | inr. fv ↦
          let u ≔ fv .fst in
          let v2 ≔ fv .snd .fst in
          let rec2 ≔ fgauto_loops S B n h f1 v2
            (le_trans (length L v2) (length L (append L u v2)) f1 (fgauto_length_suffix2 L u v2)
              (transport W (z ↦ Le (length L z) f1) v1 (append L u v2) (fv .snd .snd .fst) hl))
            q (fv .snd .snd .snd .snd) in
          let lp : W ≔ cons. x u in
          let lr : FgautoIRun S B n c lp c ≔ (r .fst, (r .snd .fst, fv .snd .snd .snd .fst)) in
          (cons. lp (rec2 .fst), (rec2 .snd .fst,
            (cons. (refl x)
               (concat W v1 (append L u v2) (append L (append L u (fgauto_concat_words S (rec2 .fst))) (rec2 .snd .fst))
                 (fv .snd .snd .fst)
                 (concat W (append L u v2) (append L u (append L (fgauto_concat_words S (rec2 .fst)) (rec2 .snd .fst)))
                   (append L (append L u (fgauto_concat_words S (rec2 .fst))) (rec2 .snd .fst))
                   (refl (append L u) (rec2 .snd .snd .fst))
                   (inverse W (append L (append L u (fgauto_concat_words S (rec2 .fst))) (rec2 .snd .fst))
                     (append L u (append L (fgauto_concat_words S (rec2 .fst)) (rec2 .snd .fst)))
                     (append_assoc L u (fgauto_concat_words S (rec2 .fst)) (rec2 .snd .fst))))),
             ((lr, rec2 .snd .snd .snd .fst), rec2 .snd .snd .snd .snd)))) ] ] ]

{` Values of concatenations. `}
def fgauto_val_concat_words (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier)
  (ls : List (SignedWord S))
  : Id (M .mcarrier) (fgauto_val_word S M val (fgauto_concat_words S ls))
      (fgauto_list_product M (fgauto_list_map (SignedWord S) (M .mcarrier) (fgauto_val_word S M val) ls))
  ≔ match ls [
  | nil. ↦ refl (M .munit)
  | cons. l t ↦ concat (M .mcarrier) (fgauto_val_word S M val (append (SignedLetter S) l (fgauto_concat_words S t)))
      (M .mmul (fgauto_val_word S M val l) (fgauto_val_word S M val (fgauto_concat_words S t)))
      (M .mmul (fgauto_val_word S M val l) (fgauto_list_product M (fgauto_list_map (SignedWord S) (M .mcarrier) (fgauto_val_word S M val) t)))
      (fgauto_val_word_append S M L val l (fgauto_concat_words S t))
      (refl (M .mmul (fgauto_val_word S M val l)) (fgauto_val_concat_words S M L val t)) ]

def fgauto_allin_map_list (A B : Type) (f : A → B) (P : A → Type) (Q : B → Type) (g : (a : A) → P a → Q (f a)) (l : List A)
  (h : FgautoAllIn A P l) : FgautoAllIn B Q (fgauto_list_map A B f l)
  ≔ match l [ nil. ↦ star. | cons. a t ↦ (g a (h .fst), fgauto_allin_map_list A B f P Q g t (h .snd)) ]

def fgauto_ky_le_of_not_lt (n k : Nat) (nh : Not (Lt n k)) : Le k n
  ≔ match le_total n k [
  | inr. le ↦ le
  | inl. le ↦ match le_split n k le [ inl. lt ↦ match nh lt [] | inr. e ↦ le_from_equal k n (inverse Nat n k e) ] ]

{` Star runs at c. `}
def fgauto_ky_star_runs (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (n : Nat) (h : Lt n (fgauto_nfa_k S B))
  (ihcc : (m : M .mcarrier) → fgauto_rat_mem M (fgauto_ky_expr S M val B n (fgauto_fin_at (fgauto_nfa_k S B) n h) (fgauto_fin_at (fgauto_nfa_k S B) n h)) m
     → FgautoKyLang S M val B n (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) m)
  (l : List (M .mcarrier))
  (hl : FgautoAllIn (M .mcarrier) (fgauto_rat_mem M (fgauto_ky_expr S M val B n (fgauto_fin_at (fgauto_nfa_k S B) n h) (fgauto_fin_at (fgauto_nfa_k S B) n h))) l)
  : FgautoKyLang S M val B (fgauto_succ n) (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h))
      (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) (fgauto_list_product M l)
  ≔ let cs ≔ fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h) in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let KLs ≔ FgautoKyLang S M val B (fgauto_succ n) cs cs in
    match l [
    | nil. ↦ fgauto_ky_lang_intro S M val B (fgauto_succ n) cs cs (M .munit) nil. (refl cs) (refl (M .munit))
    | cons. a t ↦
      mere_rec (Σ W (w ↦ Product (FgautoIRun S B n cs w cs) (Id C (fgauto_val_word S M val w) a)))
        (KLs (M .mmul a (fgauto_list_product M t))) (fgauto_ky_lang_prop S M val B (fgauto_succ n) cs cs (M .mmul a (fgauto_list_product M t)))
        (za ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) cs w cs) (Id C (fgauto_val_word S M val w) (fgauto_list_product M t))))
          (KLs (M .mmul a (fgauto_list_product M t))) (fgauto_ky_lang_prop S M val B (fgauto_succ n) cs cs (M .mmul a (fgauto_list_product M t)))
          (zt ↦ fgauto_ky_lang_intro S M val B (fgauto_succ n) cs cs (M .mmul a (fgauto_list_product M t)) (append (SignedLetter S) (za .fst) (zt .fst))
            (fgauto_irun_append S B (fgauto_succ n) cs (za .fst) cs (zt .fst) cs (fgauto_allowed_c S B n h)
              (fgauto_irun_mono S B n (fgauto_succ n) (fgauto_allowed_suc S B n) cs (za .fst) cs (za .snd .fst)) (zt .snd .fst))
            (concat C (fgauto_val_word S M val (append (SignedLetter S) (za .fst) (zt .fst)))
              (M .mmul (fgauto_val_word S M val (za .fst)) (fgauto_val_word S M val (zt .fst))) (M .mmul a (fgauto_list_product M t))
              (fgauto_val_word_append S M L val (za .fst) (zt .fst))
              (refl ((u v ↦ M .mmul u v) : C → C → C) (za .snd .snd) (zt .snd .snd))))
          (fgauto_ky_star_runs S M L val B n h ihcc t (hl .snd)))
        (ihcc a (hl .fst)) ]

{` One level up. `}
def fgauto_ky_succ_lt_out (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (n : Nat) (h : Lt n (fgauto_nfa_k S B))
  (ih : (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier)
    → FgautoIff (fgauto_rat_mem M (fgauto_ky_expr S M val B n i j) m) (FgautoKyLang S M val B n (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m))
  (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier) (w : SignedWord S)
  (r : FgautoIRun S B (fgauto_succ n) (fgauto_nfa_nth S B i) w (fgauto_nfa_nth S B j)) (e : Id (M .mcarrier) (fgauto_val_word S M val w) m)
  : fgauto_rat_mem M (fgauto_ky_step S M B (fgauto_ky_expr S M val B n) n i j (inl. h)) m
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let c ≔ fgauto_fin_at k n h in
    let cs ≔ nth c in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let Lt0 ≔ SignedLetter S in
    let R ≔ fgauto_ky_expr S M val B n in
    let A1 ≔ fgauto_rat_mem M (R i j) m in
    let A2 ≔ fgauto_rat_mem M (rat_prod. (R i c) (rat_prod. (rat_star. (R c c)) (R c j))) m in
    match w [
    | nil. ↦ mere (Sum A1 A2) (inl. (ih i j m .snd (fgauto_ky_lang_intro S M val B n (nth i) (nth j) m nil. r e)))
    | cons. x w1 ↦ match fgauto_irunfrom_first_visit S B n h (r .fst) w1 (nth j) (r .snd .snd) [
      | inl. t2 ↦ mere (Sum A1 A2) (inl. (ih i j m .snd (fgauto_ky_lang_intro S M val B n (nth i) (nth j) m (cons. x w1) (r .fst, (r .snd .fst, t2)) e)))
      | inr. fv ↦
        let u ≔ fv .fst in
        let v ≔ fv .snd .fst in
        let lp : W ≔ cons. x u in
        let rlp : FgautoIRun S B n (nth i) lp cs ≔ (r .fst, (r .snd .fst, fv .snd .snd .snd .fst)) in
        let a ≔ fgauto_val_word S M val lp in
        let lo ≔ fgauto_loops S B n h (length Lt0 v) v (le_refl (length Lt0 v)) (nth j) (fv .snd .snd .snd .snd) in
        let ls ≔ lo .fst in
        let last ≔ lo .snd .fst in
        let b1 ≔ fgauto_list_product M (fgauto_list_map W C (fgauto_val_word S M val) ls) in
        let b2 ≔ fgauto_val_word S M val last in
        let memA ≔ ih i c a .snd (fgauto_ky_lang_intro S M val B n (nth i) cs a lp rlp (refl a)) in
        let memStar : fgauto_rat_mem M (rat_star. (R c c)) b1
          ≔ mere (Σ (List C) (l ↦ Product (FgautoAllIn C (fgauto_rat_mem M (R c c)) l) (Id C b1 (fgauto_list_product M l))))
              (fgauto_list_map W C (fgauto_val_word S M val) ls,
               (fgauto_allin_map_list W C (fgauto_val_word S M val) (l0 ↦ FgautoIRun S B n cs l0 cs) (fgauto_rat_mem M (R c c))
                  (l0 rl ↦ ih c c (fgauto_val_word S M val l0) .snd (fgauto_ky_lang_intro S M val B n cs cs (fgauto_val_word S M val l0) l0 rl
                    (refl (fgauto_val_word S M val l0)))) ls (lo .snd .snd .snd .fst),
                refl b1)) in
        let memB ≔ ih c j b2 .snd (fgauto_ky_lang_intro S M val B n cs (nth j) b2 last (lo .snd .snd .snd .snd) (refl b2)) in
        let ev : Id C (fgauto_val_word S M val v) (M .mmul b1 b2)
          ≔ concat C (fgauto_val_word S M val v) (fgauto_val_word S M val (append Lt0 (fgauto_concat_words S ls) last)) (M .mmul b1 b2)
              (refl (fgauto_val_word S M val) (lo .snd .snd .fst))
              (concat C (fgauto_val_word S M val (append Lt0 (fgauto_concat_words S ls) last))
                (M .mmul (fgauto_val_word S M val (fgauto_concat_words S ls)) b2) (M .mmul b1 b2)
                (fgauto_val_word_append S M L val (fgauto_concat_words S ls) last)
                (refl ((z ↦ M .mmul z b2) : C → C) (fgauto_val_concat_words S M L val ls))) in
        let em : Id C m (M .mmul a (M .mmul b1 b2))
          ≔ calc
              m = fgauto_val_word S M val (cons. x w1) by inverse C (fgauto_val_word S M val (cons. x w1)) m e
              = M .mmul (val x) (fgauto_val_word S M val (append Lt0 u v))
                by refl ((z ↦ M .mmul (val x) (fgauto_val_word S M val z)) : W → C) (fv .snd .snd .fst)
              = M .mmul (val x) (M .mmul (fgauto_val_word S M val u) (fgauto_val_word S M val v))
                by refl (M .mmul (val x)) (fgauto_val_word_append S M L val u v)
              = M .mmul a (fgauto_val_word S M val v) by L .ml_assoc (val x) (fgauto_val_word S M val u) (fgauto_val_word S M val v)
              = M .mmul a (M .mmul b1 b2) by refl (M .mmul a) ev ∎ in
        mere (Sum A1 A2) (inr. (mere (Σ C (a0 ↦ Σ C (b0 ↦ Product (fgauto_rat_mem M (R i c) a0)
              (Product (fgauto_rat_mem M (rat_prod. (rat_star. (R c c)) (R c j)) b0) (Id C m (M .mmul a0 b0))))))
          (a, (M .mmul b1 b2, (memA,
            (mere (Σ C (a1 ↦ Σ C (b3 ↦ Product (fgauto_rat_mem M (rat_star. (R c c)) a1) (Product (fgauto_rat_mem M (R c j) b3) (Id C (M .mmul b1 b2) (M .mmul a1 b3))))))
               (b1, (b2, (memStar, (memB, refl (M .mmul b1 b2))))),
             em)))))) ] ]

def fgauto_ky_succ_lt_in (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (n : Nat) (h : Lt n (fgauto_nfa_k S B))
  (ih : (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier)
    → FgautoIff (fgauto_rat_mem M (fgauto_ky_expr S M val B n i j) m) (FgautoKyLang S M val B n (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m))
  (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier) (hm : fgauto_rat_mem M (fgauto_ky_step S M B (fgauto_ky_expr S M val B n) n i j (inl. h)) m)
  : FgautoKyLang S M val B (fgauto_succ n) (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m
  ≔ let k ≔ fgauto_nfa_k S B in
    let nth ≔ fgauto_nfa_nth S B in
    let c ≔ fgauto_fin_at k n h in
    let cs ≔ nth c in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    let Lt0 ≔ SignedLetter S in
    let R ≔ fgauto_ky_expr S M val B n in
    let KLs ≔ FgautoKyLang S M val B (fgauto_succ n) (nth i) (nth j) m in
    let hK ≔ fgauto_ky_lang_prop S M val B (fgauto_succ n) (nth i) (nth j) m in
    let up ≔ (p q : B .nstate) (mm : C) (z : FgautoKyLang S M val B n p q mm) ↦
      mere_rec (Σ W (w ↦ Product (FgautoIRun S B n p w q) (Id C (fgauto_val_word S M val w) mm))) (FgautoKyLang S M val B (fgauto_succ n) p q mm)
        (fgauto_ky_lang_prop S M val B (fgauto_succ n) p q mm)
        (y ↦ fgauto_ky_lang_intro S M val B (fgauto_succ n) p q mm (y .fst)
          (fgauto_irun_mono S B n (fgauto_succ n) (fgauto_allowed_suc S B n) p (y .fst) q (y .snd .fst)) (y .snd .snd)) z in
    mere_rec (Sum (fgauto_rat_mem M (R i j) m) (fgauto_rat_mem M (rat_prod. (R i c) (rat_prod. (rat_star. (R c c)) (R c j))) m)) KLs hK
      (s ↦ match s [
        | inl. a1 ↦ up (nth i) (nth j) m (ih i j m .fst a1)
        | inr. a2 ↦ mere_rec (Σ C (a ↦ Σ C (b ↦ Product (fgauto_rat_mem M (R i c) a)
              (Product (fgauto_rat_mem M (rat_prod. (rat_star. (R c c)) (R c j)) b) (Id C m (M .mmul a b)))))) KLs hK
            (za ↦ mere_rec (Σ C (b1 ↦ Σ C (b2 ↦ Product (fgauto_rat_mem M (rat_star. (R c c)) b1)
                  (Product (fgauto_rat_mem M (R c j) b2) (Id C (za .snd .fst) (M .mmul b1 b2)))))) KLs hK
              (zb ↦ mere_rec (Σ (List C) (l ↦ Product (FgautoAllIn C (fgauto_rat_mem M (R c c)) l) (Id C (zb .fst) (fgauto_list_product M l)))) KLs hK
                (zl ↦
                  let a ≔ za .fst in
                  let b1 ≔ zb .fst in
                  let b2 ≔ zb .snd .fst in
                  let KA ≔ up (nth i) cs a (ih i c a .fst (za .snd .snd .fst)) in
                  let KL ≔ fgauto_ky_star_runs S M L val B n h (mm hm0 ↦ ih c c mm .fst hm0) (zl .fst) (zl .snd .fst) in
                  let KB ≔ up cs (nth j) b2 (ih c j b2 .fst (zb .snd .snd .snd .fst)) in
                  mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) (nth i) w cs) (Id C (fgauto_val_word S M val w) a))) KLs hK
                    (ya ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) cs w cs) (Id C (fgauto_val_word S M val w) (fgauto_list_product M (zl .fst))))) KLs hK
                      (yl ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) cs w (nth j)) (Id C (fgauto_val_word S M val w) b2))) KLs hK
                        (yb ↦
                          let wtot ≔ append Lt0 (ya .fst) (append Lt0 (yl .fst) (yb .fst)) in
                          fgauto_ky_lang_intro S M val B (fgauto_succ n) (nth i) (nth j) m wtot
                            (fgauto_irun_append S B (fgauto_succ n) (nth i) (ya .fst) cs (append Lt0 (yl .fst) (yb .fst)) (nth j) (fgauto_allowed_c S B n h)
                              (ya .snd .fst)
                              (fgauto_irun_append S B (fgauto_succ n) cs (yl .fst) cs (yb .fst) (nth j) (fgauto_allowed_c S B n h) (yl .snd .fst) (yb .snd .fst)))
                            (calc
                              fgauto_val_word S M val wtot
                              = M .mmul (fgauto_val_word S M val (ya .fst)) (fgauto_val_word S M val (append Lt0 (yl .fst) (yb .fst)))
                                by fgauto_val_word_append S M L val (ya .fst) (append Lt0 (yl .fst) (yb .fst))
                              = M .mmul (fgauto_val_word S M val (ya .fst)) (M .mmul (fgauto_val_word S M val (yl .fst)) (fgauto_val_word S M val (yb .fst)))
                                by refl (M .mmul (fgauto_val_word S M val (ya .fst))) (fgauto_val_word_append S M L val (yl .fst) (yb .fst))
                              = M .mmul a (M .mmul b1 b2)
                                by refl ((x y z ↦ M .mmul x (M .mmul y z)) : C → C → C → C) (ya .snd .snd)
                                     (concat C (fgauto_val_word S M val (yl .fst)) (fgauto_list_product M (zl .fst)) b1 (yl .snd .snd)
                                       (inverse C b1 (fgauto_list_product M (zl .fst)) (zl .snd .snd)))
                                     (yb .snd .snd)
                              = M .mmul a (za .snd .fst) by refl (M .mmul a) (inverse C (za .snd .fst) (M .mmul b1 b2) (zb .snd .snd .snd .snd))
                              = m by inverse C m (M .mmul a (za .snd .fst)) (za .snd .snd .snd .snd) ∎)) KB) KL) KA)
                (zb .snd .snd .fst))
              (za .snd .snd .snd .fst))
            a2 ]) hm

def fgauto_ky_succ (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (n : Nat)
  (ih : (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier)
    → FgautoIff (fgauto_rat_mem M (fgauto_ky_expr S M val B n i j) m) (FgautoKyLang S M val B n (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m))
  (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier) (d : Decidable (Lt n (fgauto_nfa_k S B)))
  : FgautoIff (fgauto_rat_mem M (fgauto_ky_step S M B (fgauto_ky_expr S M val B n) n i j d) m)
      (FgautoKyLang S M val B (fgauto_succ n) (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m)
  ≔ let nth ≔ fgauto_nfa_nth S B in
    let C ≔ M .mcarrier in
    let W ≔ SignedWord S in
    match d [
    | inl. h ↦ (hm ↦ fgauto_ky_succ_lt_in S M L val B n h ih i j m hm,
        z ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) (nth i) w (nth j)) (Id C (fgauto_val_word S M val w) m)))
          (fgauto_rat_mem M (fgauto_ky_step S M B (fgauto_ky_expr S M val B n) n i j (inl. h)) m)
          (fgauto_rat_mem_prop M (fgauto_ky_step S M B (fgauto_ky_expr S M val B n) n i j (inl. h)) m)
          (y ↦ fgauto_ky_succ_lt_out S M L val B n h ih i j m (y .fst) (y .snd .fst) (y .snd .snd)) z)
    | inr. nh ↦
      let hk ≔ fgauto_ky_le_of_not_lt n (fgauto_nfa_k S B) nh in
      (hm ↦ mere_rec (Σ W (w ↦ Product (FgautoIRun S B n (nth i) w (nth j)) (Id C (fgauto_val_word S M val w) m)))
          (FgautoKyLang S M val B (fgauto_succ n) (nth i) (nth j) m) (fgauto_ky_lang_prop S M val B (fgauto_succ n) (nth i) (nth j) m)
          (y ↦ fgauto_ky_lang_intro S M val B (fgauto_succ n) (nth i) (nth j) m (y .fst)
            (fgauto_irun_mono S B n (fgauto_succ n) (fgauto_allowed_suc S B n) (nth i) (y .fst) (nth j) (y .snd .fst)) (y .snd .snd))
          (ih i j m .fst hm),
       z ↦ ih i j m .snd
         (mere_rec (Σ W (w ↦ Product (FgautoIRun S B (fgauto_succ n) (nth i) w (nth j)) (Id C (fgauto_val_word S M val w) m)))
           (FgautoKyLang S M val B n (nth i) (nth j) m) (fgauto_ky_lang_prop S M val B n (nth i) (nth j) m)
           (y ↦ fgauto_ky_lang_intro S M val B n (nth i) (nth j) m (y .fst)
             (fgauto_irun_mono S B (fgauto_succ n) n (fgauto_allowed_beyond S B n hk) (nth i) (y .fst) (nth j) (y .snd .fst)) (y .snd .snd)) z)) ]

def fgauto_ky_correct (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier) (B : FgautoNFA S)
  (n : Nat) (i j : Fin (fgauto_nfa_k S B)) (m : M .mcarrier)
  : FgautoIff (fgauto_rat_mem M (fgauto_ky_expr S M val B n i j) m) (FgautoKyLang S M val B n (fgauto_nfa_nth S B i) (fgauto_nfa_nth S B j) m)
  ≔ match n [
  | zero. ↦ fgauto_ky_zero S M L val B i j m
  | suc. n0 ↦ fgauto_ky_succ S M L val B n0 (fgauto_ky_correct S M L val B n0) i j m (lt_decidable n0 (fgauto_nfa_k S B)) ]
