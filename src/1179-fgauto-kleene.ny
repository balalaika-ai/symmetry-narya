export "1178-fgauto-benois-forward"

{` Chapter 11, automata part 30: from automata to rational expressions
   (McNaughton–Yamada), in a monoid M with a valuation val of the letters.

   For a finite automaton B with states nth : Fin k → states, R(n, i, j)
   describes the values of the runs from state i to state j all of whose
   intermediate states have index < n (FgautoIRun):
     R(0, i, j)     = {val x | i -x-> j} ∪ ({1} if i = j),
     R(n+1, i, j)   = R(n, i, j) ∪ R(n, i, c) R(n, c, c)* R(n, c, j)   (c the state of index n < k),
   and R(n+1) = R(n) once n >= k.  This module: values of words,
   restricted runs and their properties, including the first visit of the
   state c (fgauto_irunfrom_first_visit). `}

def fgauto_val_word (S : Type) (M : FgautoMonoid) (val : SignedLetter S → M .mcarrier) (w : SignedWord S) : M .mcarrier
  ≔ match w [ nil. ↦ M .munit | cons. x t ↦ M .mmul (val x) (fgauto_val_word S M val t) ]

def fgauto_val_word_append (S : Type) (M : FgautoMonoid) (L : FgautoMonoidLaws M) (val : SignedLetter S → M .mcarrier)
  (u v : SignedWord S)
  : Id (M .mcarrier) (fgauto_val_word S M val (append (SignedLetter S) u v)) (M .mmul (fgauto_val_word S M val u) (fgauto_val_word S M val v))
  ≔ match u [
  | nil. ↦ inverse (M .mcarrier) (M .mmul (M .munit) (fgauto_val_word S M val v)) (fgauto_val_word S M val v) (L .ml_unit_left (fgauto_val_word S M val v))
  | cons. x t ↦ concat (M .mcarrier) (M .mmul (val x) (fgauto_val_word S M val (append (SignedLetter S) t v)))
      (M .mmul (val x) (M .mmul (fgauto_val_word S M val t) (fgauto_val_word S M val v)))
      (M .mmul (M .mmul (val x) (fgauto_val_word S M val t)) (fgauto_val_word S M val v))
      (refl (M .mmul (val x)) (fgauto_val_word_append S M L val t v))
      (L .ml_assoc (val x) (fgauto_val_word S M val t) (fgauto_val_word S M val v)) ]

def fgauto_succ (n : Nat) : Nat ≔ suc. n

{` Positions in Fin k as numbers (own version, independent of module 32). `}
def fgauto_fin_nat (k : Nat) (j : Fin k) : Nat
  ≔ match k [ zero. ↦ match j [] | suc. k0 ↦ match j [ inl. j0 ↦ fgauto_fin_nat k0 j0 | inr. _ ↦ k0 ] ]

def fgauto_fin_nat_bound (k : Nat) (j : Fin k) : Lt (fgauto_fin_nat k j) k
  ≔ match k [
  | zero. ↦ match j []
  | suc. k0 ↦ match j [ inl. j0 ↦ le_step (suc. (fgauto_fin_nat k0 j0)) k0 (fgauto_fin_nat_bound k0 j0) | inr. _ ↦ le_refl k0 ] ]

def fgauto_fin_nat_injective (k : Nat) (i j : Fin k) (e : Id Nat (fgauto_fin_nat k i) (fgauto_fin_nat k j)) : Id (Fin k) i j
  ≔ match k [
  | zero. ↦ match i []
  | suc. k0 ↦ match i, j [
    | inl. i0, inl. j0 ↦ inl. (fgauto_fin_nat_injective k0 i0 j0 e)
    | inl. i0, inr. _ ↦ match lt_not_equal (fgauto_fin_nat k0 i0) k0 (fgauto_fin_nat_bound k0 i0) e []
    | inr. _, inl. j0 ↦ match lt_not_equal (fgauto_fin_nat k0 j0) k0 (fgauto_fin_nat_bound k0 j0) (inverse Nat k0 (fgauto_fin_nat k0 j0) e) []
    | inr. u, inr. u2 ↦ inr. (unit_prop u u2) ] ]

def fgauto_fin_of_nat_choose (k0 n : Nat) (h : Le n k0) (d : Decidable (Id Nat n k0))
  (recur : Lt n k0 → Fin k0) : Fin (suc. k0)
  ≔ match d [ inl. _ ↦ inr. star. | inr. no ↦ inl. (recur (le_not_equal_lt n k0 h no)) ]

def fgauto_fin_of_nat (k n : Nat) (h : Lt n k) : Fin k
  ≔ match k [
  | zero. ↦ match h []
  | suc. k0 ↦ fgauto_fin_of_nat_choose k0 n h (nat_dec_eq n k0) (fgauto_fin_of_nat k0 n) ]

def fgauto_fin_of_nat_choose_spec (k0 n : Nat) (h : Le n k0) (d : Decidable (Id Nat n k0)) (recur : Lt n k0 → Fin k0)
  (ih : (h0 : Lt n k0) → Id Nat (fgauto_fin_nat k0 (recur h0)) n)
  : Id Nat (fgauto_fin_nat (suc. k0) (fgauto_fin_of_nat_choose k0 n h d recur)) n
  ≔ match d [ inl. e ↦ inverse Nat n k0 e | inr. no ↦ ih (le_not_equal_lt n k0 h no) ]

def fgauto_fin_of_nat_spec (k n : Nat) (h : Lt n k) : Id Nat (fgauto_fin_nat k (fgauto_fin_of_nat k n h)) n
  ≔ match k [
  | zero. ↦ match h []
  | suc. k0 ↦ fgauto_fin_of_nat_choose_spec k0 n h (nat_dec_eq n k0) (fgauto_fin_of_nat k0 n) (fgauto_fin_of_nat_spec k0 n) ]

def fgauto_fin_at (k n : Nat) (h : Lt n k) : Fin k ≔ fgauto_fin_of_nat k n h

{` Restricted runs: after the first step every state that is left again
   must be allowed. `}
def FgautoAllowed (S : Type) (B : FgautoNFA S) (n : Nat) (v : B .nstate) : Type
  ≔ Σ (Fin (fgauto_nfa_k S B)) (j ↦ Product (Lt (fgauto_fin_nat (fgauto_nfa_k S B) j) n) (Id (B .nstate) (fgauto_nfa_nth S B j) v))

def fgauto_allowed_mk (S : Type) (B : FgautoNFA S) (n : Nat) (v : B .nstate) (j : Fin (fgauto_nfa_k S B))
  (h : Lt (fgauto_fin_nat (fgauto_nfa_k S B) j) n) (e : Id (B .nstate) (fgauto_nfa_nth S B j) v) : FgautoAllowed S B n v
  ≔ (j, (h, e))

def FgautoIRunFrom (S : Type) (B : FgautoNFA S) (n : Nat) (r : B .nstate) (w : SignedWord S) (q : B .nstate) : Type
  ≔ match w [
  | nil. ↦ Id (B .nstate) r q
  | cons. y w2 ↦ Product (FgautoAllowed S B n r)
      (Σ (B .nstate) (r2 ↦ Product (FgautoStep S (B .nstate) (B .nedges) r y r2) (FgautoIRunFrom S B n r2 w2 q))) ]

def FgautoIRun (S : Type) (B : FgautoNFA S) (n : Nat) (p : B .nstate) (w : SignedWord S) (q : B .nstate) : Type
  ≔ match w [
  | nil. ↦ Id (B .nstate) p q
  | cons. x w1 ↦ Σ (B .nstate) (r ↦ Product (FgautoStep S (B .nstate) (B .nedges) p x r) (FgautoIRunFrom S B n r w1 q)) ]

def fgauto_irunfrom_run (S : Type) (B : FgautoNFA S) (n : Nat) (r : B .nstate) (w : SignedWord S) (q : B .nstate)
  (t : FgautoIRunFrom S B n r w q) : FgautoRun S (B .nstate) (B .nedges) r w q
  ≔ match w [
  | nil. ↦ t
  | cons. y w2 ↦ (t .snd .fst, (t .snd .snd .fst, fgauto_irunfrom_run S B n (t .snd .fst) w2 q (t .snd .snd .snd))) ]

def fgauto_irun_run (S : Type) (B : FgautoNFA S) (n : Nat) (p : B .nstate) (w : SignedWord S) (q : B .nstate)
  (r : FgautoIRun S B n p w q) : FgautoRun S (B .nstate) (B .nedges) p w q
  ≔ match w [
  | nil. ↦ r
  | cons. x w1 ↦ (r .fst, (r .snd .fst, fgauto_irunfrom_run S B n (r .fst) w1 q (r .snd .snd))) ]

{` Changing the bound. `}
def fgauto_irunfrom_mono (S : Type) (B : FgautoNFA S) (n m : Nat) (f : (v : B .nstate) → FgautoAllowed S B n v → FgautoAllowed S B m v)
  (r : B .nstate) (w : SignedWord S) (q : B .nstate) (t : FgautoIRunFrom S B n r w q) : FgautoIRunFrom S B m r w q
  ≔ match w [
  | nil. ↦ t
  | cons. y w2 ↦ (f r (t .fst), (t .snd .fst, (t .snd .snd .fst, fgauto_irunfrom_mono S B n m f (t .snd .fst) w2 q (t .snd .snd .snd)))) ]

def fgauto_irun_mono (S : Type) (B : FgautoNFA S) (n m : Nat) (f : (v : B .nstate) → FgautoAllowed S B n v → FgautoAllowed S B m v)
  (p : B .nstate) (w : SignedWord S) (q : B .nstate) (r : FgautoIRun S B n p w q) : FgautoIRun S B m p w q
  ≔ match w [
  | nil. ↦ r
  | cons. x w1 ↦ (r .fst, (r .snd .fst, fgauto_irunfrom_mono S B n m f (r .fst) w1 q (r .snd .snd))) ]

def fgauto_allowed_mono (S : Type) (B : FgautoNFA S) (n m : Nat) (hnm : Le n m) (v : B .nstate) (a : FgautoAllowed S B n v)
  : FgautoAllowed S B m v
  ≔ (a .fst, (le_trans (suc. (fgauto_fin_nat (fgauto_nfa_k S B) (a .fst))) n m (a .snd .fst) hnm, a .snd .snd))

{` From a run starting at an allowed state. `}
def fgauto_irun_from_allowed (S : Type) (B : FgautoNFA S) (n : Nat) (s : B .nstate) (hs : FgautoAllowed S B n s)
  (v : SignedWord S) (q : B .nstate) (b : FgautoIRun S B n s v q) : FgautoIRunFrom S B n s v q
  ≔ match v [ nil. ↦ b | cons. y v2 ↦ (hs, b) ]

{` Concatenation through an allowed state. `}
def fgauto_irunfrom_append (S : Type) (B : FgautoNFA S) (n : Nat) (r : B .nstate) (u : SignedWord S) (s : B .nstate) (v : SignedWord S)
  (q : B .nstate) (hs : FgautoAllowed S B n s) (a : FgautoIRunFrom S B n r u s) (b : FgautoIRun S B n s v q)
  : FgautoIRunFrom S B n r (append (SignedLetter S) u v) q
  ≔ match u [
  | nil. ↦ transport (B .nstate) (z ↦ FgautoIRunFrom S B n z v q) s r (inverse (B .nstate) r s a) (fgauto_irun_from_allowed S B n s hs v q b)
  | cons. y u2 ↦ (a .fst, (a .snd .fst, (a .snd .snd .fst, fgauto_irunfrom_append S B n (a .snd .fst) u2 s v q hs (a .snd .snd .snd) b))) ]

def fgauto_irun_append (S : Type) (B : FgautoNFA S) (n : Nat) (p : B .nstate) (u : SignedWord S) (s : B .nstate) (v : SignedWord S)
  (q : B .nstate) (hs : FgautoAllowed S B n s) (a : FgautoIRun S B n p u s) (b : FgautoIRun S B n s v q)
  : FgautoIRun S B n p (append (SignedLetter S) u v) q
  ≔ match u [
  | nil. ↦ transport (B .nstate) (z ↦ FgautoIRun S B n z v q) s p (inverse (B .nstate) p s a) b
  | cons. x u1 ↦ (a .fst, (a .snd .fst, fgauto_irunfrom_append S B n (a .fst) u1 s v q hs (a .snd .snd) b)) ]

{` With n = k every run is allowed. `}
def fgauto_allowed_all (S : Type) (B : FgautoNFA S) (v : B .nstate) (m : FgautoMem (B .nstate) v (fgauto_nfa_states S B))
  : FgautoAllowed S B (fgauto_nfa_k S B) v
  ≔ fgauto_allowed_mk S B (fgauto_nfa_k S B) v (fgauto_nfa_pos S B v m) (fgauto_fin_nat_bound (fgauto_nfa_k S B) (fgauto_nfa_pos S B v m))
      (fgauto_nfa_nth_pos S B v m)

def fgauto_run_irunfrom_all (S : Type) (B : FgautoNFA S) (r : B .nstate) (m : FgautoMem (B .nstate) r (fgauto_nfa_states S B))
  (w : SignedWord S) (q : B .nstate) (t : FgautoRun S (B .nstate) (B .nedges) r w q) : FgautoIRunFrom S B (fgauto_nfa_k S B) r w q
  ≔ match w [
  | nil. ↦ t
  | cons. y w2 ↦ (fgauto_allowed_all S B r m, (t .fst, (t .snd .fst,
      fgauto_run_irunfrom_all S B (t .fst) (fgauto_nfa_endpoint_state S B r y (t .fst) (t .snd .fst)) w2 q (t .snd .snd)))) ]

def fgauto_run_irun_all (S : Type) (B : FgautoNFA S) (p : B .nstate) (w : SignedWord S) (q : B .nstate)
  (r : FgautoRun S (B .nstate) (B .nedges) p w q) : FgautoIRun S B (fgauto_nfa_k S B) p w q
  ≔ match w [
  | nil. ↦ r
  | cons. x w1 ↦ (r .fst, (r .snd .fst,
      fgauto_run_irunfrom_all S B (r .fst) (fgauto_nfa_endpoint_state S B p x (r .fst) (r .snd .fst)) w1 q (r .snd .snd))) ]

{` Allowed at level n+1: allowed at level n or the state c of index n. `}
def fgauto_allowed_split (S : Type) (B : FgautoNFA S) (n : Nat) (h : Lt n (fgauto_nfa_k S B)) (v : B .nstate)
  (a : FgautoAllowed S B (fgauto_succ n) v)
  : Sum (FgautoAllowed S B n v) (Id (B .nstate) (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) v)
  ≔ let k ≔ fgauto_nfa_k S B in
    match le_split (fgauto_fin_nat k (a .fst)) n (a .snd .fst) [
    | inl. lt ↦ inl. (fgauto_allowed_mk S B n v (a .fst) lt (a .snd .snd))
    | inr. e ↦ inr. (concat (B .nstate) (fgauto_nfa_nth S B (fgauto_fin_at k n h)) (fgauto_nfa_nth S B (a .fst)) v
        (refl (fgauto_nfa_nth S B) (fgauto_fin_nat_injective k (fgauto_fin_at k n h) (a .fst)
          (concat Nat (fgauto_fin_nat k (fgauto_fin_at k n h)) n (fgauto_fin_nat k (a .fst)) (fgauto_fin_of_nat_spec k n h) (inverse Nat (fgauto_fin_nat k (a .fst)) n e))))
        (a .snd .snd)) ]

def fgauto_allowed_beyond (S : Type) (B : FgautoNFA S) (n : Nat) (h : Le (fgauto_nfa_k S B) n) (v : B .nstate)
  (a : FgautoAllowed S B (fgauto_succ n) v) : FgautoAllowed S B n v
  ≔ fgauto_allowed_mk S B n v (a .fst) (lt_le_trans (fgauto_fin_nat (fgauto_nfa_k S B) (a .fst)) (fgauto_nfa_k S B) n (fgauto_fin_nat_bound (fgauto_nfa_k S B) (a .fst)) h) (a .snd .snd)

def fgauto_allowed_c (S : Type) (B : FgautoNFA S) (n : Nat) (h : Lt n (fgauto_nfa_k S B))
  : FgautoAllowed S B (fgauto_succ n) (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h))
  ≔ let k ≔ fgauto_nfa_k S B in
    fgauto_allowed_mk S B (fgauto_succ n) (fgauto_nfa_nth S B (fgauto_fin_at k n h)) (fgauto_fin_at k n h)
      (transport Nat (z ↦ Lt z (fgauto_succ n)) n (fgauto_fin_nat k (fgauto_fin_at k n h))
        (inverse Nat (fgauto_fin_nat k (fgauto_fin_at k n h)) n (fgauto_fin_of_nat_spec k n h)) (le_refl n))
      (refl (fgauto_nfa_nth S B (fgauto_fin_at k n h)))

{` First visit of c. `}
def FgautoFirstVisit (S : Type) (B : FgautoNFA S) (n : Nat) (c r : B .nstate) (w : SignedWord S) (q : B .nstate) : Type
  ≔ Σ (SignedWord S) (u ↦ Σ (SignedWord S) (v ↦ Product (Id (SignedWord S) w (append (SignedLetter S) u v))
      (Product (FgautoIRunFrom S B n r u c) (FgautoIRun S B (fgauto_succ n) c v q))))

def fgauto_irunfrom_first_visit (S : Type) (B : FgautoNFA S) (n : Nat) (h : Lt n (fgauto_nfa_k S B)) (r : B .nstate) (w : SignedWord S)
  (q : B .nstate) (t : FgautoIRunFrom S B (fgauto_succ n) r w q)
  : Sum (FgautoIRunFrom S B n r w q) (FgautoFirstVisit S B n (fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h)) r w q)
  ≔ let c ≔ fgauto_nfa_nth S B (fgauto_fin_at (fgauto_nfa_k S B) n h) in
    match w [
    | nil. ↦ inl. t
    | cons. y w2 ↦ match fgauto_allowed_split S B n h r (t .fst) [
      | inr. ec ↦ inr. (nil., (cons. y w2, (refl (cons. y w2 : SignedWord S), (inverse (B .nstate) c r ec,
          transport (B .nstate) (z ↦ FgautoIRun S B (fgauto_succ n) z (cons. y w2) q) r c (inverse (B .nstate) c r ec) (t .snd)))))
      | inl. an ↦ match fgauto_irunfrom_first_visit S B n h (t .snd .fst) w2 q (t .snd .snd .snd) [
        | inl. t2 ↦ inl. (an, (t .snd .fst, (t .snd .snd .fst, t2)))
        | inr. fv ↦ inr. (cons. y (fv .fst), (fv .snd .fst,
            (cons. (refl y) (fv .snd .snd .fst),
             ((an, (t .snd .fst, (t .snd .snd .fst, fv .snd .snd .snd .fst))), fv .snd .snd .snd .snd)))) ] ] ]

def fgauto_allowed_suc (S : Type) (B : FgautoNFA S) (n : Nat) (v : B .nstate) (a : FgautoAllowed S B n v) : FgautoAllowed S B (fgauto_succ n) v
  ≔ fgauto_allowed_mono S B n (fgauto_succ n) (le_step n n (le_refl n)) v a
