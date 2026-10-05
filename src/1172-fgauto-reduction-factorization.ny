export "1163-fgauto-research-statements"

{` Chapter 11, automata part 23: the combinatorics of the reduction rho
   needed for the lemma at fggroups.tex:879.

   Every word v factors as v = d0 x1 d1 x2 d2 ... xn dn with each d_k a Dyck
   word (rho(d_k) = eps) and rho(v) = x1 x2 ... xn
   (fgauto_red_factorization).  Consequently a nonempty Dyck word y w' has
   w' = d0 y-bar d1 with d0, d1 Dyck words (fgauto_dyck_first_return). `}

def FgautoFactorPiece (S : Type) : Type ≔ Product (SignedLetter S) (SignedWord S)

def fgauto_factor_concat (S : Type) (ps : List (FgautoFactorPiece S)) : SignedWord S
  ≔ match ps [ nil. ↦ nil. | cons. pd t ↦ cons. (pd .fst) (append (SignedLetter S) (pd .snd) (fgauto_factor_concat S t)) ]

def fgauto_factor_letters (S : Type) (ps : List (FgautoFactorPiece S)) : SignedWord S
  ≔ fgauto_list_map (FgautoFactorPiece S) (SignedLetter S) (pd ↦ pd .fst) ps

def FgautoRedFactor (S : Type) (dec : DecidableEquality S) (v : SignedWord S) : Type
  ≔ Σ (SignedWord S) (d0 ↦ Σ (List (FgautoFactorPiece S)) (ps ↦
      Product (Id (SignedWord S) v (append (SignedLetter S) d0 (fgauto_factor_concat S ps)))
        (Product (FgautoDyck S dec d0)
          (Product (FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) ps)
            (Id (SignedWord S) (word_reduction S dec v) (fgauto_factor_letters S ps))))))

{` rho(y d0 x1 d1) = eps when x1 = y-bar and d0, d1 are Dyck words. `}
def fgauto_dyck_wrap (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (d0 d1 : SignedWord S)
  (h0 : FgautoDyck S dec d0) (h1 : FgautoDyck S dec d1)
  : FgautoDyck S dec (cons. y (append (SignedLetter S) d0 (cons. (letter_complement S y) d1)))
  ≔ fgauto_wtrans S (word_letter_reduce S dec y (word_reduction S dec (append (SignedLetter S) d0 (cons. (letter_complement S y) d1))))
      (word_letter_reduce S dec y (cons. (letter_complement S y) nil.)) nil.
      (refl (word_letter_reduce S dec y)
        (fgauto_wtrans S (word_reduction S dec (append (SignedLetter S) d0 (cons. (letter_complement S y) d1)))
          (word_reduction S dec (cons. (letter_complement S y) d1)) (cons. (letter_complement S y) nil.)
          (fgauto_red_drop_left S dec d0 (cons. (letter_complement S y) d1) h0)
          (refl (word_letter_reduce S dec (letter_complement S y)) h1)))
      (word_letter_reduce_drop S dec y nil.)

def fgauto_factor_step_case (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (v' d0 : SignedWord S)
  (x1 : SignedLetter S) (d1 : SignedWord S) (t : List (FgautoFactorPiece S))
  (ev : Id (SignedWord S) v' (append (SignedLetter S) d0 (cons. x1 (append (SignedLetter S) d1 (fgauto_factor_concat S t)))))
  (h0 : FgautoDyck S dec d0) (h1 : FgautoDyck S dec d1) (ht : FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) t)
  (d : Decidable (Id (SignedLetter S) x1 (letter_complement S y)))
  : Σ (SignedWord S) (e0 ↦ Σ (List (FgautoFactorPiece S)) (ps ↦
      Product (Id (SignedWord S) (cons. y v') (append (SignedLetter S) e0 (fgauto_factor_concat S ps)))
        (Product (FgautoDyck S dec e0)
          (Product (FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) ps)
            (Id (SignedWord S) (fw_cancel_or_cons S y x1 (fgauto_factor_letters S t) d) (fgauto_factor_letters S ps))))))
  ≔ let L ≔ SignedLetter S in
    match d [
    | inl. e ↦
      let e0 : SignedWord S ≔ cons. y (append L d0 (cons. x1 d1)) in
      (e0, (t,
        (cons. (refl y) (fgauto_wtrans S v' (append L d0 (cons. x1 (append L d1 (fgauto_factor_concat S t))))
           (append L (append L d0 (cons. x1 d1)) (fgauto_factor_concat S t)) ev
           (fgauto_wsym S (append L (append L d0 (cons. x1 d1)) (fgauto_factor_concat S t))
             (append L d0 (cons. x1 (append L d1 (fgauto_factor_concat S t))))
             (append_assoc L d0 (cons. x1 d1) (fgauto_factor_concat S t)))),
         (transport L (z ↦ FgautoDyck S dec (cons. y (append L d0 (cons. z d1)))) (letter_complement S y) x1
            (inverse L x1 (letter_complement S y) e) (fgauto_dyck_wrap S dec y d0 d1 h0 h1),
          (ht, refl (fgauto_factor_letters S t))))))
    | inr. _ ↦
      (nil., (cons. (y, d0) (cons. (x1, d1) t),
        (cons. (refl y) ev, (refl (nil. : SignedWord S), ((h0, (h1, ht)), refl (cons. y (cons. x1 (fgauto_factor_letters S t)) : SignedWord S)))))) ]

def fgauto_red_factor_cons (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (v' d0 : SignedWord S)
  (ps : List (FgautoFactorPiece S)) (ev : Id (SignedWord S) v' (append (SignedLetter S) d0 (fgauto_factor_concat S ps)))
  (h0 : FgautoDyck S dec d0) (hps : FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) ps)
  (er : Id (SignedWord S) (word_reduction S dec v') (fgauto_factor_letters S ps)) : FgautoRedFactor S dec (cons. y v')
  ≔ let L ≔ SignedLetter S in
    match ps [
    | nil. ↦ (nil., (cons. (y, d0) nil.,
        (cons. (refl y) (fgauto_wtrans S v' (append L d0 nil.) (append L d0 nil.) ev (refl (append L d0 nil.))),
         (refl (nil. : SignedWord S), ((h0, star.), refl (word_letter_reduce S dec y) er)))))
    | cons. pd t ↦
      let z ≔ fgauto_factor_step_case S dec y v' d0 (pd .fst) (pd .snd) t ev h0 (hps .fst) (hps .snd)
        (signed_letter_decidable_equality S dec (pd .fst) (letter_complement S y)) in
      (z .fst, (z .snd .fst, (z .snd .snd .fst, (z .snd .snd .snd .fst, (z .snd .snd .snd .snd .fst,
        fgauto_wtrans S (word_letter_reduce S dec y (word_reduction S dec v'))
          (word_letter_reduce S dec y (cons. (pd .fst) (fgauto_factor_letters S t)))
          (fgauto_factor_letters S (z .snd .fst))
          (refl (word_letter_reduce S dec y) er) (z .snd .snd .snd .snd .snd)))))) ]

def fgauto_red_factorization (S : Type) (dec : DecidableEquality S) (v : SignedWord S) : FgautoRedFactor S dec v
  ≔ let L ≔ SignedLetter S in
    match v [
    | nil. ↦ (nil., (nil., (refl (nil. : SignedWord S), (refl (nil. : SignedWord S), (star., refl (nil. : SignedWord S))))))
    | cons. y v' ↦
      let f ≔ fgauto_red_factorization S dec v' in
      let d0 ≔ f .fst in
      let ps ≔ f .snd .fst in
      let ev ≔ f .snd .snd .fst in
      let h0 ≔ f .snd .snd .snd .fst in
      let hps ≔ f .snd .snd .snd .snd .fst in
      let er ≔ f .snd .snd .snd .snd .snd in
      fgauto_red_factor_cons S dec y v' d0 ps ev h0 hps er ]

{` First return of a Dyck word. `}
def fgauto_cancel_nil (S : Type) (y z : SignedLetter S) (r' : SignedWord S) (d : Decidable (Id (SignedLetter S) z (letter_complement S y)))
  (h : Id (SignedWord S) (fw_cancel_or_cons S y z r' d) nil.) : Id (SignedWord S) (cons. z r') (cons. (letter_complement S y) nil.)
  ≔ match d [
  | inl. e ↦ cons. e h
  | inr. _ ↦ match list_encode (SignedLetter S) (cons. y (cons. z r')) nil. h [] ]

def fgauto_letter_reduce_nil (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (r : SignedWord S)
  (h : Id (SignedWord S) (word_letter_reduce S dec y r) nil.) : Id (SignedWord S) r (cons. (letter_complement S y) nil.)
  ≔ match r [
  | nil. ↦ match list_encode (SignedLetter S) (cons. y nil.) nil. h []
  | cons. z r' ↦ fgauto_cancel_nil S y z r' (signed_letter_decidable_equality S dec z (letter_complement S y)) h ]

def fgauto_first_return_pieces (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (w' d0 : SignedWord S)
  (ps : List (FgautoFactorPiece S)) (ev : Id (SignedWord S) w' (append (SignedLetter S) d0 (fgauto_factor_concat S ps)))
  (h0 : FgautoDyck S dec d0) (hps : FgautoAllIn (FgautoFactorPiece S) (pd ↦ FgautoDyck S dec (pd .snd)) ps)
  (r1 : Id (SignedWord S) (fgauto_factor_letters S ps) (cons. (letter_complement S y) nil.))
  : Σ (SignedWord S) (e0 ↦ Σ (SignedWord S) (e1 ↦
      Product (Id (SignedWord S) w' (append (SignedLetter S) e0 (cons. (letter_complement S y) e1)))
        (Product (FgautoDyck S dec e0) (FgautoDyck S dec e1))))
  ≔ let L ≔ SignedLetter S in
    match ps [
    | nil. ↦ match list_encode L nil. (cons. (letter_complement S y) nil.) r1 []
    | cons. pd t ↦ match t [
      | cons. a b ↦ match list_encode L (fgauto_factor_letters S (cons. a b)) nil.
          (list_encode L (cons. (pd .fst) (fgauto_factor_letters S (cons. a b))) (cons. (letter_complement S y) nil.) r1 .snd) []
      | nil. ↦
        let ex ≔ list_encode L (cons. (pd .fst) nil.) (cons. (letter_complement S y) nil.) r1 .fst in
        (d0, (pd .snd,
          (fgauto_wtrans S w' (append L d0 (cons. (pd .fst) (append L (pd .snd) nil.))) (append L d0 (cons. (letter_complement S y) (pd .snd)))
             ev (refl ((u v ↦ append L d0 (cons. u v)) : L → SignedWord S → SignedWord S) ex (append_nil L (pd .snd))),
           (h0, hps .fst)))) ] ]

def fgauto_dyck_first_return (S : Type) (dec : DecidableEquality S) (y : SignedLetter S) (w' : SignedWord S)
  (h : FgautoDyck S dec (cons. y w'))
  : Σ (SignedWord S) (d0 ↦ Σ (SignedWord S) (d1 ↦
      Product (Id (SignedWord S) w' (append (SignedLetter S) d0 (cons. (letter_complement S y) d1)))
        (Product (FgautoDyck S dec d0) (FgautoDyck S dec d1))))
  ≔ let f ≔ fgauto_red_factorization S dec w' in
    let r1 ≔ fgauto_wtrans S (fgauto_factor_letters S (f .snd .fst)) (word_reduction S dec w') (cons. (letter_complement S y) nil.)
      (fgauto_wsym S (word_reduction S dec w') (fgauto_factor_letters S (f .snd .fst)) (f .snd .snd .snd .snd .snd))
      (fgauto_letter_reduce_nil S dec y (word_reduction S dec w') h) in
    fgauto_first_return_pieces S dec y w' (f .fst) (f .snd .fst) (f .snd .snd .fst) (f .snd .snd .snd .fst) (f .snd .snd .snd .snd .fst) r1

{` Litmus: a A A a B B b b reduces to the empty word (fggroups.tex:922). `}
def fgauto_litmus_dyck_aAAaBBbb
  : FgautoDyck Bool fw_bool_decidable_equality
      (cons. fw_letter_a (cons. fw_letter_A (cons. fw_letter_A (cons. fw_letter_a
        (cons. fw_letter_B (cons. fw_letter_B (cons. fw_letter_b (cons. fw_letter_b nil.))))))))
  ≔ refl (nil. : SignedWord Bool)
