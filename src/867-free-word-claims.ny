export "866-free-group-examples"

{` Chapter 8 (congp.tex), section "Free groups", part 5: two running-text
   claims.  (1) The hint of the xca at congp.tex:819 ("this is precisely
   the point where we need S to have decidable equality"): a reduction
   function, i.e. any map r with r(w) reduced and reached from w by
   deleting complementary pairs, exists iff S has decidable equality.
   (2) The description of F_S as an abstract group (congp.tex:771-773):
   unit eps, product rho(r s) (module 866) and inverse: the reversed
   complemented word. `}

def ReductionFunction (S : Type) : Type
  ≔ Σ (SignedWord S → SignedWord S) (r ↦
      (w : SignedWord S) → Product (IsReducedWord S (r w)) (WordReducesTo S w (r w)))

def decidable_equality_reduction_function (S : Type) (dec : DecidableEquality S) : ReductionFunction S
  ≔ (word_reduction S dec, w ↦ (word_reduction_reduced S dec w, word_reduces_to_reduction S dec w))

def fw_nil_ne_append_pair (S : Type) (u : SignedWord S) (x : SignedLetter S) (t : SignedWord S)
  (p : Id (SignedWord S) nil. (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t)))) : Empty
  ≔ match u [
  | nil. ↦ list_encode (SignedLetter S) nil. (cons. x (cons. (letter_complement S x) t)) p
  | cons. y u' ↦ list_encode (SignedLetter S) nil.
      (cons. y (append (SignedLetter S) u' (cons. x (cons. (letter_complement S x) t)))) p ]

def fw_single_ne_append_pair (S : Type) (c : SignedLetter S) (u : SignedWord S) (x : SignedLetter S)
  (t : SignedWord S)
  (p : Id (SignedWord S) (cons. c nil.) (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
  : Empty
  ≔ match u [
  | nil. ↦ list_encode (SignedLetter S) nil. (cons. (letter_complement S x) t)
      (list_encode (SignedLetter S) (cons. c nil.) (cons. x (cons. (letter_complement S x) t)) p .snd)
  | cons. y u' ↦ fw_nil_ne_append_pair S u' x t
      (list_encode (SignedLetter S) (cons. c nil.)
        (cons. y (append (SignedLetter S) u' (cons. x (cons. (letter_complement S x) t)))) p .snd) ]

{` One deletion step from a B: then b = a and the result is eps. `}
def fw_two_letter_step (S : Type) (a b : S) (u : SignedWord S) (x : SignedLetter S) (t v : SignedWord S)
  (p : Id (SignedWord S) (cons. (inl. a) (cons. (inr. b) nil.))
    (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
  (q : Id (SignedWord S) v (append (SignedLetter S) u t))
  : Product (Id S b a) (Id (SignedWord S) v nil.)
  ≔ match u [
  | nil. ↦
    let e1 ≔ list_encode (SignedLetter S) (cons. (inl. a) (cons. (inr. b) nil.))
      (cons. x (cons. (letter_complement S x) t)) p in
    let e2 ≔ list_encode (SignedLetter S) (cons. (inr. b) nil.) (cons. (letter_complement S x) t) (e1 .snd) in
    (sum_encode S S (inr. b) (inr. a)
      (concat (SignedLetter S) (inr. b) (letter_complement S x) (inr. a) (e2 .fst)
        (map_path (SignedLetter S) (SignedLetter S) (letter_complement S) x (inl. a)
          (inverse (SignedLetter S) (inl. a) x (e1 .fst)))),
     concat (SignedWord S) v t nil. q (inverse (SignedWord S) nil. t (e2 .snd)))
  | cons. y u' ↦ absurd (Product (Id S b a) (Id (SignedWord S) v nil.))
      (fw_single_ne_append_pair S (inr. b) u' x t
        (list_encode (SignedLetter S) (cons. (inl. a) (cons. (inr. b) nil.))
          (cons. y (append (SignedLetter S) u' (cons. x (cons. (letter_complement S x) t)))) p .snd)) ]

def fw_deletions_from_empty (S : Type) (n : Nat) (w v : SignedWord S) (e : Id (SignedWord S) w nil.)
  (d : WordDeletions S n w v) : Id (SignedWord S) v nil.
  ≔ match n [
  | zero. ↦ concat (SignedWord S) v w nil. (inverse (SignedWord S) w v d) e
  | suc. k ↦ absurd (Id (SignedWord S) v nil.)
      (fw_nil_ne_append_pair S (d .snd .fst .fst) (d .snd .fst .snd .fst) (d .snd .fst .snd .snd .fst)
        (concat (SignedWord S) nil. w
          (append (SignedLetter S) (d .snd .fst .fst)
            (cons. (d .snd .fst .snd .fst) (cons. (letter_complement S (d .snd .fst .snd .fst)) (d .snd .fst .snd .snd .fst))))
          (inverse (SignedWord S) w nil. e) (d .snd .fst .snd .snd .snd .fst))) ]

{` Deletion sequences from a B either do nothing or reach eps with b = a. `}
def fw_two_letter_deletions (S : Type) (a b : S) (n : Nat) (v : SignedWord S)
  (d : WordDeletions S n (cons. (inl. a) (cons. (inr. b) nil.)) v)
  : Sum (Id (SignedWord S) v (cons. (inl. a) (cons. (inr. b) nil.))) (Product (Id S b a) (Id (SignedWord S) v nil.))
  ≔ match n [
  | zero. ↦ inl. (inverse (SignedWord S) (cons. (inl. a) (cons. (inr. b) nil.)) v d)
  | suc. k ↦
    let s ≔ fw_two_letter_step S a b (d .snd .fst .fst) (d .snd .fst .snd .fst) (d .snd .fst .snd .snd .fst) (d .fst)
      (d .snd .fst .snd .snd .snd .fst) (d .snd .fst .snd .snd .snd .snd) in
    inr. (s .fst, fw_deletions_from_empty S k (d .fst) v (s .snd) (d .snd .snd)) ]

def fw_decide_two_letters (S : Type) (a b : S) (l : SignedWord S) (h : IsReducedWord S l)
  (c : Sum (Id (SignedWord S) l (cons. (inl. a) (cons. (inr. b) nil.))) (Product (Id S b a) (Id (SignedWord S) l nil.)))
  : Decidable (Id S a b)
  ≔ match c [
  | inl. e ↦ inr. (p ↦ transport (SignedWord S) (IsReducedWord S) l (cons. (inl. a) (cons. (inr. b) nil.)) e h .fst
      (inr. (inverse S a b p)))
  | inr. q ↦ inl. (inverse S b a (q .fst)) ]

{` The footnote of congp.tex:820: a reduction function decides equality
   in S, so it exists exactly when S has decidable equality. `}
def reduction_function_decidable_equality (S : Type) (r : ReductionFunction S) : DecidableEquality S
  ≔ a b ↦ fw_decide_two_letters S a b (r .fst (cons. (inl. a) (cons. (inr. b) nil.)))
      (r .snd (cons. (inl. a) (cons. (inr. b) nil.)) .fst)
      (fw_two_letter_deletions S a b (r .snd (cons. (inl. a) (cons. (inr. b) nil.)) .snd .fst)
        (r .fst (cons. (inl. a) (cons. (inr. b) nil.))) (r .snd (cons. (inl. a) (cons. (inr. b) nil.)) .snd .snd))

{` The inverse of a word: reverse it and complement every letter. `}
def word_inverse (S : Type) (w : SignedWord S) : SignedWord S
  ≔ match w [
  | nil. ↦ nil.
  | cons. x v ↦ append (SignedLetter S) (word_inverse S v) (cons. (letter_complement S x) nil.) ]

def free_word_interpretation_inverse (S : Type) (F : FreeGroupSignature S) (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (word_inverse S w))
      (inverse (F .carrier) (F .base) (F .base) (free_word_interpretation S F w))
  ≔ match w [
  | nil. ↦ inverse (Id (F .carrier) (F .base) (F .base)) (inverse (F .carrier) (F .base) (F .base) (refl (F .base)))
      (refl (F .base)) (inverse_refl (F .carrier) (F .base))
  | cons. x v ↦
    let X ≔ F .carrier in
    let b ≔ F .base in
    let W ≔ free_word_interpretation S F v in
    let l ≔ free_signed_loop S F x in
    calc
      free_word_interpretation S F (append (SignedLetter S) (word_inverse S v) (cons. (letter_complement S x) nil.))
      = concat X b b b (concat X b b b (refl b) (free_signed_loop S F (letter_complement S x)))
          (free_word_interpretation S F (word_inverse S v))
        by free_word_interpretation_append S F (word_inverse S v) (cons. (letter_complement S x) nil.)
      = concat X b b b (concat X b b b (refl b) (free_signed_loop S F (letter_complement S x))) (inverse X b b W)
        by refl (concat X b b b (concat X b b b (refl b) (free_signed_loop S F (letter_complement S x))))
          (free_word_interpretation_inverse S F v)
      = concat X b b b (free_signed_loop S F (letter_complement S x)) (inverse X b b W)
        by refl ((q ↦ concat X b b b q (inverse X b b W)) : Id X b b → Id X b b)
          (concat_1p X b b (free_signed_loop S F (letter_complement S x)))
      = concat X b b b (inverse X b b l) (inverse X b b W)
        by refl ((q ↦ concat X b b b q (inverse X b b W)) : Id X b b → Id X b b)
          (free_signed_loop_complement S F x)
      = inverse X b b (concat X b b b W l)
        by inverse (Id X b b) (inverse X b b (concat X b b b W l)) (concat X b b b (inverse X b b l) (inverse X b b W))
          (inverse_concat X b b b W l) ∎ ]

def free_group_word_inverse (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (w : SignedWord S)
  : Id (USym (free_group S dec F)) (usym_inv (free_group S dec F) (free_group_word S dec F w))
      (free_group_word S dec F (word_inverse S w))
  ≔ inverse (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (word_inverse S w))
      (inverse (F .carrier) (F .base) (F .base) (free_word_interpretation S F w))
      (free_word_interpretation_inverse S F w)

{` The abstract group structure on R_S transported from F_S: unit eps,
   product rho(r s), inverse rho(r^-1) (all as images under [-]). `}
def free_group_reduced_unit (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id (USym (free_group S dec F)) (usym_unit (free_group S dec F))
      (free_group_usym_equiv S dec F .map (reduced_image_empty S dec))
  ≔ refl (refl (F .base))

def free_group_reduced_inverse (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (r : ReducedWordImage S dec)
  : Id (USym (free_group S dec F)) (usym_inv (free_group S dec F) (free_group_usym_equiv S dec F .map r))
      (free_group_usym_equiv S dec F .map (reduced_image_factor S dec (word_inverse S (r .fst))))
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (inverse (F .carrier) (F .base) (F .base) (free_word_interpretation S F (r .fst)))
      (free_word_interpretation S F (word_inverse S (r .fst)))
      (free_word_interpretation S F (word_reduction S dec (word_inverse S (r .fst))))
      (free_group_word_inverse S dec F (r .fst))
      (inverse (Id (F .carrier) (F .base) (F .base))
        (free_word_interpretation S F (word_reduction S dec (word_inverse S (r .fst))))
        (free_word_interpretation S F (word_inverse S (r .fst)))
        (free_word_interpretation_reduction S dec F (word_inverse S (r .fst))))

{` Litmus: the inverse of a b is B A. `}
def fw_litmus_word_inverse
  : Id (SignedWord Bool) (word_inverse Bool (cons. fw_letter_a (cons. fw_letter_b nil.)))
      (cons. fw_letter_B (cons. fw_letter_A nil.))
  ≔ refl (cons. fw_letter_B (cons. fw_letter_A nil.) : SignedWord Bool)
