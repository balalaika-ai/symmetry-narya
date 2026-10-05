export "865-free-group"
export "435-circle-group-homomorphisms"
export "485-infinity-groups"

{` Chapter 8 (congp.tex), section "Free groups", part 4: the running-text
   claims around def:bfree (Z is free on one generator; a priori F_S is
   only an infinity-group and Hom(F_S, G) = (S -> USym G) for every
   infinity-group G; the multiplication of F_S on reduced words), and the
   xca at congp.tex:929: R_1 = Z with eps |-> 0 and s_* corresponding to
   the successor, hence also S~_1*/~ = Z. `}

{` congp.tex:704-709: Z = circle_group C is the free group on one
   generator (ex:Zinitial, module 435, composed with (USym G) = (1 -> USym G)). `}
def circle_group_hom_unit_equiv (C : CircleSignature) (G : Group)
  : Equiv (GroupHom (circle_group C) G) (Unit → USym G)
  ≔ compose_equiv (GroupHom (circle_group C) G) (USym G) (Unit → USym G)
      (circle_group_hom_ev C G) (unit_function_equiv (USym G))

def circle_group_is_free_on_unit (C : CircleSignature)
  : IsFreeGroupOn Unit (circle_group C) (_ ↦ circle_group_loop C)
  ≔ G ↦ circle_group_hom_unit_equiv C G .equiv

{` congp.tex:759-763: for every type S, F_S is an infinity-group (B F_S is
   pointed and connected), and Hom(F_S, G) = (S -> USym G) by evaluation for
   every infinity-group G (module 485). `}
def free_infty_group (S : Type) (F : FreeGroupSignature S) : InftyGroup
  ≔ mk_infty_group (F .carrier, F .base, free_connected S F)

def free_infty_group_hom_equiv (S : Type) (F : FreeGroupSignature S) (G : InftyGroup)
  : Equiv (InftyGroupHom (free_infty_group S F) G) (S → Id (infty_BG G .carrier) (infty_shape G) (infty_shape G))
  ≔ compose_equiv (InftyGroupHom (free_infty_group S F) G) (BookPointedMap (free_pointed S F) (infty_BG G))
      (S → Id (infty_BG G .carrier) (infty_shape G) (infty_shape G))
      (quasi_inverse_equiv (InftyGroupHom (free_infty_group S F) G) (BookPointedMap (free_pointed S F) (infty_BG G))
        (infty_hom_B (free_infty_group S F) G) (mk_infty_hom (free_infty_group S F) G) (f ↦ refl f) (k ↦ refl k))
      (free_pointed_universal_property S F (infty_BG G .carrier) (infty_shape G))

{` For decidable S the group F_S is this infinity-group. `}
def free_group_infty_group (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id InftyGroup (group_to_infty_group (free_group S dec F)) (free_infty_group S F)
  ≔ refl (free_infty_group S F)

{` congp.tex:774-777 ("a description of F_S as an abstract group"): the
   product of [r] and [s] is the interpretation of the reduced
   concatenation rho(r s). `}
def free_group_word_mul (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (u v : SignedWord S)
  : Id (USym (free_group S dec F))
      (usym_mul (free_group S dec F) (free_group_word S dec F u) (free_group_word S dec F v))
      (free_group_word S dec F (word_reduction S dec (append (SignedLetter S) u v)))
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v) (free_word_interpretation S F u))
      (free_word_interpretation S F (append (SignedLetter S) u v))
      (free_word_interpretation S F (word_reduction S dec (append (SignedLetter S) u v)))
      (inverse (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (append (SignedLetter S) u v))
        (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
          (free_word_interpretation S F u))
        (free_word_interpretation_append S F u v))
      (inverse (Id (F .carrier) (F .base) (F .base))
        (free_word_interpretation S F (word_reduction S dec (append (SignedLetter S) u v)))
        (free_word_interpretation S F (append (SignedLetter S) u v))
        (free_word_interpretation_reduction S dec F (append (SignedLetter S) u v)))

def free_group_reduced_mul (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (r s : ReducedWordImage S dec)
  : Id (USym (free_group S dec F))
      (usym_mul (free_group S dec F) (free_group_usym_equiv S dec F .map r) (free_group_usym_equiv S dec F .map s))
      (free_group_usym_equiv S dec F .map (reduced_image_factor S dec (append (SignedLetter S) (r .fst) (s .fst))))
  ≔ free_group_word_mul S dec F (r .fst) (s .fst)

{` xca at congp.tex:929.  Words over 1~ = 1 + 1: a = inl star, A = inr star;
   the degree counts a as +1 and A as -1. `}
def fw_unit_letter_shift (x : SignedLetter Unit) : Int → Int
  ≔ match x [ inl. _ ↦ int_succ | inr. _ ↦ int_pred ]

def unit_word_degree (w : SignedWord Unit) : Int
  ≔ match w [ nil. ↦ int_zero | cons. x v ↦ fw_unit_letter_shift x (unit_word_degree v) ]

{` a^n and A^(n+1). `}
def unit_power_word (n : Nat) : SignedWord Unit
  ≔ match n [ zero. ↦ nil. | suc. k ↦ cons. (inl. star.) (unit_power_word k) ]

def unit_inverse_power_word (n : Nat) : SignedWord Unit
  ≔ match n [ zero. ↦ cons. (inr. star.) nil. | suc. k ↦ cons. (inr. star.) (unit_inverse_power_word k) ]

def integer_unit_word (z : Int) : SignedWord Unit
  ≔ match z [ pos. n ↦ unit_power_word n | neg. n ↦ unit_inverse_power_word n ]

def fw_unit_power_head (k : Nat) : WordHeadNotComplement Unit (inl. star.) (unit_power_word k)
  ≔ match k [ zero. ↦ star. | suc. j ↦ p ↦ sum_encode Unit Unit (inl. star.) (inr. star.) p ]

def fw_unit_inverse_power_head (k : Nat) : WordHeadNotComplement Unit (inr. star.) (unit_inverse_power_word k)
  ≔ match k [
  | zero. ↦ p ↦ sum_encode Unit Unit (inr. star.) (inl. star.) p
  | suc. j ↦ p ↦ sum_encode Unit Unit (inr. star.) (inl. star.) p ]

def unit_power_word_reduced (n : Nat) : IsReducedWord Unit (unit_power_word n)
  ≔ match n [ zero. ↦ star. | suc. k ↦ (fw_unit_power_head k, unit_power_word_reduced k) ]

def unit_inverse_power_word_reduced (n : Nat) : IsReducedWord Unit (unit_inverse_power_word n)
  ≔ match n [
  | zero. ↦ (star., star.)
  | suc. k ↦ (fw_unit_inverse_power_head k, unit_inverse_power_word_reduced k) ]

def integer_unit_word_reduced (z : Int) : IsReducedWord Unit (integer_unit_word z)
  ≔ match z [ pos. n ↦ unit_power_word_reduced n | neg. n ↦ unit_inverse_power_word_reduced n ]

def integer_to_reduced_image (z : Int) : ReducedWordImage Unit unit_decidable_equality
  ≔ reduced_word_to_image Unit unit_decidable_equality (integer_unit_word z, integer_unit_word_reduced z)

def fw_unit_degree_power (n : Nat) : Id Int (unit_word_degree (unit_power_word n)) (pos. n)
  ≔ match n [ zero. ↦ refl (pos. zero. : Int) | suc. k ↦ refl int_succ (fw_unit_degree_power k) ]

def fw_unit_degree_inverse_power (n : Nat) : Id Int (unit_word_degree (unit_inverse_power_word n)) (neg. n)
  ≔ match n [ zero. ↦ refl (neg. zero. : Int) | suc. k ↦ refl int_pred (fw_unit_degree_inverse_power k) ]

def integer_unit_word_degree (z : Int) : Id Int (unit_word_degree (integer_unit_word z)) z
  ≔ match z [ pos. n ↦ fw_unit_degree_power n | neg. n ↦ fw_unit_degree_inverse_power n ]

{` The successor and predecessor are the letter steps of a and A. `}
def fw_unit_word_succ (z : Int)
  : Id (SignedWord Unit) (integer_unit_word (int_succ z))
      (word_letter_reduce Unit unit_decidable_equality (inl. star.) (integer_unit_word z))
  ≔ match z [
  | pos. zero. ↦ refl (cons. (inl. star.) nil. : SignedWord Unit)
  | pos. (suc. n) ↦ refl (integer_unit_word (pos. (suc. (suc. n))))
  | neg. zero. ↦ refl (nil. : SignedWord Unit)
  | neg. (suc. n) ↦ refl (unit_inverse_power_word n) ]

def fw_unit_word_pred (z : Int)
  : Id (SignedWord Unit) (integer_unit_word (int_pred z))
      (word_letter_reduce Unit unit_decidable_equality (inr. star.) (integer_unit_word z))
  ≔ match z [
  | pos. zero. ↦ refl (cons. (inr. star.) nil. : SignedWord Unit)
  | pos. (suc. n) ↦ refl (unit_power_word n)
  | neg. zero. ↦ refl (cons. (inr. star.) (cons. (inr. star.) nil.) : SignedWord Unit)
  | neg. (suc. n) ↦ refl (integer_unit_word (neg. (suc. (suc. n)))) ]

def fw_unit_word_letter (x : SignedLetter Unit) (z : Int)
  : Id (SignedWord Unit) (integer_unit_word (fw_unit_letter_shift x z))
      (word_letter_reduce Unit unit_decidable_equality x (integer_unit_word z))
  ≔ match x [
  | inl. u ↦ match u [ star. ↦ fw_unit_word_succ z ]
  | inr. u ↦ match u [ star. ↦ fw_unit_word_pred z ] ]

{` integer_unit_word (degree w) = rho(w) for every word w. `}
def integer_unit_word_degree_reduction (w : SignedWord Unit)
  : Id (SignedWord Unit) (integer_unit_word (unit_word_degree w)) (word_reduction Unit unit_decidable_equality w)
  ≔ match w [
  | nil. ↦ refl (nil. : SignedWord Unit)
  | cons. x v ↦ concat (SignedWord Unit)
      (integer_unit_word (fw_unit_letter_shift x (unit_word_degree v)))
      (word_letter_reduce Unit unit_decidable_equality x (integer_unit_word (unit_word_degree v)))
      (word_letter_reduce Unit unit_decidable_equality x (word_reduction Unit unit_decidable_equality v))
      (fw_unit_word_letter x (unit_word_degree v))
      (refl (word_letter_reduce Unit unit_decidable_equality x) (integer_unit_word_degree_reduction v)) ]

{` The degree is invariant under reduction. `}
def fw_unit_degree_cancel (x : SignedLetter Unit) (v : SignedWord Unit)
  : Id Int (unit_word_degree (cons. x (cons. (letter_complement Unit x) v))) (unit_word_degree v)
  ≔ match x [
  | inl. u ↦ int_succ_pred (unit_word_degree v)
  | inr. u ↦ int_pred_succ (unit_word_degree v) ]

def fw_unit_degree_cancel_or_cons (x y : SignedLetter Unit) (v : SignedWord Unit)
  (d : Decidable (Id (SignedLetter Unit) y (letter_complement Unit x)))
  : Id Int (unit_word_degree (fw_cancel_or_cons Unit x y v d)) (unit_word_degree (cons. x (cons. y v)))
  ≔ match d [
  | inl. p ↦ inverse Int (unit_word_degree (cons. x (cons. y v))) (unit_word_degree v)
      (concat Int (unit_word_degree (cons. x (cons. y v)))
        (unit_word_degree (cons. x (cons. (letter_complement Unit x) v))) (unit_word_degree v)
        (map_path (SignedLetter Unit) Int (z ↦ unit_word_degree (cons. x (cons. z v))) y (letter_complement Unit x) p)
        (fw_unit_degree_cancel x v))
  | inr. _ ↦ refl (unit_word_degree (cons. x (cons. y v))) ]

def fw_unit_degree_letter_reduce (x : SignedLetter Unit) (w : SignedWord Unit)
  : Id Int (unit_word_degree (word_letter_reduce Unit unit_decidable_equality x w)) (unit_word_degree (cons. x w))
  ≔ match w [
  | nil. ↦ refl (unit_word_degree (cons. x nil.))
  | cons. y v ↦ fw_unit_degree_cancel_or_cons x y v
      (signed_letter_decidable_equality Unit unit_decidable_equality y (letter_complement Unit x)) ]

def unit_word_degree_reduction (w : SignedWord Unit)
  : Id Int (unit_word_degree (word_reduction Unit unit_decidable_equality w)) (unit_word_degree w)
  ≔ match w [
  | nil. ↦ refl int_zero
  | cons. x v ↦ concat Int
      (unit_word_degree (word_letter_reduce Unit unit_decidable_equality x (word_reduction Unit unit_decidable_equality v)))
      (unit_word_degree (cons. x (word_reduction Unit unit_decidable_equality v)))
      (unit_word_degree (cons. x v))
      (fw_unit_degree_letter_reduce x (word_reduction Unit unit_decidable_equality v))
      (refl (fw_unit_letter_shift x) (unit_word_degree_reduction v)) ]

{` The equivalence R_1 = Z of the xca. `}
def reduced_words_one_degree (r : ReducedWordImage Unit unit_decidable_equality) : Int
  ≔ unit_word_degree (r .fst)

def reduced_words_one_integers_equiv : Equiv (ReducedWordImage Unit unit_decidable_equality) Int
  ≔ quasi_inverse_equiv (ReducedWordImage Unit unit_decidable_equality) Int
      reduced_words_one_degree integer_to_reduced_image
      (r ↦ reduced_image_path Unit unit_decidable_equality (integer_to_reduced_image (unit_word_degree (r .fst))) r
        (concat (SignedWord Unit) (integer_unit_word (unit_word_degree (r .fst)))
          (word_reduction Unit unit_decidable_equality (r .fst)) (r .fst)
          (integer_unit_word_degree_reduction (r .fst))
          (reduced_image_word_fixed Unit unit_decidable_equality r)))
      integer_unit_word_degree

def reduced_words_one_zero
  : Id Int (reduced_words_one_integers_equiv .map (reduced_image_empty Unit unit_decidable_equality)) int_zero
  ≔ refl int_zero

def reduced_words_one_successor (r : ReducedWordImage Unit unit_decidable_equality)
  : Id Int (reduced_words_one_integers_equiv .map (image_letter_action Unit unit_decidable_equality (inl. star.) r))
      (int_succ (reduced_words_one_integers_equiv .map r))
  ≔ unit_word_degree_reduction (cons. (inl. star.) (r .fst))

{` xca (congp.tex:929): an equivalence R_1 = Z with eps |-> 0 under which
   s_* corresponds to the successor. `}
def xca_reduced_words_one_integers
  : Σ (BookEquiv (ReducedWordImage Unit unit_decidable_equality) Int) (e ↦
      Product (Id Int (e .map (reduced_image_empty Unit unit_decidable_equality)) int_zero)
        ((r : ReducedWordImage Unit unit_decidable_equality)
          → Id Int (e .map (image_letter_action Unit unit_decidable_equality (inl. star.) r)) (int_succ (e .map r))))
  ≔ (book_equivalence (ReducedWordImage Unit unit_decidable_equality) Int reduced_words_one_integers_equiv,
      (reduced_words_one_zero, reduced_words_one_successor))

{` "two more options ... : S~_1*/~ and R_1" (footnote ft:many-integers). `}
def word_quotient_one_integers_equiv : Equiv (WordReductionQuotient Unit unit_decidable_equality) Int
  ≔ compose_equiv (WordReductionQuotient Unit unit_decidable_equality) (ReducedWordImage Unit unit_decidable_equality) Int
      (word_quotient_image_equiv Unit unit_decidable_equality) reduced_words_one_integers_equiv

{` Litmus: a a A a |-> 2, A A |-> -2 (neg. 1). `}
def fw_litmus_degree_two
  : Id Int (reduced_words_one_integers_equiv .map (reduced_image_factor Unit unit_decidable_equality
      (cons. (inl. star.) (cons. (inl. star.) (cons. (inr. star.) (cons. (inl. star.) nil.))))))
      (pos. (suc. (suc. zero.)))
  ≔ refl (pos. (suc. (suc. zero.)) : Int)

def fw_litmus_integer_minus_two
  : Id (SignedWord Unit) (integer_to_reduced_image (neg. (suc. zero.)) .fst)
      (cons. (inr. star.) (cons. (inr. star.) nil.))
  ≔ refl (cons. (inr. star.) (cons. (inr. star.) nil.) : SignedWord Unit)
