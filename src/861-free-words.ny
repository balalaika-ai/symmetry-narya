export "404-group-examples"

{` Chapter 8 (congp.tex), section "Free groups" (lines 700-954), part 1:
   signed letters, words, reduced words, the letter action s_x, the
   reduction map rho_S, the set R_S of reduced words (the image of rho_S)
   and the Dyck words D_S.

   Words are lists (module 01, def:lists) over the signed letters
   S~ = S + S, with inl a = a and inr a = A = a-bar.  The book fixes a
   decidable set S; here the hypothesis is a decision procedure
   dec : DecidableEquality S (a decidable set in the sense of module 161 by
   hedberg).  Reducedness itself needs no hypothesis on S.

   The reduction rho_S (xca at congp.tex:819: "complete the definition of
   rho_S by nested induction on words") is defined by rho(eps) = eps and
   rho(x w) = s_x(rho w), where the letter step s_x(v) deletes the head of
   v when it is x-bar and conses x otherwise.  The inner case distinction
   on the head of rho(w) is where decidable equality is used.  Module 862
   proves that rho(w) arises from w by deleting consecutive complementary
   pairs and is the only reduced word so obtained (the book's "repeatedly
   delete ... until none remain"). `}

{` congp.tex:782.  The set of signed letters S~ = S + S. `}
def SignedLetter (S : Type) : Type ≔ Sum S S

{` Complementation swaps the two copies of S.  With a = inl a and
   A = inr a we get a-bar = A and A-bar = a judgmentally. `}
def letter_complement (S : Type) (x : SignedLetter S) : SignedLetter S
  ≔ match x [ inl. a ↦ inr. a | inr. a ↦ inl. a ]

def letter_complement_left (S : Type) (a : S)
  : Id (SignedLetter S) (letter_complement S (inl. a)) (inr. a)
  ≔ refl (inr. a : SignedLetter S)

def letter_complement_right (S : Type) (a : S)
  : Id (SignedLetter S) (letter_complement S (inr. a)) (inl. a)
  ≔ refl (inl. a : SignedLetter S)

{` Complementation is an involution, hence an equivalence. `}
def letter_complement_involutive (S : Type) (x : SignedLetter S)
  : Id (SignedLetter S) (letter_complement S (letter_complement S x)) x
  ≔ match x [ inl. a ↦ refl (inl. a : SignedLetter S) | inr. a ↦ refl (inr. a : SignedLetter S) ]

def letter_complement_equiv (S : Type) : Equiv (SignedLetter S) (SignedLetter S)
  ≔ quasi_inverse_equiv (SignedLetter S) (SignedLetter S) (letter_complement S) (letter_complement S)
      (letter_complement_involutive S) (letter_complement_involutive S)

{` No signed letter is its own complement. `}
def letter_complement_distinct (S : Type) (x : SignedLetter S)
  : Not (Id (SignedLetter S) (letter_complement S x) x)
  ≔ match x [
  | inl. a ↦ p ↦ sum_encode S S (inr. a) (inl. a) p
  | inr. a ↦ p ↦ sum_encode S S (inl. a) (inr. a) p ]

{` S~ is a decidable set when S has decidable equality. `}
def signed_letter_decidable_equality (S : Type) (dec : DecidableEquality S)
  : DecidableEquality (SignedLetter S)
  ≔ sum_decidable_equality S S dec dec

def signed_letter_decidable_set (S : Type) (dec : DecidableEquality S) : DecidableSet (SignedLetter S)
  ≔ hedberg (SignedLetter S) (signed_letter_decidable_equality S dec)

def signed_letter_set (S : Type) (dec : DecidableEquality S) : isSet (SignedLetter S)
  ≔ decidable_set_is_set (SignedLetter S) (signed_letter_decidable_set S dec)

{` Words in the signed letters: the list type S~*. `}
def SignedWord (S : Type) : Type ≔ List (SignedLetter S)

def empty_word (S : Type) : SignedWord S ≔ nil.

{` Decidable equality of lists and of subtypes (helpers). `}
def fw_list_decide_cons (A : Type) (x y : A) (xt yt : List A)
  (d : Decidable (Id A x y)) (e : Decidable (Id (List A) xt yt))
  : Decidable (Id (List A) (cons. x xt) (cons. y yt))
  ≔ match d [
  | inr. n ↦ inr. (p ↦ n (list_encode A (cons. x xt) (cons. y yt) p .fst))
  | inl. q ↦ match e [
    | inl. r ↦ inl. (cons. q r)
    | inr. n ↦ inr. (p ↦ n (list_encode A (cons. x xt) (cons. y yt) p .snd)) ] ]

def fw_list_decidable_equality (A : Type) (d : DecidableEquality A) (xs ys : List A)
  : Decidable (Id (List A) xs ys)
  ≔ match xs, ys [
  | nil., nil. ↦ inl. (refl (nil. : List A))
  | nil., cons. y yt ↦ inr. (p ↦ list_encode A nil. (cons. y yt) p)
  | cons. x xt, nil. ↦ inr. (p ↦ list_encode A (cons. x xt) nil. p)
  | cons. x xt, cons. y yt ↦ fw_list_decide_cons A x y xt yt (d x y) (fw_list_decidable_equality A d xt yt) ]

def fw_subtype_decide (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a)) (u v : Σ A B)
  (e : Decidable (Id A (u .fst) (v .fst))) : Decidable (Id (Σ A B) u v)
  ≔ match e [
  | inl. p ↦ inl. (subtype_equal A B hB u v p)
  | inr. n ↦ inr. (q ↦ n (map_path (Σ A B) A (z ↦ z .fst) u v q)) ]

def fw_subtype_decidable_equality (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a))
  (d : DecidableEquality A) (u v : Σ A B) : Decidable (Id (Σ A B) u v)
  ≔ fw_subtype_decide A B hB u v (d (u .fst) (v .fst))

def signed_word_decidable_equality (S : Type) (dec : DecidableEquality S) : DecidableEquality (SignedWord S)
  ≔ fw_list_decidable_equality (SignedLetter S) (signed_letter_decidable_equality S dec)

def signed_word_set (S : Type) (dec : DecidableEquality S) : isSet (SignedWord S)
  ≔ list_set (SignedLetter S) (signed_letter_set S dec)

{` congp.tex:811, first sentence.  A word is reduced if it contains no two
   consecutive complementary letters: x w is reduced iff w is reduced and
   does not start with x-bar.  Module 862 proves the equivalence with the
   literal reading (no factorization u x x-bar t). `}
def WordHeadNotComplement (S : Type) (x : SignedLetter S) (w : SignedWord S) : Type
  ≔ match w [ nil. ↦ Unit | cons. y _ ↦ Not (Id (SignedLetter S) y (letter_complement S x)) ]

def word_head_not_complement_prop (S : Type) (x : SignedLetter S) (w : SignedWord S)
  : isProp (WordHeadNotComplement S x w)
  ≔ match w [
  | nil. ↦ unit_prop
  | cons. y _ ↦ negation_prop (Id (SignedLetter S) y (letter_complement S x)) ]

def IsReducedWord (S : Type) (w : SignedWord S) : Type
  ≔ match w [ nil. ↦ Unit | cons. x v ↦ Product (WordHeadNotComplement S x v) (IsReducedWord S v) ]

def is_reduced_word_prop (S : Type) (w : SignedWord S) : isProp (IsReducedWord S w)
  ≔ match w [
  | nil. ↦ unit_prop
  | cons. x v ↦ product_prop (WordHeadNotComplement S x v) (IsReducedWord S v)
      (word_head_not_complement_prop S x v) (is_reduced_word_prop S v) ]

{` The subtype of reduced words (equivalent to the book's R_S, see
   reduced_word_image_equiv below). `}
def ReducedWord (S : Type) : Type ≔ Σ (SignedWord S) (IsReducedWord S)

def reduced_word_empty (S : Type) : ReducedWord S ≔ (nil., star.)

def reduced_word_path (S : Type) (r s : ReducedWord S) (p : Id (SignedWord S) (r .fst) (s .fst))
  : Id (ReducedWord S) r s
  ≔ subtype_equal (SignedWord S) (IsReducedWord S) (is_reduced_word_prop S) r s p

def reduced_word_set (S : Type) (dec : DecidableEquality S) : isSet (ReducedWord S)
  ≔ sigma_set (SignedWord S) (IsReducedWord S) (signed_word_set S dec)
      (w ↦ prop_is_set (IsReducedWord S w) (is_reduced_word_prop S w))

def reduced_word_decidable_equality (S : Type) (dec : DecidableEquality S) : DecidableEquality (ReducedWord S)
  ≔ fw_subtype_decidable_equality (SignedWord S) (IsReducedWord S) (is_reduced_word_prop S)
      (signed_word_decidable_equality S dec)

{` The letter step: x v with a complementary pair at the front deleted,
   i.e. s_x(v) = rho(x v) for reduced v. `}
def fw_cancel_or_cons (S : Type) (x y : SignedLetter S) (v : SignedWord S)
  (d : Decidable (Id (SignedLetter S) y (letter_complement S x))) : SignedWord S
  ≔ match d [ inl. _ ↦ v | inr. _ ↦ cons. x (cons. y v) ]

def word_letter_reduce (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  : SignedWord S
  ≔ match w [
  | nil. ↦ cons. x nil.
  | cons. y v ↦ fw_cancel_or_cons S x y v (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

{` congp.tex:811 and the xca at 819: the reduction rho_S by nested
   induction (outer: the word; inner: the head of the reduced tail). `}
def word_reduction (S : Type) (dec : DecidableEquality S) (w : SignedWord S) : SignedWord S
  ≔ match w [ nil. ↦ nil. | cons. x v ↦ word_letter_reduce S dec x (word_reduction S dec v) ]

def word_reduction_nil (S : Type) (dec : DecidableEquality S)
  : Id (SignedWord S) (word_reduction S dec nil.) nil.
  ≔ refl (nil. : SignedWord S)

def word_reduction_cons (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (cons. x w)) (word_letter_reduce S dec x (word_reduction S dec w))
  ≔ refl (word_reduction S dec (cons. x w))

{` The letter step preserves reducedness; rho lands in reduced words. `}
def fw_cancel_or_cons_reduced (S : Type) (x y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. y v)) (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : IsReducedWord S (fw_cancel_or_cons S x y v d)
  ≔ match d [ inl. _ ↦ h .snd | inr. n ↦ (n, h) ]

def word_letter_reduce_reduced (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (w : SignedWord S) (h : IsReducedWord S w) : IsReducedWord S (word_letter_reduce S dec x w)
  ≔ match w [
  | nil. ↦ (star., star.)
  | cons. y v ↦ fw_cancel_or_cons_reduced S x y v h
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

def word_reduction_reduced (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : IsReducedWord S (word_reduction S dec w)
  ≔ match w [
  | nil. ↦ star.
  | cons. x v ↦ word_letter_reduce_reduced S dec x (word_reduction S dec v) (word_reduction_reduced S dec v) ]

{` The two cases of the letter step. `}
def fw_cancel_or_cons_keep (S : Type) (x y : SignedLetter S) (v : SignedWord S)
  (n : Not (Id (SignedLetter S) y (letter_complement S x)))
  (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : Id (SignedWord S) (fw_cancel_or_cons S x y v d) (cons. x (cons. y v))
  ≔ match d [
  | inl. p ↦ absurd (Id (SignedWord S) v (cons. x (cons. y v))) (n p)
  | inr. _ ↦ refl (cons. x (cons. y v) : SignedWord S) ]

def fw_cancel_or_cons_drop (S : Type) (x y : SignedLetter S) (v : SignedWord S)
  (p : Id (SignedLetter S) y (letter_complement S x))
  (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : Id (SignedWord S) (fw_cancel_or_cons S x y v d) v
  ≔ match d [
  | inl. _ ↦ refl v
  | inr. n ↦ absurd (Id (SignedWord S) (cons. x (cons. y v)) v) (n p) ]

def word_letter_reduce_keep (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  (n : WordHeadNotComplement S x w) : Id (SignedWord S) (word_letter_reduce S dec x w) (cons. x w)
  ≔ match w [
  | nil. ↦ refl (cons. x nil. : SignedWord S)
  | cons. y v ↦ fw_cancel_or_cons_keep S x y v n
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

def word_letter_reduce_drop (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (v : SignedWord S)
  : Id (SignedWord S) (word_letter_reduce S dec x (cons. (letter_complement S x) v)) v
  ≔ fw_cancel_or_cons_drop S x (letter_complement S x) v (refl (letter_complement S x))
      (signed_letter_decidable_equality S dec (letter_complement S x) (letter_complement S x))

{` rho fixes reduced words, so rho is idempotent. `}
def word_reduction_of_reduced (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  (h : IsReducedWord S w) : Id (SignedWord S) (word_reduction S dec w) w
  ≔ match w [
  | nil. ↦ refl (nil. : SignedWord S)
  | cons. x v ↦ concat (SignedWord S) (word_letter_reduce S dec x (word_reduction S dec v))
      (word_letter_reduce S dec x v) (cons. x v)
      (refl (word_letter_reduce S dec x) (word_reduction_of_reduced S dec v (h .snd)))
      (word_letter_reduce_keep S dec x v (h .fst)) ]

def word_reduction_idempotent (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (word_reduction S dec w)) (word_reduction S dec w)
  ≔ word_reduction_of_reduced S dec (word_reduction S dec w) (word_reduction_reduced S dec w)

{` A word is reduced iff it is fixed by rho. `}
def word_reduced_of_fixed (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  (p : Id (SignedWord S) (word_reduction S dec w) w) : IsReducedWord S w
  ≔ transport (SignedWord S) (IsReducedWord S) (word_reduction S dec w) w p (word_reduction_reduced S dec w)

{` Cancellation: s_{x-bar}(s_x(w)) = w for reduced w. `}
def fw_cancel_after_drop (S : Type) (dec : DecidableEquality S) (x y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. y v)) (p : Id (SignedLetter S) y (letter_complement S x))
  : Id (SignedWord S) (word_letter_reduce S dec (letter_complement S x) v) (cons. y v)
  ≔ match v [
  | nil. ↦ cons. (inverse (SignedLetter S) y (letter_complement S x) p) (refl (nil. : SignedWord S))
  | cons. z u ↦ concat (SignedWord S)
      (word_letter_reduce S dec (letter_complement S x) (cons. z u))
      (cons. (letter_complement S x) (cons. z u)) (cons. y (cons. z u))
      (word_letter_reduce_keep S dec (letter_complement S x) (cons. z u)
        (q ↦ h .fst (concat (SignedLetter S) z (letter_complement S (letter_complement S x))
          (letter_complement S y) q
          (refl (letter_complement S) (inverse (SignedLetter S) y (letter_complement S x) p)))))
      (cons. (inverse (SignedLetter S) y (letter_complement S x) p) (refl (cons. z u : SignedWord S))) ]

def fw_cancel_or_cons_cancel (S : Type) (dec : DecidableEquality S) (x y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. y v)) (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : Id (SignedWord S) (word_letter_reduce S dec (letter_complement S x) (fw_cancel_or_cons S x y v d)) (cons. y v)
  ≔ match d [
  | inl. p ↦ fw_cancel_after_drop S dec x y v h p
  | inr. _ ↦ fw_cancel_or_cons_drop S (letter_complement S x) x (cons. y v)
      (inverse (SignedLetter S) (letter_complement S (letter_complement S x)) x (letter_complement_involutive S x))
      (signed_letter_decidable_equality S dec x (letter_complement S (letter_complement S x))) ]

def word_letter_reduce_cancel (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  (h : IsReducedWord S w)
  : Id (SignedWord S) (word_letter_reduce S dec (letter_complement S x) (word_letter_reduce S dec x w)) w
  ≔ match w [
  | nil. ↦ fw_cancel_or_cons_drop S (letter_complement S x) x nil.
      (inverse (SignedLetter S) (letter_complement S (letter_complement S x)) x (letter_complement_involutive S x))
      (signed_letter_decidable_equality S dec x (letter_complement S (letter_complement S x)))
  | cons. y v ↦ fw_cancel_or_cons_cancel S dec x y v h
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

def word_letter_reduce_cancel_inverse (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (w : SignedWord S) (h : IsReducedWord S w)
  : Id (SignedWord S) (word_letter_reduce S dec x (word_letter_reduce S dec (letter_complement S x) w)) w
  ≔ concat (SignedWord S)
      (word_letter_reduce S dec x (word_letter_reduce S dec (letter_complement S x) w))
      (word_letter_reduce S dec (letter_complement S (letter_complement S x))
        (word_letter_reduce S dec (letter_complement S x) w)) w
      (map_path (SignedLetter S) (SignedWord S)
        (z ↦ word_letter_reduce S dec z (word_letter_reduce S dec (letter_complement S x) w))
        x (letter_complement S (letter_complement S x))
        (inverse (SignedLetter S) (letter_complement S (letter_complement S x)) x (letter_complement_involutive S x)))
      (word_letter_reduce_cancel S dec (letter_complement S x) w h)

{` rho(x x-bar w) = rho(w) and rho(x-bar x w) = rho(w). `}
def word_reduction_cancel_pair (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (cons. x (cons. (letter_complement S x) w))) (word_reduction S dec w)
  ≔ word_letter_reduce_cancel_inverse S dec x (word_reduction S dec w) (word_reduction_reduced S dec w)

def word_reduction_cancel_pair_inverse (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (w : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (cons. (letter_complement S x) (cons. x w))) (word_reduction S dec w)
  ≔ word_letter_reduce_cancel S dec x (word_reduction S dec w) (word_reduction_reduced S dec w)

{` The letter action on the subtype of reduced words, an equivalence with
   inverse s_{x-bar}; its underlying word is rho(x w). `}
def reduced_letter_action (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (r : ReducedWord S)
  : ReducedWord S
  ≔ (word_letter_reduce S dec x (r .fst), word_letter_reduce_reduced S dec x (r .fst) (r .snd))

def reduced_letter_action_is_reduction (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWord S)
  : Id (SignedWord S) (reduced_letter_action S dec x r .fst) (word_reduction S dec (cons. x (r .fst)))
  ≔ inverse (SignedWord S) (word_reduction S dec (cons. x (r .fst))) (word_letter_reduce S dec x (r .fst))
      (refl (word_letter_reduce S dec x) (word_reduction_of_reduced S dec (r .fst) (r .snd)))

def reduced_letter_action_cancel (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (r : ReducedWord S)
  : Id (ReducedWord S) (reduced_letter_action S dec (letter_complement S x) (reduced_letter_action S dec x r)) r
  ≔ reduced_word_path S (reduced_letter_action S dec (letter_complement S x) (reduced_letter_action S dec x r)) r
      (word_letter_reduce_cancel S dec x (r .fst) (r .snd))

def reduced_letter_action_cancel_inverse (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWord S)
  : Id (ReducedWord S) (reduced_letter_action S dec x (reduced_letter_action S dec (letter_complement S x) r)) r
  ≔ reduced_word_path S (reduced_letter_action S dec x (reduced_letter_action S dec (letter_complement S x) r)) r
      (word_letter_reduce_cancel_inverse S dec x (r .fst) (r .snd))

def reduced_letter_action_equiv (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  : Equiv (ReducedWord S) (ReducedWord S)
  ≔ quasi_inverse_equiv (ReducedWord S) (ReducedWord S)
      (reduced_letter_action S dec x) (reduced_letter_action S dec (letter_complement S x))
      (reduced_letter_action_cancel S dec x) (reduced_letter_action_cancel_inverse S dec x)

{` On a reduced word x w, s_x(w) = x w; on x-bar w, s_x(x-bar w) = w. `}
def reduced_letter_action_cons (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  (h : IsReducedWord S (cons. x w))
  : Id (ReducedWord S) (reduced_letter_action S dec x (w, h .snd)) (cons. x w, h)
  ≔ reduced_word_path S (reduced_letter_action S dec x (w, h .snd)) (cons. x w, h)
      (word_letter_reduce_keep S dec x w (h .fst))

def reduced_letter_action_cancel_head (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (w : SignedWord S) (h : IsReducedWord S (cons. (letter_complement S x) w))
  : Id (ReducedWord S) (reduced_letter_action S dec x (cons. (letter_complement S x) w, h)) (w, h .snd)
  ≔ reduced_word_path S (reduced_letter_action S dec x (cons. (letter_complement S x) w, h)) (w, h .snd)
      (word_letter_reduce_drop S dec x w)

{` congp.tex:824.  R_S is the image of rho_S in S~* (module 39 Image, book
   fiber orientation); its elements are the reduced words. `}
def ReducedWordImage (S : Type) (dec : DecidableEquality S) : Type
  ≔ Image (SignedWord S) (SignedWord S) (word_reduction S dec)

def reduced_image_factor (S : Type) (dec : DecidableEquality S) (w : SignedWord S) : ReducedWordImage S dec
  ≔ image_factor (SignedWord S) (SignedWord S) (word_reduction S dec) w

{` The empty word eps as an element of R_S. `}
def reduced_image_empty (S : Type) (dec : DecidableEquality S) : ReducedWordImage S dec
  ≔ reduced_image_factor S dec nil.

def reduced_image_path (S : Type) (dec : DecidableEquality S) (r s : ReducedWordImage S dec)
  (p : Id (SignedWord S) (r .fst) (s .fst)) : Id (ReducedWordImage S dec) r s
  ≔ subtype_equal (SignedWord S) (b ↦ Mere (BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) b))
      (b ↦ mere_isprop (BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) b)) r s p

def reduced_image_set (S : Type) (dec : DecidableEquality S) : isSet (ReducedWordImage S dec)
  ≔ image_set (SignedWord S) (SignedWord S) (word_reduction S dec) (signed_word_set S dec)

def reduced_image_decidable_equality (S : Type) (dec : DecidableEquality S)
  : DecidableEquality (ReducedWordImage S dec)
  ≔ fw_subtype_decidable_equality (SignedWord S)
      (b ↦ Mere (BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) b))
      (b ↦ mere_isprop (BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) b))
      (signed_word_decidable_equality S dec)

{` Elements of R_S are reduced words and fixed by rho. `}
def reduced_image_reduced (S : Type) (dec : DecidableEquality S) (r : ReducedWordImage S dec)
  : IsReducedWord S (r .fst)
  ≔ image_prop_eliminate (SignedWord S) (SignedWord S) (word_reduction S dec) (IsReducedWord S)
      (is_reduced_word_prop S) (word_reduction_reduced S dec) r

def reduced_image_word_fixed (S : Type) (dec : DecidableEquality S) (r : ReducedWordImage S dec)
  : Id (SignedWord S) (word_reduction S dec (r .fst)) (r .fst)
  ≔ word_reduction_of_reduced S dec (r .fst) (reduced_image_reduced S dec r)

def reduced_image_factor_self (S : Type) (dec : DecidableEquality S) (r : ReducedWordImage S dec)
  : Id (ReducedWordImage S dec) (reduced_image_factor S dec (r .fst)) r
  ≔ reduced_image_path S dec (reduced_image_factor S dec (r .fst)) r (reduced_image_word_fixed S dec r)

{` "whose elements are the reduced words": R_S is equivalent to the
   subtype of reduced words, by maps that keep the underlying word. `}
def reduced_word_to_image (S : Type) (dec : DecidableEquality S) (r : ReducedWord S) : ReducedWordImage S dec
  ≔ (r .fst, mere (BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) (r .fst))
      (r .fst, inverse (SignedWord S) (word_reduction S dec (r .fst)) (r .fst)
        (word_reduction_of_reduced S dec (r .fst) (r .snd))))

def reduced_image_to_word (S : Type) (dec : DecidableEquality S) (r : ReducedWordImage S dec) : ReducedWord S
  ≔ (r .fst, reduced_image_reduced S dec r)

def reduced_word_image_equiv (S : Type) (dec : DecidableEquality S)
  : Equiv (ReducedWordImage S dec) (ReducedWord S)
  ≔ quasi_inverse_equiv (ReducedWordImage S dec) (ReducedWord S)
      (reduced_image_to_word S dec) (reduced_word_to_image S dec)
      (r ↦ reduced_image_path S dec (reduced_word_to_image S dec (reduced_image_to_word S dec r)) r (refl (r .fst)))
      (r ↦ reduced_word_path S (reduced_image_to_word S dec (reduced_word_to_image S dec r)) r (refl (r .fst)))

{` The book's s_x : R_S -> R_S, w |-> rho_S(x w), literally; an
   equivalence with inverse w |-> rho_S(x-bar w) (proof of
   thm:free-group-elements). `}
def image_letter_action (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (r : ReducedWordImage S dec)
  : ReducedWordImage S dec
  ≔ reduced_image_factor S dec (cons. x (r .fst))

def image_letter_action_word (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWordImage S dec)
  : Id (SignedWord S) (image_letter_action S dec x r .fst) (word_letter_reduce S dec x (r .fst))
  ≔ refl (word_letter_reduce S dec x) (reduced_image_word_fixed S dec r)

def image_letter_action_cancel (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWordImage S dec)
  : Id (ReducedWordImage S dec) (image_letter_action S dec (letter_complement S x) (image_letter_action S dec x r)) r
  ≔ reduced_image_path S dec (image_letter_action S dec (letter_complement S x) (image_letter_action S dec x r)) r
      (calc
        word_reduction S dec (cons. (letter_complement S x) (image_letter_action S dec x r .fst))
        = word_letter_reduce S dec (letter_complement S x) (image_letter_action S dec x r .fst)
          by image_letter_action_word S dec (letter_complement S x) (image_letter_action S dec x r)
        = word_letter_reduce S dec (letter_complement S x) (word_letter_reduce S dec x (r .fst))
          by refl (word_letter_reduce S dec (letter_complement S x)) (image_letter_action_word S dec x r)
        = r .fst by word_letter_reduce_cancel S dec x (r .fst) (reduced_image_reduced S dec r) ∎)

def image_letter_action_cancel_inverse (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWordImage S dec)
  : Id (ReducedWordImage S dec) (image_letter_action S dec x (image_letter_action S dec (letter_complement S x) r)) r
  ≔ reduced_image_path S dec (image_letter_action S dec x (image_letter_action S dec (letter_complement S x) r)) r
      (calc
        word_reduction S dec (cons. x (image_letter_action S dec (letter_complement S x) r .fst))
        = word_letter_reduce S dec x (image_letter_action S dec (letter_complement S x) r .fst)
          by image_letter_action_word S dec x (image_letter_action S dec (letter_complement S x) r)
        = word_letter_reduce S dec x (word_letter_reduce S dec (letter_complement S x) (r .fst))
          by refl (word_letter_reduce S dec x) (image_letter_action_word S dec (letter_complement S x) r)
        = r .fst by word_letter_reduce_cancel_inverse S dec x (r .fst) (reduced_image_reduced S dec r) ∎)

def image_letter_action_equiv (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  : Equiv (ReducedWordImage S dec) (ReducedWordImage S dec)
  ≔ quasi_inverse_equiv (ReducedWordImage S dec) (ReducedWordImage S dec)
      (image_letter_action S dec x) (image_letter_action S dec (letter_complement S x))
      (image_letter_action_cancel S dec x) (image_letter_action_cancel_inverse S dec x)

{` The two descriptions of s_x agree under R_S = reduced words. `}
def image_letter_action_compare (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (r : ReducedWordImage S dec)
  : Id (ReducedWord S) (reduced_image_to_word S dec (image_letter_action S dec x r))
      (reduced_letter_action S dec x (reduced_image_to_word S dec r))
  ≔ reduced_word_path S (reduced_image_to_word S dec (image_letter_action S dec x r))
      (reduced_letter_action S dec x (reduced_image_to_word S dec r)) (image_letter_action_word S dec x r)

{` On classes of words: s_x(rho w) = rho(x w), and rho(x x-bar w) = rho w. `}
def image_letter_action_factor (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  : Id (ReducedWordImage S dec) (image_letter_action S dec x (reduced_image_factor S dec w))
      (reduced_image_factor S dec (cons. x w))
  ≔ reduced_image_path S dec (image_letter_action S dec x (reduced_image_factor S dec w))
      (reduced_image_factor S dec (cons. x w))
      (refl (word_letter_reduce S dec x) (word_reduction_idempotent S dec w))

def reduced_image_factor_cancel_pair (S : Type) (dec : DecidableEquality S) (x : SignedLetter S)
  (w : SignedWord S)
  : Id (ReducedWordImage S dec) (reduced_image_factor S dec (cons. x (cons. (letter_complement S x) w)))
      (reduced_image_factor S dec w)
  ≔ reduced_image_path S dec (reduced_image_factor S dec (cons. x (cons. (letter_complement S x) w)))
      (reduced_image_factor S dec w) (word_reduction_cancel_pair S dec x w)

{` congp.tex:824.  The Dyck words D_S: the fiber of rho_S over eps (book
   fiber orientation, eps = rho_S(w)). `}
def DyckWord (S : Type) (dec : DecidableEquality S) : Type
  ≔ BookFiber (SignedWord S) (SignedWord S) (word_reduction S dec) nil.

{` Litmus checks over S = Bool with a = inl false, b = inl true,
   A = inr false, B = inr true. `}
def fw_bool_decidable_equality : DecidableEquality Bool
  ≔ x y ↦ match x, y [
  | false., false. ↦ inl. (refl (false. : Bool))
  | false., true. ↦ inr. (p ↦ bool_encode false. true. p)
  | true., false. ↦ inr. (p ↦ bool_encode true. false. p)
  | true., true. ↦ inl. (refl (true. : Bool)) ]

def fw_letter_a : SignedLetter Bool ≔ inl. false.
def fw_letter_b : SignedLetter Bool ≔ inl. true.
def fw_letter_A : SignedLetter Bool ≔ inr. false.
def fw_letter_B : SignedLetter Bool ≔ inr. true.

def fw_litmus_complement : Id (SignedLetter Bool) (letter_complement Bool fw_letter_a) fw_letter_A
  ≔ refl fw_letter_A

{` rho(a b B A a) = a. `}
def fw_litmus_reduction
  : Id (SignedWord Bool)
      (word_reduction Bool fw_bool_decidable_equality
        (cons. fw_letter_a (cons. fw_letter_b (cons. fw_letter_B (cons. fw_letter_A (cons. fw_letter_a nil.))))))
      (cons. fw_letter_a nil.)
  ≔ refl (cons. fw_letter_a nil. : SignedWord Bool)

{` rho(a A) = rho(B b) = eps: these words "become trivial". `}
def fw_litmus_reduction_aA
  : Id (SignedWord Bool) (word_reduction Bool fw_bool_decidable_equality (cons. fw_letter_a (cons. fw_letter_A nil.))) nil.
  ≔ refl (nil. : SignedWord Bool)

def fw_litmus_reduction_Bb
  : Id (SignedWord Bool) (word_reduction Bool fw_bool_decidable_equality (cons. fw_letter_B (cons. fw_letter_b nil.))) nil.
  ≔ refl (nil. : SignedWord Bool)

{` s_a(A b) = b, in R_S. `}
def fw_litmus_letter_action
  : Id (SignedWord Bool)
      (image_letter_action Bool fw_bool_decidable_equality fw_letter_a
        (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_A (cons. fw_letter_b nil.))) .fst)
      (cons. fw_letter_b nil.)
  ≔ refl (cons. fw_letter_b nil. : SignedWord Bool)

{` s_a(b) = a b (no cancellation). `}
def fw_litmus_letter_action_cons
  : Id (SignedWord Bool)
      (image_letter_action Bool fw_bool_decidable_equality fw_letter_a
        (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_b nil.)) .fst)
      (cons. fw_letter_a (cons. fw_letter_b nil.))
  ≔ refl (cons. fw_letter_a (cons. fw_letter_b nil.) : SignedWord Bool)
