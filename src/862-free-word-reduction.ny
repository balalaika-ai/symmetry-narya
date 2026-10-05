export "861-free-words"

{` Chapter 8 (congp.tex), section "Free groups", part 2: the properties of
   the reduction rho_S behind the book's description "obtained by
   repeatedly deleting consecutive pairs of complementary letters until
   none remain" (congp.tex:811, xca 819), the literal reading of
   "reduced", rho on concatenations, the remark at congp.tex:842
   (S~*/~ = R_S), the Dyck-language footnote of congp.tex:824, and the
   enumeration of short words (congp.tex:800). `}

{` One deletion step: w = u x x-bar t and v = u t. `}
def WordDeletionStep (S : Type) (w v : SignedWord S) : Type
  ≔ Σ (SignedWord S) (u ↦ Σ (SignedLetter S) (x ↦ Σ (SignedWord S) (t ↦
      Product (Id (SignedWord S) w (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
        (Id (SignedWord S) v (append (SignedLetter S) u t)))))

{` n successive deletion steps from w to v. `}
def WordDeletions (S : Type) (n : Nat) (w v : SignedWord S) : Type
  ≔ match n [
  | zero. ↦ Id (SignedWord S) w v
  | suc. k ↦ Σ (SignedWord S) (w' ↦ Product (WordDeletionStep S w w') (WordDeletions S k w' v)) ]

{` v is obtained from w by repeatedly deleting complementary pairs. `}
def WordReducesTo (S : Type) (w v : SignedWord S) : Type ≔ Σ Nat (n ↦ WordDeletions S n w v)

{` Deleting a complementary pair anywhere does not change rho. `}
def word_reduction_delete_pair (S : Type) (dec : DecidableEquality S) (u : SignedWord S) (x : SignedLetter S)
  (t : SignedWord S)
  : Id (SignedWord S)
      (word_reduction S dec (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
      (word_reduction S dec (append (SignedLetter S) u t))
  ≔ match u [
  | nil. ↦ word_reduction_cancel_pair S dec x t
  | cons. y u' ↦ refl (word_letter_reduce S dec y) (word_reduction_delete_pair S dec u' x t) ]

def fw_deletion_reduction (S : Type) (dec : DecidableEquality S) (w v u : SignedWord S) (x : SignedLetter S)
  (t : SignedWord S)
  (p : Id (SignedWord S) w (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
  (q : Id (SignedWord S) v (append (SignedLetter S) u t))
  : Id (SignedWord S) (word_reduction S dec w) (word_reduction S dec v)
  ≔ concat (SignedWord S) (word_reduction S dec w)
      (word_reduction S dec (append (SignedLetter S) u t)) (word_reduction S dec v)
      (concat (SignedWord S) (word_reduction S dec w)
        (word_reduction S dec (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))
        (word_reduction S dec (append (SignedLetter S) u t))
        (refl (word_reduction S dec) p) (word_reduction_delete_pair S dec u x t))
      (refl (word_reduction S dec) (inverse (SignedWord S) v (append (SignedLetter S) u t) q))

def word_deletion_step_reduction (S : Type) (dec : DecidableEquality S) (w v : SignedWord S)
  (d : WordDeletionStep S w v) : Id (SignedWord S) (word_reduction S dec w) (word_reduction S dec v)
  ≔ fw_deletion_reduction S dec w v (d .fst) (d .snd .fst) (d .snd .snd .fst)
      (d .snd .snd .snd .fst) (d .snd .snd .snd .snd)

def word_deletions_reduction (S : Type) (dec : DecidableEquality S) (n : Nat) (w v : SignedWord S)
  (d : WordDeletions S n w v) : Id (SignedWord S) (word_reduction S dec w) (word_reduction S dec v)
  ≔ match n [
  | zero. ↦ refl (word_reduction S dec) d
  | suc. k ↦ concat (SignedWord S) (word_reduction S dec w) (word_reduction S dec (d .fst))
      (word_reduction S dec v)
      (word_deletion_step_reduction S dec w (d .fst) (d .snd .fst))
      (word_deletions_reduction S dec k (d .fst) v (d .snd .snd)) ]

{` Deletion sequences under a common first letter, and their composition. `}
def fw_deletion_step_cons (S : Type) (y : SignedLetter S) (w v : SignedWord S) (d : WordDeletionStep S w v)
  : WordDeletionStep S (cons. y w) (cons. y v)
  ≔ (cons. y (d .fst), (d .snd .fst, (d .snd .snd .fst,
      (cons. (refl y) (d .snd .snd .snd .fst), cons. (refl y) (d .snd .snd .snd .snd)))))

def fw_deletions_cons (S : Type) (y : SignedLetter S) (n : Nat) (w v : SignedWord S)
  (d : WordDeletions S n w v) : WordDeletions S n (cons. y w) (cons. y v)
  ≔ match n [
  | zero. ↦ cons. (refl y) d
  | suc. k ↦ (cons. y (d .fst), (fw_deletion_step_cons S y w (d .fst) (d .snd .fst),
      fw_deletions_cons S y k (d .fst) v (d .snd .snd))) ]

def fw_deletions_concat (S : Type) (n m : Nat) (w v t : SignedWord S)
  (d : WordDeletions S n w v) (e : WordDeletions S m v t) : WordDeletions S (add m n) w t
  ≔ match n [
  | zero. ↦ transport (SignedWord S) (z ↦ WordDeletions S m z t) v w (inverse (SignedWord S) w v d) e
  | suc. k ↦ (d .fst, (d .snd .fst, fw_deletions_concat S k m (d .fst) v t (d .snd .snd) e)) ]

def word_reduces_cons (S : Type) (y : SignedLetter S) (w v : SignedWord S) (e : WordReducesTo S w v)
  : WordReducesTo S (cons. y w) (cons. y v)
  ≔ (e .fst, fw_deletions_cons S y (e .fst) w v (e .snd))

def word_reduces_concat (S : Type) (w v t : SignedWord S) (d : WordReducesTo S w v) (e : WordReducesTo S v t)
  : WordReducesTo S w t
  ≔ (add (e .fst) (d .fst), fw_deletions_concat S (d .fst) (e .fst) w v t (d .snd) (e .snd))

def fw_cancel_or_cons_reduces (S : Type) (x y : SignedLetter S) (v : SignedWord S)
  (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : WordReducesTo S (cons. x (cons. y v)) (fw_cancel_or_cons S x y v d)
  ≔ match d [
  | inl. p ↦ (suc. zero., (v, ((nil., (x, (v, (cons. (refl x) (cons. p (refl v)), refl v)))), refl v)))
  | inr. _ ↦ (zero., refl (cons. x (cons. y v) : SignedWord S)) ]

def word_letter_reduce_reduces (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (w : SignedWord S)
  : WordReducesTo S (cons. x w) (word_letter_reduce S dec x w)
  ≔ match w [
  | nil. ↦ (zero., refl (cons. x nil. : SignedWord S))
  | cons. y v ↦ fw_cancel_or_cons_reduces S x y v
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

{` rho(w) is obtained from w by deleting complementary pairs. `}
def word_reduces_to_reduction (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : WordReducesTo S w (word_reduction S dec w)
  ≔ match w [
  | nil. ↦ (zero., refl (nil. : SignedWord S))
  | cons. x v ↦ word_reduces_concat S (cons. x v) (cons. x (word_reduction S dec v))
      (word_letter_reduce S dec x (word_reduction S dec v))
      (word_reduces_cons S x v (word_reduction S dec v) (word_reduces_to_reduction S dec v))
      (word_letter_reduce_reduces S dec x (word_reduction S dec v)) ]

{` Any reduced word obtained from w by deletions is rho(w). `}
def word_reduction_unique (S : Type) (dec : DecidableEquality S) (w v : SignedWord S)
  (e : WordReducesTo S w v) (h : IsReducedWord S v) : Id (SignedWord S) v (word_reduction S dec w)
  ≔ concat (SignedWord S) v (word_reduction S dec v) (word_reduction S dec w)
      (inverse (SignedWord S) (word_reduction S dec v) v (word_reduction_of_reduced S dec v h))
      (inverse (SignedWord S) (word_reduction S dec w) (word_reduction S dec v)
        (word_deletions_reduction S dec (e .fst) w v (e .snd)))

{` congp.tex:811 together with the xca at 819: rho(w) is reached from w by
   deleting consecutive complementary pairs, no pair remains in it, and it
   is the only reduced word reached in this way. `}
def word_reduction_characterization (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : Product (WordReducesTo S w (word_reduction S dec w))
      (Product (IsReducedWord S (word_reduction S dec w))
        ((v : SignedWord S) → WordReducesTo S w v → IsReducedWord S v → Id (SignedWord S) v (word_reduction S dec w)))
  ≔ (word_reduces_to_reduction S dec w, (word_reduction_reduced S dec w, word_reduction_unique S dec w))

{` The literal reading of "reduced": no factorization w = u x x-bar t. `}
def ContainsComplementaryPair (S : Type) (w : SignedWord S) : Type
  ≔ Σ (SignedWord S) (u ↦ Σ (SignedLetter S) (x ↦ Σ (SignedWord S) (t ↦
      Id (SignedWord S) w (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t))))))

def fw_not_reduced_with_pair (S : Type) (u : SignedWord S) (x : SignedLetter S) (t : SignedWord S)
  (h : IsReducedWord S (append (SignedLetter S) u (cons. x (cons. (letter_complement S x) t)))) : Empty
  ≔ match u [
  | nil. ↦ h .fst (refl (letter_complement S x))
  | cons. y u' ↦ fw_not_reduced_with_pair S u' x t (h .snd) ]

def reduced_word_no_pair (S : Type) (w : SignedWord S) (h : IsReducedWord S w)
  : Not (ContainsComplementaryPair S w)
  ≔ c ↦ fw_not_reduced_with_pair S (c .fst) (c .snd .fst) (c .snd .snd .fst)
      (transport (SignedWord S) (IsReducedWord S) w
        (append (SignedLetter S) (c .fst) (cons. (c .snd .fst) (cons. (letter_complement S (c .snd .fst)) (c .snd .snd .fst))))
        (c .snd .snd .snd) h)

def fw_no_pair_head (S : Type) (x : SignedLetter S) (v : SignedWord S)
  (n : Not (ContainsComplementaryPair S (cons. x v))) : WordHeadNotComplement S x v
  ≔ match v [
  | nil. ↦ star.
  | cons. y v' ↦ q ↦ n (nil., (x, (v', cons. (refl x) (cons. q (refl v'))))) ]

def no_pair_reduced_word (S : Type) (w : SignedWord S) (n : Not (ContainsComplementaryPair S w))
  : IsReducedWord S w
  ≔ match w [
  | nil. ↦ star.
  | cons. x v ↦ (fw_no_pair_head S x v n,
      no_pair_reduced_word S v (c ↦ n (cons. x (c .fst), (c .snd .fst, (c .snd .snd .fst,
        cons. (refl x) (c .snd .snd .snd)))))) ]

def is_reduced_word_iff_no_pair (S : Type) (w : SignedWord S)
  : Equiv (IsReducedWord S w) (Not (ContainsComplementaryPair S w))
  ≔ iff_equiv (IsReducedWord S w) (Not (ContainsComplementaryPair S w))
      (is_reduced_word_prop S w) (negation_prop (ContainsComplementaryPair S w))
      (reduced_word_no_pair S w) (no_pair_reduced_word S w)

{` Reducedness is decidable (w is reduced iff rho(w) = w). `}
def fw_reduced_decide (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  (e : Decidable (Id (SignedWord S) (word_reduction S dec w) w)) : Decidable (IsReducedWord S w)
  ≔ match e [
  | inl. p ↦ inl. (word_reduced_of_fixed S dec w p)
  | inr. n ↦ inr. (h ↦ n (word_reduction_of_reduced S dec w h)) ]

def is_reduced_word_decidable (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : Decidable (IsReducedWord S w)
  ≔ fw_reduced_decide S dec w (signed_word_decidable_equality S dec (word_reduction S dec w) w)

{` rho on concatenations: rho(u v) = rho(u rho(v)) = rho(rho(u) v)
   = rho(rho(u) rho(v)). `}
def word_reduction_append_right (S : Type) (dec : DecidableEquality S) (u v : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (append (SignedLetter S) u v))
      (word_reduction S dec (append (SignedLetter S) u (word_reduction S dec v)))
  ≔ match u [
  | nil. ↦ inverse (SignedWord S) (word_reduction S dec (word_reduction S dec v)) (word_reduction S dec v)
      (word_reduction_idempotent S dec v)
  | cons. x u' ↦ refl (word_letter_reduce S dec x) (word_reduction_append_right S dec u' v) ]

def fw_letter_reduce_append_step (S : Type) (dec : DecidableEquality S) (x y : SignedLetter S)
  (r v : SignedWord S) (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : Id (SignedWord S)
      (word_letter_reduce S dec x (word_reduction S dec (append (SignedLetter S) (cons. y r) v)))
      (word_reduction S dec (append (SignedLetter S) (fw_cancel_or_cons S x y r d) v))
  ≔ match d [
  | inl. p ↦ concat (SignedWord S)
      (word_letter_reduce S dec x (word_letter_reduce S dec y (word_reduction S dec (append (SignedLetter S) r v))))
      (word_letter_reduce S dec x (word_letter_reduce S dec (letter_complement S x)
        (word_reduction S dec (append (SignedLetter S) r v))))
      (word_reduction S dec (append (SignedLetter S) r v))
      (map_path (SignedLetter S) (SignedWord S)
        (z ↦ word_letter_reduce S dec x (word_letter_reduce S dec z (word_reduction S dec (append (SignedLetter S) r v))))
        y (letter_complement S x) p)
      (word_letter_reduce_cancel_inverse S dec x (word_reduction S dec (append (SignedLetter S) r v))
        (word_reduction_reduced S dec (append (SignedLetter S) r v)))
  | inr. _ ↦ refl (word_letter_reduce S dec x (word_reduction S dec (append (SignedLetter S) (cons. y r) v))) ]

def fw_letter_reduce_append (S : Type) (dec : DecidableEquality S) (x : SignedLetter S) (r v : SignedWord S)
  : Id (SignedWord S) (word_letter_reduce S dec x (word_reduction S dec (append (SignedLetter S) r v)))
      (word_reduction S dec (append (SignedLetter S) (word_letter_reduce S dec x r) v))
  ≔ match r [
  | nil. ↦ refl (word_letter_reduce S dec x (word_reduction S dec v))
  | cons. y r' ↦ fw_letter_reduce_append_step S dec x y r' v
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

def word_reduction_append_left (S : Type) (dec : DecidableEquality S) (u v : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (append (SignedLetter S) u v))
      (word_reduction S dec (append (SignedLetter S) (word_reduction S dec u) v))
  ≔ match u [
  | nil. ↦ refl (word_reduction S dec v)
  | cons. x u' ↦ concat (SignedWord S)
      (word_letter_reduce S dec x (word_reduction S dec (append (SignedLetter S) u' v)))
      (word_letter_reduce S dec x (word_reduction S dec (append (SignedLetter S) (word_reduction S dec u') v)))
      (word_reduction S dec (append (SignedLetter S) (word_letter_reduce S dec x (word_reduction S dec u')) v))
      (refl (word_letter_reduce S dec x) (word_reduction_append_left S dec u' v))
      (fw_letter_reduce_append S dec x (word_reduction S dec u') v) ]

def word_reduction_append (S : Type) (dec : DecidableEquality S) (u v : SignedWord S)
  : Id (SignedWord S) (word_reduction S dec (append (SignedLetter S) u v))
      (word_reduction S dec (append (SignedLetter S) (word_reduction S dec u) (word_reduction S dec v)))
  ≔ concat (SignedWord S) (word_reduction S dec (append (SignedLetter S) u v))
      (word_reduction S dec (append (SignedLetter S) (word_reduction S dec u) v))
      (word_reduction S dec (append (SignedLetter S) (word_reduction S dec u) (word_reduction S dec v)))
      (word_reduction_append_left S dec u v)
      (word_reduction_append_right S dec (word_reduction S dec u) v)

{` congp.tex:842.  The equivalence relation induced by rho_S,
   u ~ v iff rho(u) = rho(v), and S~*/~ = R_S (set quotient of module 41). `}
def word_reduction_relation (S : Type) (dec : DecidableEquality S) : EquivalenceRelation (SignedWord S)
  ≔ ((u v ↦ (Id (SignedWord S) (word_reduction S dec u) (word_reduction S dec v),
        signed_word_set S dec (word_reduction S dec u) (word_reduction S dec v))),
      (u ↦ refl (word_reduction S dec u)),
      (u v p ↦ inverse (SignedWord S) (word_reduction S dec u) (word_reduction S dec v) p),
      (u v t p q ↦ concat (SignedWord S) (word_reduction S dec u) (word_reduction S dec v)
        (word_reduction S dec t) p q))

def WordReductionQuotient (S : Type) (dec : DecidableEquality S) : Type
  ≔ Quotient (SignedWord S) (word_reduction_relation S dec)

def word_quotient_class (S : Type) (dec : DecidableEquality S) (w : SignedWord S) : WordReductionQuotient S dec
  ≔ quotient_class (SignedWord S) (word_reduction_relation S dec) w

def word_quotient_to_image (S : Type) (dec : DecidableEquality S) (z : WordReductionQuotient S dec)
  : ReducedWordImage S dec
  ≔ quotient_rec (SignedWord S) (ReducedWordImage S dec) (word_reduction_relation S dec) (reduced_image_set S dec)
      (reduced_image_factor S dec)
      (u v p ↦ reduced_image_path S dec (reduced_image_factor S dec u) (reduced_image_factor S dec v) p) z

def word_image_to_quotient (S : Type) (dec : DecidableEquality S) (r : ReducedWordImage S dec)
  : WordReductionQuotient S dec
  ≔ word_quotient_class S dec (r .fst)

def fw_word_quotient_roundtrip (S : Type) (dec : DecidableEquality S)
  : Id (WordReductionQuotient S dec → WordReductionQuotient S dec)
      (z ↦ word_image_to_quotient S dec (word_quotient_to_image S dec z))
      (identity (WordReductionQuotient S dec))
  ≔ surjection_function_ext (SignedWord S) (WordReductionQuotient S dec) (WordReductionQuotient S dec)
      (word_quotient_class S dec) (quotient_surjective (SignedWord S) (word_reduction_relation S dec))
      (quotient_set (SignedWord S) (word_reduction_relation S dec))
      (z ↦ word_image_to_quotient S dec (word_quotient_to_image S dec z))
      (identity (WordReductionQuotient S dec))
      (funext (SignedWord S) (_ ↦ WordReductionQuotient S dec)
        (u ↦ word_quotient_class S dec (word_reduction S dec u)) (word_quotient_class S dec)
        (u ↦ quotient_encode (SignedWord S) (word_reduction_relation S dec) (word_reduction S dec u) u
          (word_reduction_idempotent S dec u)))

def word_quotient_image_equiv (S : Type) (dec : DecidableEquality S)
  : Equiv (WordReductionQuotient S dec) (ReducedWordImage S dec)
  ≔ quasi_inverse_equiv (WordReductionQuotient S dec) (ReducedWordImage S dec)
      (word_quotient_to_image S dec) (word_image_to_quotient S dec)
      (z ↦ fw_word_quotient_roundtrip S dec (refl z))
      (reduced_image_factor_self S dec)

{` The triangle: the equivalence sends the class of w to rho(w). `}
def word_quotient_image_class (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  : Id (ReducedWordImage S dec) (word_quotient_image_equiv S dec .map (word_quotient_class S dec w))
      (reduced_image_factor S dec w)
  ≔ refl (reduced_image_factor S dec w)

{` Footnote of congp.tex:824.  For S = 1, "(" = inl star and ")" = inr star.
   D_S contains ")(" and "))(()(". `}
def fw_paren_open : SignedLetter Unit ≔ inl. star.
def fw_paren_close : SignedLetter Unit ≔ inr. star.

def dyck_word_close_open : DyckWord Unit unit_decidable_equality
  ≔ (cons. fw_paren_close (cons. fw_paren_open nil.), refl (nil. : SignedWord Unit))

def dyck_word_long_example : DyckWord Unit unit_decidable_equality
  ≔ (cons. fw_paren_close (cons. fw_paren_close (cons. fw_paren_open (cons. fw_paren_open
      (cons. fw_paren_close (cons. fw_paren_open nil.))))), refl (nil. : SignedWord Unit))

{` The 1-sided Dyck language (balanced parentheses) as the words of the
   grammar D ::= eps | ( D ) D. `}
def OneSidedDyckTree : Type ≔ data [ dyck_leaf. | dyck_node. (_ : OneSidedDyckTree) (_ : OneSidedDyckTree) ]

def one_sided_dyck_word (t : OneSidedDyckTree) : SignedWord Unit
  ≔ match t [
  | dyck_leaf. ↦ nil.
  | dyck_node. s u ↦ cons. fw_paren_open
      (append (SignedLetter Unit) (one_sided_dyck_word s) (cons. fw_paren_close (one_sided_dyck_word u))) ]

def OneSidedDyckWord : Type ≔ Image OneSidedDyckTree (SignedWord Unit) one_sided_dyck_word

{` Every balanced word lies in D_1 ... `}
def one_sided_dyck_reduction (t : OneSidedDyckTree)
  : Id (SignedWord Unit) (word_reduction Unit unit_decidable_equality (one_sided_dyck_word t)) nil.
  ≔ match t [
  | dyck_leaf. ↦ refl (nil. : SignedWord Unit)
  | dyck_node. s u ↦ refl (word_letter_reduce Unit unit_decidable_equality fw_paren_open)
      (calc
        word_reduction Unit unit_decidable_equality
          (append (SignedLetter Unit) (one_sided_dyck_word s) (cons. fw_paren_close (one_sided_dyck_word u)))
        = word_reduction Unit unit_decidable_equality
            (append (SignedLetter Unit) (word_reduction Unit unit_decidable_equality (one_sided_dyck_word s))
              (cons. fw_paren_close (one_sided_dyck_word u)))
          by word_reduction_append_left Unit unit_decidable_equality (one_sided_dyck_word s)
            (cons. fw_paren_close (one_sided_dyck_word u))
        = word_reduction Unit unit_decidable_equality (cons. fw_paren_close (one_sided_dyck_word u))
          by refl ((l ↦ word_reduction Unit unit_decidable_equality
              (append (SignedLetter Unit) l (cons. fw_paren_close (one_sided_dyck_word u))))
              : SignedWord Unit → SignedWord Unit)
            (one_sided_dyck_reduction s)
        = cons. fw_paren_close nil.
          by refl (word_letter_reduce Unit unit_decidable_equality fw_paren_close) (one_sided_dyck_reduction u) ∎) ]

def one_sided_dyck_to_dyck (t : OneSidedDyckTree) : DyckWord Unit unit_decidable_equality
  ≔ (one_sided_dyck_word t, inverse (SignedWord Unit)
      (word_reduction Unit unit_decidable_equality (one_sided_dyck_word t)) nil. (one_sided_dyck_reduction t))

def one_sided_dyck_in_dyck (w : OneSidedDyckWord)
  : Id (SignedWord Unit) nil. (word_reduction Unit unit_decidable_equality (w .fst))
  ≔ image_prop_eliminate OneSidedDyckTree (SignedWord Unit) one_sided_dyck_word
      (b ↦ Id (SignedWord Unit) nil. (word_reduction Unit unit_decidable_equality b))
      (b ↦ signed_word_set Unit unit_decidable_equality nil. (word_reduction Unit unit_decidable_equality b))
      (t ↦ one_sided_dyck_to_dyck t .snd) w

{` ... but ")(" is in D_1 and not balanced. `}
def fw_tree_not_close_open (t : OneSidedDyckTree)
  (p : Id (SignedWord Unit) (cons. fw_paren_close (cons. fw_paren_open nil.)) (one_sided_dyck_word t)) : Empty
  ≔ match t [
  | dyck_leaf. ↦ list_encode (SignedLetter Unit) (cons. fw_paren_close (cons. fw_paren_open nil.)) nil. p
  | dyck_node. s u ↦ sum_encode Unit Unit fw_paren_close fw_paren_open
      (list_encode (SignedLetter Unit) (cons. fw_paren_close (cons. fw_paren_open nil.))
        (one_sided_dyck_word (dyck_node. s u)) p .fst) ]

def close_open_not_one_sided
  : Not (Mere (BookFiber OneSidedDyckTree (SignedWord Unit) one_sided_dyck_word
      (cons. fw_paren_close (cons. fw_paren_open nil.))))
  ≔ m ↦ mere_rec (BookFiber OneSidedDyckTree (SignedWord Unit) one_sided_dyck_word
      (cons. fw_paren_close (cons. fw_paren_open nil.))) Empty empty_prop
      (f ↦ fw_tree_not_close_open (f .fst) (f .snd)) m

{` congp.tex:800.  The words over a, b, A, B (S = Bool) of length 2, in the
   book's order, and the number of reduced words of length 0, 1, 2. `}
def fw_prefix_all (A : Type) (x : A) (ws : List (List A)) : List (List A)
  ≔ match ws [ nil. ↦ nil. | cons. w wt ↦ cons. (cons. x w) (fw_prefix_all A x wt) ]

def fw_extend_words (A : Type) (letters : List A) (ws : List (List A)) : List (List A)
  ≔ match letters [
  | nil. ↦ nil.
  | cons. x xt ↦ append (List A) (fw_prefix_all A x ws) (fw_extend_words A xt ws) ]

def words_of_length (A : Type) (letters : List A) (n : Nat) : List (List A)
  ≔ match n [ zero. ↦ cons. nil. nil. | suc. k ↦ fw_extend_words A letters (words_of_length A letters k) ]

def fw_count_step (P : Type) (e : Decidable P) (n : Nat) : Nat ≔ match e [ inl. _ ↦ suc. n | inr. _ ↦ n ]

def count_decided (A : Type) (P : A → Type) (d : (a : A) → Decidable (P a)) (xs : List A) : Nat
  ≔ match xs [ nil. ↦ zero. | cons. x xt ↦ fw_count_step (P x) (d x) (count_decided A P d xt) ]

def fw_bool_letters : List (SignedLetter Bool)
  ≔ cons. fw_letter_a (cons. fw_letter_b (cons. fw_letter_A (cons. fw_letter_B nil.)))

def fw_w2 (x y : SignedLetter Bool) : SignedWord Bool ≔ cons. x (cons. y nil.)

def fw_litmus_words_length_two
  : Id (List (SignedWord Bool)) (words_of_length (SignedLetter Bool) fw_bool_letters (suc. (suc. zero.)))
      (cons. (fw_w2 fw_letter_a fw_letter_a) (cons. (fw_w2 fw_letter_a fw_letter_b)
      (cons. (fw_w2 fw_letter_a fw_letter_A) (cons. (fw_w2 fw_letter_a fw_letter_B)
      (cons. (fw_w2 fw_letter_b fw_letter_a) (cons. (fw_w2 fw_letter_b fw_letter_b)
      (cons. (fw_w2 fw_letter_b fw_letter_A) (cons. (fw_w2 fw_letter_b fw_letter_B)
      (cons. (fw_w2 fw_letter_A fw_letter_a) (cons. (fw_w2 fw_letter_A fw_letter_b)
      (cons. (fw_w2 fw_letter_A fw_letter_A) (cons. (fw_w2 fw_letter_A fw_letter_B)
      (cons. (fw_w2 fw_letter_B fw_letter_a) (cons. (fw_w2 fw_letter_B fw_letter_b)
      (cons. (fw_w2 fw_letter_B fw_letter_A) (cons. (fw_w2 fw_letter_B fw_letter_B) nil.))))))))))))))))
  ≔ refl (words_of_length (SignedLetter Bool) fw_bool_letters (suc. (suc. zero.)))

def fw_count_reduced_bool (n : Nat) : Nat
  ≔ count_decided (SignedWord Bool) (IsReducedWord Bool) (is_reduced_word_decidable Bool fw_bool_decidable_equality)
      (words_of_length (SignedLetter Bool) fw_bool_letters n)

def fw_litmus_reduced_length_zero : Id Nat (fw_count_reduced_bool zero.) (suc. zero.)
  ≔ refl (suc. zero. : Nat)

def fw_litmus_reduced_length_one : Id Nat (fw_count_reduced_bool (suc. zero.)) (suc. (suc. (suc. (suc. zero.))))
  ≔ refl (suc. (suc. (suc. (suc. zero.))) : Nat)

{` 12 = 16 - 4 reduced words of length 2 (aA, bB, Aa, Bb are not reduced). `}
def fw_litmus_reduced_length_two
  : Id Nat (fw_count_reduced_bool (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))
  ≔ refl (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))) : Nat)
