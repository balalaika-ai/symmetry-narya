export "860-free-group-signatures"
export "862-free-word-reduction"

{` congp.tex:857.  The interpretation of words as loops in B F_S, for every
   FreeGroupSignature S F and every type S:
     [eps] = refl base,  [a w] = loop_a . [w],  [A w] = loop_a^-1 . [w].
   The book's composition q . p is concat p q (p first), so [a w] is
   concat [w] loop_a: first [w], then loop_a.  The interpretation lands in
   base = base, which is USym F_S judgmentally once F_S is formed (module
   865).  Also: [x x-bar w] = [w] ("aA and Bb become trivial",
   congp.tex:805) and [rho w] = [w] for decidable S. `}

{` The loop of a signed letter: loop_a for a, loop_a^-1 for A. `}
def free_signed_loop (S : Type) (F : FreeGroupSignature S) (x : SignedLetter S)
  : Id (F .carrier) (F .base) (F .base)
  ≔ match x [
  | inl. a ↦ F .loop a
  | inr. a ↦ inverse (F .carrier) (F .base) (F .base) (F .loop a) ]

def free_word_interpretation (S : Type) (F : FreeGroupSignature S) (w : SignedWord S)
  : Id (F .carrier) (F .base) (F .base)
  ≔ match w [
  | nil. ↦ refl (F .base)
  | cons. x v ↦ concat (F .carrier) (F .base) (F .base) (F .base)
      (free_word_interpretation S F v) (free_signed_loop S F x) ]

{` The three defining clauses (all judgmental). `}
def free_word_interpretation_nil (S : Type) (F : FreeGroupSignature S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F nil.) (refl (F .base))
  ≔ refl (refl (F .base))

def free_word_interpretation_generator (S : Type) (F : FreeGroupSignature S) (a : S) (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (cons. (inl. a) w))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F w) (F .loop a))
  ≔ refl (free_word_interpretation S F (cons. (inl. a) w))

def free_word_interpretation_inverse_generator (S : Type) (F : FreeGroupSignature S) (a : S) (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (cons. (inr. a) w))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F w)
        (inverse (F .carrier) (F .base) (F .base) (F .loop a)))
  ≔ refl (free_word_interpretation S F (cons. (inr. a) w))

def free_signed_loop_complement (S : Type) (F : FreeGroupSignature S) (x : SignedLetter S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_signed_loop S F (letter_complement S x))
      (inverse (F .carrier) (F .base) (F .base) (free_signed_loop S F x))
  ≔ match x [
  | inl. a ↦ refl (inverse (F .carrier) (F .base) (F .base) (F .loop a))
  | inr. a ↦ inverse (Id (F .carrier) (F .base) (F .base))
      (inverse (F .carrier) (F .base) (F .base) (inverse (F .carrier) (F .base) (F .base) (F .loop a)))
      (F .loop a) (inverse_inverse (F .carrier) (F .base) (F .base) (F .loop a)) ]

def fw_concat_cancel_inverse (A : Type) (a b : A) (w : Id A a b) (l : Id A b b)
  : Id (Id A a b) (concat A a b b (concat A a b b w (inverse A b b l)) l) w
  ≔ calc
      concat A a b b (concat A a b b w (inverse A b b l)) l
      = concat A a b b w (concat A b b b (inverse A b b l) l) by concat_assoc A a b b b w (inverse A b b l) l
      = concat A a b b w (refl b) by refl (concat A a b b w) (concat_inverse_left A b b l)
      = w by concat_p1 A a b w ∎

{` [x x-bar w] = [w]: complementary pairs are interpreted trivially. `}
def free_word_interpretation_cancel (S : Type) (F : FreeGroupSignature S) (x : SignedLetter S) (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation S F (cons. x (cons. (letter_complement S x) w))) (free_word_interpretation S F w)
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation S F (cons. x (cons. (letter_complement S x) w)))
      (concat (F .carrier) (F .base) (F .base) (F .base)
        (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F w)
          (inverse (F .carrier) (F .base) (F .base) (free_signed_loop S F x)))
        (free_signed_loop S F x))
      (free_word_interpretation S F w)
      (map_path (Id (F .carrier) (F .base) (F .base)) (Id (F .carrier) (F .base) (F .base))
        (q ↦ concat (F .carrier) (F .base) (F .base) (F .base)
          (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F w) q)
          (free_signed_loop S F x))
        (free_signed_loop S F (letter_complement S x))
        (inverse (F .carrier) (F .base) (F .base) (free_signed_loop S F x))
        (free_signed_loop_complement S F x))
      (fw_concat_cancel_inverse (F .carrier) (F .base) (F .base) (free_word_interpretation S F w)
        (free_signed_loop S F x))

{` Litmus (congp.tex:805): over S = Bool, [a A] = refl and [B b] = refl. `}
def free_word_interpretation_aA (F : FreeGroupSignature Bool)
  : Id (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation Bool F (cons. fw_letter_a (cons. fw_letter_A nil.))) (refl (F .base))
  ≔ free_word_interpretation_cancel Bool F fw_letter_a nil.

def free_word_interpretation_Bb (F : FreeGroupSignature Bool)
  : Id (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation Bool F (cons. fw_letter_B (cons. fw_letter_b nil.))) (refl (F .base))
  ≔ free_word_interpretation_cancel Bool F fw_letter_B nil.

{` [u v] = [u] . [v], i.e. concat [v] [u]. `}
def free_word_interpretation_append (S : Type) (F : FreeGroupSignature S) (u v : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (append (SignedLetter S) u v))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
        (free_word_interpretation S F u))
  ≔ match u [
  | nil. ↦ inverse (Id (F .carrier) (F .base) (F .base))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v) (refl (F .base)))
      (free_word_interpretation S F v)
      (concat_p1 (F .carrier) (F .base) (F .base) (free_word_interpretation S F v))
  | cons. x u' ↦ concat (Id (F .carrier) (F .base) (F .base))
      (concat (F .carrier) (F .base) (F .base) (F .base)
        (free_word_interpretation S F (append (SignedLetter S) u' v)) (free_signed_loop S F x))
      (concat (F .carrier) (F .base) (F .base) (F .base)
        (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
          (free_word_interpretation S F u'))
        (free_signed_loop S F x))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
        (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F u')
          (free_signed_loop S F x)))
      (map_path (Id (F .carrier) (F .base) (F .base)) (Id (F .carrier) (F .base) (F .base))
        (q ↦ concat (F .carrier) (F .base) (F .base) (F .base) q (free_signed_loop S F x))
        (free_word_interpretation S F (append (SignedLetter S) u' v))
        (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
          (free_word_interpretation S F u'))
        (free_word_interpretation_append S F u' v))
      (concat_assoc (F .carrier) (F .base) (F .base) (F .base) (F .base) (free_word_interpretation S F v)
        (free_word_interpretation S F u') (free_signed_loop S F x)) ]

{` The interpretation is invariant under the letter step and under rho. `}
def fw_interpretation_cancel_or_cons (S : Type) (F : FreeGroupSignature S) (x y : SignedLetter S)
  (v : SignedWord S) (d : Decidable (Id (SignedLetter S) y (letter_complement S x)))
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (fw_cancel_or_cons S x y v d))
      (free_word_interpretation S F (cons. x (cons. y v)))
  ≔ match d [
  | inl. p ↦ inverse (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation S F (cons. x (cons. y v))) (free_word_interpretation S F v)
      (concat (Id (F .carrier) (F .base) (F .base))
        (free_word_interpretation S F (cons. x (cons. y v)))
        (free_word_interpretation S F (cons. x (cons. (letter_complement S x) v)))
        (free_word_interpretation S F v)
        (map_path (SignedLetter S) (Id (F .carrier) (F .base) (F .base))
          (z ↦ free_word_interpretation S F (cons. x (cons. z v))) y (letter_complement S x) p)
        (free_word_interpretation_cancel S F x v))
  | inr. _ ↦ refl (free_word_interpretation S F (cons. x (cons. y v))) ]

def free_word_interpretation_letter_reduce (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (x : SignedLetter S) (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (word_letter_reduce S dec x w))
      (free_word_interpretation S F (cons. x w))
  ≔ match w [
  | nil. ↦ refl (free_word_interpretation S F (cons. x nil.))
  | cons. y v ↦ fw_interpretation_cancel_or_cons S F x y v
      (signed_letter_decidable_equality S dec y (letter_complement S x)) ]

def free_word_interpretation_reduction (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (w : SignedWord S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (word_reduction S dec w))
      (free_word_interpretation S F w)
  ≔ match w [
  | nil. ↦ refl (refl (F .base))
  | cons. x v ↦ concat (Id (F .carrier) (F .base) (F .base))
      (free_word_interpretation S F (word_letter_reduce S dec x (word_reduction S dec v)))
      (free_word_interpretation S F (cons. x (word_reduction S dec v)))
      (free_word_interpretation S F (cons. x v))
      (free_word_interpretation_letter_reduce S dec F x (word_reduction S dec v))
      (map_path (Id (F .carrier) (F .base) (F .base)) (Id (F .carrier) (F .base) (F .base))
        (q ↦ concat (F .carrier) (F .base) (F .base) (F .base) q (free_signed_loop S F x))
        (free_word_interpretation S F (word_reduction S dec v)) (free_word_interpretation S F v)
        (free_word_interpretation_reduction S dec F v)) ]

{` The restriction of the interpretation to R_S (thm:free-group-elements). `}
def free_reduced_interpretation (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (r : ReducedWordImage S dec) : Id (F .carrier) (F .base) (F .base)
  ≔ free_word_interpretation S F (r .fst)
