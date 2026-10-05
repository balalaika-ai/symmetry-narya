export "15-hlevels"

{` Encode/decode for coproducts, without set assumptions. `}
def SumCode (A B : Type) (x y : Sum A B) : Type ≔ match x, y [
  | inl. a, inl. a1 ↦ Id A a a1
  | inl. a, inr. b ↦ Empty
  | inr. b, inl. a ↦ Empty
  | inr. b, inr. b1 ↦ Id B b b1 ]

def sum_encode (A B : Type) (x y : Sum A B) (p : Id (Sum A B) x y) : SumCode A B x y
  ≔ match p [ inl. a ⤇ a.2 | inr. b ⤇ b.2 ]

def sum_decode (A B : Type) (x y : Sum A B) (c : SumCode A B x y) : Id (Sum A B) x y
  ≔ match x, y [
  | inl. a, inl. a1 ↦ inl. c
  | inl. a, inr. b ↦ match c []
  | inr. b, inl. a ↦ match c []
  | inr. b, inr. b1 ↦ inr. c ]

def sum_decode_encode (A B : Type) (x y : Sum A B) (p : Id (Sum A B) x y)
  : Id (Id (Sum A B) x y) (sum_decode A B x y (sum_encode A B x y p)) p
  ≔ match p [ inl. a ⤇ inl. (refl a.2) | inr. b ⤇ inr. (refl b.2) ]

def sum_encode_decode (A B : Type) (x y : Sum A B) (c : SumCode A B x y)
  : Id (SumCode A B x y) (sum_encode A B x y (sum_decode A B x y c)) c
  ≔ match x, y [
  | inl. a, inl. a1 ↦ refl c
  | inl. a, inr. b ↦ match c []
  | inr. b, inl. a ↦ match c []
  | inr. b, inr. b1 ↦ refl c ]

{` xca:binary-sum-id `}
def sum_path_equiv (A B : Type) (x y : Sum A B) : Equiv (Id (Sum A B) x y) (SumCode A B x y)
  ≔ quasi_inverse_equiv (Id (Sum A B) x y) (SumCode A B x y)
      (sum_encode A B x y) (sum_decode A B x y)
      (sum_decode_encode A B x y) (sum_encode_decode A B x y)

def sum_code_prop (A B : Type) (hA : isSet A) (hB : isSet B) (x y : Sum A B)
  : isProp (SumCode A B x y)
  ≔ match x, y [
  | inl. a, inl. a1 ↦ hA a a1
  | inl. a, inr. b ↦ empty_prop
  | inr. b, inl. a ↦ empty_prop
  | inr. b, inr. b1 ↦ hB b b1 ]

{` xca:set-sum `}
def sum_set (A B : Type) (hA : isSet A) (hB : isSet B) : isSet (Sum A B)
  ≔ x y ↦ retract_prop (SumCode A B x y) (Id (Sum A B) x y) (sum_code_prop A B hA hB x y)
      (sum_decode A B x y) (sum_encode A B x y) (sum_decode_encode A B x y)

def ListCode (A : Type) (xs ys : List A) : Type ≔ match xs, ys [
  | nil., nil. ↦ Unit
  | nil., cons. y ys ↦ Empty
  | cons. x xs, nil. ↦ Empty
  | cons. x xs, cons. y ys ↦ Product (Id A x y) (Id (List A) xs ys) ]

def list_encode (A : Type) (xs ys : List A) (p : Id (List A) xs ys) : ListCode A xs ys
  ≔ match p [ nil. ⤇ star. | cons. x xs ⤇ (x.2, xs.2) ]

def list_decode (A : Type) (xs ys : List A) (c : ListCode A xs ys) : Id (List A) xs ys
  ≔ match xs, ys [
  | nil., nil. ↦ nil.
  | nil., cons. y ys ↦ match c []
  | cons. x xs, nil. ↦ match c []
  | cons. x xs, cons. y ys ↦ cons. (c .fst) (c .snd) ]

def list_decode_encode (A : Type) (xs ys : List A) (p : Id (List A) xs ys)
  : Id (Id (List A) xs ys) (list_decode A xs ys (list_encode A xs ys p)) p
  ≔ match p [ nil. ⤇ nil. | cons. x xs ⤇ cons. (refl x.2) (refl xs.2) ]

def list_encode_decode (A : Type) (xs ys : List A) (c : ListCode A xs ys)
  : Id (ListCode A xs ys) (list_encode A xs ys (list_decode A xs ys c)) c
  ≔ match xs, ys [
  | nil., nil. ↦ unit_prop star. c
  | nil., cons. y ys ↦ match c []
  | cons. x xs, nil. ↦ match c []
  | cons. x xs, cons. y ys ↦ refl c ]

def list_path_equiv (A : Type) (xs ys : List A) : Equiv (Id (List A) xs ys) (ListCode A xs ys)
  ≔ quasi_inverse_equiv (Id (List A) xs ys) (ListCode A xs ys)
      (list_encode A xs ys) (list_decode A xs ys) (list_decode_encode A xs ys) (list_encode_decode A xs ys)

{` thm:isset-inductive-types, the list case. Each recursive call removes
   one constructor from both lists. `}
def list_set (A : Type) (hA : isSet A) (xs ys : List A) : isProp (Id (List A) xs ys)
  ≔ retract_prop (ListCode A xs ys) (Id (List A) xs ys)
      (match xs, ys [
       | nil., nil. ↦ unit_prop
       | nil., cons. y ys ↦ empty_prop
       | cons. x xs, nil. ↦ empty_prop
       | cons. x xs, cons. y ys ↦ product_prop (Id A x y) (Id (List A) xs ys)
           (hA x y) (list_set A hA xs ys) ])
      (list_decode A xs ys) (list_encode A xs ys) (list_decode_encode A xs ys)

def proposition_hlevel (n : Nat) (P : Type) (hP : isProp P) : HLevel (suc. n) P
  ≔ match n [
  | zero. ↦ prop_to_hlevel_one P hP
  | suc. n ↦ hlevel_raise (suc. n) P (proposition_hlevel n P hP) ]

{` The higher-level list assertion in the footnote to
   thm:isset-inductive-types. Recursion is on the two lists, not on n. `}
def list_hlevel (n : Nat) (A : Type) (hA : HLevel (suc. (suc. n)) A)
  (xs ys : List A) : HLevel (suc. n) (Id (List A) xs ys)
  ≔ hlevel_equiv (suc. n) (ListCode A xs ys) (Id (List A) xs ys)
      (canonical_inverse_equiv (Id (List A) xs ys) (ListCode A xs ys) (list_path_equiv A xs ys))
      (match xs, ys [
       | nil., nil. ↦ proposition_hlevel n Unit unit_prop
       | nil., cons. y ys ↦ proposition_hlevel n Empty empty_prop
       | cons. x xs, nil. ↦ proposition_hlevel n Empty empty_prop
       | cons. x xs, cons. y ys ↦ hlevel_product (suc. n) (Id A x y) (Id (List A) xs ys)
           (hA x y) (list_hlevel n A hA xs ys) ])

{` The one-constructor unary sum from sec:unary-sum-types. `}
def Copy (A : Type) : Type ≔ data [ copy. (_ : A) ]
def copy_value (A : Type) : Copy A → A ≔ [ copy. a ↦ a ]

def copy_equiv (A : Type) : Equiv (Copy A) A
  ≔ quasi_inverse_equiv (Copy A) A (copy_value A) (a ↦ copy. a)
      [ copy. a ↦ refl (copy. a : Copy A) ] (a ↦ refl a)

def copy_set (A : Type) (hA : isSet A) : isSet (Copy A)
  ≔ hlevel_two_to_set (Copy A) (hlevel_equiv (suc. (suc. zero.)) A (Copy A)
      (canonical_inverse_equiv (Copy A) A (copy_equiv A)) (set_to_hlevel_two A hA))

def empty_set : isSet Empty ≔ prop_is_set Empty empty_prop
def unit_set : isSet Unit ≔ prop_is_set Unit unit_prop

{` xca:list-contr: the actual length map is an equivalence for contractible A. `}
def repeat (A : Type) (a : A) (n : Nat) : List A
  ≔ match n [ zero. ↦ nil. | suc. n ↦ cons. a (repeat A a n) ]

def length_repeat (A : Type) (a : A) (n : Nat) : Id Nat (length A (repeat A a n)) n
  ≔ match n [ zero. ↦ zero. | suc. n ↦ suc. (length_repeat A a n) ]

def repeat_length (A : Type) (hA : isContr A) (xs : List A)
  : Id (List A) (repeat A (hA .center) (length A xs)) xs
  ≔ match xs [
  | nil. ↦ nil.
  | cons. x xs ↦ cons. (inverse A x (hA .center) (hA .contract x)) (repeat_length A hA xs) ]

def length_equiv (A : Type) (hA : isContr A) : Equiv (List A) Nat
  ≔ quasi_inverse_equiv (List A) Nat (length A) (repeat A (hA .center))
      (repeat_length A hA) (length_repeat A (hA .center))
