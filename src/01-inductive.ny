export "00-foundations"

{` Chapter 2: finite types, coproducts, natural numbers, and lists. `}
def Empty : Type ≔ data []
def Unit : Type ≔ data [ star. ]
def Bool : Type ≔ data [ false. | true. ]
def Sum (A B : Type) : Type ≔ data [ inl. (_ : A) | inr. (_ : B) ]
def Nat : Type ≔ data [ zero. | suc. (_ : Nat) ]
def List (A : Type) : Type ≔ data [ nil. | cons. (_ : A) (_ : List A) ]

def absurd (A : Type) (e : Empty) : A ≔ match e []
def Not (A : Type) : Type ≔ A → Empty
def Decidable (A : Type) : Type ≔ Sum A (Not A)

def unit_contractible : isContr Unit ≔
  (star., [ star. ↦ refl (star. : Unit) ])

def unit_prop : isProp Unit ≔ [ star., star. ↦ refl (star. : Unit) ]
def empty_prop : isProp Empty ≔ x y ↦ match x []

def bool_not : Bool → Bool ≔ [ false. ↦ true. | true. ↦ false. ]
def bool_not_involutive (b : Bool) : Id Bool (bool_not (bool_not b)) b
  ≔ match b [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def sum_elim (A B C : Type) (f : A → C) (g : B → C) : Sum A B → C
  ≔ [ inl. a ↦ f a | inr. b ↦ g b ]
def sum_swap (A B : Type) : Sum A B → Sum B A
  ≔ [ inl. a ↦ inr. a | inr. b ↦ inl. b ]
def sum_swap_involutive (A B : Type) (s : Sum A B)
  : Id (Sum A B) (sum_swap B A (sum_swap A B s)) s
  ≔ match s [ inl. a ↦ refl (inl. a : Sum A B) | inr. b ↦ refl (inr. b : Sum A B) ]

def nat_ind (P : Nat → Type) (z : P zero.)
  (s : (n : Nat) → P n → P (suc. n)) (n : Nat) : P n
  ≔ match n [ zero. ↦ z | suc. k ↦ s k (nat_ind P z s k) ]

def add (m n : Nat) : Nat ≔ match n [ zero. ↦ m | suc. k ↦ suc. (add m k) ]
def mul (m n : Nat) : Nat ≔ match n [ zero. ↦ zero. | suc. k ↦ add (mul m k) m ]

def add_zero_left (n : Nat) : Id Nat (add zero. n) n
  ≔ match n [ zero. ↦ refl (zero. : Nat) | suc. k ↦ suc. (add_zero_left k) ]

def add_suc_left (m n : Nat) : Id Nat (add (suc. m) n) (suc. (add m n))
  ≔ match n [ zero. ↦ refl (suc. m : Nat) | suc. k ↦ suc. (add_suc_left m k) ]

def add_comm (m n : Nat) : Id Nat (add m n) (add n m)
  ≔ match n [
  | zero. ↦ inverse Nat (add zero. m) m (add_zero_left m)
  | suc. k ↦ concat Nat (suc. (add m k)) (suc. (add k m)) (add (suc. k) m)
      (suc. (add_comm m k))
      (inverse Nat (add (suc. k) m) (suc. (add k m)) (add_suc_left k m)) ]

def add_assoc (a b c : Nat) : Id Nat (add (add a b) c) (add a (add b c))
  ≔ match c [ zero. ↦ refl (add a b) | suc. k ↦ suc. (add_assoc a b k) ]

def iterate (A : Type) (f : A → A) (n : Nat) (a : A) : A
  ≔ match n [ zero. ↦ a | suc. k ↦ f (iterate A f k a) ]

def iterate_add (A : Type) (f : A → A) (m n : Nat) (a : A)
  : Id A (iterate A f (add m n) a) (iterate A f n (iterate A f m a))
  ≔ match n [ zero. ↦ refl (iterate A f m a)
  | suc. k ↦ refl f (iterate_add A f m k a) ]

def append (A : Type) (xs ys : List A) : List A
  ≔ match xs [ nil. ↦ ys | cons. x tail ↦ cons. x (append A tail ys) ]

def append_nil (A : Type) (xs : List A) : Id (List A) (append A xs nil.) xs
  ≔ match xs [ nil. ↦ refl (nil. : List A)
  | cons. x tail ↦ cons. (refl x) (append_nil A tail) ]

def append_assoc (A : Type) (xs ys zs : List A)
  : Id (List A) (append A (append A xs ys) zs) (append A xs (append A ys zs))
  ≔ match xs [ nil. ↦ refl (append A ys zs)
  | cons. x tail ↦ cons. (refl x) (append_assoc A tail ys zs) ]

def reverse (A : Type) (xs : List A) : List A
  ≔ match xs [ nil. ↦ nil.
  | cons. x tail ↦ append A (reverse A tail) (cons. x nil.) ]

def reverse_append (A : Type) (xs ys : List A)
  : Id (List A) (reverse A (append A xs ys)) (append A (reverse A ys) (reverse A xs))
  ≔ match xs [
  | nil. ↦ inverse (List A) (append A (reverse A ys) nil.) (reverse A ys)
      (append_nil A (reverse A ys))
  | cons. x tail ↦
      concat (List A)
        (append A (reverse A (append A tail ys)) (cons. x nil.))
        (append A (append A (reverse A ys) (reverse A tail)) (cons. x nil.))
        (append A (reverse A ys) (append A (reverse A tail) (cons. x nil.)))
        (refl ((l ↦ append A l (cons. x nil.)) : List A → List A)
          (reverse_append A tail ys))
        (append_assoc A (reverse A ys) (reverse A tail) (cons. x nil.)) ]

def reverse_involutive (A : Type) (xs : List A)
  : Id (List A) (reverse A (reverse A xs)) xs
  ≔ match xs [
  | nil. ↦ refl (nil. : List A)
  | cons. x tail ↦ concat (List A)
      (reverse A (append A (reverse A tail) (cons. x nil.)))
      (cons. x (reverse A (reverse A tail))) (cons. x tail)
      (reverse_append A (reverse A tail) (cons. x nil.))
      (cons. (refl x) (reverse_involutive A tail)) ]

def length (A : Type) (xs : List A) : Nat
  ≔ match xs [ nil. ↦ zero. | cons. x tail ↦ suc. (length A tail) ]

{` xca:concat-assoc uses the opposite orientation from append_assoc. `}
def append_assoc_book (A : Type) (xs ys zs : List A)
  : Id (List A) (append A xs (append A ys zs)) (append A (append A xs ys) zs)
  ≔ inverse (List A) (append A (append A xs ys) zs) (append A xs (append A ys zs))
      (append_assoc A xs ys zs)
