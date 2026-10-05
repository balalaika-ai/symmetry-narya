export "01-inductive"

def pi_prop (A : Type) (B : A → Type) (h : (a : A) → isProp (B a))
  : isProp ((a : A) → B a)
  ≔ f g ↦ funext A B f g (a ↦ h a (f a) (g a))

def product_prop (A B : Type) (hA : isProp A) (hB : isProp B)
  : isProp (Product A B)
  ≔ u v ↦ (hA (u .fst) (v .fst), hB (u .snd) (v .snd))

def sigma_prop (A : Type) (B : A → Type) (hA : isProp A)
  (hB : (a : A) → isProp (B a)) : isProp (Σ A B)
  ≔ u v ↦
    let p ≔ hA (u .fst) (v .fst) in
    (p, pathover_of_eq A B (u .fst) (v .fst) p (u .snd) (v .snd)
      (hB (v .fst) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd)))

def negation_prop (A : Type) : isProp (Not A)
  ≔ pi_prop A (_ ↦ Empty) (_ ↦ empty_prop)

{` Path reflection, f x = f y → x = y (xca:inj-sets). This is the book's notion of
   injectivity only for set codomains; the book's injection (embedding) is IsEmbedding (module 12). `}
def PathReflecting (A B : Type) (f : A → B) : Type
  ≔ (x y : A) → Id B (f x) (f y) → Id A x y

def fiber_prop_of_injective (A B : Type) (setB : isSet B)
  (f : A → B) (inj : PathReflecting A B f) (b : B)
  : isProp (Fiber A B f b)
  ≔ u v ↦
    let p ≔ inj (u .fst) (v .fst)
      (concat B (f (u .fst)) b (f (v .fst)) (u .snd)
        (inverse B (f (v .fst)) b (v .snd))) in
    (p, pathover_of_eq A (a ↦ Id B (f a) b) (u .fst) (v .fst) p
      (u .snd) (v .snd)
      (setB (f (v .fst)) b
        (transport A (a ↦ Id B (f a) b) (u .fst) (v .fst) p (u .snd))
        (v .snd)))

def equiv_of_injective_section (A B : Type) (setB : isSet B)
  (f : A → B) (inj : PathReflecting A B f) (g : B → A)
  (sec : (b : B) → Id B (f (g b)) b) : Equiv A B
  ≔ (f, b ↦ ((g b, sec b), u ↦
    fiber_prop_of_injective A B setB f inj b u (g b, sec b)))

def injective_of_retraction (A B : Type) (f : A → B) (g : B → A)
  (r : (a : A) → Id A (g (f a)) a) : PathReflecting A B f
  ≔ x y p ↦ concat A x (g (f x)) y
    (inverse A (g (f x)) x (r x))
    (concat A (g (f x)) (g (f y)) y (refl g p) (r y))

def set_iso_equiv (A B : Type) (setB : isSet B) (f : A → B) (g : B → A)
  (r : (a : A) → Id A (g (f a)) a)
  (s : (b : B) → Id B (f (g b)) b) : Equiv A B
  ≔ equiv_of_injective_section A B setB f (injective_of_retraction A B f g r) g s

{` Retracts of propositions are propositions. `}
def retract_prop (A B : Type) (hA : isProp A) (f : A → B) (g : B → A)
  (s : (b : B) → Id B (f (g b)) b) : isProp B
  ≔ x y ↦ concat B x (f (g x)) y
      (inverse B (f (g x)) x (s x))
      (concat B (f (g x)) (f (g y)) y (refl f (hA (g x) (g y))) (s y))

def NatCode (m n : Nat) : Type ≔ match m, n [
  | zero., zero. ↦ Unit
  | zero., suc. n ↦ Empty
  | suc. m, zero. ↦ Empty
  | suc. m, suc. n ↦ NatCode m n ]

def nat_encode (m n : Nat) (p : Id Nat m n) : NatCode m n
  ≔ match p [ zero. ⤇ star. | suc. p ⤇ nat_encode p.0 p.1 p.2 ]

def nat_decode (m n : Nat) (c : NatCode m n) : Id Nat m n
  ≔ match m, n [
  | zero., zero. ↦ zero.
  | zero., suc. n ↦ match c []
  | suc. m, zero. ↦ match c []
  | suc. m, suc. n ↦ suc. (nat_decode m n c) ]

def nat_decode_encode (m n : Nat) (p : Id Nat m n)
  : Id (Id Nat m n) (nat_decode m n (nat_encode m n p)) p
  ≔ match p [ zero. ⤇ zero. | suc. p ⤇ suc. (nat_decode_encode p.0 p.1 p.2) ]

def nat_code_prop (m n : Nat) : isProp (NatCode m n)
  ≔ match m, n [
  | zero., zero. ↦ unit_prop
  | zero., suc. n ↦ empty_prop
  | suc. m, zero. ↦ empty_prop
  | suc. m, suc. n ↦ nat_code_prop m n ]

def nat_set (m n : Nat) : isProp (Id Nat m n)
  ≔ retract_prop (NatCode m n) (Id Nat m n) (nat_code_prop m n)
      (nat_decode m n) (nat_encode m n) (nat_decode_encode m n)

def BoolCode (a b : Bool) : Type ≔ match a, b [
  | false., false. ↦ Unit
  | false., true. ↦ Empty
  | true., false. ↦ Empty
  | true., true. ↦ Unit ]

def bool_encode (a b : Bool) (p : Id Bool a b) : BoolCode a b
  ≔ match p [ false. ⤇ star. | true. ⤇ star. ]

def bool_decode (a b : Bool) (c : BoolCode a b) : Id Bool a b
  ≔ match a, b [
  | false., false. ↦ false.
  | false., true. ↦ match c []
  | true., false. ↦ match c []
  | true., true. ↦ true. ]

def bool_decode_encode (a b : Bool) (p : Id Bool a b)
  : Id (Id Bool a b) (bool_decode a b (bool_encode a b p)) p
  ≔ match p [ false. ⤇ false. | true. ⤇ true. ]

def bool_code_prop (a b : Bool) : isProp (BoolCode a b)
  ≔ match a, b [
  | false., false. ↦ unit_prop
  | false., true. ↦ empty_prop
  | true., false. ↦ empty_prop
  | true., true. ↦ unit_prop ]

def bool_set (a b : Bool) : isProp (Id Bool a b)
  ≔ retract_prop (BoolCode a b) (Id Bool a b) (bool_code_prop a b)
      (bool_decode a b) (bool_encode a b) (bool_decode_encode a b)
