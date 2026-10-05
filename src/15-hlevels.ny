export "14-propositions"

{` Standard h-level indexing: 0 contractible, 1 proposition, 2 set.
   Book n-types (n>=0) have h-level n+2. All recursion decreases n. `}
def HLevel (n : Nat) (A : Type) : Type ≔ match n [
  | zero. ↦ isContr A
  | suc. n ↦ (x y : A) → HLevel n (Id A x y) ]

def hlevel_one_to_prop (A : Type) (h : HLevel (suc. zero.) A) : isProp A
  ≔ x y ↦ h x y .center

def prop_to_hlevel_one (A : Type) (h : isProp A) : HLevel (suc. zero.) A
  ≔ prop_paths_contractible A h

def hlevel_two_to_set (A : Type) (h : HLevel (suc. (suc. zero.)) A) : isSet A
  ≔ x y ↦ hlevel_one_to_prop (Id A x y) (h x y)

def set_to_hlevel_two (A : Type) (h : isSet A) : HLevel (suc. (suc. zero.)) A
  ≔ x y ↦ prop_to_hlevel_one (Id A x y) (h x y)

def hlevel_isprop (n : Nat) (A : Type) : isProp (HLevel n A)
  ≔ match n [
  | zero. ↦ iscontr_isprop A
  | suc. n ↦ pi_prop A (x ↦ (y : A) → HLevel n (Id A x y))
      (x ↦ pi_prop A (y ↦ HLevel n (Id A x y)) (y ↦ hlevel_isprop n (Id A x y))) ]

def hlevel_raise (n : Nat) (A : Type) (h : HLevel n A) : HLevel (suc. n) A
  ≔ match n [
  | zero. ↦ prop_paths_contractible A (contractible_prop A h)
  | suc. n ↦ x y ↦ hlevel_raise n (Id A x y) (h x y) ]

def hlevel_equiv (n : Nat) (A B : Type) (e : Equiv A B) (h : HLevel n A)
  : HLevel n B ≔ transport Type (HLevel n) A B (ua A B e) h

def pi_contractible (A : Type) (B : A → Type) (h : (a : A) → isContr (B a))
  : isContr ((a : A) → B a)
  ≔ ((a ↦ h a .center), f ↦ funext A B f (a ↦ h a .center) (a ↦ h a .contract (f a)))

def sigma_contractible (A : Type) (B : A → Type) (hA : isContr A)
  (hB : (a : A) → isContr (B a)) : isContr (Σ A B)
  ≔ ((hA .center, hB (hA .center) .center), t ↦
      let p ≔ hA .contract (t .fst) in
      (p, pathover_of_eq A B (t .fst) (hA .center) p (t .snd) (hB (hA .center) .center)
        (hB (hA .center) .contract (transport A B (t .fst) (hA .center) p (t .snd)))))

{` A heterogeneous identity has the expected level. The motive retains
   its varying endpoint v; it does not turn dependent paths into ordinary
   equality by fiat. `}
def pathover_hlevel (n : Nat) (A : Type) (B : A → Type)
  (hB : (a : A) → HLevel (suc. n) (B a)) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) : HLevel n (Id B p u v)
  ≔ J A x
      (y p ↦ (v : B y) → HLevel n (Id B p u v))
      (hB x u) y p v

{` lem:level-n-utils, dependent products and sums. `}
def hlevel_pi (n : Nat) (A : Type) (B : A → Type) (hB : (a : A) → HLevel n (B a))
  : HLevel n ((a : A) → B a)
  ≔ match n [
  | zero. ↦ pi_contractible A B hB
  | suc. n ↦ f g ↦ hlevel_equiv n (Homotopy A B f g) (Id ((a : A) → B a) f g)
      (canonical_inverse_equiv (Id ((a : A) → B a) f g) (Homotopy A B f g)
        (function_extensionality A B f g))
      (hlevel_pi n A (a ↦ Id (B a) (f a) (g a)) (a ↦ hB a (f a) (g a))) ]

def hlevel_sigma (n : Nat) (A : Type) (B : A → Type) (hA : HLevel n A)
  (hB : (a : A) → HLevel n (B a)) : HLevel n (Σ A B)
  ≔ match n [
  | zero. ↦ sigma_contractible A B hA hB
  | suc. n ↦ u v ↦ hlevel_equiv n (SigmaPath A B u v) (Id (Σ A B) u v)
      (sigma_path_equiv A B u v)
      (hlevel_sigma n (Id A (u .fst) (v .fst)) (p ↦ Id B p (u .snd) (v .snd))
        (hA (u .fst) (v .fst))
        (p ↦ pathover_hlevel n A B hB (u .fst) (v .fst) p (u .snd) (v .snd))) ]

def hlevel_product (n : Nat) (A B : Type) (hA : HLevel n A) (hB : HLevel n B)
  : HLevel n (Product A B) ≔ hlevel_sigma n A (_ ↦ B) hA (_ ↦ hB)

def hlevel_function (n : Nat) (A B : Type) (hB : HLevel n B)
  : HLevel n (A → B) ≔ hlevel_pi n A (_ ↦ B) (_ ↦ hB)

{` Convenient instances in the book's direct isSet notation. `}
def pi_set (A : Type) (B : A → Type) (hB : (a : A) → isSet (B a)) : isSet ((a : A) → B a)
  ≔ hlevel_two_to_set ((a : A) → B a)
      (hlevel_pi (suc. (suc. zero.)) A B (a ↦ set_to_hlevel_two (B a) (hB a)))

def sigma_set (A : Type) (B : A → Type) (hA : isSet A) (hB : (a : A) → isSet (B a))
  : isSet (Σ A B)
  ≔ hlevel_two_to_set (Σ A B)
      (hlevel_sigma (suc. (suc. zero.)) A B (set_to_hlevel_two A hA)
        (a ↦ set_to_hlevel_two (B a) (hB a)))

def product_set (A B : Type) (hA : isSet A) (hB : isSet B) : isSet (Product A B)
  ≔ sigma_set A (_ ↦ B) hA (_ ↦ hB)
