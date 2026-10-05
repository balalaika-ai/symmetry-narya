{` SymmetryBook chapter 2. Native HOTT identity, not an inductive replacement.
   The two imported upstream modules construct J (including typal beta)
   and equivalence-to-universe-path using Narya's transport and glue. `}
export "../vendor/narya/test/black/hott.t/J"
export "../vendor/narya/test/black/hott.t/univalence"

def identity (A : Type) : A → A ≔ x ↦ x

def compose (A B C : Type) (g : B → C) (f : A → B) : A → C ≔ x ↦ g (f x)

def constant (A B : Type) (b : B) : A → B ≔ _ ↦ b

def map_path (A B : Type) (f : A → B) (x y : A) (p : Id A x y)
  : Id B (f x) (f y) ≔ refl f p

def apd (A : Type) (B : A → Type) (f : (x : A) → B x)
  (x y : A) (p : Id A x y) : Id B p (f x) (f y) ≔ refl f p

def ap_identity (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (map_path A A (identity A) x y p) p ≔ refl p

def ap_compose (A B C : Type) (f : A → B) (g : B → C)
  (x y : A) (p : Id A x y)
  : Id (Id C (g (f x)) (g (f y)))
      (map_path A C (compose A B C g f) x y p)
      (map_path B C g (f x) (f y) (map_path A B f x y p))
  ≔ refl (refl g (refl f p))

def ap_refl (A B : Type) (f : A → B) (x : A)
  : Id (Id B (f x) (f x)) (map_path A B f x x (refl x)) (refl (f x))
  ≔ refl (refl (f x))

def Homotopy (A : Type) (B : A → Type) (f g : (x : A) → B x)
  : Type ≔ (x : A) → Id (B x) (f x) (g x)

def happly (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (p : Id ((x : A) → B x) f g) : Homotopy A B f g
  ≔ x ↦ p (refl x)

def funext (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (h : Homotopy A B f g) : Id ((x : A) → B x) f g
  ≔ x ⤇ J A x.0 (y p ↦ Id B p (f x.0) (g y)) (h x.0) x.1 x.2

def funext_beta (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (h : Homotopy A B f g) (x : A)
  : Id (Id (B x) (f x) (g x)) (h x) (happly A B f g (funext A B f g h) x)
  ≔ Jβ A x (y p ↦ Id B p (f x) (g y)) (h x)

def pathover_of_eq (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id (B y) (transport A B x y p u) v)
  : Id B p u v
  ≔ refl ((w ↦ Id B p u w) : B y → Type) q .trr (refl B p .liftr u)

def Product (A B : Type) : Type ≔ Σ A (_ ↦ B)

def isProp (A : Type) : Type ≔ (x y : A) → Id A x y

def isSet (A : Type) : Type ≔ (x y : A) → isProp (Id A x y)

def isGroupoid (A : Type) : Type ≔ (x y : A) → isSet (Id A x y)

def Fiber (A B : Type) (f : A → B) (b : B) : Type ≔ Σ A (a ↦ Id B (f a) b)

def isEquiv (A B : Type) (f : A → B) : Type ≔ (b : B) → isContr (Fiber A B f b)

def Equiv (A B : Type) : Type ≔ sig (map : A → B, equiv : isEquiv A B map)

def equiv_inverse_map (A B : Type) (e : Equiv A B) : B → A
  ≔ b ↦ e .equiv b .center .fst

def equiv_counit (A B : Type) (e : Equiv A B) (b : B)
  : Id B (e .map (equiv_inverse_map A B e b)) b
  ≔ e .equiv b .center .snd

def equiv_unit (A B : Type) (e : Equiv A B) (a : A)
  : Id A a (equiv_inverse_map A B e (e .map a))
  ≔ e .equiv (e .map a) .contract (a, refl (e .map a)) .fst

def ua (A B : Type) (e : Equiv A B) : Id Type A B
  ≔ univalence A B (e .map) (e .equiv)

{` The forward transport of this glue construction computes to the map. `}
def ua_transport (A B : Type) (e : Equiv A B) (a : A)
  : Id B (ua A B e .trr a) (e .map a) ≔ refl (e .map a)

def Pointed : Type ≔ sig (carrier : Type, point : carrier)

def PointedMap (A B : Pointed) : Type ≔ sig (
  map : A .carrier → B .carrier,
  point : Id (B .carrier) (map (A .point)) (B .point))

def Loop (A : Pointed) : Type ≔ Id (A .carrier) (A .point) (A .point)

def FreeLoop (A : Type) : Type ≔ Σ A (a ↦ Id A a a)
