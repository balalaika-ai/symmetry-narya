export "136-roots-of-infinite-cycles"

{` The remark after def:pathsoverpaths: over a constant family, paths over
   p are ordinary identifications. Native Id computes this judgmentally;
   the book obtains it by induction on p. `}
def pathover_constant_type (X Z : Type) (a a' : X) (p : Id X a a') (z z' : Z)
  : Id Type (Id ((_ ↦ Z) : X → Type) p z z') (Id Z z z')
  ≔ refl (Id Z z z')

def pathover_constant_equiv (X Z : Type) (a a' : X) (p : Id X a a') (z z' : Z)
  : Equiv (Id ((_ ↦ Z) : X → Type) p z z') (Id Z z z')
  ≔ identity_equiv (Id Z z z')

{` xca:cp. Groupoid laws for pathover_concat and pathover_inverse, each
   lying over the base component of the corresponding law for paths in
   Σ A B. That component is not identified here with the law in A. `}
def pathover_concat_refl_right (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (concat_p1 (Σ A B) (x, u) (y, v) (p, q) .fst)
      (pathover_concat A B x y y p (refl y) u v v q (refl v)) q
  ≔ concat_p1 (Σ A B) (x, u) (y, v) (p, q) .snd

def pathover_concat_refl_left (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (concat_1p (Σ A B) (x, u) (y, v) (p, q) .fst)
      (pathover_concat A B x x y (refl x) p u u v (refl u) q) q
  ≔ concat_1p (Σ A B) (x, u) (y, v) (p, q) .snd

def pathover_concat_inverse_right (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u u) : Id A x x → Type)
      (concat_inverse_right (Σ A B) (x, u) (y, v) (p, q) .fst)
      (pathover_concat A B x y x p (inverse A x y p) u v u q (pathover_inverse A B x y p u v q))
      (refl u)
  ≔ concat_inverse_right (Σ A B) (x, u) (y, v) (p, q) .snd

def pathover_concat_inverse_left (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t v v) : Id A y y → Type)
      (concat_inverse_left (Σ A B) (x, u) (y, v) (p, q) .fst)
      (pathover_concat A B y x y (inverse A x y p) p v u v (pathover_inverse A B x y p u v q) q)
      (refl v)
  ≔ concat_inverse_left (Σ A B) (x, u) (y, v) (p, q) .snd

def pathover_inverse_inverse (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (inverse_inverse (Σ A B) (x, u) (y, v) (p, q) .fst)
      (pathover_inverse A B y x (inverse A x y p) v u (pathover_inverse A B x y p u v q)) q
  ≔ inverse_inverse (Σ A B) (x, u) (y, v) (p, q) .snd

def pathover_concat_assoc (A : Type) (B : A → Type) (x y z w : A)
  (p : Id A x y) (r : Id A y z) (s : Id A z w) (a : B x) (b : B y) (c : B z) (d : B w)
  (q₁ : Id B p a b) (q₂ : Id B r b c) (q₃ : Id B s c d)
  : Id ((t ↦ Id B t a d) : Id A x w → Type)
      (concat_assoc (Σ A B) (x, a) (y, b) (z, c) (w, d) (p, q₁) (r, q₂) (s, q₃) .fst)
      (pathover_concat A B x z w (concat A x y z p r) s a c d
        (pathover_concat A B x y z p r a b c q₁ q₂) q₃)
      (pathover_concat A B x y w p (concat A y z w r s) a b d q₁
        (pathover_concat A B y z w r s b c d q₂ q₃))
  ≔ concat_assoc (Σ A B) (x, a) (y, b) (z, c) (w, d) (p, q₁) (r, q₂) (s, q₃) .snd

{` def:applfun2. Application of a function of two variables to a path p
   and a path q over p. The reflexive computation rule is judgmental. `}
def apap (X : Type) (Y : X → Type) (Z : Type) (g : (x : X) → Y x → Z)
  (x x' : X) (y : Y x) (y' : Y x') (p : Id X x x') (q : Id Y p y y')
  : Id Z (g x y) (g x' y')
  ≔ refl g p q

def apap_refl (X : Type) (Y : X → Type) (Z : Type) (g : (x : X) → Y x → Z)
  (x : X) (y : Y x)
  : Id (Id Z (g x y) (g x y)) (apap X Y Z g x x y y (refl x) (refl y)) (refl (g x y))
  ≔ refl (refl (g x y))

{` def:applfun2comp, holding judgmentally for native Id. `}
def apap_refl_left (X : Type) (Y : X → Type) (Z : Type) (g : (x : X) → Y x → Z)
  (x : X) (y y' : Y x) (q : Id (Y x) y y')
  : Id (Id Z (g x y) (g x y')) (apap X Y Z g x x y y' (refl x) q) (map_path (Y x) Z (g x) y y' q)
  ≔ refl (map_path (Y x) Z (g x) y y' q)

{` def:pairtopath: pair(x)(y) = (x,y) and pair=(p,q) = apap pair p q. `}
def pair (X : Type) (Y : X → Type) (x : X) (y : Y x) : Σ X Y ≔ (x, y)

def pair_path (X : Type) (Y : X → Type) (x x' : X) (y : Y x) (y' : Y x')
  (p : Id X x x') (q : Id Y p y y') : Id (Σ X Y) (x, y) (x', y')
  ≔ apap X Y (Σ X Y) (pair X Y) x x' y y' p q

def pair_path_sigma (X : Type) (Y : X → Type) (x x' : X) (y : Y x) (y' : Y x')
  (p : Id X x x') (q : Id Y p y y')
  : Id (Id (Σ X Y) (x, y) (x', y')) (pair_path X Y x x' y y' p q)
      (sigma_path_pair X Y (x, y) (x', y') (p, q))
  ≔ refl (sigma_path_pair X Y (x, y) (x', y') (p, q))

{` cor:isEq-pair=. The book proves it by induction on q. `}
def pair_path_refl_left (X : Type) (Y : X → Type) (x : X) (y y' : Y x) (q : Id (Y x) y y')
  : Id (Id (Σ X Y) (x, y) (x, y')) (pair_path X Y x x y y' (refl x) q)
      (map_path (Y x) (Σ X Y) (pair X Y x) y y' q)
  ≔ refl (map_path (Y x) (Σ X Y) (pair X Y x) y y' q)

{` The three identifications stated after lem:isEq-pair=. `}
def pair_path_fst (X : Type) (Y : X → Type) (x x' : X) (y : Y x) (y' : Y x')
  (p : Id X x x') (q : Id Y p y y')
  : Id (Id X x x') (map_path (Σ X Y) X (t ↦ t .fst) (x, y) (x', y') (pair_path X Y x x' y y' p q)) p
  ≔ refl p

def pair_path_snd (X : Type) (Y : X → Type) (x x' : X) (y : Y x) (y' : Y x')
  (p : Id X x x') (q : Id Y p y y')
  : Id (Id Y p y y') (apd (Σ X Y) (t ↦ Y (t .fst)) (t ↦ t .snd) (x, y) (x', y')
      (pair_path X Y x x' y y' p q)) q
  ≔ refl q

def pair_path_eta (X : Type) (Y : X → Type) (u v : Σ X Y) (r : Id (Σ X Y) u v)
  : Id (Id (Σ X Y) u v) r (pair_path X Y (u .fst) (v .fst) (u .snd) (v .snd) (r .fst) (r .snd))
  ≔ refl r

{` lem:isEq-pair-bin=, with the map (p,q) |-> pair=(p,q) for the constant
   family, where q is read as a path over p. `}
def product_pair_path (X Y : Type) (x x' : X) (y y' : Y)
  (pq : Product (Id X x x') (Id Y y y')) : Id (Product X Y) (x, y) (x', y')
  ≔ pair_path X (_ ↦ Y) x x' y y' (pq .fst) (pq .snd)

def product_path_equiv (X Y : Type) (x x' : X) (y y' : Y)
  : Equiv (Product (Id X x x') (Id Y y y')) (Id (Product X Y) (x, y) (x', y'))
  ≔ quasi_inverse_equiv (Product (Id X x x') (Id Y y y')) (Id (Product X Y) (x, y) (x', y'))
      (product_pair_path X Y x x' y y') (r ↦ (r .fst, r .snd))
      (pq ↦ refl pq) (r ↦ refl r)

def book_product_path_equiv (X Y : Type) (x x' : X) (y y' : Y)
  : BookIsEquiv (Product (Id X x x') (Id Y y y')) (Id (Product X Y) (x, y) (x', y'))
      (product_pair_path X Y x x' y y')
  ≔ book_equivalence (Product (Id X x x') (Id Y y y')) (Id (Product X Y) (x, y) (x', y'))
      (product_path_equiv X Y x x' y y') .equiv
