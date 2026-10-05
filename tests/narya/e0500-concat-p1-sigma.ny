{` Self-contained projection reproducer (concat and concat_p1 are
   copied from vendor/narya/test/black/hott.t/J.ny).  With `import "J"` instead of
   the two copied definitions the result is the same.
   The .fst of the right-unit law in Σ A B is compared with the right-unit law in A. `}
def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )
def Id2 (A : Type) (x y : A) (p q : Id A x y) : Type ≔ Id (Id A x y) p q
def concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z
  ≔ refl ((y ↦ Id A x y) : A → Type) q .trr.1 p
def concat_p1 (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x y y p (refl y)) p
  ≔ refl ((q ↦ Id2 A x y q p) : Id A x y → Type)
        (refl ((z ↦ Id A x z) : A → Type) (refl y) .liftr.1 p)
      .trr.1 (refl p)
def conv (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (u : B x) (v : B y) (q : Id B p u v)
  (K : Id (Id A x y) (concat A x y y p (refl y)) p → Type)
  (t : K (concat_p1 A x y p)) : K (concat_p1 (Σ A B) (x, u) (y, v) (p, q) .fst)
  ≔ t
