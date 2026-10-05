{` Control for e0500-truncation-step.ny: the same proof with the base case moved
   into a separate definition `base`.  This checks without error (the workaround
   used in symmetry-narya src/201-truncation-step.ny, trunc_step_decode_base). `}
def transport (A : Type) (B : A → Type) (x y : A) (p : Id A x y) : B x → B y
  ≔ refl B p .trr.1
def inverse (A : Type) (x y : A) (p : Id A x y) : Id A y x
  ≔ refl ((z ↦ Id A z x) : A → Type) p .trr.1 (refl x)
def J (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a)) (b : A) (p : Id A a b)
  : P b p
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) p in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  refl P q (sym s) .trr.1 pa
def transport_refl (A : Type) (B : A → Type) (x : A) (b : B x)
  : Id (B x) (transport A B x x (refl x) b) b
  ≔ inverse (B x) b (transport A B x x (refl x) b) (refl B (refl x) .liftr b)
def inverse_refl (A : Type) (x : A) : Id (Id A x x) (inverse A x x (refl x)) (refl x)
  ≔ transport_refl A (z ↦ Id A z x) x (refl x)
def R (A : Type) : Type ≔ sig ( fst : A )
def base (X : Type) (v : X)
  : Id X (transport (R Type) (w ↦ w .fst) (X,) (X,) (inverse (R Type) (X,) (X,) (refl ((X,) : R Type))) v)
      (transport (R Type) (w ↦ w .fst) (X,) (X,) (refl ((X,) : R Type)) v)
  ≔ refl ((q ↦ transport (R Type) (w ↦ w .fst) (X,) (X,) q v) : Id (R Type) (X,) (X,) → X)
         (inverse_refl (R Type) (X,))
def c (X : Type) (v : X) (A : Type) (x y : A) (r : Id A x y)
  : Id X (transport (R Type) (w ↦ w .fst) (X,) (X,) (inverse (R Type) (X,) (X,) (refl ((X,) : R Type))) v)
      (transport (R Type) (w ↦ w .fst) (X,) (X,) (refl ((X,) : R Type)) v)
  ≔ J A x
      (y r ↦
       Id X (transport (R Type) (w ↦ w .fst) (X,) (X,) (inverse (R Type) (X,) (X,) (refl ((X,) : R Type))) v)
         (transport (R Type) (w ↦ w .fst) (X,) (X,) (refl ((X,) : R Type)) v))
      (base X v)
      y r
