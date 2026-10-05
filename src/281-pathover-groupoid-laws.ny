export "150-paths-over-and-pairs"

{` xca:cp (intro-uf.tex, after def:pathovercomposition), strong form.

   The book notes that the path-groupoid laws hold for paths over paths
   "after some modification": e.g. q⁻¹ ∘ q : y =_{p⁻¹∘p} y and refl y :
   y =_{refl x} y cannot be compared directly, because they lie over
   different paths in the base. The modification is to compare them over
   the corresponding law in the base. For fixed endpoints u : B x and
   v : B y, the paths over the various paths t : x = y form the family
   t ↦ (u =_t v) over the type x = y. The base law is a 2-path θ between
   two such t, and the dependent law is a path over θ in that family:

     Id ((t ↦ Id B t u v) : Id A x y → Type) θ lhs rhs.

   This is a square in B lying over the square θ in A. Here θ is exactly
   the law for A from module 04 or J.ny: concat_p1, concat_1p,
   concat_inverse_right, concat_inverse_left, inverse_inverse and
   concat_assoc.

   Module 150 states the same six laws over the first projection of the
   corresponding law in Σ A B. That base 2-path depends on q. It cannot be
   identified with the law in A by projecting: Narya efafad2 raises
   bug[E0500] ("dimension mismatch in field of struct") when the .fst of
   concat_p1 (Σ A B) … is compared with another term (checking the
   projection against its own type succeeds; minimal reproducer:
   tests/narya/e0500-minimal.ny). The laws below
   never form 2-dimensional Σ-paths. They are about the same operations
   pathover_concat and pathover_inverse (module 17) as module 150.

   Proof method:
   - The right unit law copies the cylinder transport that defines
     concat_p1. It transports refl q along the lift L of refl y through
     the family (t, c, θ) ↦ (c =_θ q).
   - The dependent version of inverse_refl, at refl, is built the same way.
   - The remaining laws use J on the base path p and then J on the path
     over refl, which is an ordinary path in B x. In the reflexive case,
     the base law is a J-term whose computation rule Jβ is only typal. The
     dependent 2-path is therefore built over the J base case (by
     pathover_concat and pathover_inverse one level up, in the family
     t ↦ Id B t u v over Id A x x) and then transported along Jβ
     (pathover2_transport).
   - For the left unit law, the base case is the right unit law at refl,
     transported along concat_p1_1p_refl. `}

{` Transport of a path over θ along a 2-path θ = θ' in the base. `}
def pathover2_transport (X : Type) (C : X → Type) (a b : X) (θ θ' : Id X a b)
  (ω : Id (Id X a b) θ θ') (c : C a) (d : C b) (D : Id C θ c d)
  : Id C θ' c d
  ≔ refl ((τ ↦ Id C τ c d) : Id X a b → Type) ω .trr.1 D

{` xca:cp, right unit law over concat_p1 A x y p. `}
def pathover_concat_refl_right_strong (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (concat_p1 A x y p)
      (pathover_concat A B x y y p (refl y) u v v q (refl v)) q
  ≔ let L : Id (Id A x y) p (concat A x y y p (refl y))
      ≔ refl ((z ↦ Id A x z) : A → Type) (refl y) .liftr.1 p in
    let M : Id ((t ↦ Id B t u v) : Id A x y → Type) L q
        (pathover_concat A B x y y p (refl y) u v v q (refl v))
      ≔ refl ((t ↦ Id B t u v) : Id A x y → Type) L .liftr.1 q in
    let N : Id ((t ↦ Id (Id A x y) t p) : Id A x y → Type) L (refl p) (concat_p1 A x y p)
      ≔ refl ((t ↦ Id (Id A x y) t p) : Id A x y → Type) L .liftr.1 (refl p) in
    refl ((t c θ ↦ Id ((t' ↦ Id B t' u v) : Id A x y → Type) θ c q)
        : (t : Id A x y) → Id B t u v → Id (Id A x y) t p → Type) L M N
      .trr.1 (refl q)

{` At refl, the two unit laws of J.ny agree: both transport refl (refl x)
   along the same lift. One uses the reflexivity square and the other the
   J-defined connection coconn, and these are identified by Jβ. `}
def concat_p1_1p_refl (A : Type) (x : A)
  : Id (Id (Id A x x) (concat A x x x (refl x) (refl x)) (refl x))
      (concat_p1 A x x (refl x)) (concat_1p A x x (refl x))
  ≔ refl ((σ ↦ refl (Id2 A x) (refl x)
              (refl ((z ↦ Id A x z) : A → Type) (refl x) .liftr.1 (refl x)) σ
            .trr.1 (refl (refl x)))
        : Sq A x x (refl x) x x (refl x) (refl x) (refl x)
          → Id (Id A x x) (concat A x x x (refl x) (refl x)) (refl x))
      (Jβ A x (z q ↦ Sq A x x (refl x) x z q (refl x) q) (refl (refl x)))

{` The dependent counterpart of inverse_refl (module 04): the inverse of
   refl u over refl x is refl u, over inverse_refl A x. `}
def pathover_inverse_refl_strong (A : Type) (B : A → Type) (x : A) (u : B x)
  : Id ((t ↦ Id B t u u) : Id A x x → Type) (inverse_refl A x)
      (pathover_inverse A B x x (refl x) u u (refl u)) (refl u)
  ≔ let ℓ : Id (Id A x x) (refl x) (inverse A x x (refl x))
      ≔ refl ((z ↦ Id A z x) : A → Type) (refl x) .liftr.1 (refl x) in
    let M : Id ((t ↦ Id B t u u) : Id A x x → Type) ℓ (refl u)
        (pathover_inverse A B x x (refl x) u u (refl u))
      ≔ refl ((t ↦ Id B t u u) : Id A x x → Type) ℓ .liftr.1 (refl u) in
    let N : Id ((t ↦ Id (Id A x x) t (refl x)) : Id A x x → Type) ℓ (refl (refl x))
        (inverse_refl A x)
      ≔ refl ((t ↦ Id (Id A x x) t (refl x)) : Id A x x → Type) ℓ .liftr.1 (refl (refl x)) in
    refl ((t c θ ↦ Id ((t' ↦ Id B t' u u) : Id A x x → Type) θ c (refl u))
        : (t : Id A x x) → Id B t u u → Id (Id A x x) t (refl x) → Type) ℓ M N
      .trr.1 (refl (refl u))

{` xca:cp, left unit law over concat_1p A x y p. `}
def pathover_concat_refl_left_strong (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (concat_1p A x y p)
      (pathover_concat A B x x y (refl x) p u u v (refl u) q) q
  ≔ J A x
      (y p ↦ (v : B y) (q : Id B p u v)
        → Id ((t ↦ Id B t u v) : Id A x y → Type) (concat_1p A x y p)
            (pathover_concat A B x x y (refl x) p u u v (refl u) q) q)
      (v q ↦ J (B x) u
        (v q ↦ Id ((t ↦ Id B t u v) : Id A x x → Type) (concat_1p A x x (refl x))
          (pathover_concat A B x x x (refl x) (refl x) u u v (refl u) q) q)
        (pathover2_transport (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
          (concat A x x x (refl x) (refl x)) (refl x)
          (concat_p1 A x x (refl x)) (concat_1p A x x (refl x)) (concat_p1_1p_refl A x)
          (pathover_concat A B x x x (refl x) (refl x) u u u (refl u) (refl u)) (refl u)
          (pathover_concat_refl_right_strong A B x x (refl x) u u (refl u)))
        v q)
      y p v q

{` xca:cp, double inverse over inverse_inverse A x y p. `}
def pathover_inverse_inverse_strong (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u v) : Id A x y → Type) (inverse_inverse A x y p)
      (pathover_inverse A B y x (inverse A x y p) v u (pathover_inverse A B x y p u v q)) q
  ≔ J A x
      (y p ↦ (v : B y) (q : Id B p u v)
        → Id ((t ↦ Id B t u v) : Id A x y → Type) (inverse_inverse A x y p)
            (pathover_inverse A B y x (inverse A x y p) v u (pathover_inverse A B x y p u v q)) q)
      (v q ↦ J (B x) u
        (v q ↦ Id ((t ↦ Id B t u v) : Id A x x → Type) (inverse_inverse A x x (refl x))
          (pathover_inverse A B x x (inverse A x x (refl x)) v u
            (pathover_inverse A B x x (refl x) u v q)) q)
        (pathover2_transport (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
          (inverse A x x (inverse A x x (refl x))) (refl x)
          (concat (Id A x x)
            (inverse A x x (inverse A x x (refl x)))
            (inverse A x x (refl x)) (refl x)
            (refl (inverse A x x) (inverse_refl A x))
            (inverse_refl A x))
          (inverse_inverse A x x (refl x))
          (Jβ A x (y p ↦ Id (Id A x y) (inverse A y x (inverse A x y p)) p)
            (concat (Id A x x)
              (inverse A x x (inverse A x x (refl x)))
              (inverse A x x (refl x)) (refl x)
              (refl (inverse A x x) (inverse_refl A x))
              (inverse_refl A x)))
          (pathover_inverse A B x x (inverse A x x (refl x)) u u
            (pathover_inverse A B x x (refl x) u u (refl u))) (refl u)
          (pathover_concat (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
            (inverse A x x (inverse A x x (refl x))) (inverse A x x (refl x)) (refl x)
            (refl (inverse A x x) (inverse_refl A x)) (inverse_refl A x)
            (pathover_inverse A B x x (inverse A x x (refl x)) u u
              (pathover_inverse A B x x (refl x) u u (refl u)))
            (pathover_inverse A B x x (refl x) u u (refl u)) (refl u)
            (refl ((t c ↦ pathover_inverse A B x x t u u c)
                : (t : Id A x x) → Id B t u u → Id B (inverse A x x t) u u)
              (inverse_refl A x) (pathover_inverse_refl_strong A B x u))
            (pathover_inverse_refl_strong A B x u)))
        v q)
      y p v q

{` xca:cp, right inverse law over concat_inverse_right A x y p. `}
def pathover_concat_inverse_right_strong (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t u u) : Id A x x → Type) (concat_inverse_right A x y p)
      (pathover_concat A B x y x p (inverse A x y p) u v u q (pathover_inverse A B x y p u v q))
      (refl u)
  ≔ J A x
      (y p ↦ (v : B y) (q : Id B p u v)
        → Id ((t ↦ Id B t u u) : Id A x x → Type) (concat_inverse_right A x y p)
            (pathover_concat A B x y x p (inverse A x y p) u v u q
              (pathover_inverse A B x y p u v q)) (refl u))
      (v q ↦ J (B x) u
        (v q ↦ Id ((t ↦ Id B t u u) : Id A x x → Type) (concat_inverse_right A x x (refl x))
          (pathover_concat A B x x x (refl x) (inverse A x x (refl x)) u v u q
            (pathover_inverse A B x x (refl x) u v q)) (refl u))
        (pathover2_transport (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
          (concat A x x x (refl x) (inverse A x x (refl x))) (refl x)
          (concat (Id A x x)
            (concat A x x x (refl x) (inverse A x x (refl x)))
            (inverse A x x (refl x)) (refl x)
            (concat_1p A x x (inverse A x x (refl x)))
            (inverse_refl A x))
          (concat_inverse_right A x x (refl x))
          (Jβ A x (y p ↦ Id (Id A x x) (concat A x y x p (inverse A x y p)) (refl x))
            (concat (Id A x x)
              (concat A x x x (refl x) (inverse A x x (refl x)))
              (inverse A x x (refl x)) (refl x)
              (concat_1p A x x (inverse A x x (refl x)))
              (inverse_refl A x)))
          (pathover_concat A B x x x (refl x) (inverse A x x (refl x)) u u u (refl u)
            (pathover_inverse A B x x (refl x) u u (refl u))) (refl u)
          (pathover_concat (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
            (concat A x x x (refl x) (inverse A x x (refl x)))
            (inverse A x x (refl x)) (refl x)
            (concat_1p A x x (inverse A x x (refl x))) (inverse_refl A x)
            (pathover_concat A B x x x (refl x) (inverse A x x (refl x)) u u u (refl u)
              (pathover_inverse A B x x (refl x) u u (refl u)))
            (pathover_inverse A B x x (refl x) u u (refl u)) (refl u)
            (pathover_concat_refl_left_strong A B x x (inverse A x x (refl x)) u u
              (pathover_inverse A B x x (refl x) u u (refl u)))
            (pathover_inverse_refl_strong A B x u)))
        v q)
      y p v q

{` xca:cp, left inverse law over concat_inverse_left A x y p. This is the
   book's example: q⁻¹ ∘ q and refl are compared over p⁻¹ ∘ p = refl. `}
def pathover_concat_inverse_left_strong (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v)
  : Id ((t ↦ Id B t v v) : Id A y y → Type) (concat_inverse_left A x y p)
      (pathover_concat A B y x y (inverse A x y p) p v u v (pathover_inverse A B x y p u v q) q)
      (refl v)
  ≔ J A x
      (y p ↦ (v : B y) (q : Id B p u v)
        → Id ((t ↦ Id B t v v) : Id A y y → Type) (concat_inverse_left A x y p)
            (pathover_concat A B y x y (inverse A x y p) p v u v
              (pathover_inverse A B x y p u v q) q) (refl v))
      (v q ↦ J (B x) u
        (v q ↦ Id ((t ↦ Id B t v v) : Id A x x → Type) (concat_inverse_left A x x (refl x))
          (pathover_concat A B x x x (inverse A x x (refl x)) (refl x) v u v
            (pathover_inverse A B x x (refl x) u v q) q) (refl v))
        (pathover2_transport (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
          (concat A x x x (inverse A x x (refl x)) (refl x)) (refl x)
          (concat (Id A x x)
            (concat A x x x (inverse A x x (refl x)) (refl x))
            (inverse A x x (refl x)) (refl x)
            (concat_p1 A x x (inverse A x x (refl x)))
            (inverse_refl A x))
          (concat_inverse_left A x x (refl x))
          (Jβ A x (y p ↦ Id (Id A y y) (concat A y x y (inverse A x y p) p) (refl y))
            (concat (Id A x x)
              (concat A x x x (inverse A x x (refl x)) (refl x))
              (inverse A x x (refl x)) (refl x)
              (concat_p1 A x x (inverse A x x (refl x)))
              (inverse_refl A x)))
          (pathover_concat A B x x x (inverse A x x (refl x)) (refl x) u u u
            (pathover_inverse A B x x (refl x) u u (refl u)) (refl u)) (refl u)
          (pathover_concat (Id A x x) ((t ↦ Id B t u u) : Id A x x → Type)
            (concat A x x x (inverse A x x (refl x)) (refl x))
            (inverse A x x (refl x)) (refl x)
            (concat_p1 A x x (inverse A x x (refl x))) (inverse_refl A x)
            (pathover_concat A B x x x (inverse A x x (refl x)) (refl x) u u u
              (pathover_inverse A B x x (refl x) u u (refl u)) (refl u))
            (pathover_inverse A B x x (refl x) u u (refl u)) (refl u)
            (pathover_concat_refl_right_strong A B x x (inverse A x x (refl x)) u u
              (pathover_inverse A B x x (refl x) u u (refl u)))
            (pathover_inverse_refl_strong A B x u)))
        v q)
      y p v q

{` xca:cp, associativity over concat_assoc A x y z w p r s. `}
def pathover_concat_assoc_strong (A : Type) (B : A → Type) (x y z w : A)
  (p : Id A x y) (r : Id A y z) (s : Id A z w) (a : B x) (b : B y) (c : B z) (d : B w)
  (q₁ : Id B p a b) (q₂ : Id B r b c) (q₃ : Id B s c d)
  : Id ((t ↦ Id B t a d) : Id A x w → Type) (concat_assoc A x y z w p r s)
      (pathover_concat A B x z w (concat A x y z p r) s a c d
        (pathover_concat A B x y z p r a b c q₁ q₂) q₃)
      (pathover_concat A B x y w p (concat A y z w r s) a b d q₁
        (pathover_concat A B y z w r s b c d q₂ q₃))
  ≔ J A z
      (w s ↦ (d : B w) (q₃ : Id B s c d)
        → Id ((t ↦ Id B t a d) : Id A x w → Type) (concat_assoc A x y z w p r s)
            (pathover_concat A B x z w (concat A x y z p r) s a c d
              (pathover_concat A B x y z p r a b c q₁ q₂) q₃)
            (pathover_concat A B x y w p (concat A y z w r s) a b d q₁
              (pathover_concat A B y z w r s b c d q₂ q₃)))
      (d q₃ ↦ J (B z) c
        (d q₃ ↦ Id ((t ↦ Id B t a d) : Id A x z → Type) (concat_assoc A x y z z p r (refl z))
          (pathover_concat A B x z z (concat A x y z p r) (refl z) a c d
            (pathover_concat A B x y z p r a b c q₁ q₂) q₃)
          (pathover_concat A B x y z p (concat A y z z r (refl z)) a b d q₁
            (pathover_concat A B y z z r (refl z) b c d q₂ q₃)))
        (pathover2_transport (Id A x z) ((t ↦ Id B t a c) : Id A x z → Type)
          (concat A x z z (concat A x y z p r) (refl z))
          (concat A x y z p (concat A y z z r (refl z)))
          (concat (Id A x z)
            (concat A x z z (concat A x y z p r) (refl z))
            (concat A x y z p r)
            (concat A x y z p (concat A y z z r (refl z)))
            (concat_p1 A x z (concat A x y z p r))
            (inverse (Id A x z)
              (concat A x y z p (concat A y z z r (refl z)))
              (concat A x y z p r)
              (refl (concat A x y z p) (concat_p1 A y z r))))
          (concat_assoc A x y z z p r (refl z))
          (Jβ A z
            (w s ↦ Id (Id A x w)
              (concat A x z w (concat A x y z p r) s)
              (concat A x y w p (concat A y z w r s)))
            (concat (Id A x z)
              (concat A x z z (concat A x y z p r) (refl z))
              (concat A x y z p r)
              (concat A x y z p (concat A y z z r (refl z)))
              (concat_p1 A x z (concat A x y z p r))
              (inverse (Id A x z)
                (concat A x y z p (concat A y z z r (refl z)))
                (concat A x y z p r)
                (refl (concat A x y z p) (concat_p1 A y z r)))))
          (pathover_concat A B x z z (concat A x y z p r) (refl z) a c c
            (pathover_concat A B x y z p r a b c q₁ q₂) (refl c))
          (pathover_concat A B x y z p (concat A y z z r (refl z)) a b c q₁
            (pathover_concat A B y z z r (refl z) b c c q₂ (refl c)))
          (pathover_concat (Id A x z) ((t ↦ Id B t a c) : Id A x z → Type)
            (concat A x z z (concat A x y z p r) (refl z))
            (concat A x y z p r)
            (concat A x y z p (concat A y z z r (refl z)))
            (concat_p1 A x z (concat A x y z p r))
            (inverse (Id A x z)
              (concat A x y z p (concat A y z z r (refl z)))
              (concat A x y z p r)
              (refl (concat A x y z p) (concat_p1 A y z r)))
            (pathover_concat A B x z z (concat A x y z p r) (refl z) a c c
              (pathover_concat A B x y z p r a b c q₁ q₂) (refl c))
            (pathover_concat A B x y z p r a b c q₁ q₂)
            (pathover_concat A B x y z p (concat A y z z r (refl z)) a b c q₁
              (pathover_concat A B y z z r (refl z) b c c q₂ (refl c)))
            (pathover_concat_refl_right_strong A B x z (concat A x y z p r) a c
              (pathover_concat A B x y z p r a b c q₁ q₂))
            (pathover_inverse (Id A x z) ((t ↦ Id B t a c) : Id A x z → Type)
              (concat A x y z p (concat A y z z r (refl z)))
              (concat A x y z p r)
              (refl (concat A x y z p) (concat_p1 A y z r))
              (pathover_concat A B x y z p (concat A y z z r (refl z)) a b c q₁
                (pathover_concat A B y z z r (refl z) b c c q₂ (refl c)))
              (pathover_concat A B x y z p r a b c q₁ q₂)
              (refl ((t e ↦ pathover_concat A B x y z p t a b c q₁ e)
                  : (t : Id A y z) → Id B t b c → Id B (concat A x y z p t) a c)
                (concat_p1 A y z r) (pathover_concat_refl_right_strong A B y z r b c q₂)))))
        d q₃)
      w s d q₃
