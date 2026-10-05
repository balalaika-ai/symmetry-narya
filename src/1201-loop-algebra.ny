export "1200-abelian-group-basics"
export "200-truncation-structures"

{` Chapter 12 (abelian.tex): path-algebra helpers used throughout the
   chapter. All paths are in concatenation order (concat p q follows p, then
   q); pointed_loop_conjugate A a x p l = p · l · p⁻¹ in that order. `}

{` Conjugation by a path is injective. `}
def loop_conjugate_injective (A : Type) (a x : A) (p : Id A a x) (l l' : Id A x x)
  (e : Id (Id A a a) (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p l'))
  : Id (Id A x x) l l'
  ≔ J A a (x p ↦ (l l' : Id A x x) → Id (Id A a a) (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p l')
        → Id (Id A x x) l l')
      (l l' e ↦ calc
        l = pointed_loop_conjugate A a a (refl a) l
          by inverse (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l (loop_conjugate_at_refl A a l)
        = pointed_loop_conjugate A a a (refl a) l' by e
        = l' by loop_conjugate_at_refl A a l' ∎)
      x p l l' e

{` Conjugating back and forth along p is the identity. `}
def loop_conjugate_inverse_cancel (A : Type) (a x : A) (p : Id A a x) (l : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (pointed_loop_conjugate A x a (inverse A a x p) l)) l
  ≔ J A a (x p ↦ Id (Id A a a) (pointed_loop_conjugate A a x p (pointed_loop_conjugate A x a (inverse A a x p) l)) l)
      (calc
        pointed_loop_conjugate A a a (refl a) (pointed_loop_conjugate A a a (inverse A a a (refl a)) l)
          = pointed_loop_conjugate A a a (inverse A a a (refl a)) l
          by loop_conjugate_at_refl A a (pointed_loop_conjugate A a a (inverse A a a (refl a)) l)
        = pointed_loop_conjugate A a a (refl a) l
          by refl ((q ↦ pointed_loop_conjugate A a a q l) : Id A a a → Id A a a) (inverse_refl A a)
        = l by loop_conjugate_at_refl A a l ∎)
      x p

def loop_conjugate_cancel_inverse (A : Type) (a x : A) (p : Id A a x) (l : Id A x x)
  : Id (Id A x x) (pointed_loop_conjugate A x a (inverse A a x p) (pointed_loop_conjugate A a x p l)) l
  ≔ J A a (x p ↦ (l : Id A x x) → Id (Id A x x) (pointed_loop_conjugate A x a (inverse A a x p) (pointed_loop_conjugate A a x p l)) l)
      (l ↦ calc
        pointed_loop_conjugate A a a (inverse A a a (refl a)) (pointed_loop_conjugate A a a (refl a) l)
          = pointed_loop_conjugate A a a (refl a) (pointed_loop_conjugate A a a (refl a) l)
          by refl ((q ↦ pointed_loop_conjugate A a a q (pointed_loop_conjugate A a a (refl a) l)) : Id A a a → Id A a a)
            (inverse_refl A a)
        = pointed_loop_conjugate A a a (refl a) l by loop_conjugate_at_refl A a (pointed_loop_conjugate A a a (refl a) l)
        = l by loop_conjugate_at_refl A a l ∎)
      x p l

{` Ω of a self-map f pointed by a homotopy ι : id ~ f is the identity
   (by naturality of ι). `}
def loops_map_homotopic_identity (A : Type) (f : A → A) (ι : (x : A) → Id A x (f x)) (a : A) (h : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a (f a) (ι a) (refl f h)) h
  ≔ calc
      pointed_loop_conjugate A a (f a) (ι a) (refl f h)
        = concat A a (f a) a (concat A a (f a) (f a) (ι a) (refl f h)) (inverse A a (f a) (ι a))
        by inverse (Id A a a) (concat A a (f a) a (concat A a (f a) (f a) (ι a) (refl f h)) (inverse A a (f a) (ι a)))
          (pointed_loop_conjugate A a (f a) (ι a) (refl f h))
          (concat_assoc A a (f a) (f a) a (ι a) (refl f h) (inverse A a (f a) (ι a)))
      = concat A a (f a) a (concat A a a (f a) h (ι a)) (inverse A a (f a) (ι a))
        by refl ((q ↦ concat A a (f a) a q (inverse A a (f a) (ι a))) : Id A a (f a) → Id A a a)
          (inverse (Id A a (f a)) (concat A a a (f a) h (ι a)) (concat A a (f a) (f a) (ι a) (refl f h))
            (naturality A A (x ↦ x) f ι a a h))
      = concat A a a a h (concat A a (f a) a (ι a) (inverse A a (f a) (ι a)))
        by concat_assoc A a a (f a) a h (ι a) (inverse A a (f a) (ι a))
      = concat A a a a h (refl a) by refl (concat A a a a h) (concat_inverse_right A a (f a) (ι a))
      = h by concat_p1 A a a h ∎

{` Conjugation is a homomorphism for the book's product (usym_mul order). `}
def loop_conjugate_mul (A : Type) (a x : A) (p : Id A a x) (l m : Id A x x)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (concat A x x x l m))
      (concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m))
  ≔ loop_conjugate_concat A a x p l m

{` Commuting loops stay commuting after conjugation. `}
def loop_conjugate_commute (A : Type) (a x : A) (p : Id A a x) (l m : Id A x x)
  (c : Id (Id A x x) (concat A x x x l m) (concat A x x x m l))
  : Id (Id A a a) (concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m))
      (concat A a a a (pointed_loop_conjugate A a x p m) (pointed_loop_conjugate A a x p l))
  ≔ calc
      concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m)
        = pointed_loop_conjugate A a x p (concat A x x x l m)
        by inverse (Id A a a) (pointed_loop_conjugate A a x p (concat A x x x l m))
          (concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m))
          (loop_conjugate_concat A a x p l m)
      = pointed_loop_conjugate A a x p (concat A x x x m l) by refl (pointed_loop_conjugate A a x p) c
      = concat A a a a (pointed_loop_conjugate A a x p m) (pointed_loop_conjugate A a x p l)
        by loop_conjugate_concat A a x p m l ∎

{` Homotopies out of a connected type into a groupoid are determined by
   their value at one point. `}
def connected_homotopy_determined (A B : Type) (hA : Connected A) (hB : isGroupoid B) (a : A) (f g : A → B)
  (H K : Homotopy A (_ ↦ B) f g) (e : Id (Id B (f a) (g a)) (H a) (K a)) : Id (Homotopy A (_ ↦ B) f g) H K
  ≔ funext A (x ↦ Id B (f x) (g x)) H K
      (connected_based_elim native_truncation A hA a (x ↦ Id (Id B (f x) (g x)) (H x) (K x))
        (x ↦ hB (f x) (g x) (H x) (K x)) e)

{` Paths between equivalences are paths between their underlying maps. `}
def equiv_map_path_equiv (A B : Type) (e d : Equiv A B)
  : Equiv (Id (Equiv A B) e d) (Id (A → B) (e .map) (d .map))
  ≔ compose_equiv (Id (Equiv A B) e d) (Id (Σ (A → B) (isEquiv A B)) (e .map, e .equiv) (d .map, d .equiv))
      (Id (A → B) (e .map) (d .map))
      (equivalence_on_paths (Equiv A B) (Σ (A → B) (isEquiv A B)) (equiv_sigma_equiv A B) e d)
      (subtype_path_equiv (A → B) (isEquiv A B) (isequiv_isprop A B) (e .map, e .equiv) (d .map, d .equiv))

{` Paths between identifications of types φ ψ : A = B are homotopies
   between the transports (univalence plus function extensionality). The
   underlying map is σ ↦ happly(ap_{trr}(σ)), so evaluating at x is
   ap_{χ ↦ χ.trr x}(σ) (universe_path_homotopy_map). `}
def universe_path_homotopy_equiv (A B : Type) (φ ψ : Id Type A B)
  : Equiv (Id (Id Type A B) φ ψ) (Homotopy A (_ ↦ B) (φ .trr) (ψ .trr))
  ≔ compose_equiv (Id (Id Type A B) φ ψ) (Id (Equiv A B) (transport_equiv A B φ) (transport_equiv A B ψ))
      (Homotopy A (_ ↦ B) (φ .trr) (ψ .trr))
      (equivalence_on_paths (Id Type A B) (Equiv A B) (transport_univalence_equiv A B) φ ψ)
      (compose_equiv (Id (Equiv A B) (transport_equiv A B φ) (transport_equiv A B ψ)) (Id (A → B) (φ .trr) (ψ .trr))
        (Homotopy A (_ ↦ B) (φ .trr) (ψ .trr))
        (equiv_map_path_equiv A B (transport_equiv A B φ) (transport_equiv A B ψ))
        (function_extensionality A (_ ↦ B) (φ .trr) (ψ .trr)))

def universe_path_homotopy_map (A B : Type) (φ ψ : Id Type A B) (σ : Id (Id Type A B) φ ψ) (x : A)
  : Id (Id B (φ .trr x) (ψ .trr x)) (universe_path_homotopy_equiv A B φ ψ .map σ x)
      (refl ((χ ↦ χ .trr x) : Id Type A B → B) σ)
  ≔ refl (refl ((χ ↦ χ .trr x) : Id Type A B → B) σ)

{` A = B is a groupoid when B is (univalence and equiv_hlevel). `}
def universe_paths_groupoid (A B : Type) (hB : isGroupoid B) : isGroupoid (Id Type A B)
  ≔ hlevel_to_groupoid (Id Type A B)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (Equiv A B) (Id Type A B)
        (canonical_inverse_equiv (Id Type A B) (Equiv A B) (univalence_equiv A B))
        (equiv_hlevel (suc. (suc. zero.)) A B (groupoid_to_hlevel B hB)))

{` Paths with given endpoints and their reversal. `}
def path_endpoints_equiv (B : Type) (u u' v v' : B) (p : Id B u' u) (q : Id B v v')
  : Equiv (Id B u v) (Id B u' v')
  ≔ J B u' (u p ↦ Equiv (Id B u v) (Id B u' v'))
      (J B v (v' q ↦ Equiv (Id B u' v) (Id B u' v')) (identity_equiv (Id B u' v)) v' q) u p


{` Conjugating along a composite path is conjugating twice. `}
def loop_conjugate_compose (A : Type) (a x y : A) (p : Id A a x) (q : Id A x y) (l : Id A y y)
  : Id (Id A a a) (pointed_loop_conjugate A a y (concat A a x y p q) l)
      (pointed_loop_conjugate A a x p (pointed_loop_conjugate A x y q l))
  ≔ J A x (y q ↦ (l : Id A y y) → Id (Id A a a) (pointed_loop_conjugate A a y (concat A a x y p q) l)
        (pointed_loop_conjugate A a x p (pointed_loop_conjugate A x y q l)))
      (l ↦ calc
        pointed_loop_conjugate A a x (concat A a x x p (refl x)) l = pointed_loop_conjugate A a x p l
          by refl ((r ↦ pointed_loop_conjugate A a x r l) : Id A a x → Id A a a) (concat_p1 A a x p)
        = pointed_loop_conjugate A a x p (pointed_loop_conjugate A x x (refl x) l)
          by refl (pointed_loop_conjugate A a x p)
            (inverse (Id A x x) (pointed_loop_conjugate A x x (refl x) l) l (loop_conjugate_at_refl A x l)) ∎)
      y q l

{` ap of a pointwise concatenation of two families of paths:
   ap_{w ↦ u(w)·v(w)}(γ) = (ap_{t ↦ t·v(w₀)}(ap_u γ)) · (ap_{u(w₁)·-}(ap_v γ))
   (concatenation order). `}
def map_path_pointwise_concat (W Y : Type) (a b c : Y) (u : W → Id Y a b) (v : W → Id Y b c)
  (w0 w1 : W) (γ : Id W w0 w1)
  : Id (Id (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w1) (v w1)))
      (refl ((w ↦ concat Y a b c (u w) (v w)) : W → Id Y a c) γ)
      (concat (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w1) (v w0)) (concat Y a b c (u w1) (v w1))
        (refl ((t ↦ concat Y a b c t (v w0)) : Id Y a b → Id Y a c) (refl u γ))
        (refl (concat Y a b c (u w1)) (refl v γ)))
  ≔ J W w0
      (w1 γ ↦ Id (Id (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w1) (v w1)))
        (refl ((w ↦ concat Y a b c (u w) (v w)) : W → Id Y a c) γ)
        (concat (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w1) (v w0)) (concat Y a b c (u w1) (v w1))
          (refl ((t ↦ concat Y a b c t (v w0)) : Id Y a b → Id Y a c) (refl u γ))
          (refl (concat Y a b c (u w1)) (refl v γ))))
      (inverse (Id (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w0) (v w0)))
        (concat (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w0) (v w0))
          (refl (concat Y a b c (u w0) (v w0))) (refl (concat Y a b c (u w0) (v w0))))
        (refl (concat Y a b c (u w0) (v w0)))
        (concat_p1 (Id Y a c) (concat Y a b c (u w0) (v w0)) (concat Y a b c (u w0) (v w0))
          (refl (concat Y a b c (u w0) (v w0)))))
      w1 γ
