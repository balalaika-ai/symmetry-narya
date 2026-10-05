export "58-orbits-and-cycles"

def set_bijection_equiv (A B : Type) (hb : isSet B) (f : A → B)
  (hi : PathReflecting A B f) (hs : Surjective A B f) : Equiv A B
  ≔ (f, b ↦ let hp ≔ fiber_prop_of_injective A B hb f hi b in
      let c ≔ mere_rec (BookFiber A B f b) (Fiber A B f b) hp (fiber_from_book A B f b) (hs b) in
      (c, x ↦ hp x c))

def quotient_rec_injective (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (hp : Respects A B R f)
  (hr : (x y : A) → Id B (f x) (f y) → Rel A R x y)
  : PathReflecting (Quotient A R) B (quotient_rec A B R hb f hp)
  ≔ u v ↦ let F ≔ quotient_rec A B R hb f hp in
      mere_rec (BookFiber A (Quotient A R) (quotient_class A R) u)
        (Id B (F u) (F v) → Id (Quotient A R) u v)
        (pi_prop (Id B (F u) (F v)) (_ ↦ Id (Quotient A R) u v) (_ ↦ quotient_set A R u v))
        (a ↦ mere_rec (BookFiber A (Quotient A R) (quotient_class A R) v)
          (Id B (F u) (F v) → Id (Quotient A R) u v)
          (pi_prop (Id B (F u) (F v)) (_ ↦ Id (Quotient A R) u v) (_ ↦ quotient_set A R u v))
          (b p ↦ calc
            u = quotient_class A R (a .fst) by a .snd
            = quotient_class A R (b .fst) by quotient_encode A R (a .fst) (b .fst)
                (hr (a .fst) (b .fst) (calc
                  f (a .fst) = F u by refl F (a .snd)
                  = F v by p
                  = f (b .fst) by refl F (b .snd) ∎))
            = v by b .snd ∎) (quotient_surjective A R v)) (quotient_surjective A R u)

def quotient_rec_surjective (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (hp : Respects A B R f) (hs : Surjective A B f)
  : Surjective (Quotient A R) B (quotient_rec A B R hb f hp)
  ≔ b ↦ trunc_map native_truncation (BookFiber A B f b)
      (BookFiber (Quotient A R) B (quotient_rec A B R hb f hp) b)
      (w ↦ (quotient_class A R (w .fst), w .snd)) (hs b)

{` A surjection to a set presents its codomain as the quotient by exactly
   the relation detected by equality of its values. `}
def quotient_presentation_equiv (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (hp : Respects A B R f)
  (hr : (x y : A) → Id B (f x) (f y) → Rel A R x y) (hs : Surjective A B f)
  : Equiv (Quotient A R) B
  ≔ set_bijection_equiv (Quotient A R) B hb (quotient_rec A B R hb f hp)
      (quotient_rec_injective A B R hb f hp hr) (quotient_rec_surjective A B R hb f hp hs)
