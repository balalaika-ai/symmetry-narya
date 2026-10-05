export "193-replacement"
export "202-higher-truncations"

def trunc_unit_surjective (k : Nat) (A : Type) : Surjective A (Trunc k A) (trunc_unit k A)
  ≔ match k [
  | zero. ↦ t ↦ mere_rec A (Mere (BookFiber A (Mere A) (mere A) t)) (mere_isprop (BookFiber A (Mere A) (mere A) t))
      (a ↦ mere (BookFiber A (Mere A) (mere A) t) (a, mere_isprop A t (mere A a))) t
  | suc. k ↦ image_factor_surjective A (A → NTypes k) (trunc_path_family k (truncation k) A) ]

def surjection_image_equiv (A B : Type) (f : A → B) (s : Surjective A B f) : Equiv (Image A B f) B
  ≔ contractible_fiber_projection B (b ↦ Mere (BookFiber A B f b))
      (b ↦ (s b, t ↦ mere_isprop (BookFiber A B f b) t (s b)))

{` The final step of the implementation of def:join-construction-of-truncation:
   for a universe U satisfying replacement, the n-truncation of an essentially
   U-small type is essentially U-small, for every n ≥ -1. Level -1 uses the
   closure of U under propositional truncation. `}
def trunc_essentially_small (U : Universe) (repl : Replacement U) (k : Nat) (A : Type) (hA : EssentiallySmall U A)
  : EssentiallySmall U (Trunc k A)
  ≔ match k [
  | zero. ↦ mere_essentially_small U A hA
  | suc. k ↦
      let T ≔ Trunc (suc. k) A in
      let u ≔ trunc_unit (suc. k) A in
      let unit_paths ≔ ((x y ↦ essentially_small_equiv U (Trunc k (Id A x y)) (Id T (u x) (u y))
          (trunc_path_equiv k A x y)
          (trunc_essentially_small U repl k (Id A x y) (essentially_small_locally_small U A hA x y)))
        : (x y : A) → EssentiallySmall U (Id T (u x) (u y))) in
      let local : LocallySmall U T ≔ z w ↦
        mere_rec (BookFiber A T u z) (EssentiallySmall U (Id T z w)) (essentially_small_prop U (Id T z w))
          (sx ↦ mere_rec (BookFiber A T u w) (EssentiallySmall U (Id T z w)) (essentially_small_prop U (Id T z w))
            (sy ↦ transport T (v ↦ EssentiallySmall U (Id T v w)) (u (sx .fst)) z (inverse T z (u (sx .fst)) (sx .snd))
              (transport T (v ↦ EssentiallySmall U (Id T (u (sx .fst)) v)) (u (sy .fst)) w (inverse T w (u (sy .fst)) (sy .snd))
                (unit_paths (sx .fst) (sy .fst))))
            (trunc_unit_surjective (suc. k) A w))
          (trunc_unit_surjective (suc. k) A z) in
      essentially_small_equiv U (Image A T u) T (surjection_image_equiv A T u (trunc_unit_surjective (suc. k) A))
        (repl A T u hA local) ]

def trunc_small (U : Universe) (repl : Replacement U) (k : Nat) (A : Type) (sA : U .small A) : U .small (Trunc k A)
  ≔ essentially_small_is_small U (Trunc k A)
      (trunc_essentially_small U repl k A (small_essentially_small U A sA))
