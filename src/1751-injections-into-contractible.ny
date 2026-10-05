export "1750-lpo-halting"

{` rem:injectionsurjectionisnotwhatyouthink (metamath.tex:240). Injections
   are the book's injections (def:injection, IsEmbedding: propositional
   fibers). The topological picture (the real line, its homotopy type,
   cohesion) is intuition and is not formalized; its internal content is:
   an injection into a contractible type has propositional domain, so the
   non-connected two-point set Bool admits no injection into a contractible
   (or any connected) type, and every fiber of a map Bool → C into a
   contractible C contains both points. `}

def book_injection_prop (A B : Type) (f : A → B) : isProp (IsEmbedding A B f)
  ≔ pi_prop B (b ↦ isProp (BookFiber A B f b)) (b ↦ isprop_isprop (BookFiber A B f b))

{` "All elements of a contractible type are identical". `}
def contractible_all_identified (C : Type) (hC : BookIsContr C) (x y : C) : Id C x y
  ≔ contractible_prop C (native_contraction C hC) x y

{` Injections into a contractible type have propositional domain, and
   conversely every map from a proposition into a contractible type is an
   injection. `}
def injection_into_contractible_prop (A C : Type) (f : A → C) (hC : BookIsContr C) (h : IsEmbedding A C f)
  : isProp A
  ≔ a a' ↦ map_path (BookFiber A C f (hC .center)) A (t ↦ t .fst) (a, hC .contract (f a)) (a', hC .contract (f a'))
      (h (hC .center) (a, hC .contract (f a)) (a', hC .contract (f a')))

def prop_into_contractible_injection (A C : Type) (f : A → C) (hC : BookIsContr C) (hA : isProp A)
  : IsEmbedding A C f
  ≔ c ↦ sigma_prop A (a ↦ Id C c (f a)) hA
      (a ↦ prop_is_set C (contractible_prop C (native_contraction C hC)) c (f a))

def injection_into_contractible_iff (A C : Type) (f : A → C) (hC : BookIsContr C)
  : Equiv (IsEmbedding A C f) (isProp A)
  ≔ iff_equiv (IsEmbedding A C f) (isProp A) (book_injection_prop A C f) (isprop_isprop A)
      (injection_into_contractible_prop A C f hC) (prop_into_contractible_injection A C f hC)

{` The inclusion of {0,1} into a contractible type is not an injection. `}
def bool_into_contractible_not_injection (C : Type) (hC : BookIsContr C) (f : Bool → C)
  (h : IsEmbedding Bool C f) : Empty
  ≔ bool_encode false. true. (injection_into_contractible_prop Bool C f hC h false. true.)

{` "Our preimage of 3.25 contains both 0 and 1": over every point the fiber
   contains (0, _) and (1, _), which are distinct, so it is not a proposition. `}
def bool_fiber_two_points (C : Type) (hC : BookIsContr C) (f : Bool → C) (c : C)
  : Σ (BookFiber Bool C f c) (u ↦ Σ (BookFiber Bool C f c) (v ↦
      Product (Id Bool (u .fst) false.) (Product (Id Bool (v .fst) true.) (Not (Id (BookFiber Bool C f c) u v)))))
  ≔ ((false., contractible_all_identified C hC c (f false.)),
      ((true., contractible_all_identified C hC c (f true.)),
        (refl (false. : Bool), (refl (true. : Bool),
          q ↦ bool_encode false. true.
            (map_path (BookFiber Bool C f c) Bool (t ↦ t .fst)
              (false., contractible_all_identified C hC c (f false.))
              (true., contractible_all_identified C hC c (f true.)) q)))))

def bool_fiber_not_prop (C : Type) (hC : BookIsContr C) (f : Bool → C) (c : C)
  (h : isProp (BookFiber Bool C f c)) : Empty
  ≔ let w ≔ bool_fiber_two_points C hC f c in
    w .snd .snd .snd .snd (h (w .fst) (w .snd .fst))

{` Bool is not connected (module 121), so cor:inj+connected leaves no room
   for an injection of Bool into a connected type: it would be an
   equivalence. `}
def bool_into_connected_not_injection (B : Type) (hB : Connected B) (f : Bool → B)
  (h : IsEmbedding Bool B f) : Empty
  ≔ boolean_not_connected
      (transport Type Connected B Bool
        (inverse Type Bool B
          (ua Bool B (native_equivalence Bool B (native_nonempty_connected_embedding_equiv Bool B f
            (mere Bool false.) hB h))))
        hB)

{` Litmus: Unit (a contractible type) and the map Bool → Unit. `}
def unit_book_contractible : BookIsContr Unit ≔ (star., u ↦ unit_prop star. u)

def bool_to_unit_not_injection (h : IsEmbedding Bool Unit (_ ↦ star.)) : Empty
  ≔ bool_into_contractible_not_injection Unit unit_book_contractible (_ ↦ star.) h

def unit_to_unit_injection : IsEmbedding Unit Unit (_ ↦ star.)
  ≔ prop_into_contractible_injection Unit Unit (_ ↦ star.) unit_book_contractible unit_prop
