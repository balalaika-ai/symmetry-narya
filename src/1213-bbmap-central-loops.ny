export "1208-abelian-hom-pointwise"

{` Chapter 12, helpers for the lemma at abelian.tex 928 (BB is fully faithful
   on abelian groups). For an abelian group L every symmetry g : USym L
   extends to a "central" loop field Π(y : BL) y = y (conjugate g along any
   path sh_L = y; the result does not depend on the path). Consequences:
   (1) for a connected type X with a point x0 and f : X → BL, evaluation
       Π(x : X) (f x = f x) → (f x0 = f x0) is an equivalence, hence
       evaluation at x0 is an equivalence from the component of f in
       X → BL to BL;
   (2) two pointed maps X →* BL are equal as soon as their underlying maps
       are homotopic (the pointing coherence is repaired by a central loop). `}

{` The central loop field attached to g : USym L (L abelian). `}
def bbmap_central_constant (L : Group) (hL : IsAbelian L) (g : USym L) (y : BG L .carrier)
  : WeaklyConstant (Id (BG L .carrier) (shape L) y) (Id (BG L .carrier) y y)
      (e ↦ pointed_loop_conjugate (BG L .carrier) y (shape L) (inverse (BG L .carrier) (shape L) y e) g)
  ≔ e e' ↦
    let A ≔ BG L .carrier in let a ≔ shape L in
    let c' ≔ pointed_loop_conjugate A y a (inverse A a y e') g in
    let back : Id (USym L) (pointed_loop_conjugate A a y e c') g
      ≔ calc
          pointed_loop_conjugate A a y e c' = pointed_loop_conjugate A a a (concat A a y a e (inverse A a y e')) g
            by inverse (USym L) (pointed_loop_conjugate A a a (concat A a y a e (inverse A a y e')) g)
              (pointed_loop_conjugate A a y e c') (loop_conjugate_compose A a y a e (inverse A a y e') g)
          = g by abelian_conjugate_trivial L hL (concat A a y a e (inverse A a y e')) g ∎ in
    calc
      pointed_loop_conjugate A y a (inverse A a y e) g
        = pointed_loop_conjugate A y a (inverse A a y e) (pointed_loop_conjugate A a y e c')
        by refl (pointed_loop_conjugate A y a (inverse A a y e))
          (inverse (USym L) (pointed_loop_conjugate A a y e c') g back)
      = c' by loop_conjugate_cancel_inverse A a y e c' ∎

def bbmap_central_loop (L : Group) (hL : IsAbelian L) (g : USym L) (y : BG L .carrier) : Id (BG L .carrier) y y
  ≔ weakly_constant_rec (Id (BG L .carrier) (shape L) y) (Id (BG L .carrier) y y)
      (e ↦ pointed_loop_conjugate (BG L .carrier) y (shape L) (inverse (BG L .carrier) (shape L) y e) g)
      (bg_groupoid L y y) (bbmap_central_constant L hL g y) (bg_connected L .snd (shape L) y)

def bbmap_central_loop_value (L : Group) (hL : IsAbelian L) (g : USym L) (y : BG L .carrier)
  (e : Id (BG L .carrier) (shape L) y)
  : Id (Id (BG L .carrier) y y) (bbmap_central_loop L hL g y)
      (pointed_loop_conjugate (BG L .carrier) y (shape L) (inverse (BG L .carrier) (shape L) y e) g)
  ≔ weakly_constant_rec_value (Id (BG L .carrier) (shape L) y) (Id (BG L .carrier) y y)
      (e ↦ pointed_loop_conjugate (BG L .carrier) y (shape L) (inverse (BG L .carrier) (shape L) y e) g)
      (bg_groupoid L y y) (bbmap_central_constant L hL g y) (bg_connected L .snd (shape L) y) e

{` Every loop β at y is the value at y of the central field of its free loop
   symmetry (module 1208). `}
def bbmap_central_loop_free (L : Group) (hL : IsAbelian L) (y : BG L .carrier) (β : Id (BG L .carrier) y y)
  : Id (Id (BG L .carrier) y y) (bbmap_central_loop L hL (free_loop_symmetry L hL y β) y) β
  ≔ let A ≔ BG L .carrier in let a ≔ shape L in
    mere_rec (Id A a y) (Id (Id A y y) (bbmap_central_loop L hL (free_loop_symmetry L hL y β) y) β)
      (bg_groupoid L y y (bbmap_central_loop L hL (free_loop_symmetry L hL y β) y) β)
      (e ↦ calc
        bbmap_central_loop L hL (free_loop_symmetry L hL y β) y
          = pointed_loop_conjugate A y a (inverse A a y e) (free_loop_symmetry L hL y β)
          by bbmap_central_loop_value L hL (free_loop_symmetry L hL y β) y e
        = pointed_loop_conjugate A y a (inverse A a y e) (pointed_loop_conjugate A a y e β)
          by refl (pointed_loop_conjugate A y a (inverse A a y e)) (free_loop_symmetry_value L hL y β e)
        = β by loop_conjugate_cancel_inverse A a y e β ∎)
      (bg_connected L .snd a y)

{` (1) Self-homotopies of a map f : X → BL from a connected X are
   determined by their value at x0, and every loop at f(x0) occurs. `}
def bbmap_self_homotopy_eval_equiv (X : Type) (hX : Connected X) (x0 : X) (L : Group) (hL : IsAbelian L)
  (f : X → BG L .carrier)
  : Equiv ((x : X) → Id (BG L .carrier) (f x) (f x)) (Id (BG L .carrier) (f x0) (f x0))
  ≔ let B ≔ BG L .carrier in
    let back ≔ (β ↦ x ↦ bbmap_central_loop L hL (free_loop_symmetry L hL (f x0) β) (f x))
      : Id B (f x0) (f x0) → (x : X) → Id B (f x) (f x) in
    quasi_inverse_equiv ((x : X) → Id B (f x) (f x)) (Id B (f x0) (f x0)) (H ↦ H x0) back
      (H ↦ funext X (x ↦ Id B (f x) (f x)) (back (H x0)) H
        (connected_based_elim native_truncation X hX x0 (x ↦ Id (Id B (f x) (f x)) (back (H x0) x) (H x))
          (x ↦ bg_groupoid L (f x) (f x) (back (H x0) x) (H x))
          (bbmap_central_loop_free L hL (f x0) (H x0))))
      (β ↦ bbmap_central_loop_free L hL (f x0) β)

{` Lemma E: evaluation at x0 is an equivalence NativeComponent (X → BL) f ≃ BL
   (L abelian, X connected). `}
def bbmap_component_point (X B : Type) (f : X → B) : NativeComponent (X → B) f ≔ (f, mere (Id (X → B) f f) (refl f))

def bbmap_component_loops_equiv (X : Type) (hX : Connected X) (x0 : X) (L : Group) (hL : IsAbelian L)
  (f : X → BG L .carrier)
  : Equiv (Id (NativeComponent (X → BG L .carrier) f) (bbmap_component_point X (BG L .carrier) f)
        (bbmap_component_point X (BG L .carrier) f))
      (Id (BG L .carrier) (f x0) (f x0))
  ≔ let B ≔ BG L .carrier in let c ≔ bbmap_component_point X B f in
    compose_equiv (Id (NativeComponent (X → B) f) c c) (Id (X → B) f f) (Id B (f x0) (f x0))
      (subtype_path_equiv (X → B) (k ↦ Mere (Id (X → B) f k)) (k ↦ mere_isprop (Id (X → B) f k)) c c)
      (compose_equiv (Id (X → B) f f) ((x : X) → Id B (f x) (f x)) (Id B (f x0) (f x0))
        (function_extensionality X (_ ↦ B) f f)
        (bbmap_self_homotopy_eval_equiv X hX x0 L hL f))

def bbmap_component_eval_equiv (X : Type) (hX : Connected X) (x0 : X) (L : Group) (hL : IsAbelian L)
  (f : X → BG L .carrier)
  : BookIsEquiv (NativeComponent (X → BG L .carrier) f) (BG L .carrier) (c ↦ c .fst x0)
  ≔ let B ≔ BG L .carrier in let c ≔ bbmap_component_point X B f in
    native_connected_map_equiv_from_loops_book_map (NativeComponent (X → B) f) B (c ↦ c .fst x0)
      (native_component_connected (X → B) f) (bg_connected L) c
      (book_equivalence (Id (NativeComponent (X → B) f) c c) (Id B (f x0) (f x0))
        (bbmap_component_loops_equiv X hX x0 L hL f) .equiv)

{` (2) Pointed maps into BL (L abelian) are equal when their underlying maps
   are homotopic: the homotopy H is corrected by the central loop field of
   the loop (f_pt · H(x0))⁻¹ · g_pt at g(x0). `}
def bbmap_pointed_path_from_homotopy (X : Pointed) (L : Group) (hL : IsAbelian L) (f g : BookPointedMap X (BG L))
  (H : (x : X .carrier) → Id (BG L .carrier) (f .fst x) (g .fst x)) : Id (BookPointedMap X (BG L)) f g
  ≔ let B ≔ BG L .carrier in let a ≔ shape L in let x0 ≔ X .point in
    let y ≔ g .fst x0 in
    let p ≔ concat B a (f .fst x0) y (f .snd) (H x0) in
    let β ≔ concat B y a y (inverse B a y p) (g .snd) in
    let ζ ≔ bbmap_central_loop L hL (free_loop_symmetry L hL y β) in
    let H' ≔ (x ↦ concat B (f .fst x) (g .fst x) (g .fst x) (H x) (ζ (g .fst x)))
      : (x : X .carrier) → Id B (f .fst x) (g .fst x) in
    equiv_inverse_map (Id (BookPointedMap X (BG L)) f g) (PointedHomotopy X (BG L) f g)
      (pointed_map_path_equiv X (BG L) f g)
      (H', calc
        concat B a (f .fst x0) y (f .snd) (H' x0)
          = concat B a (f .fst x0) y (f .snd) (concat B (f .fst x0) y y (H x0) β)
          by refl ((t ↦ concat B a (f .fst x0) y (f .snd) (concat B (f .fst x0) y y (H x0) t)) : Id B y y → Id B a y)
            (bbmap_central_loop_free L hL y β)
        = concat B a y y p β
          by inverse (Id B a y) (concat B a y y p β) (concat B a (f .fst x0) y (f .snd) (concat B (f .fst x0) y y (H x0) β))
            (concat_assoc B a (f .fst x0) y y (f .snd) (H x0) β)
        = g .snd by concat_left_right_inverse B a y y p (g .snd) ∎)
