export "87-circle-delooping"

def loop_coordinate_unit (A B : Type) (a : A) (b : B) (e : Equiv (Id A a a) (Id B b b))
  (u : Equiv (Id A a a) Int) (v : Equiv (Id B b b) Int)
  (value : (p : Id A a a) → Id Int (v .map (e .map p)) (u .map p))
  (unit_u : Id Int (u .map (refl a)) int_zero) (unit_v : Id Int (v .map (refl b)) int_zero)
  : LoopMapUnit A B a b (e .map)
  ≔ equivalence_injective (Id B b b) Int v (e .map (refl a)) (refl b) (calc
      v .map (e .map (refl a)) = u .map (refl a) by value (refl a)
      = int_zero by unit_u
      = v .map (refl b) by unit_v ∎)

def loop_coordinate_composition (A B : Type) (a : A) (b : B) (e : Equiv (Id A a a) (Id B b b))
  (u : Equiv (Id A a a) Int) (v : Equiv (Id B b b) Int)
  (value : (p : Id A a a) → Id Int (v .map (e .map p)) (u .map p))
  (composition_u : (p q : Id A a a) → Id Int (u .map (concat A a a a p q)) (int_add (u .map p) (u .map q)))
  (composition_v : (p q : Id B b b) → Id Int (v .map (concat B b b b p q)) (int_add (v .map p) (v .map q)))
  : LoopMapComposition A B a b (e .map)
  ≔ p q ↦ equivalence_injective (Id B b b) Int v (e .map (concat A a a a p q))
      (concat B b b b (e .map p) (e .map q)) (calc
        v .map (e .map (concat A a a a p q)) = u .map (concat A a a a p q) by value (concat A a a a p q)
        = int_add (u .map p) (u .map q) by composition_u p q
        = int_add (v .map (e .map p)) (v .map (e .map q)) by refl int_add (value p) (value q)
        = v .map (concat B b b b (e .map p) (e .map q)) by composition_v (e .map p) (e .map q) ∎)

def circle_coordinate_loop_equiv (C : CircleSignature) (x : C .carrier)
  : Equiv (Id (C .carrier) (C .base) (C .base)) (Id (C .carrier) x x)
  ≔ compose_equiv (Id (C .carrier) (C .base) (C .base)) Int (Id (C .carrier) x x)
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
      (canonical_inverse_equiv (Id (C .carrier) x x) Int (circle_general_winding_equiv C x))

def circle_coordinate_loop_winding (C : CircleSignature) (x : C .carrier) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_general_winding C x (circle_coordinate_loop_equiv C x .map p)) (circle_winding C p)
  ≔ equiv_counit (Id (C .carrier) x x) Int (circle_general_winding_equiv C x) (circle_winding C p)

def circle_coordinate_loop_unit (C : CircleSignature) (x : C .carrier)
  : LoopMapUnit (C .carrier) (C .carrier) (C .base) x (circle_coordinate_loop_equiv C x .map)
  ≔ loop_coordinate_unit (C .carrier) (C .carrier) (C .base) x (circle_coordinate_loop_equiv C x)
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
      (circle_general_winding_equiv C x) (circle_coordinate_loop_winding C x) (circle_winding_refl C) (circle_general_winding_refl C x)

def circle_coordinate_loop_composition (C : CircleSignature) (x : C .carrier)
  : LoopMapComposition (C .carrier) (C .carrier) (C .base) x (circle_coordinate_loop_equiv C x .map)
  ≔ loop_coordinate_composition (C .carrier) (C .carrier) (C .base) x (circle_coordinate_loop_equiv C x)
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
      (circle_general_winding_equiv C x) (circle_coordinate_loop_winding C x)
      (circle_winding_composition C) (circle_general_winding_composition C x)

{` Second part of xca:general-winding.  No global choice of a path to x is
   used. The base law is propositional, as required by CircleSignature. `}
def circle_translation (C : CircleSignature) (x : C .carrier) : BookEquiv (C .carrier) (C .carrier)
  ≔ circle_delooping_equiv C (C .carrier) (native_circle_connected C) x (circle_coordinate_loop_equiv C x)
      (circle_coordinate_loop_unit C x) (circle_coordinate_loop_composition C x)

def circle_translation_base (C : CircleSignature) (x : C .carrier)
  : Id (C .carrier) (circle_translation C x .map (C .base)) x
  ≔ circle_rec_beta C (C .carrier) (x, circle_coordinate_loop_equiv C x .map (C .loop)) .fst
