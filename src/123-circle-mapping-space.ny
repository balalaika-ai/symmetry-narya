export "122-covering-flavors"

def connected_product_component_to (A B : Type) (a : A) (b : B)
  : NativeComponent (Σ A (_ ↦ B)) (a, b) → A
  ≔ c ↦ c .fst .fst

def connected_product_component_from (A B : Type) (ha : Connected A) (a : A) (b : B)
  : A → NativeComponent (Σ A (_ ↦ B)) (a, b)
  ≔ x ↦ ((x, b), trunc_map native_truncation (Id A a x)
      (Id (Σ A (_ ↦ B)) (a, b) (x, b)) (p ↦ (p, refl b)) (ha .snd a x))

def connected_product_component_coordinate (A B : Type) (hb : isSet B) (a : A) (b : B)
  (c : NativeComponent (Σ A (_ ↦ B)) (a, b)) : Id B b (c .fst .snd)
  ≔ mere_rec (Id (Σ A (_ ↦ B)) (a, b) (c .fst)) (Id B b (c .fst .snd))
      (hb b (c .fst .snd)) (p ↦ refl ((u ↦ u .snd) : Σ A (_ ↦ B) → B) p) (c .snd)

def connected_product_component_equiv (A B : Type) (ha : Connected A) (hb : isSet B) (a : A) (b : B)
  : Equiv (NativeComponent (Σ A (_ ↦ B)) (a, b)) A
  ≔ quasi_inverse_equiv (NativeComponent (Σ A (_ ↦ B)) (a, b)) A
      (connected_product_component_to A B a b) (connected_product_component_from A B ha a b)
      (c ↦ subtype_equal (Σ A (_ ↦ B)) (u ↦ Mere (Id (Σ A (_ ↦ B)) (a, b) u))
        (u ↦ mere_isprop (Id (Σ A (_ ↦ B)) (a, b) u))
        (connected_product_component_from A B ha a b (connected_product_component_to A B a b c)) c
        (refl (c .fst .fst), connected_product_component_coordinate A B hb a b c))
      (x ↦ refl x)

def circle_free_loop_coordinates (C : CircleSignature)
  : Equiv (FreeLoop (C .carrier)) (Σ (C .carrier) (_ ↦ Int))
  ≔ family_equiv (C .carrier) (x ↦ Id (C .carrier) x x) (_ ↦ Int)
      (circle_general_winding_equiv C)

def circle_mapping_coordinates (C : CircleSignature)
  : Equiv (C .carrier → C .carrier) (Σ (C .carrier) (_ ↦ Int))
  ≔ compose_equiv (C .carrier → C .carrier) (FreeLoop (C .carrier))
      (Σ (C .carrier) (_ ↦ Int)) (circle_universal_property C (C .carrier))
      (circle_free_loop_coordinates C)

def circle_map_degree (C : CircleSignature) (f : C .carrier → C .carrier) : Int
  ≔ circle_general_winding C (f (C .base)) (refl f (C .loop))

{` xca:(S1->S1)_(f)-eqv-S1. This equivalence uses the actual component
   of f, with mere equality in the full function type. `}
def circle_map_component_equiv (C : CircleSignature) (f : C .carrier → C .carrier)
  : Equiv (C .carrier) (NativeComponent (C .carrier → C .carrier) f)
  ≔ canonical_inverse_equiv (NativeComponent (C .carrier → C .carrier) f) (C .carrier)
      (compose_equiv (NativeComponent (C .carrier → C .carrier) f)
        (NativeComponent (Σ (C .carrier) (_ ↦ Int)) (circle_mapping_coordinates C .map f))
        (C .carrier)
        (component_equiv (C .carrier → C .carrier) (Σ (C .carrier) (_ ↦ Int))
          (circle_mapping_coordinates C) f)
        (connected_product_component_equiv (C .carrier) Int (native_circle_connected C) int_set
          (f (C .base)) (circle_map_degree C f)))
