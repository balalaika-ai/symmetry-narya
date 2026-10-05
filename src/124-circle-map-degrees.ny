export "123-circle-mapping-space"

def circle_degree_rec (C : CircleSignature) (x : C .carrier) (p : Id (C .carrier) x x)
  : Id Int (circle_map_degree C (circle_rec C (C .carrier) (x, p)))
      (circle_general_winding C x p)
  ≔ refl ((t ↦ circle_general_winding C (t .fst) (t .snd)) : FreeLoop (C .carrier) → Int)
      (circle_rec_beta C (C .carrier) (x, p))

def circle_degree_identity (C : CircleSignature)
  : Id Int (circle_map_degree C (identity (C .carrier))) (pos. (suc. zero.))
  ≔ concat Int (circle_map_degree C (identity (C .carrier))) (circle_winding C (C .loop))
      (pos. (suc. zero.)) (circle_general_winding_base_value C (C .loop)) (circle_winding_loop C)

{` The map denoted -id in xca:S1=S1-components, with exactly its stated
   recursion boundary. Base computation is propositional in this model. `}
def circle_reflection (C : CircleSignature) : C .carrier → C .carrier
  ≔ circle_rec C (C .carrier)
      (C .base, inverse (C .carrier) (C .base) (C .base) (C .loop))

def circle_degree_reflection (C : CircleSignature)
  : Id Int (circle_map_degree C (circle_reflection C)) (neg. zero.)
  ≔ calc
      circle_map_degree C (circle_reflection C)
      = circle_general_winding C (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop))
        by circle_degree_rec C (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop))
      = circle_winding C (inverse (C .carrier) (C .base) (C .base) (C .loop))
        by circle_general_winding_base_value C (inverse (C .carrier) (C .base) (C .base) (C .loop))
      = (neg. zero. : Int) by circle_winding_inverse_loop C ∎

def circle_component_degree (C : CircleSignature) (f g : C .carrier → C .carrier)
  (h : Mere (Id (C .carrier → C .carrier) f g)) : Id Int (circle_map_degree C f) (circle_map_degree C g)
  ≔ mere_rec (Id (C .carrier → C .carrier) f g)
      (Id Int (circle_map_degree C f) (circle_map_degree C g))
      (int_set (circle_map_degree C f) (circle_map_degree C g))
      (map_path (C .carrier → C .carrier) Int (circle_map_degree C) f g) h

def circle_equal_degree_component (C : CircleSignature) (f g : C .carrier → C .carrier)
  (q : Id Int (circle_map_degree C f) (circle_map_degree C g))
  : Mere (Id (C .carrier → C .carrier) f g)
  ≔ trunc_map native_truncation (Id (C .carrier) (f (C .base)) (g (C .base)))
      (Id (C .carrier → C .carrier) f g)
      (p ↦ equiv_inverse_map (Id (C .carrier → C .carrier) f g)
        (Id (Σ (C .carrier) (_ ↦ Int)) (circle_mapping_coordinates C .map f) (circle_mapping_coordinates C .map g))
        (equivalence_on_paths (C .carrier → C .carrier) (Σ (C .carrier) (_ ↦ Int))
          (circle_mapping_coordinates C) f g) (p, q))
      (native_circle_connected C .snd (f (C .base)) (g (C .base)))

def circle_degree_component_equiv (C : CircleSignature) (f g : C .carrier → C .carrier)
  : Equiv (Mere (Id (C .carrier → C .carrier) f g)) (Id Int (circle_map_degree C f) (circle_map_degree C g))
  ≔ iff_equiv (Mere (Id (C .carrier → C .carrier) f g)) (Id Int (circle_map_degree C f) (circle_map_degree C g))
      (mere_isprop (Id (C .carrier → C .carrier) f g)) (int_set (circle_map_degree C f) (circle_map_degree C g))
      (circle_component_degree C f g) (circle_equal_degree_component C f g)

def circle_identity_reflection_different_components (C : CircleSignature)
  : Mere (Id (C .carrier → C .carrier) (identity (C .carrier)) (circle_reflection C)) → Empty
  ≔ h ↦ int_encode (pos. (suc. zero.)) (neg. zero.) (calc
      (pos. (suc. zero.) : Int) = circle_map_degree C (identity (C .carrier)) by circle_degree_identity C
      = circle_map_degree C (circle_reflection C)
        by circle_component_degree C (identity (C .carrier)) (circle_reflection C) h
      = (neg. zero. : Int) by circle_degree_reflection C ∎)
