export "80-circle-degree-action"

def positive_integer_multiplication_injective (m : Nat) (positive : BookLt zero. m)
  : PathReflecting Int Int (int_mul (pos. m))
  ≔ x y p ↦ integer_division_equal_pairs x y zero. zero. m positive positive (calc
      integer_division_value x zero. m = int_mul (pos. m) x by int_mul_comm x (pos. m)
      = int_mul (pos. m) y by p
      = integer_division_value y zero. m by int_mul_comm y (pos. m) ∎) .fst

def circle_degree_based_injective (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : PathReflecting (Id (C .carrier) (C .base) (C .base)) (Id (C .carrier) (C .base) (C .base))
      (circle_degree_based_action C m)
  ≔ p q h ↦ equivalence_injective (Id (C .carrier) (C .base) (C .base)) Int
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C)) p q
      (positive_integer_multiplication_injective m positive (circle_winding C p) (circle_winding C q) (calc
        int_mul (pos. m) (circle_winding C p) = circle_winding C (circle_degree_based_action C m p)
          by circle_degree_winding C m p
        = circle_winding C (circle_degree_based_action C m q) by refl (circle_winding C) h
        = int_mul (pos. m) (circle_winding C q) by circle_degree_winding C m q ∎))

def circle_degree_loops_injective (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : PathReflecting (Id (C .carrier) (C .base) (C .base))
      (Id (C .carrier) (circle_degree_map C m (C .base)) (circle_degree_map C m (C .base)))
      (map_path (C .carrier) (C .carrier) (circle_degree_map C m) (C .base) (C .base))
  ≔ p q h ↦ circle_degree_based_injective C m positive p q
      (refl (transport (C .carrier) (x ↦ Id (C .carrier) x x)
        (circle_degree_map C m (C .base)) (C .base) (circle_degree_boundary C m .fst)) h)

def injective_into_set_embedding (A B : Type) (f : A → B) (hb : isSet B) (hi : PathReflecting A B f)
  : IsEmbedding A B f
  ≔ b u v ↦ subtype_equal A (a ↦ Id B b (f a)) (a ↦ hb b (f a)) u v
      (hi (u .fst) (v .fst) (concat B (f (u .fst)) b (f (v .fst))
        (inverse B b (f (u .fst)) (u .snd)) (v .snd)))

def circle_degree_is_covering (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : IsCovering (C .carrier) (C .carrier) (circle_degree_map C m)
  ≔ b ↦ hlevel_two_to_set (BookFiber (C .carrier) (C .carrier) (circle_degree_map C m) b)
      (loop_fibers_to_fibers native_truncation (suc. zero.) (C .carrier) (C .carrier) (circle_degree_map C m)
        (native_circle_connected C) (C .base)
        (p ↦ prop_to_hlevel_one
          (BookFiber (Id (C .carrier) (C .base) (C .base))
            (Id (C .carrier) (circle_degree_map C m (C .base)) (circle_degree_map C m (C .base)))
            (map_path (C .carrier) (C .carrier) (circle_degree_map C m) (C .base) (C .base)) p)
          (injective_into_set_embedding (Id (C .carrier) (C .base) (C .base))
            (Id (C .carrier) (circle_degree_map C m (C .base)) (circle_degree_map C m (C .base)))
            (map_path (C .carrier) (C .carrier) (circle_degree_map C m) (C .base) (C .base))
            (circle_groupoid C (circle_degree_map C m (C .base)) (circle_degree_map C m (C .base)))
            (circle_degree_loops_injective C m positive) p)) b)

def circle_degree_cover (C : CircleSignature) (m : Nat) (positive : BookLt zero. m) : Coverings (C .carrier)
  ≔ (C .carrier, (circle_degree_map C m, circle_degree_is_covering C m positive))

{` cor:dgm-conncov, for every CircleSignature (instantiated at constructed_circle in module 250). `}
def circle_degree_connected_cover (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : ConnectedCoverings (C .carrier)
  ≔ (circle_degree_cover C m positive, native_circle_connected C)

def degree_winding_map (C : CircleSignature) (m : Nat) (p : Id (C .carrier) (C .base) (C .base)) : Int
  ≔ circle_winding C (circle_degree_based_action C m p)

def degree_winding_image (C : CircleSignature) (m : Nat) : Subtypes Int
  ≔ z ↦ (Mere (BookFiber (Id (C .carrier) (C .base) (C .base)) Int (degree_winding_map C m) z),
      mere_isprop (BookFiber (Id (C .carrier) (C .base) (C .base)) Int (degree_winding_map C m) z))

def degree_winding_multiple (C : CircleSignature) (m : Nat) (z : Int)
  : degree_winding_image C m z .fst → Multiples m z .fst
  ≔ trunc_map native_truncation (BookFiber (Id (C .carrier) (C .base) (C .base)) Int (degree_winding_map C m) z)
      (MultipleWitness m z)
      (w ↦ (circle_winding C (w .fst), calc
        z = degree_winding_map C m (w .fst) by w .snd
        = int_mul (pos. m) (circle_winding C (w .fst)) by circle_degree_winding C m (w .fst)
        = int_mul (circle_winding C (w .fst)) (pos. m) by int_mul_comm (pos. m) (circle_winding C (w .fst)) ∎))

def multiple_degree_winding (C : CircleSignature) (m : Nat) (z : Int)
  : Multiples m z .fst → degree_winding_image C m z .fst
  ≔ trunc_map native_truncation (MultipleWitness m z)
      (BookFiber (Id (C .carrier) (C .base) (C .base)) Int (degree_winding_map C m) z)
      (w ↦ (loop_power (C .carrier) (C .base) (C .loop) (w .fst), calc
        z = int_mul (w .fst) (pos. m) by w .snd
        = int_mul (pos. m) (w .fst) by int_mul_comm (w .fst) (pos. m)
        = int_mul (pos. m) (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (w .fst)))
          by refl (int_mul (pos. m)) (circle_winding_power C (w .fst))
        = degree_winding_map C m (loop_power (C .carrier) (C .base) (C .loop) (w .fst))
          by circle_degree_winding C m (loop_power (C .carrier) (C .base) (C .loop) (w .fst)) ∎))

def degree_winding_image_multiples (C : CircleSignature) (m : Nat)
  : Id (Subtypes Int) (degree_winding_image C m) (Multiples m)
  ≔ funext Int (_ ↦ PropTypes) (degree_winding_image C m) (Multiples m)
      (z ↦ proposition_extensionality (degree_winding_image C m z) (Multiples m z)
        (degree_winding_multiple C m z) (multiple_degree_winding C m z))
