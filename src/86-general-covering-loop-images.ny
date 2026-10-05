export "85-general-winding"

def circle_general_winding_conjugate (C : CircleSignature) (x y : C .carrier) (r : Id (C .carrier) x y)
  (p : Id (C .carrier) x x)
  : Id Int (circle_general_winding C y (loop_conjugate (C .carrier) x y r p)) (circle_general_winding C x p)
  ≔ concat Int (circle_general_winding C y (loop_conjugate (C .carrier) x y r p))
      (circle_general_winding C y (transport (C .carrier) (z ↦ Id (C .carrier) z z) x y r p))
      (circle_general_winding C x p)
      (inverse Int (circle_general_winding C y (transport (C .carrier) (z ↦ Id (C .carrier) z z) x y r p))
        (circle_general_winding C y (loop_conjugate (C .carrier) x y r p))
        (refl (circle_general_winding C y) (loop_transport_conjugate (C .carrier) x y r p)))
      (circle_general_winding_transport C x y r p)

def circle_general_winding_inverse (C : CircleSignature) (z : C .carrier) (p : Id (C .carrier) z z)
  : Id Int (circle_general_winding C z (inverse (C .carrier) z z p)) (int_neg (circle_general_winding C z p))
  ≔ int_neg_unique (circle_general_winding C z p) (circle_general_winding C z (inverse (C .carrier) z z p)) (calc
      int_add (circle_general_winding C z p) (circle_general_winding C z (inverse (C .carrier) z z p))
      = circle_general_winding C z (concat (C .carrier) z z z p (inverse (C .carrier) z z p))
        by circle_general_winding_composition C z p (inverse (C .carrier) z z p)
      = circle_general_winding C z (refl z)
        by refl (circle_general_winding C z) (concat_inverse_right (C .carrier) z z p)
      = int_zero by circle_general_winding_refl C z ∎)

def general_loop_winding (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst) (p : Id (t .fst) a a) : Int
  ≔ circle_general_winding C (t .snd a) (refl (t .snd) p)

def general_loop_image (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst) : Subtypes Int
  ≔ map_image_predicate (Id (t .fst) a a) Int (general_loop_winding C t a)

def general_based_loop_images (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst)
  (base : Id (C .carrier) (t .snd a) (C .base))
  : Id (Subtypes Int) (general_loop_image C t a) (based_loop_image C t a base)
  ≔ map_image_homotopy (Id (t .fst) a a) Int (general_loop_winding C t a) (based_loop_winding C t a base)
      (p ↦ circle_general_winding_based C (t .snd a) base (refl (t .snd) p))

{` lem:cycle-order-point-ap, image of the printed composite at every point.
   The winding function and this theorem require no connecting-path input.
   Connectedness is eliminated only into equality of subtypes, a proposition. `}
def covering_periods_general_image (C : CircleSignature) (c : ConnectedCoverings (C .carrier)) (a : c .fst .fst)
  : Id (Subtypes Int) (CyclePeriods (circle_connected_coverings_cycles C .map c))
      (general_loop_image C (forget_covering (C .carrier) (c .fst)) a)
  ≔ let t ≔ forget_covering (C .carrier) (c .fst) in
    let H ≔ CyclePeriods (circle_connected_coverings_cycles C .map c) in
    mere_rec (Id (C .carrier) (t .snd a) (C .base))
      (Id (Subtypes Int) H (general_loop_image C t a)) (subtypes_set Int H (general_loop_image C t a))
      (base ↦ concat (Subtypes Int) H (based_loop_image C t a base) (general_loop_image C t a)
        (covering_periods_based_image C c a base)
        (inverse (Subtypes Int) (general_loop_image C t a) (based_loop_image C t a base) (general_based_loop_images C t a base)))
      (native_circle_connected C .snd (t .snd a) (C .base))
