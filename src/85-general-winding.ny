export "84-book-covering-classification"

def loop_conjugate (A : Type) (x y : A) (r : Id A x y) (p : Id A x x) : Id A y y
  ≔ concat A y x y (inverse A x y r) (concat A x x y p r)

def loop_transport_conjugate (A : Type) (x y : A) (r : Id A x y) (p : Id A x x)
  : Id (Id A y y) (transport A (z ↦ Id A z z) x y r p) (loop_conjugate A x y r p)
  ≔ J A x (y r ↦ Id (Id A y y) (transport A (z ↦ Id A z z) x y r p) (loop_conjugate A x y r p))
      (calc
        transport A (z ↦ Id A z z) x x (refl x) p = p by transport_refl A (z ↦ Id A z z) x p
        = concat A x x x (refl x) p by concat_1p A x x p
        = concat A x x x (inverse A x x (refl x)) p
          by refl ((q ↦ concat A x x x q p) : Id A x x → Id A x x) (inverse_refl A x)
        = loop_conjugate A x x (refl x) p
          by refl (concat A x x x (inverse A x x (refl x))) (concat_p1 A x x p) ∎) y r

def dependent_domain_pathover (A : Type) (B : A → Type) (D : Type) (x y : A) (r : Id A x y)
  (f : B x → D) (g : B y → D) (h : (b : B x) → Id D (f b) (g (transport A B x y r b)))
  : Id (z ↦ B z → D) r f g
  ≔ J A x
      (y r ↦ (g : B y → D) → ((b : B x) → Id D (f b) (g (transport A B x y r b)))
        → Id (z ↦ B z → D) r f g)
      (g h ↦ funext (B x) (_ ↦ D) f g (b ↦ concat D (f b) (g (transport A B x x (refl x) b)) (g b)
        (h b) (refl g (transport_refl A B x b)))) y r g h

def circle_winding_conjugate (C : CircleSignature) (q p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (loop_conjugate (C .carrier) (C .base) (C .base) q p)) (circle_winding C p)
  ≔ calc
      circle_winding C (loop_conjugate (C .carrier) (C .base) (C .base) q p)
      = int_add (circle_winding C (inverse (C .carrier) (C .base) (C .base) q))
          (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q))
        by circle_winding_composition C (inverse (C .carrier) (C .base) (C .base) q)
          (concat (C .carrier) (C .base) (C .base) (C .base) p q)
      = int_add (int_neg (circle_winding C q)) (int_add (circle_winding C p) (circle_winding C q))
        by refl int_add (circle_winding_inverse C q) (circle_winding_composition C p q)
      = int_add (int_neg (circle_winding C q)) (int_add (circle_winding C q) (circle_winding C p))
        by refl (int_add (int_neg (circle_winding C q))) (int_add_comm (circle_winding C p) (circle_winding C q))
      = circle_winding C p by int_translate_inverse (circle_winding C q) (circle_winding C p) ∎

def WindingFunctions (C : CircleSignature) (z : C .carrier) : Type ≔ Id (C .carrier) z z → Int

def winding_function_boundary (C : CircleSignature)
  : CircleBoundary (C .carrier) (C .base) (C .loop) (WindingFunctions C)
  ≔ (circle_winding C,
      dependent_domain_pathover (C .carrier) (z ↦ Id (C .carrier) z z) Int (C .base) (C .base) (C .loop)
        (circle_winding C) (circle_winding C) (p ↦ inverse Int
          (circle_winding C (transport (C .carrier) (z ↦ Id (C .carrier) z z) (C .base) (C .base) (C .loop) p))
          (circle_winding C p) (calc
            circle_winding C (transport (C .carrier) (z ↦ Id (C .carrier) z z) (C .base) (C .base) (C .loop) p)
            = circle_winding C (loop_conjugate (C .carrier) (C .base) (C .base) (C .loop) p)
              by refl (circle_winding C) (loop_transport_conjugate (C .carrier) (C .base) (C .base) (C .loop) p)
            = circle_winding C p by circle_winding_conjugate C (C .loop) p ∎)))

{` xca:general-winding, first part: the function is constructed by dependent
   circle induction.  No connecting path is supplied or selected. `}
def circle_general_winding (C : CircleSignature) (z : C .carrier) : WindingFunctions C z
  ≔ C .induction (WindingFunctions C) (winding_function_boundary C) .fst z

def circle_general_winding_base (C : CircleSignature)
  : Id (WindingFunctions C (C .base)) (circle_general_winding C (C .base)) (circle_winding C)
  ≔ C .induction (WindingFunctions C) (winding_function_boundary C) .snd .fst

def circle_general_winding_base_value (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_general_winding C (C .base) p) (circle_winding C p)
  ≔ refl ((f ↦ f p) : WindingFunctions C (C .base) → Int) (circle_general_winding_base C)

def circle_general_winding_equiv (C : CircleSignature) (z : C .carrier)
  : Equiv (Id (C .carrier) z z) Int
  ≔ (circle_general_winding C z,
      circle_ind_prop C (z ↦ isEquiv (Id (C .carrier) z z) Int (circle_general_winding C z))
        (z ↦ isequiv_isprop (Id (C .carrier) z z) Int (circle_general_winding C z))
        (equiv_change_map (Id (C .carrier) (C .base) (C .base)) Int
          (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
          (circle_general_winding C (C .base))
          (p ↦ inverse Int (circle_general_winding C (C .base) p) (circle_winding C p) (circle_general_winding_base_value C p)) .equiv) z)

def dependent_function_transport (A : Type) (B : A → Type) (D : Type) (f : (x : A) → B x → D)
  (x y : A) (r : Id A x y) (b : B x) : Id D (f y (transport A B x y r b)) (f x b)
  ≔ J A x (y r ↦ Id D (f y (transport A B x y r b)) (f x b))
      (refl (f x) (transport_refl A B x b)) y r

def circle_general_winding_transport (C : CircleSignature) (x y : C .carrier) (r : Id (C .carrier) x y)
  (p : Id (C .carrier) x x)
  : Id Int (circle_general_winding C y (transport (C .carrier) (z ↦ Id (C .carrier) z z) x y r p))
      (circle_general_winding C x p)
  ≔ dependent_function_transport (C .carrier) (z ↦ Id (C .carrier) z z) Int (circle_general_winding C) x y r p

def circle_general_winding_based (C : CircleSignature) (z : C .carrier) (r : Id (C .carrier) z (C .base))
  (p : Id (C .carrier) z z)
  : Id Int (circle_general_winding C z p)
      (circle_winding C (transport (C .carrier) (x ↦ Id (C .carrier) x x) z (C .base) r p))
  ≔ concat Int (circle_general_winding C z p)
      (circle_general_winding C (C .base) (transport (C .carrier) (x ↦ Id (C .carrier) x x) z (C .base) r p))
      (circle_winding C (transport (C .carrier) (x ↦ Id (C .carrier) x x) z (C .base) r p))
      (inverse Int (circle_general_winding C (C .base) (transport (C .carrier) (x ↦ Id (C .carrier) x x) z (C .base) r p))
        (circle_general_winding C z p) (circle_general_winding_transport C z (C .base) r p))
      (circle_general_winding_base_value C (transport (C .carrier) (x ↦ Id (C .carrier) x x) z (C .base) r p))

def circle_general_winding_refl (C : CircleSignature) (z : C .carrier)
  : Id Int (circle_general_winding C z (refl z)) int_zero
  ≔ circle_ind_prop C (z ↦ Id Int (circle_general_winding C z (refl z)) int_zero)
      (z ↦ int_set (circle_general_winding C z (refl z)) int_zero)
      (concat Int (circle_general_winding C (C .base) (refl (C .base))) (circle_winding C (refl (C .base))) int_zero
        (circle_general_winding_base_value C (refl (C .base))) (circle_winding_refl C)) z

def circle_general_winding_composition (C : CircleSignature) (z : C .carrier)
  (p q : Id (C .carrier) z z)
  : Id Int (circle_general_winding C z (concat (C .carrier) z z z p q))
      (int_add (circle_general_winding C z p) (circle_general_winding C z q))
  ≔ circle_ind_prop C
      (z ↦ (p q : Id (C .carrier) z z) → Id Int (circle_general_winding C z (concat (C .carrier) z z z p q))
        (int_add (circle_general_winding C z p) (circle_general_winding C z q)))
      (z ↦ pi_prop (Id (C .carrier) z z)
        (p ↦ (q : Id (C .carrier) z z) → Id Int (circle_general_winding C z (concat (C .carrier) z z z p q))
          (int_add (circle_general_winding C z p) (circle_general_winding C z q)))
        (p ↦ pi_prop (Id (C .carrier) z z)
          (q ↦ Id Int (circle_general_winding C z (concat (C .carrier) z z z p q))
            (int_add (circle_general_winding C z p) (circle_general_winding C z q)))
          (q ↦ int_set (circle_general_winding C z (concat (C .carrier) z z z p q))
            (int_add (circle_general_winding C z p) (circle_general_winding C z q)))))
      (p q ↦ calc
        circle_general_winding C (C .base) (concat (C .carrier) (C .base) (C .base) (C .base) p q)
        = circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q)
          by circle_general_winding_base_value C (concat (C .carrier) (C .base) (C .base) (C .base) p q)
        = int_add (circle_winding C p) (circle_winding C q) by circle_winding_composition C p q
        = int_add (circle_general_winding C (C .base) p) (circle_general_winding C (C .base) q)
          by refl int_add (circle_general_winding_base_value C p) (circle_general_winding_base_value C q) ∎) z p q
