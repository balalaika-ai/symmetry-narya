export "1413-dimension-invariance"
export "1412-gram-schmidt-theorem"
export "500-gsets"

{` Chapter 14, def:OrthogonalGroup (geometry.tex 57-71). O(n) ≔ mkgroup OS_n,
   pointed at 𝕍ⁿ; OS_n is connected by thm:GramSchmidt (module 1412) and a
   groupoid by lem:InnerProductSpace1Type (module 1401). Its symmetries are
   the linear isometries of 𝕍ⁿ. The standard action of O(n) composed with
   the map B O(n) → (vector spaces) forgetting the inner product is the
   O(n)-set V ↦ V (underlying set Kⁿ); a symmetry given by an isometry φ acts
   by φ (by computation). Litmus: O(2) is not abelian (a reflection and the
   coordinate swap do not commute; uses 1 ≠ -1 in an ordered field). `}

def orthogonal_group_connected (K : EuclideanField) (n : Nat) : Connected (InnerProductSpaceDim K n)
  ≔ let A ≔ InnerProductSpaceDim K n in let a ≔ standard_inner_product_space_dim K n in
    let k : (x : A) → Mere (Id A a x)
      ≔ x ↦ mere_rec (Id A x a) (Mere (Id A a x)) (mere_isprop (Id A a x)) (p ↦ mere (Id A a x) (inverse A x a p))
          (gram_schmidt_theorem K n x) in
    (mere A a, x y ↦ merely_paths_compose native_truncation A a x y (k x) (k y))

def orthogonal_group_classifying (K : EuclideanField) (n : Nat) : PointedConnectedGroupoid
  ≔ (InnerProductSpaceDim K n, standard_inner_product_space_dim K n, orthogonal_group_connected K n,
     inner_product_space_dim_groupoid K n)

{` def:OrthogonalGroup. `}
def orthogonal_group (K : EuclideanField) (n : Nat) : Group ≔ mkgroup (orthogonal_group_classifying K n)

def orthogonal_group_classifying_type (K : EuclideanField) (n : Nat)
  : Id Type (BG (orthogonal_group K n) .carrier) (InnerProductSpaceDim K n)
  ≔ refl (InnerProductSpaceDim K n)

def orthogonal_group_shape (K : EuclideanField) (n : Nat)
  : Id (InnerProductSpaceDim K n) (shape (orthogonal_group K n)) (standard_inner_product_space_dim K n)
  ≔ refl (standard_inner_product_space_dim K n)

{` The symmetries of O(n) are the linear isometries of 𝕍ⁿ. `}
def orthogonal_usym_isometry_equiv (K : EuclideanField) (n : Nat)
  : Equiv (USym (orthogonal_group K n))
      (LinearIsometry K (standard_inner_product_space K n) (standard_inner_product_space K n))
  ≔ let E ≔ standard_inner_product_space_dim K n in
    compose_equiv (USym (orthogonal_group K n)) (Id (InnerProductSpace K) (E .fst) (E .fst))
      (LinearIsometry K (E .fst) (E .fst))
      (ip_space_dim_path_equiv K n E E) (ip_space_path_isometry_equiv K (E .fst) (E .fst))

def orthogonal_symmetry (K : EuclideanField) (n : Nat)
  (φ : LinearIsometry K (standard_inner_product_space K n) (standard_inner_product_space K n))
  : USym (orthogonal_group K n)
  ≔ ip_space_dim_path_from_isometry K n (standard_inner_product_space_dim K n) (standard_inner_product_space_dim K n) φ

{` The projection B O(n) → (vector spaces) forgetting the inner product,
   and the resulting action of O(n) on Kⁿ. `}
def orthogonal_forget_inner_product (K : EuclideanField) (n : Nat)
  : BG (orthogonal_group K n) .carrier → VectorSpace (K .field)
  ≔ V ↦ V .fst .space

def orthogonal_standard_gset (K : EuclideanField) (n : Nat) : GSet (orthogonal_group K n)
  ≔ V ↦ (V .fst .space .carrier, module_set (K .field .fst) (V .fst .space))

def orthogonal_standard_gset_underlying (K : EuclideanField) (n : Nat)
  : Id Type (gset_underlying (orthogonal_group K n) (orthogonal_standard_gset K n)) (Fin n → ef_carrier K)
  ≔ refl (Fin n → ef_carrier K)

def orthogonal_symmetry_act (K : EuclideanField) (n : Nat)
  (φ : LinearIsometry K (standard_inner_product_space K n) (standard_inner_product_space K n))
  (v : Fin n → ef_carrier K)
  : Id (Fin n → ef_carrier K)
      (gset_usym_act (orthogonal_group K n) (orthogonal_standard_gset K n) (orthogonal_symmetry K n φ) v)
      (φ .fst .fst .map v)
  ≔ refl (φ .fst .fst .map v)

{` Litmus: O(2) is not abelian. Vectors of K² are functions on Fin 2;
   fin_two_first, fin_two_second are the two indices (module 1315). `}
def fin_two_funext (S : Type) (f g : Fin 2 → S) (h0 : Id S (f fin_two_first) (g fin_two_first))
  (h1 : Id S (f fin_two_second) (g fin_two_second)) : Id (Fin 2 → S) f g
  ≔ funext (Fin 2) (_ ↦ S) f g
      (t ↦ match t [
       | inl. u ↦ match u [ inl. e ↦ match e [ ] | inr. star. ↦ h0 ]
       | inr. star. ↦ h1 ])

def ring_zero_add_swap (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .add (R .add (R .zero) a) b) (R .add (R .add (R .zero) b) a)
  ≔ let S ≔ R .carrier in
    calc
      R .add (R .add (R .zero) a) b = R .add a b by refl ((y ↦ R .add y b) : S → S) (R .add_laws .unit_left a)
      = R .add b a by ring_add_comm R a b
      = R .add (R .add (R .zero) b) a
        by refl ((y ↦ R .add y a) : S → S) (inverse S (R .add (R .zero) b) b (R .add_laws .unit_left b)) ∎

def coordinate_swap (S : Type) (x : Fin 2 → S) : Fin 2 → S
  ≔ [ inl. _ ↦ x fin_two_second | inr. _ ↦ x fin_two_first ]

def coordinate_swap_isometry (K : EuclideanField)
  : LinearIsometry K (standard_inner_product_space K 2) (standard_inner_product_space K 2)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let V ≔ standard_module R 2 in
    let sw ≔ coordinate_swap S in
    ((quasi_inverse_equiv (Fin 2 → S) (Fin 2 → S) sw sw
        (x ↦ fin_two_funext S (sw (sw x)) x (refl (x fin_two_first)) (refl (x fin_two_second)))
        (x ↦ fin_two_funext S (sw (sw x)) x (refl (x fin_two_first)) (refl (x fin_two_second))),
      (x y ↦ fin_two_funext S (sw (V .add x y)) (V .add (sw x) (sw y))
         (refl (R .add (x fin_two_second) (y fin_two_second))) (refl (R .add (x fin_two_first) (y fin_two_first))),
       a x ↦ fin_two_funext S (sw (V .smul a x)) (V .smul a (sw x))
         (refl (R .mul a (x fin_two_second))) (refl (R .mul a (x fin_two_first))))),
     x y ↦ ring_zero_add_swap R (R .mul (x fin_two_first) (y fin_two_first)) (R .mul (x fin_two_second) (y fin_two_second)))

def first_coordinate_negation (S : Type) (neg : S → S) (x : Fin 2 → S) : Fin 2 → S
  ≔ [ inl. _ ↦ neg (x fin_two_first) | inr. _ ↦ x fin_two_second ]

def ring_neg_neg_mul (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .mul a b) (R .mul (R .neg a) (R .neg b))
  ≔ let S ≔ R .carrier in let G ≔ ring_additive_group R in
    inverse S (R .mul (R .neg a) (R .neg b)) (R .mul a b)
      (calc
         R .mul (R .neg a) (R .neg b) = R .neg (R .mul a (R .neg b)) by ring_mul_neg_left R a (R .neg b)
         = R .neg (R .neg (R .mul a b)) by refl (R .neg) (ring_mul_neg_right R a b)
         = R .mul a b by ag_inv_inv G (R .mul a b) ∎)

def first_coordinate_negation_isometry (K : EuclideanField)
  : LinearIsometry K (standard_inner_product_space K 2) (standard_inner_product_space K 2)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let V ≔ standard_module R 2 in
    let G ≔ ring_additive_group R in
    let ng ≔ first_coordinate_negation S (R .neg) in
    ((quasi_inverse_equiv (Fin 2 → S) (Fin 2 → S) ng ng
        (x ↦ fin_two_funext S (ng (ng x)) x (ag_inv_inv G (x fin_two_first)) (refl (x fin_two_second)))
        (x ↦ fin_two_funext S (ng (ng x)) x (ag_inv_inv G (x fin_two_first)) (refl (x fin_two_second))),
      (x y ↦ fin_two_funext S (ng (V .add x y)) (V .add (ng x) (ng y))
         (concat S (R .neg (R .add (x fin_two_first) (y fin_two_first)))
            (R .add (R .neg (y fin_two_first)) (R .neg (x fin_two_first)))
            (R .add (R .neg (x fin_two_first)) (R .neg (y fin_two_first)))
            (ag_inv_mul G (x fin_two_first) (y fin_two_first))
            (ring_add_comm R (R .neg (y fin_two_first)) (R .neg (x fin_two_first))))
         (refl (R .add (x fin_two_second) (y fin_two_second))),
       a x ↦ fin_two_funext S (ng (V .smul a x)) (V .smul a (ng x))
         (inverse S (R .mul a (R .neg (x fin_two_first))) (R .neg (R .mul a (x fin_two_first)))
            (ring_mul_neg_right R a (x fin_two_first)))
         (refl (R .mul a (x fin_two_second))))),
     x y ↦ refl ((t ↦ R .add (R .add (R .zero) t) (R .mul (x fin_two_second) (y fin_two_second))) : S → S)
       (ring_neg_neg_mul R (x fin_two_first) (y fin_two_first)))

{` In an ordered field -1 ≠ 1 (else 1 + 1 = 0). `}
def ef_neg_one_ne_one (K : EuclideanField)
  (p : Id (ef_carrier K) (K .field .fst .neg (K .field .fst .one)) (K .field .fst .one)) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let o ≔ R .one in
    ef_nat_succ_nonzero K 1
      (calc
         R .add (R .add (R .zero) o) o = R .add o o by refl ((y ↦ R .add y o) : S → S) (R .add_laws .unit_left o)
         = R .add o (R .neg o) by refl (R .add o) (inverse S (R .neg o) o p)
         = R .zero by R .add_laws .inv_right o ∎)

def orthogonal_two_litmus_eval (S : Type) (u v : Fin 2 → S) (q : Id (Fin 2 → S) u v)
  : Id S (u fin_two_second) (v fin_two_second)
  ≔ refl ((y ↦ y fin_two_second) : (Fin 2 → S) → S) q

def orthogonal_two_not_abelian (K : EuclideanField) (h : IsAbelian (orthogonal_group K 2)) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let G ≔ orthogonal_group K 2 in let X ≔ orthogonal_standard_gset K 2 in
    let sw ≔ orthogonal_symmetry K 2 (coordinate_swap_isometry K) in
    let ng ≔ orthogonal_symmetry K 2 (first_coordinate_negation_isometry K) in
    let e0 : Fin 2 → S ≔ [ inl. _ ↦ R .one | inr. _ ↦ R .zero ] in
    let act ≔ gset_usym_act G X in
    let F ≔ Fin 2 → S in
    let swf ≔ coordinate_swap S in let ngf ≔ first_coordinate_negation S (R .neg) in
    let q : Id F (act sw (act ng e0)) (act ng (act sw e0))
      ≔ calc
          act sw (act ng e0) = act (usym_mul G sw ng) e0
            by inverse F (act (usym_mul G sw ng) e0) (act sw (act ng e0)) (gset_act_mul G X sw ng e0)
          = act (usym_mul G ng sw) e0 by refl ((g ↦ act g e0) : USym G → F) (h sw ng)
          = act ng (act sw e0) by gset_act_mul G X ng sw e0 ∎ in
    let l : Id F (act sw (act ng e0)) (swf (ngf e0))
      ≔ concat F (act sw (act ng e0)) (swf (act ng e0)) (swf (ngf e0))
          (orthogonal_symmetry_act K 2 (coordinate_swap_isometry K) (act ng e0))
          (refl swf (orthogonal_symmetry_act K 2 (first_coordinate_negation_isometry K) e0)) in
    let r : Id F (act ng (act sw e0)) (ngf (swf e0))
      ≔ concat F (act ng (act sw e0)) (ngf (act sw e0)) (ngf (swf e0))
          (orthogonal_symmetry_act K 2 (first_coordinate_negation_isometry K) (act sw e0))
          (refl ngf (orthogonal_symmetry_act K 2 (coordinate_swap_isometry K) e0)) in
    let q' : Id F (swf (ngf e0)) (ngf (swf e0))
      ≔ concat F (swf (ngf e0)) (act sw (act ng e0)) (ngf (swf e0)) (inverse F (act sw (act ng e0)) (swf (ngf e0)) l)
          (concat F (act sw (act ng e0)) (act ng (act sw e0)) (ngf (swf e0)) q r) in
    ef_neg_one_ne_one K (orthogonal_two_litmus_eval S (swf (ngf e0)) (ngf (swf e0)) q')
