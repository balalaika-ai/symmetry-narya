export "808-dihedral-group-cardinality"
export "803-semidirect-kernel"
export "417-cyclic-groups"
export "420-group-products-abelian"

{` Chapter 8, xca (congp.tex:196): the quaternion group Q_8 (def:Dinfty-Q,
   chapter 4's quaternion_group = Aut_Bicyc(Fin 8, a, b)) and the dihedral
   group D_4 = Σ_2 ⋉ C̃_4 are not isomorphic.

   Following the hint (elements of order 2): Q_8 has at most one symmetry g ≠ e
   with g·g = e (AtMostOneInvolution), computed through the normal quaternion
   bicycle (evaluation at 0 is a bijection, symmetries commute with the words
   reaching each point); D_4 has two different ones, s(σ) and j(x) with σ the swap
   of Σ_2 and x the element of order 2 of C_4. The property is transported along
   an identification of groups, so no group isomorphism Q_8 ≅ D_4 exists. `}

def AtMostOneInvolution (G : Group) : Type
  ≔ (g g' : USym G) → Not (Id (USym G) g (usym_unit G)) → Not (Id (USym G) g' (usym_unit G))
      → Id (USym G) (usym_mul G g g) (usym_unit G) → Id (USym G) (usym_mul G g' g') (usym_unit G)
      → Id (USym G) g g'

{` Quaternion side. `}
def quaternion_zero : Fin eight ≔ inr. star.

def quaternion_four : Fin eight ≔ inl. (inl. (inl. (inl. (inr. star.))))

def quaternion_eval (g : USym quaternion_group) : Fin eight
  ≔ bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst) quaternion_zero

def quaternion_zero_code : Fin eight → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def quaternion_not_zero (z : Fin eight) (c : quaternion_zero_code z → Empty) (p : Id (Fin eight) z quaternion_zero) : Empty
  ≔ c (transport (Fin eight) quaternion_zero_code quaternion_zero z (inverse (Fin eight) z quaternion_zero p) star.)

{` If ⟦w_y⟧(y) = 0 for the word w_y from 0 to y, then y = 0 or y = 4
   (eight computations). `}
def quaternion_square_value (y : Fin eight) : Fin eight
  ≔ bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (quaternion_word_from_zero y .fst) .map y

def quaternion_square_cases (y : Fin eight) (e : Id (Fin eight) (quaternion_square_value y) quaternion_zero)
  : Sum (Id (Fin eight) y quaternion_zero) (Id (Fin eight) y quaternion_four)
  ≔ match y [
  | inr. star. ↦ inl. (refl quaternion_zero)
  | inl. (inr. star.) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inr. star.))) (v ↦ v) e []
  | inl. (inl. (inr. star.)) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inl. (inr. star.)))) (v ↦ v) e []
  | inl. (inl. (inl. (inr. star.))) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inl. (inl. (inr. star.))))) (v ↦ v) e []
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inr. (refl quaternion_four)
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) (v ↦ v) e []
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) (v ↦ v) e []
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ match quaternion_not_zero (quaternion_square_value (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) (v ↦ v) e []
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]

def quaternion_eval_mul (g : USym quaternion_group)
  : Id (Fin eight) (quaternion_eval (usym_mul quaternion_group g g))
      (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst) (quaternion_eval g))
  ≔ concat (Fin eight) (quaternion_eval (usym_mul quaternion_group g g))
      (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle
        (concat Bicycles quaternion_bicycle quaternion_bicycle quaternion_bicycle (g .fst) (g .fst)) quaternion_zero)
      (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst) (quaternion_eval g))
      (refl ((p ↦ bicycle_path_evaluate quaternion_bicycle quaternion_bicycle p quaternion_zero)
             : Id Bicycles quaternion_bicycle quaternion_bicycle → Fin eight)
        (map_path_concat (NativeComponent Bicycles quaternion_bicycle) Bicycles (u ↦ u .fst)
          (component_point Bicycles quaternion_bicycle) (component_point Bicycles quaternion_bicycle)
          (component_point Bicycles quaternion_bicycle) g g))
      (bicycle_path_evaluate_concat quaternion_bicycle quaternion_bicycle quaternion_bicycle (g .fst) (g .fst) quaternion_zero)

def quaternion_eval_unit : Id (Fin eight) (quaternion_eval (usym_unit quaternion_group)) quaternion_zero
  ≔ bicycle_path_evaluate_refl quaternion_bicycle quaternion_zero

def quaternion_eval_injective (g g' : USym quaternion_group) (p : Id (Fin eight) (quaternion_eval g) (quaternion_eval g'))
  : Id (USym quaternion_group) g g'
  ≔ equivalence_injective (USym quaternion_group) (Fin eight) quaternion_usym_equiv g g' p

{` An involution evaluates to 0 or 4. `}
def quaternion_involution_value (g : USym quaternion_group)
  (h : Id (USym quaternion_group) (usym_mul quaternion_group g g) (usym_unit quaternion_group))
  : Sum (Id (Fin eight) (quaternion_eval g) quaternion_zero) (Id (Fin eight) (quaternion_eval g) quaternion_four)
  ≔ let y : Fin eight ≔ quaternion_eval g in
    let w : BicycleWordFrom (Fin eight) quaternion_a_equiv quaternion_b_equiv quaternion_zero y ≔ quaternion_word_from_zero y in
    quaternion_square_cases y
      (calc
        quaternion_square_value y
          = bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst)
              (bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (w .fst) .map quaternion_zero)
          by inverse (Fin eight) (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst)
                (bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (w .fst) .map quaternion_zero))
              (bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (w .fst) .map y)
              (bicycle_path_evaluate_meaning quaternion_bicycle quaternion_bicycle (g .fst) (w .fst) quaternion_zero)
        = bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst) y
          by refl (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst))
               (inverse (Fin eight) y (bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (w .fst) .map quaternion_zero)
                 (w .snd))
        = quaternion_eval (usym_mul quaternion_group g g)
          by inverse (Fin eight) (quaternion_eval (usym_mul quaternion_group g g))
               (bicycle_path_evaluate quaternion_bicycle quaternion_bicycle (g .fst) y) (quaternion_eval_mul g)
        = quaternion_eval (usym_unit quaternion_group) by refl quaternion_eval h
        = quaternion_zero by quaternion_eval_unit ∎)

def quaternion_nontrivial_involution_value (g : USym quaternion_group)
  (n : Not (Id (USym quaternion_group) g (usym_unit quaternion_group)))
  (h : Id (USym quaternion_group) (usym_mul quaternion_group g g) (usym_unit quaternion_group))
  : Id (Fin eight) (quaternion_eval g) quaternion_four
  ≔ match quaternion_involution_value g h [
  | inl. p ↦ match n (quaternion_eval_injective g (usym_unit quaternion_group)
        (concat (Fin eight) (quaternion_eval g) quaternion_zero (quaternion_eval (usym_unit quaternion_group)) p
          (inverse (Fin eight) (quaternion_eval (usym_unit quaternion_group)) quaternion_zero quaternion_eval_unit))) []
  | inr. q ↦ q ]

def quaternion_at_most_one_involution : AtMostOneInvolution quaternion_group
  ≔ g g' n n' h h' ↦ quaternion_eval_injective g g'
      (concat (Fin eight) (quaternion_eval g) quaternion_four (quaternion_eval g')
        (quaternion_nontrivial_involution_value g n h)
        (inverse (Fin eight) (quaternion_eval g') quaternion_four (quaternion_nontrivial_involution_value g' n' h')))

{` Dihedral side. `}
def dihedral_four : Nat ≔ suc. three

def dihedral_four_group : Group ≔ generalized_dihedral_group (principal_order dihedral_four)

def dihedral_four_action : TwoElementSets → Group ≔ dihedral_order_action (principal_order dihedral_four)

def InvolutionWitness (G : Group) : Type
  ≔ Σ (USym G) (x ↦ Product (Not (Id (USym G) x (usym_unit G))) (Id (USym G) (usym_mul G x x) (usym_unit G)))

def dihedral_hom_involution (G K : Group) (f : GroupHom G K) (x : USym G)
  (h : Id (USym G) (usym_mul G x x) (usym_unit G))
  : Id (USym K) (usym_mul K (usym_hom G K f x) (usym_hom G K f x)) (usym_unit K)
  ≔ calc
      usym_mul K (usym_hom G K f x) (usym_hom G K f x) = usym_hom G K f (usym_mul G x x)
        by inverse (USym K) (usym_hom G K f (usym_mul G x x)) (usym_mul K (usym_hom G K f x) (usym_hom G K f x))
             (usym_hom_mul G K f x x)
      = usym_hom G K f (usym_unit G) by refl (usym_hom G K f) h
      = usym_unit K by usym_hom_unit G K f ∎

def dihedral_four_section (σ : USym (symmetric_group two)) : USym dihedral_four_group
  ≔ usym_hom (symmetric_group two) dihedral_four_group (semidirect_section (symmetric_group two) dihedral_four_action) σ

def dihedral_four_inclusion (x : USym (dihedral_four_action (shape (symmetric_group two)))) : USym dihedral_four_group
  ≔ usym_hom (dihedral_four_action (shape (symmetric_group two))) dihedral_four_group
      (semidirect_inclusion (symmetric_group two) dihedral_four_action) x

def dihedral_four_project (e : USym dihedral_four_group) : USym (symmetric_group two)
  ≔ usym_hom dihedral_four_group (symmetric_group two) (semidirect_projection (symmetric_group two) dihedral_four_action) e

def dihedral_four_project_inclusion (x : USym (dihedral_four_action (shape (symmetric_group two))))
  : Id (USym (symmetric_group two)) (dihedral_four_project (dihedral_four_inclusion x)) (usym_unit (symmetric_group two))
  ≔ concat (USym (symmetric_group two)) (dihedral_four_project (dihedral_four_inclusion x))
      (semidirect_usym_pair (symmetric_group two) dihedral_four_action (dihedral_four_inclusion x) .fst)
      (usym_unit (symmetric_group two))
      (semidirect_usym_projection (symmetric_group two) dihedral_four_action (dihedral_four_inclusion x))
      (refl ((u ↦ u .fst) : Product (USym (symmetric_group two)) (USym (dihedral_four_action (shape (symmetric_group two))))
              → USym (symmetric_group two))
        (semidirect_usym_pair_inclusion (symmetric_group two) dihedral_four_action x))

def dihedral_four_inclusion_injective (x : USym (dihedral_four_action (shape (symmetric_group two))))
  (p : Id (USym dihedral_four_group) (dihedral_four_inclusion x) (usym_unit dihedral_four_group))
  : Id (USym (dihedral_four_action (shape (symmetric_group two)))) x (usym_unit (dihedral_four_action (shape (symmetric_group two))))
  ≔ let K : Group ≔ dihedral_four_action (shape (symmetric_group two)) in
    let j : GroupHom K dihedral_four_group ≔ semidirect_inclusion (symmetric_group two) dihedral_four_action in
    refl ((u ↦ u .fst) : BookFiber (USym K) (USym dihedral_four_group) (usym_hom K dihedral_four_group j)
                           (usym_hom K dihedral_four_group j (usym_unit K)) → USym K)
      (semidirect_inclusion_mono (symmetric_group two) dihedral_four_action (usym_hom K dihedral_four_group j (usym_unit K))
        (x, concat (USym dihedral_four_group) (usym_hom K dihedral_four_group j (usym_unit K)) (usym_unit dihedral_four_group)
              (usym_hom K dihedral_four_group j x)
              (usym_hom_unit K dihedral_four_group j)
              (inverse (USym dihedral_four_group) (usym_hom K dihedral_four_group j x) (usym_unit dihedral_four_group) p))
        (usym_unit K, refl (usym_hom K dihedral_four_group j (usym_unit K))))

def dihedral_four_two_involutions (w : InvolutionWitness (dihedral_four_action (shape (symmetric_group two))))
  (a : AtMostOneInvolution dihedral_four_group) : Empty
  ≔ let σ : USym (symmetric_group two) ≔ sigma2_swap in
    let i1 : USym dihedral_four_group ≔ dihedral_four_section σ in
    let i2 : USym dihedral_four_group ≔ dihedral_four_inclusion (w .fst) in
    let sec : Id (USym (symmetric_group two)) (dihedral_four_project i1) σ
      ≔ semidirect_projection_section_usym (symmetric_group two) dihedral_four_action σ in
    let i1_ne : Not (Id (USym dihedral_four_group) i1 (usym_unit dihedral_four_group))
      ≔ p ↦ sigma2_swap_nontrivial
          (calc σ = dihedral_four_project i1 by inverse (USym (symmetric_group two)) (dihedral_four_project i1) σ sec
             = dihedral_four_project (usym_unit dihedral_four_group) by refl dihedral_four_project p
             = usym_unit (symmetric_group two)
               by usym_hom_unit dihedral_four_group (symmetric_group two)
                    (semidirect_projection (symmetric_group two) dihedral_four_action) ∎) in
    let i2_ne : Not (Id (USym dihedral_four_group) i2 (usym_unit dihedral_four_group))
      ≔ p ↦ w .snd .fst (dihedral_four_inclusion_injective (w .fst) p) in
    let i1_sq : Id (USym dihedral_four_group) (usym_mul dihedral_four_group i1 i1) (usym_unit dihedral_four_group)
      ≔ dihedral_hom_involution (symmetric_group two) dihedral_four_group
          (semidirect_section (symmetric_group two) dihedral_four_action) σ (sigma2_exponent_two σ) in
    let i2_sq : Id (USym dihedral_four_group) (usym_mul dihedral_four_group i2 i2) (usym_unit dihedral_four_group)
      ≔ dihedral_hom_involution (dihedral_four_action (shape (symmetric_group two))) dihedral_four_group
          (semidirect_inclusion (symmetric_group two) dihedral_four_action) (w .fst) (w .snd .snd) in
    sigma2_swap_nontrivial
      (calc σ = dihedral_four_project i1 by inverse (USym (symmetric_group two)) (dihedral_four_project i1) σ sec
         = dihedral_four_project i2 by refl dihedral_four_project (a i1 i2 i1_ne i2_ne i1_sq i2_sq)
         = usym_unit (symmetric_group two) by dihedral_four_project_inclusion (w .fst) ∎)

{` C_4 has an element of order 2 (evaluation 2 in Z/4). `}
def dihedral_four_remainder_two : Remainder dihedral_four ≔ remainder_at three two star.

def cyclic_four_involution : InvolutionWitness (cyclic_group dihedral_four)
  ≔ let x : USym (cyclic_group dihedral_four)
      ≔ equiv_inverse_map (USym (cyclic_group dihedral_four)) (Remainder dihedral_four) (cyclic_group_eval_equiv three)
          dihedral_four_remainder_two in
    let ev2 : Id (Remainder dihedral_four) (cyclic_group_eval three x) dihedral_four_remainder_two
      ≔ equiv_counit (USym (cyclic_group dihedral_four)) (Remainder dihedral_four) (cyclic_group_eval_equiv three)
          dihedral_four_remainder_two in
    (x,
     (p ↦ nat_encode two zero.
        (refl ((r ↦ r .fst) : Remainder dihedral_four → Nat)
          (calc dihedral_four_remainder_two = cyclic_group_eval three x
                  by inverse (Remainder dihedral_four) (cyclic_group_eval three x) dihedral_four_remainder_two ev2
             = cyclic_group_eval three (usym_unit (cyclic_group dihedral_four)) by refl (cyclic_group_eval three) p
             = modular_zero three by cyclic_group_eval_unit three ∎)),
      equivalence_injective (USym (cyclic_group dihedral_four)) (Remainder dihedral_four) (cyclic_group_eval_equiv three)
        (usym_mul (cyclic_group dihedral_four) x x) (usym_unit (cyclic_group dihedral_four))
        (calc cyclic_group_eval three (usym_mul (cyclic_group dihedral_four) x x)
                = modular_add three (cyclic_group_eval three x) (cyclic_group_eval three x)
                by cyclic_group_eval_mul three x x
           = modular_add three dihedral_four_remainder_two dihedral_four_remainder_two
             by refl ((r ↦ modular_add three r r) : Remainder dihedral_four → Remainder dihedral_four) ev2
           = modular_zero three
             by remainder_equal dihedral_four (modular_add three dihedral_four_remainder_two dihedral_four_remainder_two)
                  (modular_zero three) (refl (zero. : Nat))
           = cyclic_group_eval three (usym_unit (cyclic_group dihedral_four))
             by inverse (Remainder dihedral_four) (cyclic_group_eval three (usym_unit (cyclic_group dihedral_four)))
                  (modular_zero three) (cyclic_group_eval_unit three) ∎)))

def dihedral_four_cyclic_mere_path
  : Mere (Id Group (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two))))
  ≔ mere_rec (Id Cycles (principal_cycle dihedral_four) (standard_cycle (principal_order dihedral_four)))
      (Mere (Id Group (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two)))))
      (mere_isprop (Id Group (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two)))))
      (p ↦ mere (Id Group (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two))))
        (concat Group (cyclic_group dihedral_four) (order_cyclic_group (principal_order dihedral_four))
          (dihedral_four_action (shape (symmetric_group two)))
          (automorphism_group_point_path Cycles cycles_groupoid (principal_cycle dihedral_four)
            (standard_cycle (principal_order dihedral_four)) p)
          (inverse Group (dihedral_four_action (shape (symmetric_group two))) (order_cyclic_group (principal_order dihedral_four))
            (dihedral_order_action_shape_path (principal_order dihedral_four)))))
      (cycle_order_paths (standard_cycle (principal_order dihedral_four)) (principal_cycle dihedral_four)
        (standard_cycle_order (principal_order dihedral_four)))

def dihedral_four_not_at_most_one : Not (AtMostOneInvolution dihedral_four_group)
  ≔ a ↦ mere_rec (Id Group (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two)))) Empty empty_prop
      (q ↦ dihedral_four_two_involutions
        (transport Group InvolutionWitness (cyclic_group dihedral_four) (dihedral_four_action (shape (symmetric_group two))) q
          cyclic_four_involution) a)
      dihedral_four_cyclic_mere_path

{` The exercise: Q_8 and D_4 are not isomorphic. `}
def quaternion_dihedral_not_isomorphic (f : GroupIso quaternion_group dihedral_four_group) : Empty
  ≔ dihedral_four_not_at_most_one
      (transport Group AtMostOneInvolution quaternion_group dihedral_four_group
        (group_path_from_iso quaternion_group dihedral_four_group f) quaternion_at_most_one_involution)
