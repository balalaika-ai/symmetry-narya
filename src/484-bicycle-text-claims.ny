export "483-figure-eight-coverings"

{` Remaining claims of section "Bicycles": powers of a cycle commute with it
   (group.tex 2040–2041); the two 6-element bicycles of the exercise at
   group.tex 2303 are normal and lie in different components of Bicyc; and
   the footnote to the exercise at group.tex 2146: the automorphism group of
   the pictured 4-element commuting bicycle is C₂ × C₂ (= Σ₂ × Σ₂, the Klein
   four-group, via C₂ = Σ₂, xca:CG2isSG2). `}

{` group.tex 2040: for a cycle (X, t), every power tⁿ commutes with t. `}
def cycle_power_commutes (c : Cycles) (n : Int) (x : cycle_carrier_type c)
  : Id (cycle_carrier_type c)
      (permutation_power (cycle_carrier_type c) (cycle_generator c) n (cycle_generator c .map x))
      (cycle_generator c .map (permutation_power (cycle_carrier_type c) (cycle_generator c) n x))
  ≔ bicycle_power_commutes (cycle_carrier_type c) (cycle_generator c) (cycle_generator c .map)
      (w ↦ refl (cycle_generator c .map (cycle_generator c .map w))) n x

{` Cayley bicycles are normal: the symmetry of a loop z sends refl to z. `}
def cayley_bicycle_normal (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : IsNormalBicycle (cayley_bicycle G g h gen)
  ≔ normal_bicycle_from_point_surjective (cayley_bicycle G g h gen) (refl (shape G))
      (z ↦ mere (BookFiber (Id Bicycles (cayley_bicycle G g h gen) (cayley_bicycle G g h gen)) (USym G)
          (bicycle_evaluation (cayley_bicycle G g h gen) (refl (shape G))) z)
        (refl (cayley_bicycle_family G g h gen) z,
         inverse (USym G) (concat (BG G .carrier) (shape G) (shape G) (shape G) (refl (shape G)) z) z
           (concat_1p (BG G .carrier) (shape G) (shape G) z)))

{` "Two (normal) bicycles": both pictured 6-element bicycles are normal. `}
def hexagon_bicycle_normal : IsNormalBicycle hexagon_bicycle
  ≔ transport Bicycles IsNormalBicycle
      (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating)
      hexagon_bicycle
      (inverse Bicycles hexagon_bicycle
        (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating)
        hexagon_cayley_path)
      (cayley_bicycle_normal (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating)

def prism_bicycle_normal : IsNormalBicycle prism_bicycle
  ≔ transport Bicycles IsNormalBicycle
      (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating)
      prism_bicycle
      (inverse Bicycles prism_bicycle
        (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating)
        prism_cayley_path)
      (cayley_bicycle_normal (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating)

{` "they belong to two different components of Bicyc": an isomorphism would
   turn the fixed point 0 of a² in the hexagon (a is an involution there)
   into a fixed point of a² in the prism, which has none. `}
def prism_point_code (w : Sum (Fin three) (Fin three)) : Sum (Fin three) (Fin three) → Type
  ≔ match w [
  | inl. (inr. _) ↦ [
      | inl. (inr. _) ↦ Unit
      | inl. (inl. (inr. _)) ↦ Empty
      | inl. (inl. (inl. (inr. _))) ↦ Empty
      | inr. (inr. _) ↦ Empty
      | inr. (inl. (inr. _)) ↦ Empty
      | inr. (inl. (inl. (inr. _))) ↦ Empty
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inr. _)) ↦ [
      | inl. (inr. _) ↦ Empty
      | inl. (inl. (inr. _)) ↦ Unit
      | inl. (inl. (inl. (inr. _))) ↦ Empty
      | inr. (inr. _) ↦ Empty
      | inr. (inl. (inr. _)) ↦ Empty
      | inr. (inl. (inl. (inr. _))) ↦ Empty
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inl. (inr. _))) ↦ [
      | inl. (inr. _) ↦ Empty
      | inl. (inl. (inr. _)) ↦ Empty
      | inl. (inl. (inl. (inr. _))) ↦ Unit
      | inr. (inr. _) ↦ Empty
      | inr. (inl. (inr. _)) ↦ Empty
      | inr. (inl. (inl. (inr. _))) ↦ Empty
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inr. (inr. _) ↦ [
      | inl. (inr. _) ↦ Empty
      | inl. (inl. (inr. _)) ↦ Empty
      | inl. (inl. (inl. (inr. _))) ↦ Empty
      | inr. (inr. _) ↦ Unit
      | inr. (inl. (inr. _)) ↦ Empty
      | inr. (inl. (inl. (inr. _))) ↦ Empty
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inr. (inl. (inr. _)) ↦ [
      | inl. (inr. _) ↦ Empty
      | inl. (inl. (inr. _)) ↦ Empty
      | inl. (inl. (inl. (inr. _))) ↦ Empty
      | inr. (inr. _) ↦ Empty
      | inr. (inl. (inr. _)) ↦ Unit
      | inr. (inl. (inl. (inr. _))) ↦ Empty
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inr. (inl. (inl. (inr. _))) ↦ [
      | inl. (inr. _) ↦ Empty
      | inl. (inl. (inr. _)) ↦ Empty
      | inl. (inl. (inl. (inr. _))) ↦ Empty
      | inr. (inr. _) ↦ Empty
      | inr. (inl. (inr. _)) ↦ Empty
      | inr. (inl. (inl. (inr. _))) ↦ Unit
      | inl. (inl. (inl. (inl. e))) ↦ match e []
      | inr. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_point_code_refl (w : Sum (Fin three) (Fin three)) : prism_point_code w w
  ≔ match w [
  | inl. (inr. _) ↦ star.
  | inl. (inl. (inr. _)) ↦ star.
  | inl. (inl. (inl. (inr. _))) ↦ star.
  | inr. (inr. _) ↦ star.
  | inr. (inl. (inr. _)) ↦ star.
  | inr. (inl. (inl. (inr. _))) ↦ star.
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_a_square_moves (y : Sum (Fin three) (Fin three)) : Id (Sum (Fin three) (Fin three)) y (prism_a_map (prism_a_map y)) → Empty
  ≔ match y [
  | inl. (inr. star.) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inl. (inr. star.))) (inl. (inr. star.)) (inl. (inl. (inr. star.))) h
      (prism_point_code_refl (inl. (inr. star.)))
  | inl. (inl. (inr. star.)) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.))) (inl. (inl. (inl. (inr. star.)))) h
      (prism_point_code_refl (inl. (inl. (inr. star.))))
  | inl. (inl. (inl. (inr. star.))) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inl. (inl. (inl. (inr. star.))))) (inl. (inl. (inl. (inr. star.)))) (inl. (inr. star.)) h
      (prism_point_code_refl (inl. (inl. (inl. (inr. star.)))))
  | inr. (inr. star.) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inr. (inr. star.))) (inr. (inr. star.)) (inr. (inl. (inl. (inr. star.)))) h
      (prism_point_code_refl (inr. (inr. star.)))
  | inr. (inl. (inr. star.)) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inr. (inl. (inr. star.)))) (inr. (inl. (inr. star.))) (inr. (inr. star.)) h
      (prism_point_code_refl (inr. (inl. (inr. star.))))
  | inr. (inl. (inl. (inr. star.))) ↦ h ↦ transport (Sum (Fin three) (Fin three)) (prism_point_code (inr. (inl. (inl. (inr. star.))))) (inr. (inl. (inl. (inr. star.)))) (inr. (inl. (inr. star.))) h
      (prism_point_code_refl (inr. (inl. (inl. (inr. star.)))))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def hexagon_prism_not_isomorphic (e : BicycleIsomorphisms hexagon_bicycle prism_bicycle) : Empty
  ≔ let f ≔ e .fst .map in
    prism_a_square_moves (f (inr. star.))
      (concat (Sum (Fin three) (Fin three)) (f (inr. star.)) (prism_a_map (f (hexagon_a_map (inr. star.))))
        (prism_a_map (prism_a_map (f (inr. star.))))
        (e .snd .fst (hexagon_a_map (inr. star.)))
        (refl prism_a_map (e .snd .fst (inr. star.))))

def hexagon_prism_different_components (h : Mere (Id Bicycles hexagon_bicycle prism_bicycle)) : Empty
  ≔ mere_rec (Id Bicycles hexagon_bicycle prism_bicycle) Empty empty_prop
      (q ↦ hexagon_prism_not_isomorphic (bicycle_paths_equiv hexagon_bicycle prism_bicycle .map q)) h

{` Footnote to the exercise at group.tex 2146: the pictured commuting bicycle
   on the four nodes n_{xy} (x, y ∈ {0, 1}), with a flipping y and b flipping
   x, read off the TikZ code. `}
def klein_flip_map : Fin two → Fin two ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. e) ↦ match e [] ]

def klein_flip_involutive (x : Fin two) : Id (Fin two) (klein_flip_map (klein_flip_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin two)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin two)
  | inl. (inl. e) ↦ match e [] ]

def klein_flip_equiv : Equiv (Fin two) (Fin two)
  ≔ quasi_inverse_equiv (Fin two) (Fin two) klein_flip_map klein_flip_map klein_flip_involutive klein_flip_involutive

def klein_bicycle_a : Equiv (Product (Fin two) (Fin two)) (Product (Fin two) (Fin two))
  ≔ product_equiv (Fin two) (Fin two) (Fin two) (Fin two) (identity_equiv (Fin two)) klein_flip_equiv

def klein_bicycle_b : Equiv (Product (Fin two) (Fin two)) (Product (Fin two) (Fin two))
  ≔ product_equiv (Fin two) (Fin two) (Fin two) (Fin two) klein_flip_equiv (identity_equiv (Fin two))

def klein_word_from_origin_at (x y : Fin two)
  : BicycleWordFrom (Product (Fin two) (Fin two)) klein_bicycle_a klein_bicycle_b (inr. star., inr. star.) (x, y)
  ≔ match x, y [
  | inr. star., inr. star. ↦ (nil., refl ((inr. star., inr. star.) : Product (Fin two) (Fin two)))
  | inr. star., inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) nil.,
      refl ((inr. star., inl. (inr. star.)) : Product (Fin two) (Fin two)))
  | inl. (inr. star.), inr. star. ↦ (cons. (inr. (pos. (suc. zero.))) nil.,
      refl ((inl. (inr. star.), inr. star.) : Product (Fin two) (Fin two)))
  | inl. (inr. star.), inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) nil.),
      refl ((inl. (inr. star.), inl. (inr. star.)) : Product (Fin two) (Fin two)))
  | inr. star., inl. (inl. e) ↦ match e []
  | inl. (inr. star.), inl. (inl. e) ↦ match e []
  | inl. (inl. e), _ ↦ match e [] ]

def klein_word_from_origin (p : Product (Fin two) (Fin two))
  : BicycleWordFrom (Product (Fin two) (Fin two)) klein_bicycle_a klein_bicycle_b (inr. star., inr. star.) p
  ≔ klein_word_from_origin_at (p .fst) (p .snd)

def klein_bicycle : Bicycles
  ≔ mkbicycle (Product (Fin two) (Fin two), sigma_set (Fin two) (_ ↦ Fin two) (fin_set two) (_ ↦ fin_set two))
      klein_bicycle_a klein_bicycle_b
      (bicycle_connected_from_point (Product (Fin two) (Fin two)) klein_bicycle_a klein_bicycle_b (inr. star., inr. star.)
        (p ↦ mere (BicycleWordFrom (Product (Fin two) (Fin two)) klein_bicycle_a klein_bicycle_b (inr. star., inr. star.) p)
          (klein_word_from_origin p)))

def klein_bicycle_commuting : IsCommutingBicycle klein_bicycle
  ≔ p ↦ refl ((klein_flip_map (p .fst), klein_flip_map (p .snd)) : Product (Fin two) (Fin two))

{` The 2-cycle (Fin 2, s) of cyclic_group_fin 1 = C₂ acts by the flip. `}
def klein_successor_is_flip (y : Fin two)
  : Id (Fin two) (cycle_generator (finite_fin_cycle (suc. zero.)) .map y) (klein_flip_map y)
  ≔ match y [
  | inr. star. ↦ refl (inl. (inr. star.) : Fin two)
  | inl. (inr. star.) ↦ refl (inr. star. : Fin two)
  | inl. (inl. e) ↦ match e [] ]

{` The pictured bicycle is the product bicycle of two copies of the 2-cycle
   (swap the coordinates). `}
def klein_swap_map (p : Product (Fin two) (Fin two)) : Product (Fin two) (Fin two) ≔ (p .snd, p .fst)

def klein_swap_equiv : Equiv (Product (Fin two) (Fin two)) (Product (Fin two) (Fin two))
  ≔ quasi_inverse_equiv (Product (Fin two) (Fin two)) (Product (Fin two) (Fin two)) klein_swap_map klein_swap_map
      (p ↦ refl p) (p ↦ refl p)

def klein_bicycle_product_path
  : Id Bicycles klein_bicycle (cycle_product_bicycle (finite_fin_cycle (suc. zero.)) (finite_fin_cycle (suc. zero.)))
  ≔ bicycle_path_from_iso klein_bicycle (cycle_product_bicycle (finite_fin_cycle (suc. zero.)) (finite_fin_cycle (suc. zero.)))
      (klein_swap_equiv,
       (p ↦ (inverse (Fin two) (cycle_generator (finite_fin_cycle (suc. zero.)) .map (p .snd)) (klein_flip_map (p .snd))
               (klein_successor_is_flip (p .snd)),
             refl (p .fst)),
        p ↦ (refl (p .snd),
             inverse (Fin two) (cycle_generator (finite_fin_cycle (suc. zero.)) .map (p .fst)) (klein_flip_map (p .fst))
               (klein_successor_is_flip (p .fst)))))

{` Aut_Bicyc(pictured bicycle) = C₂ × C₂. `}
def klein_bicycle_automorphism_path
  : Id Group (bicycle_automorphism_group klein_bicycle)
      (product_group (cyclic_group_fin (suc. zero.)) (cyclic_group_fin (suc. zero.)))
  ≔ concat Group (bicycle_automorphism_group klein_bicycle)
      (bicycle_automorphism_group (cycle_product_bicycle (finite_fin_cycle (suc. zero.)) (finite_fin_cycle (suc. zero.))))
      (product_group (cyclic_group_fin (suc. zero.)) (cyclic_group_fin (suc. zero.)))
      (refl bicycle_automorphism_group klein_bicycle_product_path)
      (cycle_product_bicycle_automorphism_path (finite_fin_cycle (suc. zero.)) (finite_fin_cycle (suc. zero.)))
