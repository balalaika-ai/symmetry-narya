export "bridge-03-homs"
export "../../../src/433-permutation-group-homomorphisms"
export "../../../src/418-cyclic-group-images"

{` Bridges for ex:groups-morphisms (line 1141) and the remark after
   it (line 1202), blind file 03-homs.ny. The classifying types of the blind
   and our permutation, trivial, product and cyclic groups agree on the
   nose (only the groupoid witnesses differ), so the blind classifying maps
   are compared with ours directly as pointed maps. `}

{` (1) - ⊔ T and - × T. `}
def bridge_def_hom_coprod (S T : SetTypes)
  : Id (BookPointedMap (BG (permutation_group S)) (BG (permutation_group (set_sum_right T S))))
      (blind_Bhom (blind_SG_set S) (blind_SG_set (blind_set_sum S T)) (blind_hom_coprod S T))
      (hom_B (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T))
  ≔ refl (hom_B (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T))

def bridge_def_hom_prod (S T : SetTypes)
  : Id (BookPointedMap (BG (permutation_group S)) (BG (permutation_group (set_product_right T S))))
      (blind_Bhom (blind_SG_set S) (blind_SG_set (blind_set_prod S T)) (blind_hom_prod S T))
      (hom_B (permutation_group S) (permutation_group (set_product_right T S)) (permutation_product_hom S T))
  ≔ refl (hom_B (permutation_group S) (permutation_group (set_product_right T S)) (permutation_product_hom S T))

def bridge_ex_fin_sum_identification : blind_ex_fin_sum_identification
  ≔ m n ↦ ua (Fin (add m n)) (Sum (Fin m) (Fin n)) (fin_sum_identification m n)

def bridge_ex_fin_prod_identification : blind_ex_fin_prod_identification
  ≔ m n ↦ ua (Fin (mul m n)) (Product (Fin m) (Fin n)) (fin_product_identification m n)

{` (2) Homomorphisms to and from the trivial group: blind_TG has the
   classifying type of our trivial_group, so BlindHom G TG is GroupHom
   (bridge_g G) trivial_group up to the Copy wrapper. `}
def bridge_hom_trivial_to (G : BlindGroup) : Equiv (BlindHom G blind_TG) (GroupHom (bridge_g G) trivial_group)
  ≔ quasi_inverse_equiv (BlindHom G blind_TG) (GroupHom (bridge_g G) trivial_group)
      (f ↦ mkhom (bridge_g G) trivial_group (blind_Bhom G blind_TG f))
      (f ↦ blind_mkhom G blind_TG (hom_B (bridge_g G) trivial_group f))
      [ copy. k ↦ refl (blind_mkhom G blind_TG k) ] (f ↦ refl f)

def bridge_hom_trivial_from (G : BlindGroup) : Equiv (BlindHom blind_TG G) (GroupHom trivial_group (bridge_g G))
  ≔ quasi_inverse_equiv (BlindHom blind_TG G) (GroupHom trivial_group (bridge_g G))
      (f ↦ mkhom trivial_group (bridge_g G) (blind_Bhom blind_TG G f))
      (f ↦ blind_mkhom blind_TG G (hom_B trivial_group (bridge_g G) f))
      [ copy. k ↦ refl (blind_mkhom blind_TG G k) ] (f ↦ refl f)

def bridge_ex_hom_to_trivial : blind_ex_hom_to_trivial
  ≔ G ↦ book_contractibility_equiv (GroupHom (bridge_g G) trivial_group) (BlindHom G blind_TG)
      (canonical_inverse_equiv (BlindHom G blind_TG) (GroupHom (bridge_g G) trivial_group) (bridge_hom_trivial_to G))
      .map (group_hom_to_trivial_unique (bridge_g G))

def bridge_ex_hom_from_trivial : blind_ex_hom_from_trivial
  ≔ G ↦ book_contractibility_equiv (GroupHom trivial_group (bridge_g G)) (BlindHom blind_TG G)
      (canonical_inverse_equiv (BlindHom blind_TG G) (GroupHom trivial_group (bridge_g G)) (bridge_hom_trivial_from G))
      .map (group_hom_from_trivial_unique (bridge_g G))

{` (3) Projections and inclusions: ours on the nose. `}
def bridge_def_hom_proj1 (G H : BlindGroup)
  : Id (BookPointedMap (BG (product_group (bridge_g G) (bridge_g H))) (BG (bridge_g G)))
      (blind_Bhom (blind_group_product G H) G (blind_hom_proj1 G H))
      (hom_B (product_group (bridge_g G) (bridge_g H)) (bridge_g G) (product_group_proj1 (bridge_g G) (bridge_g H)))
  ≔ refl (blind_Bhom (blind_group_product G H) G (blind_hom_proj1 G H))

def bridge_def_hom_incl1 (G H : BlindGroup)
  : Id (BookPointedMap (BG (bridge_g G)) (BG (product_group (bridge_g G) (bridge_g H))))
      (blind_Bhom G (blind_group_product G H) (blind_hom_incl1 G H))
      (hom_B (bridge_g G) (product_group (bridge_g G) (bridge_g H)) (product_group_incl1 (bridge_g G) (bridge_g H)))
  ≔ refl (blind_Bhom G (blind_group_product G H) (blind_hom_incl1 G H))

{` (4) R_m, mod_m and the forgetful map are ours (power_finset_pointed,
   mod_pointed, cycle_forget_pointed): the blind circle-recursion data are
   ours by refl for abstract arguments (bridge_circle_rec_pointed,
   bridge_component_set_loop), which keeps the conversion checks small; the
   factorization is mod_forget_factorization. `}
def bridge_circle_rec_pointed (C : CircleSignature) (A : Type) (d : FreeLoop A)
  : Id (BookPointedMap (circle_pointed C) (A, d .fst)) (circle_rec C A d, blind_circle_rec_pointing C A d)
      (pointed_circle_loop_rec C A (d .fst) (d .snd))
  ≔ refl (pointed_circle_loop_rec C A (d .fst) (d .snd))

def bridge_component_set_loop (S : SetTypes) (e : Equiv (S .fst) (S .fst))
  : Id (USym (permutation_group S)) (blind_component_loop SetTypes S (blind_set_loop S e)) (permutation_symmetry S e)
  ≔ refl (permutation_symmetry S e)

def bridge_component_cycle_loop (c : Cycles)
  : Id (USym (automorphism_group Cycles cycles_groupoid c)) (blind_component_loop Cycles c (cycle_generating_loop c)) (cycle_group_generator c)
  ≔ refl (cycle_group_generator c)

def bridge_def_Rm_hom (C : CircleSignature) (n : Nat)
  : Id (BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))))
      (blind_Bhom (blind_ZZ C) (blind_SG (suc. n)) (blind_Rm_hom C n)) (power_finset_pointed C n)
  ≔ let S ≔ standard_set (suc. n) in
    let A ≔ NativeComponent SetTypes S in
    let l ≔ blind_component_loop SetTypes S (blind_set_loop S (finite_fin_successor n)) in
    concat (BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))))
      (circle_rec C A (component_point SetTypes S, l), blind_circle_rec_pointing C A (component_point SetTypes S, l))
      (pointed_circle_loop_rec C A (component_point SetTypes S) l)
      (power_finset_pointed C n)
      (bridge_circle_rec_pointed C A (component_point SetTypes S, l))
      (refl (pointed_circle_loop_rec C A (component_point SetTypes S))
        (bridge_component_set_loop S (finite_fin_successor n)))

def bridge_def_mod_m (C : CircleSignature) (n : Nat)
  : Id (BookPointedMap (circle_pointed C) (BG (cyclic_group_fin n)))
      (blind_Bhom (blind_ZZ C) (blind_CG n) (blind_mod_m C n)) (mod_pointed C n)
  ≔ let c ≔ finite_fin_cycle n in
    let A ≔ NativeComponent Cycles c in
    let l ≔ blind_component_loop Cycles c (cycle_generating_loop c) in
    concat (BookPointedMap (circle_pointed C) (BG (cyclic_group_fin n)))
      (circle_rec C A (component_point Cycles c, l), blind_circle_rec_pointing C A (component_point Cycles c, l))
      (pointed_circle_loop_rec C A (component_point Cycles c) l)
      (mod_pointed C n)
      (bridge_circle_rec_pointed C A (component_point Cycles c, l))
      (refl (pointed_circle_loop_rec C A (component_point Cycles c)) (bridge_component_cycle_loop c))

def bridge_def_hom_forget_cycle (n : Nat)
  : Id (BookPointedMap (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n))))
      (blind_Bhom (blind_CG n) (blind_SG (suc. n)) (blind_hom_forget_cycle n)) (cycle_forget_pointed n)
  ≔ refl (cycle_forget_pointed n)

def bridge_ex_mod_m_factorization : blind_ex_mod_m_factorization
  ≔ C n ↦
    let Z ≔ blind_ZZ C in let S ≔ blind_SG (suc. n) in
    let X ≔ circle_pointed C in let Y ≔ BG (cyclic_group_fin n) in let W ≔ BG (symmetric_group (suc. n)) in
    let M ≔ BookPointedMap X W in
    let bm ≔ blind_Bhom Z (blind_CG n) (blind_mod_m C n) in
    let bf ≔ blind_Bhom (blind_CG n) S (blind_hom_forget_cycle n) in
    bridge_hpath Z S (blind_Rm_hom C n) (blind_hom_compose Z (blind_CG n) S (blind_mod_m C n) (blind_hom_forget_cycle n))
      (map_path M (GroupHom (bridge_g Z) (bridge_g S)) (mkhom (bridge_g Z) (bridge_g S))
        (blind_Bhom Z S (blind_Rm_hom C n)) (book_pointed_compose X Y W bm bf)
        (concat M (blind_Bhom Z S (blind_Rm_hom C n)) (power_finset_pointed C n) (book_pointed_compose X Y W bm bf)
          (bridge_def_Rm_hom C n)
          (concat M (power_finset_pointed C n) (mod_forget_pointed C n) (book_pointed_compose X Y W bm bf)
            (inverse M (mod_forget_pointed C n) (power_finset_pointed C n) (mod_forget_factorization C n))
            (inverse M (book_pointed_compose X Y W bm bf) (mod_forget_pointed C n)
              (refl (book_pointed_compose X Y W) (bridge_def_mod_m C n) (bridge_def_hom_forget_cycle n))))))

{` Remark after ex:groups-morphisms (line 1202). The blind τ = (0 1) in the
   blind numbering (fin_val) is our fin3_swap12 (sigma3_sigma); ours
   (sigma3_two_homs_differ) uses fin3_swap01. The same argument
   (loop_conjugate_fixed_commutes, sigma3_tau_sigma_noncommuting) applies. `}
def bridge_tau3_pointwise (x : Fin three) : Id (Fin three) (blind_tau3 .map x) (fin3_swap12_equiv .map x)
  ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin three) ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin three) ]
    | inl. z ↦ match z [
      | inr. u ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin three) ]
      | inl. e ↦ match e [ ] ] ] ]

def bridge_tau3_path : Id (USym (symmetric_group three)) blind_tau3_path sigma3_sigma
  ≔ refl (permutation_symmetry (standard_set three))
      (equiv_homotopy (Fin three) (Fin three) blind_tau3 fin3_swap12_equiv bridge_tau3_pointwise)

def bridge_rem_tau_conjugation : blind_rem_tau_conjugation
  ≔ σ ↦ refl (blind_usym_hom (blind_SG blind_three) (blind_SG blind_three) blind_tau_tilde σ)

def bridge_rem_id_ne_tau : blind_rem_id_ne_tau
  ≔ h ↦
    let S ≔ symmetric_group three in let A ≔ BG S .carrier in let a ≔ shape S in
    let T ≔ blind_tau3_path in let g ≔ sigma3_tau in
    let P ≔ BookPointedMap (BG S) (BG S) in
    let h' : Id P (book_pointed_identity (BG S)) (identity A, T)
      ≔ map_path (BlindHom (blind_SG blind_three) (blind_SG blind_three)) P
          (blind_Bhom (blind_SG blind_three) (blind_SG blind_three))
          (blind_id_hom (blind_SG blind_three)) blind_tau_tilde h in
    let e : Id (USym S) (concat A a a a T (concat A a a a g (inverse A a a T))) g
      ≔ concat (USym S) (loops_map (BG S) (BG S) (identity A, T) g) (loops_map (BG S) (BG S) (book_pointed_identity (BG S)) g) g
          (inverse (USym S) (loops_map (BG S) (BG S) (book_pointed_identity (BG S)) g) (loops_map (BG S) (BG S) (identity A, T) g)
            (map_path P (USym S) (k ↦ loops_map (BG S) (BG S) k g) (book_pointed_identity (BG S)) (identity A, T) h'))
          (loop_conjugate_at_refl A a g) in
    let c : Id (USym S) (concat A a a a g T) (concat A a a a T g) ≔ loop_conjugate_fixed_commutes A a g T e in
    sigma3_tau_sigma_noncommuting
      (transport (USym S) (t ↦ Id (USym S) (concat A a a a g t) (concat A a a a t g)) T sigma3_sigma bridge_tau3_path c)
