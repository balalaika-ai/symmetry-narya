export "809-dihedral-three-comparison"
export "412-symmetric-group-two"

{` Chapter 8: the action C̃_n of Σ_2 on C_n is nontrivial, and D_n is not
   abelian when 2 ∉ nZ (n ≠ 1, 2); litmus: D_3 is a non-abelian group of
   order 6 (with module 808).

   Computation: r ∈ USym C̃_n(Fin 2) is the symmetry of (X, f) given by f_yes;
   the semidirect action of the swap σ of Σ_2 is r^σ = transport of r along σ⁻¹
   (module 801). Evaluating loops on the carrier X (ev), ev(r^σ) is ev(r)
   conjugated by the transport of X along σ, which sends [(s,z)] to [(σ s, z)];
   so ev(r^σ)[(yes,0)] = [(yes,-1)] while ev(r)[(yes,0)] = [(yes,1)].
   Commuting s(σ) and j(r) would force r^σ = r (multiplication formula). `}

{` A general fact about the J-defined loop action of module 801: for any
   evaluation ev of loops on a family K, ev_x(q'^p)(p^*(y)) = p^*(ev_{x'}(q')(y)). `}
def section_loop_action_eval (X : Type) (Y : X → Type) (f : (x : X) → Y x) (K : X → Type)
  (ev : (x : X) → Id (Y x) (f x) (f x) → K x → K x) (x x' : X) (p : Id X x x')
  (q' : Id (Y x') (f x') (f x')) (y : K x')
  : Id (K x) (ev x (section_loop_action X Y f x x' p q') (refl K p .trl y)) (refl K p .trl (ev x' q' y))
  ≔ J X x (x' p ↦ (q' : Id (Y x') (f x') (f x')) (y : K x')
                    → Id (K x) (ev x (section_loop_action X Y f x x' p q') (refl K p .trl y)) (refl K p .trl (ev x' q' y)))
      (q y ↦ calc
        ev x (section_loop_action X Y f x x (refl x) q) (refl K (refl x) .trl y)
          = ev x q (refl K (refl x) .trl y)
          by refl ((m ↦ ev x m (refl K (refl x) .trl y)) : Id (Y x) (f x) (f x) → K x) (section_loop_action_refl X Y f x q)
        = ev x q y by refl (ev x q) (refl K (refl x) .liftl y)
        = refl K (refl x) .trl (ev x q y)
          by inverse (K x) (refl K (refl x) .trl (ev x q y)) (ev x q y) (refl K (refl x) .liftl (ev x q y)) ∎)
      x' p q' y

{` Transport of X = (S × Z)/~ along an identification of 2-element sets. `}
def dihedral_class_transport (H : Subtypes Int) (h : IntegerSubgroupLaws H) (S S' : TwoElementSets)
  (p : Id TwoElementSets S S') (s' : two_set_carrier S') (m : Int)
  : Id (DihedralCycleSet S H h)
      (refl ((z ↦ DihedralCycleSet z H h) : TwoElementSets → Type) p .trl (dihedral_class S' H h s' m))
      (dihedral_class S H h (refl two_set_carrier p .trl s') m)
  ≔ J TwoElementSets S (S' p ↦ (s' : two_set_carrier S')
                              → Id (DihedralCycleSet S H h)
                                  (refl ((z ↦ DihedralCycleSet z H h) : TwoElementSets → Type) p .trl (dihedral_class S' H h s' m))
                                  (dihedral_class S H h (refl two_set_carrier p .trl s') m))
      (s ↦ calc
        refl ((z ↦ DihedralCycleSet z H h) : TwoElementSets → Type) (refl S) .trl (dihedral_class S H h s m)
          = dihedral_class S H h s m
          by refl ((z ↦ DihedralCycleSet z H h) : TwoElementSets → Type) (refl S) .liftl (dihedral_class S H h s m)
        = dihedral_class S H h (refl two_set_carrier (refl S) .trl s) m
          by refl ((t ↦ dihedral_class S H h t m) : two_set_carrier S → DihedralCycleSet S H h)
               (inverse (two_set_carrier S) (refl two_set_carrier (refl S) .trl s) s (refl two_set_carrier (refl S) .liftl s)) ∎)
      S' p s'

{` The maps f_a commute with each other. `}
def dihedral_steps_commute (A : Type) (a b s : A) (d1 : Decidable (Id A s a)) (d2 : Decidable (Id A s b)) (z : Int)
  : Id Int (dihedral_step A a s d1 (dihedral_step A b s d2 z)) (dihedral_step A b s d2 (dihedral_step A a s d1 z))
  ≔ match d1, d2 [
  | inl. _, inl. _ ↦ refl (int_succ (int_succ z))
  | inl. _, inr. _ ↦ concat Int (int_succ (int_pred z)) z (int_pred (int_succ z)) (int_succ_pred z)
      (inverse Int (int_pred (int_succ z)) z (int_pred_succ z))
  | inr. _, inl. _ ↦ concat Int (int_pred (int_succ z)) z (int_succ (int_pred z)) (int_pred_succ z)
      (inverse Int (int_succ (int_pred z)) z (int_succ_pred z))
  | inr. _, inr. _ ↦ refl (int_pred (int_pred z)) ]

def dihedral_moves_commute (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (a b : two_set_carrier S)
  (x : DihedralCycleSet S H h)
  : Id (DihedralCycleSet S H h) (dihedral_move S H h a (dihedral_move S H h b x)) (dihedral_move S H h b (dihedral_move S H h a x))
  ≔ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (x ↦ Id (DihedralCycleSet S H h) (dihedral_move S H h a (dihedral_move S H h b x)) (dihedral_move S H h b (dihedral_move S H h a x)))
      (x ↦ dihedral_cycle_set_set S H h (dihedral_move S H h a (dihedral_move S H h b x)) (dihedral_move S H h b (dihedral_move S H h a x)))
      (u ↦ refl ((m ↦ dihedral_class S H h (u .fst) m) : Int → DihedralCycleSet S H h)
        (dihedral_steps_commute (two_set_carrier S) a b (u .fst) (two_set_decidable S (u .fst) a)
          (two_set_decidable S (u .fst) b) (u .snd)))
      x

{` The rotation r: the symmetry of (X, f) in T_S given by f_s. Its carrier
   path is set_types_path of f_s (so transport along it computes to f_s), and
   the endomap component comes from the commuting square via module 873. `}
def dihedral_rotation_path (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Id (S2C3Type S) (dihedral_point S H h) (dihedral_point S H h)
  ≔ (set_types_path (dihedral_cycle_set S H h) (dihedral_cycle_set S H h) (dihedral_move_equiv S H h s),
     equiv_inverse_map
       (Id (s_action_family (two_set_carrier S))
         (ua (DihedralCycleSet S H h) (DihedralCycleSet S H h) (dihedral_move_equiv S H h s))
         (dihedral_point S H h .snd) (dihedral_point S H h .snd))
       (SActionCommutes (two_set_carrier S) (DihedralCycleSet S H h) (DihedralCycleSet S H h)
         (dihedral_point S H h .snd) (dihedral_point S H h .snd)
         (ua (DihedralCycleSet S H h) (DihedralCycleSet S H h) (dihedral_move_equiv S H h s) .trr))
       (s_action_pathover_equiv (two_set_carrier S) (DihedralCycleSet S H h) (DihedralCycleSet S H h)
         (ua (DihedralCycleSet S H h) (DihedralCycleSet S H h) (dihedral_move_equiv S H h s))
         (dihedral_point S H h .snd) (dihedral_point S H h .snd))
       (a x ↦ dihedral_moves_commute S H h s a x))

def dihedral_rotation (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : USym (dihedral_action_group H h S)
  ≔ component_path (S2C3Type S) (dihedral_point S H h)
      (component_point (S2C3Type S) (dihedral_point S H h)) (component_point (S2C3Type S) (dihedral_point S H h))
      (dihedral_rotation_path S H h s)

{` Evaluation of symmetries of (X, f) on X. `}
def dihedral_symmetry_eval (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (q : USym (dihedral_action_group H h S)) (x : DihedralCycleSet S H h) : DihedralCycleSet S H h
  ≔ q .fst .fst .fst .trr x

def dihedral_rotation_eval (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h)
  : Id (DihedralCycleSet S H h) (dihedral_symmetry_eval S H h (dihedral_rotation S H h s) x) (dihedral_move S H h s x)
  ≔ refl (dihedral_move S H h s x)

{` The action of the swap on any symmetry R that acts on X as f_yes,
   evaluated at [(yes, 0)]. (R is kept abstract: instantiating such statements
   at the concrete rotation is very slow in Narya.) `}
def DihedralActsAsRotation (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (R : USym (dihedral_action_group H h (shape (symmetric_group two)))) : Type
  ≔ (x : DihedralCycleSet (shape (symmetric_group two)) H h)
    → Id (DihedralCycleSet (shape (symmetric_group two)) H h)
        (dihedral_symmetry_eval (shape (symmetric_group two)) H h R x) (dihedral_move (shape (symmetric_group two)) H h s2c3_fin2_yes x)

def dihedral_swap_action (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (R : USym (dihedral_action_group H h (shape (symmetric_group two))))
  : USym (dihedral_action_group H h (shape (symmetric_group two)))
  ≔ section_loop_action TwoElementSets (t ↦ BG (dihedral_action_group H h t) .carrier)
      (t ↦ shape (dihedral_action_group H h t)) (shape (symmetric_group two)) (shape (symmetric_group two)) sigma2_swap R

def dihedral_swap_action_eval (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (R : USym (dihedral_action_group H h (shape (symmetric_group two)))) (hR : DihedralActsAsRotation H h R)
  : Id (DihedralCycleSet (shape (symmetric_group two)) H h)
      (dihedral_symmetry_eval (shape (symmetric_group two)) H h (dihedral_swap_action H h R)
        (dihedral_class (shape (symmetric_group two)) H h s2c3_fin2_yes int_zero))
      (dihedral_class (shape (symmetric_group two)) H h s2c3_fin2_yes (neg. zero.))
  ≔ let S : TwoElementSets ≔ shape (symmetric_group two) in
    let K : TwoElementSets → Type ≔ z ↦ DihedralCycleSet z H h in
    calc
      dihedral_symmetry_eval S H h (dihedral_swap_action H h R) (dihedral_class S H h s2c3_fin2_yes int_zero)
        = dihedral_symmetry_eval S H h (dihedral_swap_action H h R) (refl K sigma2_swap .trl (dihedral_class S H h s2c3_fin2_no int_zero))
        by refl (dihedral_symmetry_eval S H h (dihedral_swap_action H h R))
             (inverse (DihedralCycleSet S H h) (refl K sigma2_swap .trl (dihedral_class S H h s2c3_fin2_no int_zero))
               (dihedral_class S H h s2c3_fin2_yes int_zero)
               (dihedral_class_transport H h S S sigma2_swap s2c3_fin2_no int_zero))
      = refl K sigma2_swap .trl (dihedral_symmetry_eval S H h R (dihedral_class S H h s2c3_fin2_no int_zero))
        by section_loop_action_eval TwoElementSets (t ↦ BG (dihedral_action_group H h t) .carrier)
             (t ↦ shape (dihedral_action_group H h t)) K (t q x ↦ dihedral_symmetry_eval t H h q x) S S sigma2_swap R
             (dihedral_class S H h s2c3_fin2_no int_zero)
      = refl K sigma2_swap .trl (dihedral_move S H h s2c3_fin2_yes (dihedral_class S H h s2c3_fin2_no int_zero))
        by refl (refl K sigma2_swap .trl) (hR (dihedral_class S H h s2c3_fin2_no int_zero))
      = refl K sigma2_swap .trl (dihedral_class S H h s2c3_fin2_no (neg. zero.))
        by refl (refl K sigma2_swap .trl)
             (dihedral_move_other S H h s2c3_fin2_yes s2c3_fin2_no s2c3_fin2_no_not_yes int_zero)
      = dihedral_class S H h s2c3_fin2_yes (neg. zero.)
        by dihedral_class_transport H h S S sigma2_swap s2c3_fin2_no (neg. zero.) ∎

{` If 2 ∉ H, then R^σ ≠ R. `}
def dihedral_swap_action_nontrivial (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (n2 : Not (SubgroupMember H (pos. two)))
  (R : USym (dihedral_action_group H h (shape (symmetric_group two)))) (hR : DihedralActsAsRotation H h R)
  (e : Id (USym (dihedral_action_group H h (shape (symmetric_group two)))) R (dihedral_swap_action H h R))
  : Empty
  ≔ let S : TwoElementSets ≔ shape (symmetric_group two) in
    let x0 : DihedralCycleSet S H h ≔ dihedral_class S H h s2c3_fin2_yes int_zero in
    let path : Id (DihedralCycleSet S H h) (dihedral_class S H h s2c3_fin2_yes (neg. zero.))
                 (dihedral_class S H h s2c3_fin2_yes (pos. (suc. zero.)))
      ≔ calc
          dihedral_class S H h s2c3_fin2_yes (neg. zero.)
            = dihedral_symmetry_eval S H h (dihedral_swap_action H h R) x0
            by inverse (DihedralCycleSet S H h) (dihedral_symmetry_eval S H h (dihedral_swap_action H h R) x0)
                 (dihedral_class S H h s2c3_fin2_yes (neg. zero.)) (dihedral_swap_action_eval H h R hR)
          = dihedral_symmetry_eval S H h R x0
            by refl ((q ↦ dihedral_symmetry_eval S H h q x0) : USym (dihedral_action_group H h S) → DihedralCycleSet S H h)
                 (inverse (USym (dihedral_action_group H h S)) R (dihedral_swap_action H h R) e)
          = dihedral_move S H h s2c3_fin2_yes x0 by hR x0
          = dihedral_class S H h s2c3_fin2_yes (pos. (suc. zero.)) by dihedral_move_self S H h s2c3_fin2_yes int_zero ∎ in
    match quotient_effective (DihedralPair S) (dihedral_relation S H h) (s2c3_fin2_yes, neg. zero.) (s2c3_fin2_yes, pos. (suc. zero.))
      .map path [
    | inl. a ↦ n2 (h .snd .snd (neg. (suc. zero.)) (a .snd))
    | inr. b ↦ b .fst (refl s2c3_fin2_yes) ]

{` A semidirect product with q^p ≠ q for some p, q is not abelian:
   s(p)·j(q) and j(q)·s(p) have second components q and q^p. `}
def semidirect_nontrivial_action_not_abelian (G : Group) (Hf : BG G .carrier → Group) (σ : USym G) (r : USym (Hf (shape G)))
  (hne : Not (Id (USym (Hf (shape G))) r (semidirect_loop_action G Hf σ r)))
  (ab : IsAbelian (semidirect_product G Hf)) : Empty
  ≔ let D : Group ≔ semidirect_product G Hf in
    let K : Group ≔ Hf (shape G) in
    let a : USym D ≔ usym_hom G D (semidirect_section G Hf) σ in
    let b : USym D ≔ usym_hom K D (semidirect_inclusion G Hf) r in
    let pa : Id (Product (USym G) (USym K)) (semidirect_usym_pair G Hf a) (σ, usym_unit K)
      ≔ semidirect_usym_pair_section G Hf σ in
    let pb : Id (Product (USym G) (USym K)) (semidirect_usym_pair G Hf b) (usym_unit G, r)
      ≔ semidirect_usym_pair_inclusion G Hf r in
    let snd_mul : Product (USym G) (USym K) → Product (USym G) (USym K) → USym K
      ≔ u v ↦ semidirect_pair_mul G Hf u v .snd in
    let products : Id (USym K) (snd_mul (σ, usym_unit K) (usym_unit G, r)) (snd_mul (usym_unit G, r) (σ, usym_unit K))
      ≔ calc
          snd_mul (σ, usym_unit K) (usym_unit G, r)
            = snd_mul (semidirect_usym_pair G Hf a) (semidirect_usym_pair G Hf b)
            by inverse (USym K) (snd_mul (semidirect_usym_pair G Hf a) (semidirect_usym_pair G Hf b))
                 (snd_mul (σ, usym_unit K) (usym_unit G, r))
                 (refl snd_mul pa pb)
          = semidirect_usym_pair G Hf (usym_mul D a b) .snd
            by inverse (USym K) (semidirect_usym_pair G Hf (usym_mul D a b) .snd)
                 (snd_mul (semidirect_usym_pair G Hf a) (semidirect_usym_pair G Hf b))
                 (refl ((u ↦ u .snd) : Product (USym G) (USym K) → USym K) (semidirect_usym_mul G Hf a b))
          = semidirect_usym_pair G Hf (usym_mul D b a) .snd
            by refl ((e ↦ semidirect_usym_pair G Hf e .snd) : USym D → USym K) (ab a b)
          = snd_mul (semidirect_usym_pair G Hf b) (semidirect_usym_pair G Hf a)
            by refl ((u ↦ u .snd) : Product (USym G) (USym K) → USym K) (semidirect_usym_mul G Hf b a)
          = snd_mul (usym_unit G, r) (σ, usym_unit K) by refl snd_mul pb pa ∎ in
    hne
        (calc
          r = usym_mul K (usym_unit K) r
            by inverse (USym K) (usym_mul K (usym_unit K) r) r (concat_p1 (BG K .carrier) (shape K) (shape K) r)
          = usym_mul K (semidirect_loop_action G Hf (usym_unit G) (usym_unit K)) r
            by refl ((q ↦ usym_mul K q r) : USym K → USym K)
                 (inverse (USym K) (semidirect_loop_action G Hf (usym_unit G) (usym_unit K)) (usym_unit K)
                   (semidirect_loop_action_unit G Hf (usym_unit K)))
          = usym_mul K (semidirect_loop_action G Hf σ r) (usym_unit K) by products
          = semidirect_loop_action G Hf σ r
            by concat_1p (BG K .carrier) (shape K) (shape K) (semidirect_loop_action G Hf σ r) ∎)

{` D_n is not abelian when 2 ∉ nZ; stated for any subgroup (H, h) of Z
   (D_n is the case H = order_periods n, h = order_subgroup_laws n). `}
def dihedral_semidirect_not_abelian_at (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n2 : Not (SubgroupMember H (pos. two)))
  (R : USym (dihedral_action_group H h (shape (symmetric_group two)))) (hR : DihedralActsAsRotation H h R)
  (ab : IsAbelian (semidirect_product (symmetric_group two) (dihedral_action_group H h))) : Empty
  ≔ semidirect_nontrivial_action_not_abelian (symmetric_group two) (dihedral_action_group H h) sigma2_swap R
      (e ↦ dihedral_swap_action_nontrivial H h n2 R hR e) ab

def dihedral_semidirect_not_abelian (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n2 : Not (SubgroupMember H (pos. two)))
  (ab : IsAbelian (semidirect_product (symmetric_group two) (dihedral_action_group H h))) : Empty
  ≔ dihedral_semidirect_not_abelian_at H h n2 (dihedral_rotation (shape (symmetric_group two)) H h s2c3_fin2_yes)
      (x ↦ dihedral_rotation_eval (shape (symmetric_group two)) H h s2c3_fin2_yes x) ab

def generalized_dihedral_not_abelian (n : Order) (n2 : Not (SubgroupMember (order_periods n) (pos. two)))
  (ab : IsAbelian (generalized_dihedral_group n)) : Empty
  ≔ dihedral_semidirect_not_abelian (order_periods n) (order_subgroup_laws n) n2 ab

{` Litmus: D_3 = Σ_2 ⋉ C̃_3 is not abelian; with dihedral_three_card it is a
   non-abelian group of order 6. D_3 is the instance h = order_subgroup_laws
   (principal_order 3) of the statement below, which holds for every witness h
   of the (propositional) subgroup laws of 3Z. It is stated for all h and wrapped
   in a one-field record because instantiating at the concrete laws proof makes
   Narya's conversion check run for more than 15 minutes. `}
def DihedralNotAbelian (H : Subtypes Int) : Type ≔ sig (
  not_abelian : (h : IntegerSubgroupLaws H)
    → Not (IsAbelian (semidirect_product (symmetric_group two) (dihedral_action_group H h))) )

def dihedral_not_abelian_record (H : Subtypes Int) (n2 : Not (SubgroupMember H (pos. two))) : DihedralNotAbelian H
  ≔ (not_abelian ≔ h ab ↦ dihedral_semidirect_not_abelian H h n2 ab)

def dihedral_three_not_abelian : DihedralNotAbelian dihedral_three_H
  ≔ dihedral_not_abelian_record dihedral_three_H (k ↦ dihedral_three_not_two k)
