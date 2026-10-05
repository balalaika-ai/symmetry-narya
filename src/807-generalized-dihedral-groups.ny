export "806-dihedral-cycle-identification"
export "802-semidirect-symmetries"

{` Chapter 8, def:gen-dihedral (congp.tex:90) and the claim before it ("thus,
   we've constructed an action of Σ_2 on C_n").

   C̃_n(S) ≔ Aut_{T_S}(X, f) with T_S = Σ_{X:Set} (S → (X → X)) (module 568's
   S2C3Type, as in ex:S2-acts-on-C3) and (X, f) the bidirectional cycle of
   modules 805-806; D_n ≔ Σ_2 ⋉ C̃_n (semidirect_product of module 800).
   C_n for an order n is Aut_Cyc(Z/~_n, succ) =
   automorphism_group Cycles cycles_groupoid (standard_cycle n).

   C̃_n(S) = C_n for every 2-element set S and s : S (dihedral_action_cyclic_path):
   T_S ⊇ {(X,f) | f_{s̄} is a two-sided inverse of f_s} ≃ Permutations,
   (X,f) ↦ (X, f_s), followed by the identification of (X, f_s) with the
   standard n-cycle (dihedral_cycle_path). At the base point S = Fin 2 this
   says that C̃_n is an action of Σ_2 on C_n. `}

{` Permutations is a groupoid. Module 417 (permutations_groupoid) is not
   imported: with the pinned Narya, loading 417 here raised an internal anomaly
   (Meta.Map.find_opt), so the same one-line proof is repeated here. `}
def dihedral_permutations_groupoid : isGroupoid Permutations
  ≔ hlevel_to_groupoid Permutations
      (hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes (S ↦ Equiv (S .fst) (S .fst))
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (S ↦ x y ↦ set_to_hlevel_two (Id (Equiv (S .fst) (S .fst)) x y)
          (prop_is_set (Id (Equiv (S .fst) (S .fst)) x y) (equivalences_set (S .fst) (S .fst) (S .snd) x y))))

def dihedral_action_group (H : Subtypes Int) (h : IntegerSubgroupLaws H) (S : TwoElementSets) : Group
  ≔ automorphism_group (S2C3Type S) (s2c3_type_groupoid S) (dihedral_point S H h)

{` C_n for an order n (the book's Aut_Cyc of the standard n-cycle). `}
def order_cyclic_group (n : Order) : Group ≔ automorphism_group Cycles cycles_groupoid (standard_cycle n)

{` C̃_n : BΣ_2 → Group. `}
def dihedral_order_action (n : Order) (S : TwoElementSets) : Group
  ≔ dihedral_action_group (order_periods n) (order_subgroup_laws n) S

{` def:gen-dihedral: D_n ≔ Σ_2 ⋉ C̃_n. `}
def generalized_dihedral_group (n : Order) : Group
  ≔ semidirect_product (symmetric_group two) (dihedral_order_action n)

{` f_{s̄} is a two-sided inverse of f_s. `}
def DihedralInversePair (S : TwoElementSets) (s : two_set_carrier S) (t : S2C3Type S) : Type
  ≔ Product ((x : t .fst .fst) → Id (t .fst .fst) (t .snd (two_set_swap S s) (t .snd s x)) x)
            ((x : t .fst .fst) → Id (t .fst .fst) (t .snd s (t .snd (two_set_swap S s) x)) x)

def dihedral_inverse_pair_prop (S : TwoElementSets) (s : two_set_carrier S) (t : S2C3Type S)
  : isProp (DihedralInversePair S s t)
  ≔ product_prop ((x : t .fst .fst) → Id (t .fst .fst) (t .snd (two_set_swap S s) (t .snd s x)) x)
      ((x : t .fst .fst) → Id (t .fst .fst) (t .snd s (t .snd (two_set_swap S s) x)) x)
      (pi_prop (t .fst .fst) (x ↦ Id (t .fst .fst) (t .snd (two_set_swap S s) (t .snd s x)) x)
        (x ↦ t .fst .snd (t .snd (two_set_swap S s) (t .snd s x)) x))
      (pi_prop (t .fst .fst) (x ↦ Id (t .fst .fst) (t .snd s (t .snd (two_set_swap S s) x)) x)
        (x ↦ t .fst .snd (t .snd s (t .snd (two_set_swap S s) x)) x))

def DihedralInverseTypes (S : TwoElementSets) (s : two_set_carrier S) : Type
  ≔ Σ (S2C3Type S) (DihedralInversePair S s)

def dihedral_inverse_types_groupoid (S : TwoElementSets) (s : two_set_carrier S)
  : isGroupoid (DihedralInverseTypes S s)
  ≔ hlevel_to_groupoid (DihedralInverseTypes S s)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (S2C3Type S) (DihedralInversePair S s)
        (groupoid_to_hlevel (S2C3Type S) (s2c3_type_groupoid S))
        (t ↦ hlevel_raise (suc. (suc. zero.)) (DihedralInversePair S s t)
          (hlevel_raise (suc. zero.) (DihedralInversePair S s t)
            (prop_to_hlevel_one (DihedralInversePair S s t) (dihedral_inverse_pair_prop S s t)))))

def dihedral_to_permutation (S : TwoElementSets) (s : two_set_carrier S) (u : DihedralInverseTypes S s) : Permutations
  ≔ (u .fst .fst, quasi_inverse_equiv (u .fst .fst .fst) (u .fst .fst .fst) (u .fst .snd s) (u .fst .snd (two_set_swap S s))
       (u .snd .fst) (u .snd .snd))

{` The family t ↦ (a if t = s, b otherwise). `}
def dihedral_extend (A X : Type) (s t : A) (a b : X → X) (d : Decidable (Id A t s)) : X → X
  ≔ match d [ inl. _ ↦ a | inr. _ ↦ b ]

def dihedral_extend_map (S : TwoElementSets) (s : two_set_carrier S) (X : Type) (a b : X → X)
  : two_set_carrier S → X → X
  ≔ t ↦ dihedral_extend (two_set_carrier S) X s t a b (two_set_decidable S t s)

def dihedral_extend_self (S : TwoElementSets) (s : two_set_carrier S) (X : Type) (a b : X → X)
  : Id (X → X) (dihedral_extend_map S s X a b s) a
  ≔ refl ((d ↦ dihedral_extend (two_set_carrier S) X s s a b d) : Decidable (Id (two_set_carrier S) s s) → X → X)
      (dihedral_decidable_prop (Id (two_set_carrier S) s s) (S .fst .snd s s) (two_set_decidable S s s) (inl. (refl s)))

def dihedral_extend_swap (S : TwoElementSets) (s : two_set_carrier S) (X : Type) (a b : X → X)
  : Id (X → X) (dihedral_extend_map S s X a b (two_set_swap S s)) b
  ≔ refl ((d ↦ dihedral_extend (two_set_carrier S) X s (two_set_swap S s) a b d)
          : Decidable (Id (two_set_carrier S) (two_set_swap S s) s) → X → X)
      (dihedral_decidable_prop (Id (two_set_carrier S) (two_set_swap S s) s) (S .fst .snd (two_set_swap S s) s)
        (two_set_decidable S (two_set_swap S s) s) (inr. (two_set_swap_ne S s)))

def dihedral_from_permutation_map (S : TwoElementSets) (s : two_set_carrier S) (p : Permutations)
  : two_set_carrier S → p .fst .fst → p .fst .fst
  ≔ dihedral_extend_map S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd))

def dihedral_from_permutation_left (S : TwoElementSets) (s : two_set_carrier S) (p : Permutations) (x : p .fst .fst)
  : Id (p .fst .fst) (dihedral_from_permutation_map S s p (two_set_swap S s) (dihedral_from_permutation_map S s p s x)) x
  ≔ calc
      dihedral_from_permutation_map S s p (two_set_swap S s) (dihedral_from_permutation_map S s p s x)
        = equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd) (dihedral_from_permutation_map S s p s x)
        by dihedral_extend_swap S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd))
             (refl (dihedral_from_permutation_map S s p s x))
      = equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd) (p .snd .map x)
        by refl (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd))
             (dihedral_extend_self S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd)) (refl x))
      = x by equiv_retraction (p .fst .fst) (p .fst .fst) (p .snd) x ∎

def dihedral_from_permutation_right (S : TwoElementSets) (s : two_set_carrier S) (p : Permutations) (x : p .fst .fst)
  : Id (p .fst .fst) (dihedral_from_permutation_map S s p s (dihedral_from_permutation_map S s p (two_set_swap S s) x)) x
  ≔ calc
      dihedral_from_permutation_map S s p s (dihedral_from_permutation_map S s p (two_set_swap S s) x)
        = p .snd .map (dihedral_from_permutation_map S s p (two_set_swap S s) x)
        by dihedral_extend_self S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd))
             (refl (dihedral_from_permutation_map S s p (two_set_swap S s) x))
      = p .snd .map (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd) x)
        by refl (p .snd .map)
             (dihedral_extend_swap S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd)) (refl x))
      = x by equiv_counit (p .fst .fst) (p .fst .fst) (p .snd) x ∎

def dihedral_from_permutation (S : TwoElementSets) (s : two_set_carrier S) (p : Permutations) : DihedralInverseTypes S s
  ≔ ((p .fst, dihedral_from_permutation_map S s p),
     (x ↦ dihedral_from_permutation_left S s p x, x ↦ dihedral_from_permutation_right S s p x))

def dihedral_permutation_roundtrip (S : TwoElementSets) (s : two_set_carrier S) (p : Permutations)
  : Id Permutations (dihedral_to_permutation S s (dihedral_from_permutation S s p)) p
  ≔ (refl (p .fst),
     equiv_path (p .fst .fst) (p .fst .fst) (dihedral_to_permutation S s (dihedral_from_permutation S s p) .snd) (p .snd)
       (dihedral_extend_self S s (p .fst .fst) (p .snd .map) (equiv_inverse_map (p .fst .fst) (p .fst .fst) (p .snd))))

{` The inverse map of a quasi-inverse equivalence is the given inverse. `}
def dihedral_inverse_map_unique (X : Type) (f g : X → X) (l : (x : X) → Id X (g (f x)) x) (r : (x : X) → Id X (f (g x)) x)
  (x : X) : Id X (equiv_inverse_map X X (quasi_inverse_equiv X X f g l r) x) (g x)
  ≔ let e : Equiv X X ≔ quasi_inverse_equiv X X f g l r in
    let y : X ≔ equiv_inverse_map X X e x in
    calc
      y = g (f y) by inverse X (g (f y)) y (l y)
      = g x by refl g (equiv_counit X X e x) ∎

def dihedral_extend_agree (S : TwoElementSets) (s : two_set_carrier S) (X : Type) (f : two_set_carrier S → X → X)
  (b : X → X) (hb : Id (X → X) b (f (two_set_swap S s))) (t : two_set_carrier S) (d : Decidable (Id (two_set_carrier S) t s))
  : Id (X → X) (dihedral_extend (two_set_carrier S) X s t (f s) b d) (f t)
  ≔ match d [
  | inl. p ↦ refl f (inverse (two_set_carrier S) t s p)
  | inr. n ↦ concat (X → X) b (f (two_set_swap S s)) (f t) hb
      (refl f (inverse (two_set_carrier S) t (two_set_swap S s) (two_set_other_is_swap S s t n))) ]

def dihedral_types_roundtrip (S : TwoElementSets) (s : two_set_carrier S) (u : DihedralInverseTypes S s)
  : Id (DihedralInverseTypes S s) (dihedral_from_permutation S s (dihedral_to_permutation S s u)) u
  ≔ let X : Type ≔ u .fst .fst .fst in
    let f : two_set_carrier S → X → X ≔ u .fst .snd in
    let b : X → X ≔ equiv_inverse_map X X (dihedral_to_permutation S s u .snd) in
    subtype_equal (S2C3Type S) (DihedralInversePair S s) (dihedral_inverse_pair_prop S s)
      (dihedral_from_permutation S s (dihedral_to_permutation S s u)) u
      (refl (u .fst .fst),
       funext (two_set_carrier S) (_ ↦ X → X) (dihedral_extend_map S s X (f s) b) f
         (t ↦ dihedral_extend_agree S s X f b
           (funext X (_ ↦ X) b (f (two_set_swap S s))
             (x ↦ dihedral_inverse_map_unique X (f s) (f (two_set_swap S s)) (u .snd .fst) (u .snd .snd) x))
           t (two_set_decidable S t s)))

def dihedral_permutation_types_equiv (S : TwoElementSets) (s : two_set_carrier S)
  : Equiv (DihedralInverseTypes S s) Permutations
  ≔ quasi_inverse_equiv (DihedralInverseTypes S s) Permutations
      (dihedral_to_permutation S s) (dihedral_from_permutation S s)
      (dihedral_types_roundtrip S s) (dihedral_permutation_roundtrip S s)

{` The point (X, f) satisfies the inverse-pair condition. `}
def dihedral_point_inverse_at (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (z : Int) (d1 : Decidable (Id (two_set_carrier S) s' s)) (d2 : Decidable (Id (two_set_carrier S) s' (two_set_swap S s)))
  : Id (DihedralCycleSet S H h)
      (dihedral_class S H h s' (dihedral_step (two_set_carrier S) (two_set_swap S s) s' d2
        (dihedral_step (two_set_carrier S) s s' d1 z)))
      (dihedral_class S H h s' z)
  ≔ match d1, d2 [
  | inl. p, inl. q ↦ match two_set_swap_ne S s (concat (two_set_carrier S) (two_set_swap S s) s' s
        (inverse (two_set_carrier S) s' (two_set_swap S s) q) p) []
  | inl. _, inr. _ ↦ refl (dihedral_class S H h s') (int_pred_succ z)
  | inr. _, inl. _ ↦ refl (dihedral_class S H h s') (int_succ_pred z)
  | inr. n, inr. m ↦ match m (two_set_other_is_swap S s s' n) [] ]

def dihedral_point_inverse_at_other (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (z : Int) (d1 : Decidable (Id (two_set_carrier S) s' s)) (d2 : Decidable (Id (two_set_carrier S) s' (two_set_swap S s)))
  : Id (DihedralCycleSet S H h)
      (dihedral_class S H h s' (dihedral_step (two_set_carrier S) s s' d1
        (dihedral_step (two_set_carrier S) (two_set_swap S s) s' d2 z)))
      (dihedral_class S H h s' z)
  ≔ match d1, d2 [
  | inl. p, inl. q ↦ match two_set_swap_ne S s (concat (two_set_carrier S) (two_set_swap S s) s' s
        (inverse (two_set_carrier S) s' (two_set_swap S s) q) p) []
  | inl. _, inr. _ ↦ refl (dihedral_class S H h s') (int_succ_pred z)
  | inr. _, inl. _ ↦ refl (dihedral_class S H h s') (int_pred_succ z)
  | inr. n, inr. m ↦ match m (two_set_other_is_swap S s s' n) [] ]

def dihedral_point_inverse_pair (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : DihedralInversePair S s (dihedral_point S H h)
  ≔ (x ↦ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
         (x ↦ Id (DihedralCycleSet S H h) (dihedral_move S H h (two_set_swap S s) (dihedral_move S H h s x)) x)
         (x ↦ dihedral_cycle_set_set S H h (dihedral_move S H h (two_set_swap S s) (dihedral_move S H h s x)) x)
         (u ↦ dihedral_point_inverse_at S H h s (u .fst) (u .snd)
           (two_set_decidable S (u .fst) s) (two_set_decidable S (u .fst) (two_set_swap S s))) x,
     x ↦ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
         (x ↦ Id (DihedralCycleSet S H h) (dihedral_move S H h s (dihedral_move S H h (two_set_swap S s) x)) x)
         (x ↦ dihedral_cycle_set_set S H h (dihedral_move S H h s (dihedral_move S H h (two_set_swap S s) x)) x)
         (u ↦ dihedral_point_inverse_at_other S H h s (u .fst) (u .snd)
           (two_set_decidable S (u .fst) s) (two_set_decidable S (u .fst) (two_set_swap S s))) x)

def dihedral_point_permutation_path (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Id Permutations
      (dihedral_permutation_types_equiv S s .map (dihedral_point S H h, dihedral_point_inverse_pair S H h s))
      (dihedral_permutation S H h s)
  ≔ (refl (dihedral_cycle_set S H h),
     equiv_path (DihedralCycleSet S H h) (DihedralCycleSet S H h)
       (dihedral_permutation_types_equiv S s .map (dihedral_point S H h, dihedral_point_inverse_pair S H h s) .snd)
       (dihedral_move_equiv S H h s) (refl (dihedral_move S H h s)))

{` C̃_n(S) = C_n for every 2-element set S with a chosen s : S. `}
def dihedral_action_cyclic_path (H : Subtypes Int) (h : IntegerSubgroupLaws H) (S : TwoElementSets) (s : two_set_carrier S)
  : Id Group (dihedral_action_group H h S) (automorphism_group Cycles cycles_groupoid (subgroup_cycle H h))
  ≔ let u : DihedralInverseTypes S s ≔ (dihedral_point S H h, dihedral_point_inverse_pair S H h s) in
    let G0 : Group ≔ dihedral_action_group H h S in
    let G1 : Group ≔ automorphism_group (DihedralInverseTypes S s) (dihedral_inverse_types_groupoid S s) u in
    let G2 : Group ≔ automorphism_group Permutations dihedral_permutations_groupoid (dihedral_permutation_types_equiv S s .map u) in
    let G3 : Group ≔ automorphism_group Permutations dihedral_permutations_groupoid (dihedral_permutation S H h s) in
    let G4 : Group ≔ automorphism_group Cycles cycles_groupoid (dihedral_cycle S H h s) in
    let G5 : Group ≔ automorphism_group Cycles cycles_groupoid (subgroup_cycle H h) in
    calc
      G0 = G1 by inverse Group G1 G0
                  (automorphism_group_subtype_path (S2C3Type S) (DihedralInversePair S s) (dihedral_inverse_pair_prop S s)
                    (dihedral_inverse_types_groupoid S s) (s2c3_type_groupoid S) u)
      = G2 by automorphism_group_equiv_path (DihedralInverseTypes S s) Permutations (dihedral_inverse_types_groupoid S s)
                dihedral_permutations_groupoid (dihedral_permutation_types_equiv S s) u
      = G3 by automorphism_group_point_path Permutations dihedral_permutations_groupoid
                (dihedral_permutation_types_equiv S s .map u) (dihedral_permutation S H h s)
                (dihedral_point_permutation_path S H h s)
      = G4 by inverse Group G4 G3 (automorphism_group_subtype_path Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd))
                cycles_groupoid dihedral_permutations_groupoid (dihedral_cycle S H h s))
      = G5 by automorphism_group_point_path Cycles cycles_groupoid (dihedral_cycle S H h s) (subgroup_cycle H h)
                (dihedral_cycle_path S H h s) ∎

{` "Thus, we've constructed an action of Σ_2 on C_n": C̃_n(sh_{Σ_2}) = C_n. `}
def dihedral_order_action_shape_path (n : Order)
  : Id Group (dihedral_order_action n (shape (symmetric_group two))) (order_cyclic_group n)
  ≔ dihedral_action_cyclic_path (order_periods n) (order_subgroup_laws n) (shape (symmetric_group two)) s2c3_fin2_yes

{` USym D_n ≃ USym Σ_2 × USym C_n. `}
def generalized_dihedral_usym_equiv (n : Order)
  : Equiv (USym (generalized_dihedral_group n)) (Product (USym (symmetric_group two)) (USym (order_cyclic_group n)))
  ≔ compose_equiv (USym (generalized_dihedral_group n))
      (Product (USym (symmetric_group two)) (USym (dihedral_order_action n (shape (symmetric_group two)))))
      (Product (USym (symmetric_group two)) (USym (order_cyclic_group n)))
      (semidirect_usym_equiv (symmetric_group two) (dihedral_order_action n))
      (id_to_equiv (Product (USym (symmetric_group two)) (USym (dihedral_order_action n (shape (symmetric_group two)))))
        (Product (USym (symmetric_group two)) (USym (order_cyclic_group n)))
        (refl ((G ↦ Product (USym (symmetric_group two)) (USym G)) : Group → Type) (dihedral_order_action_shape_path n)))
