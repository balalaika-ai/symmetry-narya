export "807-generalized-dihedral-groups"
export "412-symmetric-group-two"

{` Chapter 8 (congp.tex 100-102 and 190-192): "if n is finite, then D_n is a
   finite group of cardinality 2n".  A finite order is principal_order m with
   m ≥ 1 (principal cycle Z/m); we write m = k+1.  USym D_n ≃ USym Σ_2 × USym C_n
   (module 807); C_n is merely identified with C_{k+1} = cyclic_group_fin k
   (the standard cycle of the order merely equals the principal cycle,
   cycle_order_paths), so |USym D_n| = 2(k+1).  The book derives the count
   from con:bidirectional-bicycle and normality of the standard dihedral
   bicycles; here it is derived from the semidirect-product bijection. `}

def dihedral_cyclic_fin_mere_path (k : Nat)
  : Mere (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k))
  ≔ mere_rec (Id Cycles (principal_cycle (suc. k)) (standard_cycle (principal_order (suc. k))))
      (Mere (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k)))
      (mere_isprop (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k)))
      (p ↦ mere (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k))
        (concat Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group (suc. k)) (cyclic_group_fin k)
          (automorphism_group_point_path Cycles cycles_groupoid (standard_cycle (principal_order (suc. k)))
            (principal_cycle (suc. k))
            (inverse Cycles (principal_cycle (suc. k)) (standard_cycle (principal_order (suc. k))) p))
          (inverse Group (cyclic_group_fin k) (cyclic_group (suc. k)) (cyclic_group_fin_path k))))
      (cycle_order_paths (standard_cycle (principal_order (suc. k))) (principal_cycle (suc. k))
        (standard_cycle_order (principal_order (suc. k))))

def dihedral_finite_usym_equiv (k : Nat)
  (q : Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k))
  : Equiv (USym (generalized_dihedral_group (principal_order (suc. k)))) (Fin (mul two (suc. k)))
  ≔ compose_equiv (USym (generalized_dihedral_group (principal_order (suc. k))))
      (Product (USym (symmetric_group two)) (USym (order_cyclic_group (principal_order (suc. k)))))
      (Fin (mul two (suc. k)))
      (generalized_dihedral_usym_equiv (principal_order (suc. k)))
      (compose_equiv (Product (USym (symmetric_group two)) (USym (order_cyclic_group (principal_order (suc. k)))))
        (Product (USym (symmetric_group two)) (USym (cyclic_group_fin k)))
        (Fin (mul two (suc. k)))
        (id_to_equiv (Product (USym (symmetric_group two)) (USym (order_cyclic_group (principal_order (suc. k)))))
          (Product (USym (symmetric_group two)) (USym (cyclic_group_fin k)))
          (refl ((G ↦ Product (USym (symmetric_group two)) (USym G)) : Group → Type) q))
        (compose_equiv (Product (USym (symmetric_group two)) (USym (cyclic_group_fin k)))
          (Product (Fin two) (Fin (suc. k))) (Fin (mul two (suc. k)))
          (product_equiv (USym (symmetric_group two)) (USym (cyclic_group_fin k)) (Fin two) (Fin (suc. k))
            sigma2_usym_equiv (cyclic_group_fin_usym_equiv k))
          (fin_product_equiv two (suc. k))))

def generalized_dihedral_finite (k : Nat) : IsFiniteGroup (generalized_dihedral_group (principal_order (suc. k)))
  ≔ mere_rec (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k))
      (IsFiniteGroup (generalized_dihedral_group (principal_order (suc. k))))
      (is_finite_group_prop (generalized_dihedral_group (principal_order (suc. k))))
      (q ↦ mere (Σ Nat (m ↦ Id Type (USym (generalized_dihedral_group (principal_order (suc. k)))) (Fin m)))
        (mul two (suc. k), ua (USym (generalized_dihedral_group (principal_order (suc. k)))) (Fin (mul two (suc. k)))
          (dihedral_finite_usym_equiv k q)))
      (dihedral_cyclic_fin_mere_path k)

{` |D_n| = 2n for the finite order n = k+1. `}
def generalized_dihedral_card (k : Nat)
  : Id Nat (group_card (generalized_dihedral_group (principal_order (suc. k))) (generalized_dihedral_finite k))
      (mul two (suc. k))
  ≔ mere_rec (Id Group (order_cyclic_group (principal_order (suc. k))) (cyclic_group_fin k))
      (Id Nat (group_card (generalized_dihedral_group (principal_order (suc. k))) (generalized_dihedral_finite k))
        (mul two (suc. k)))
      (nat_set (group_card (generalized_dihedral_group (principal_order (suc. k))) (generalized_dihedral_finite k))
        (mul two (suc. k)))
      (q ↦ cardinality_from_path (USym (generalized_dihedral_group (principal_order (suc. k))))
        (generalized_dihedral_finite k) (mul two (suc. k))
        (ua (USym (generalized_dihedral_group (principal_order (suc. k)))) (Fin (mul two (suc. k)))
          (dihedral_finite_usym_equiv k q)))
      (dihedral_cyclic_fin_mere_path k)

{` Litmus: |D_3| = 6, |D_1| = 2. `}
def dihedral_three_card
  : Id Nat (group_card (generalized_dihedral_group (principal_order three)) (generalized_dihedral_finite two))
      (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ generalized_dihedral_card two

def dihedral_one_card
  : Id Nat (group_card (generalized_dihedral_group (principal_order (suc. zero.))) (generalized_dihedral_finite zero.))
      two
  ≔ generalized_dihedral_card zero.
