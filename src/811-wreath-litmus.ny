export "810-wreath-products"
export "802-semidirect-symmetries"
export "505-gset-core-litmus"
export "412-symmetric-group-two"

{` Litmus for wreath products: Σ_2 ≀ Σ_2 via the standard Σ_2-set (the
   symmetry group of the square, order 2 · 2² = 8): its symmetries are in
   bijection with Fin 2 × (Fin 2 → Fin 2), via the semidirect bijection
   USym(G ⋉ H) ≃ USym G × USym H(sh_G) and H^X(sh_G) = Σ_2^{Fin 2}. `}

def wreath_square_group : Group
  ≔ wreath_product (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)

def wreath_square_acted_on_usym_equiv
  : Equiv (USym (wreath_power_action (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)
      (shape (symmetric_group two))))
      (Fin two → USym (symmetric_group two))
  ≔ compose_equiv
      (USym (wreath_power_action (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)
        (shape (symmetric_group two))))
      (USym (power_group (Fin two) (fin_is_finite two) (symmetric_group two)))
      (Fin two → USym (symmetric_group two))
      (id_to_equiv
        (USym (wreath_power_action (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)
          (shape (symmetric_group two))))
        (USym (power_group (Fin two) (fin_is_finite two) (symmetric_group two)))
        (refl USym (wreath_acted_on_group (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)
          (fin_is_finite two))))
      (power_group_usym_equiv (Fin two) (fin_is_finite two) (symmetric_group two))

def wreath_square_usym_equiv : Equiv (USym wreath_square_group) (Product (Fin two) (Fin two → Fin two))
  ≔ let G ≔ symmetric_group two in
    let Hx ≔ wreath_power_action G G (standard_symmetric_gset two) in
    compose_equiv (USym wreath_square_group) (Product (USym G) (USym (Hx (shape G))))
      (Product (Fin two) (Fin two → Fin two))
      (semidirect_usym_equiv G Hx)
      (product_equiv (USym G) (USym (Hx (shape G))) (Fin two) (Fin two → Fin two)
        sigma2_usym_equiv
        (compose_equiv (USym (Hx (shape G))) (Fin two → USym G) (Fin two → Fin two)
          wreath_square_acted_on_usym_equiv
          (pi_family_equiv (Fin two) (_ ↦ USym G) (_ ↦ Fin two) (_ ↦ sigma2_usym_equiv))))
