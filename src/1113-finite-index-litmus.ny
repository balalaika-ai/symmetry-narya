export "1110-finite-index"

{` Litmus: the trivial subgroup (principal torsor) of C_{n+1} has index n+1, and
   G itself (the trivial G-set Unit) has index 1. `}
def principal_gset_index_cyclic (n : Nat) : GSetHasIndex (cyclic_group_fin n) (principal_gset (cyclic_group_fin n)) (suc. n)
  ≔ gset_index_iff_shape (cyclic_group_fin n) (principal_gset (cyclic_group_fin n)) (suc. n) .snd
      (mere (Id Type (USym (cyclic_group_fin n)) (Fin (suc. n)))
        (ua (USym (cyclic_group_fin n)) (Fin (suc. n)) (cyclic_group_fin_usym_equiv n)))

def unit_set_type : SetTypes ≔ (Unit, unit_set)

def trivial_gset_index_one (G : Group) : GSetHasIndex G (gset_trivial G unit_set_type) (suc. zero.)
  ≔ _ ↦ mere (Id Type Unit (Fin (suc. zero.)))
      (ua Unit (Fin (suc. zero.)) (quasi_inverse_equiv Unit (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ star.)
        (u ↦ match u [ star. ↦ refl (star. : Unit) ])
        (i ↦ match i [ inl. z ↦ match z [] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ])))
