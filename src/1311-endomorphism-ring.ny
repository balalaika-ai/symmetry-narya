export "1310-integer-ring"
export "430-pointwise-abstract-groups"

{` Chapter 13 (fields.tex), running text of sec:rings (line 28): "Note
   that multiplication in a ring need not be commutative." Witness: the
   endomorphism ring End(A) of an abelian abstract group A, with additive
   group absHom_ptw(A, A) (abstract_hom_ptw_group, module 1300),
   multiplication f · g = f ∘ g (g first) and unit the identity; its
   multiplicative monoid is abstract_endo_monoid A of module 701. For
   A = ℤ^Bool (≅ ℤ × ℤ, pointwise_abstract_group of module 430) the swap
   s(u) = u ∘ not and the constant projection c(u) = (_ ↦ u(true)) do not
   commute: (s · c)(u) = (_ ↦ u(true)) but (c · s)(u) = (_ ↦ u(false)). `}

def endo_ring_distr (A : AbstractGroup) (hab : IsAbstractAbelian A)
  : DistrLaws (AbstractHom A A) (abstract_endo_monoid A .mul) (ptw_mul_hom A A hab)
  ≔ (f g h ↦ abstract_hom_ext A A
       (abstract_endo_monoid A .mul f (ptw_mul_hom A A hab g h))
       (ptw_mul_hom A A hab (abstract_endo_monoid A .mul f g) (abstract_endo_monoid A .mul f h))
       (t ↦ f .snd (g .fst t) (h .fst t)),
     f g h ↦ abstract_hom_ext A A
       (abstract_endo_monoid A .mul (ptw_mul_hom A A hab f g) h)
       (ptw_mul_hom A A hab (abstract_endo_monoid A .mul f h) (abstract_endo_monoid A .mul g h))
       (t ↦ refl (A .mul (f .fst (h .fst t)) (g .fst (h .fst t)))))

{` End(A) = (absHom(A, A), 0, +, -, id, ∘). `}
def endomorphism_ring (A : AbstractGroup) (hab : IsAbstractAbelian A) : AbstractRing
  ≔ (AbstractHom A A, ptw_unit_hom A A, ptw_mul_hom A A hab, ptw_inv_hom A A hab,
     abstract_hom_ptw_group_laws A A hab, abstract_hom_id A, abstract_endo_monoid A .mul,
     abstract_endo_monoid A .laws, endo_ring_distr A hab)

{` Litmus: the multiplication is composition (f first applied second) and
   the addition is pointwise, judgmentally. `}
def endomorphism_ring_mul_apply (A : AbstractGroup) (hab : IsAbstractAbelian A) (f g : AbstractHom A A)
  (t : A .carrier)
  : Id (A .carrier) (endomorphism_ring A hab .mul f g .fst t) (f .fst (g .fst t))
  ≔ refl (f .fst (g .fst t))

def endomorphism_ring_add_apply (A : AbstractGroup) (hab : IsAbstractAbelian A) (f g : AbstractHom A A)
  (t : A .carrier)
  : Id (A .carrier) (endomorphism_ring A hab .add f g .fst t) (A .mul (f .fst t) (g .fst t))
  ≔ refl (A .mul (f .fst t) (g .fst t))

{` The abelian group ℤ^Bool ≅ ℤ × ℤ. `}
def int_pair_group : AbstractGroup ≔ pointwise_abstract_group int_add_abstract_group Bool

def int_pair_group_abelian : IsAbstractAbelian int_pair_group
  ≔ pointwise_abelian int_add_abstract_group Bool int_add_comm

def int_pair_endo_ring : AbstractRing ≔ endomorphism_ring int_pair_group int_pair_group_abelian

def int_pair_swap : AbstractHom int_pair_group int_pair_group
  ≔ (u b ↦ u (bool_not b), u v ↦ refl (pointwise_mul int_add_abstract_group Bool (b ↦ u (bool_not b)) (b ↦ v (bool_not b))))

def int_pair_const_true : AbstractHom int_pair_group int_pair_group
  ≔ (u _ ↦ u true., u v ↦ refl (pointwise_mul int_add_abstract_group Bool (_ ↦ u true.) (_ ↦ v true.)))

def int_pair_indicator : Bool → Int ≔ [ true. ↦ int_one | false. ↦ int_zero ]

{` s · c ≠ c · s: evaluating both at the indicator of true and at false
   gives 1 = 0 in ℤ. `}
def int_pair_endo_noncommuting
  : Not (Id (AbstractHom int_pair_group int_pair_group)
      (int_pair_endo_ring .mul int_pair_swap int_pair_const_true)
      (int_pair_endo_ring .mul int_pair_const_true int_pair_swap))
  ≔ p ↦ int_encode int_one int_zero
      (refl ((φ ↦ φ .fst int_pair_indicator false.) : AbstractHom int_pair_group int_pair_group → Int) p)

def int_pair_endo_ring_not_commutative : Not (IsCommutativeRing int_pair_endo_ring)
  ≔ h ↦ int_pair_endo_noncommuting (h int_pair_swap int_pair_const_true)

def int_pair_endo_ring_non_trivial : IsNonTrivialRing int_pair_endo_ring
  ≔ p ↦ int_encode int_zero int_one
      (refl ((φ ↦ φ .fst int_pair_indicator true.) : AbstractHom int_pair_group int_pair_group → Int) p)
