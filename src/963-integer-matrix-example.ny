export "901-kernels-cokernels-images"
export "824-integer-intersection"
export "282-explicit-power-degree"

{` Chapter 9 (subgroups.tex 1186-1191), the example on integer matrices,
   for 1 × 1 matrices m (homomorphisms Z → Z, loop ↦ loop^m, with Z the
   circle group of an arbitrary circle C). Proved: m = n+1 > 0 gives a
   monomorphism whose cokernel coker(m)(sh) = ‖(Bm)⁻¹(base)‖₀ is a finite
   set with exactly m elements (Bm is the degree map, module 282); m = 0 is
   not a monomorphism (module 824). Not formalized: negative m (the same by
   composing with the inversion of Z), and n × n matrices with the
   determinant (Z^n and determinants are not available); the "picture" of
   coverings of tori and the nullspace/rowspace sentence are informal. `}

def matrix1_hom (C : CircleSignature) (n : Nat) : GroupHom (circle_group C) (circle_group C)
  ≔ circle_multiplication_hom C (pos. (suc. n))

def matrix1_mono (C : CircleSignature) (n : Nat)
  : IsGroupMono (circle_group C) (circle_group C) (matrix1_hom C n)
  ≔ circle_multiplication_mono C n

def matrix1_monomorphism (C : CircleSignature) (n : Nat)
  : IsGroupMonomorphism (circle_group C) (circle_group C) (matrix1_hom C n)
  ≔ usym_injective_group_mono (circle_group C) (circle_group C) (matrix1_hom C n) (matrix1_mono C n)

def matrix1_zero_not_mono (C : CircleSignature)
  (h : IsGroupMono (circle_group C) (circle_group C) (circle_multiplication_hom C (pos. zero.))) : Empty
  ≔ circle_multiplication_zero_not_mono C h

{` The fiber of Bm over the shape is Fin m, so the cokernel at the shape is
   a set with m elements. `}
def matrix1_fiber_equiv (C : CircleSignature) (n : Nat)
  : Equiv (Fin (suc. n)) (HomFiber (circle_group C) (circle_group C) (matrix1_hom C n) (shape (circle_group C)))
  ≔ power_degree_explicit_fiber_equiv C n

def matrix1_fiber_set (C : CircleSignature) (n : Nat)
  : isSet (HomFiber (circle_group C) (circle_group C) (matrix1_hom C n) (shape (circle_group C)))
  ≔ hlevel_two_to_set (HomFiber (circle_group C) (circle_group C) (matrix1_hom C n) (shape (circle_group C)))
      (hlevel_equiv (suc. (suc. zero.)) (Fin (suc. n)) (HomFiber (circle_group C) (circle_group C) (matrix1_hom C n) (shape (circle_group C)))
        (matrix1_fiber_equiv C n) (set_to_hlevel_two (Fin (suc. n)) (fin_set (suc. n))))

def matrix1_cokernel_card (C : CircleSignature) (n : Nat)
  : Equiv (gset_underlying (circle_group C) (cokernel (circle_group C) (circle_group C) (matrix1_hom C n))) (Fin (suc. n))
  ≔ let F ≔ HomFiber (circle_group C) (circle_group C) (matrix1_hom C n) (shape (circle_group C)) in
    compose_equiv (SetTrunc F) F (Fin (suc. n)) (set_trunc_of_set_equiv F (matrix1_fiber_set C n))
      (canonical_inverse_equiv (Fin (suc. n)) F (matrix1_fiber_equiv C n))
