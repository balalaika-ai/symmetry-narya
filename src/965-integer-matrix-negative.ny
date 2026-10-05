export "963-integer-matrix-example"
export "1010-usym-powers"

{` Chapter 9 (subgroups.tex 1186), the 1 × 1 case for negative m = −(n+1):
   multiplication by m is (multiplication by n+1) ∘ ι with ι the inversion
   loop ↦ loop⁻¹ of Z (an automorphism, ι ∘ ι = id); hence it is a
   monomorphism and its cokernel at the shape is Fin |m| = Fin (n+1). `}

def int_inversion_hom (C : CircleSignature) : GroupHom (circle_group C) (circle_group C)
  ≔ circle_multiplication_hom C (neg. zero.)

def int_inversion_loop (C : CircleSignature)
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (int_inversion_hom C) (C .loop))
      (usym_inv (circle_group C) (C .loop))
  ≔ concat (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (int_inversion_hom C) (C .loop))
      (circle_power C (neg. zero.)) (usym_inv (circle_group C) (C .loop))
      (circle_multiplication_loop C (neg. zero.))
      (concat_1p (C .carrier) (C .base) (C .base) (usym_inv (circle_group C) (C .loop)))

def int_inversion_involutive_usym (C : CircleSignature) (g : USym (circle_group C))
  : Id (USym (circle_group C))
      (usym_hom (circle_group C) (circle_group C) (int_inversion_hom C) (usym_hom (circle_group C) (circle_group C) (int_inversion_hom C) g)) g
  ≔ let Z ≔ circle_group C in let ι ≔ usym_hom Z Z (int_inversion_hom C) in
    happly (USym Z) (_ ↦ USym Z) (x ↦ ι (ι x)) (x ↦ x)
      (concat (USym Z → USym Z) (x ↦ ι (ι x)) (usym_hom Z Z (group_hom_id Z)) (x ↦ x)
        (concat (USym Z → USym Z) (x ↦ ι (ι x)) (usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)))
          (usym_hom Z Z (group_hom_id Z))
          (inverse (USym Z → USym Z) (usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C))) (x ↦ ι (ι x))
            (usym_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)))
          (refl ((h ↦ usym_hom Z Z h) : GroupHom Z Z → USym Z → USym Z)
            (pbg_circle_hom_ext C Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (group_hom_id Z)
              (calc
                usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (circle_group_loop C)
                = ι (ι (C .loop)) by happly (USym Z) (_ ↦ USym Z) (usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)))
                     (x ↦ ι (ι x)) (usym_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (C .loop)
                = ι (usym_inv Z (C .loop)) by refl ι (int_inversion_loop C)
                = usym_inv Z (ι (C .loop)) by usym_hom_inv Z Z (int_inversion_hom C) (C .loop)
                = usym_inv Z (usym_inv Z (C .loop)) by refl (usym_inv Z) (int_inversion_loop C)
                = C .loop by inverse_inverse (C .carrier) (C .base) (C .base) (C .loop)
                = usym_hom Z Z (group_hom_id Z) (circle_group_loop C)
                  by inverse (USym Z) (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop) (usym_hom_id Z (C .loop)) ∎))))
        (funext (USym Z) (_ ↦ USym Z) (usym_hom Z Z (group_hom_id Z)) (x ↦ x) (usym_hom_id Z))) g

{` The classifying map of ι is an equivalence (ι ∘ ι = id as homomorphisms). `}
def int_inversion_compose_id (C : CircleSignature)
  : Id (GroupHom (circle_group C) (circle_group C))
      (group_hom_compose (circle_group C) (circle_group C) (circle_group C) (int_inversion_hom C) (int_inversion_hom C))
      (group_hom_id (circle_group C))
  ≔ let Z ≔ circle_group C in
    pbg_circle_hom_ext C Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (group_hom_id Z)
      (concat (USym Z) (usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (C .loop))
        (usym_hom Z Z (int_inversion_hom C) (usym_hom Z Z (int_inversion_hom C) (C .loop))) (usym_hom Z Z (group_hom_id Z) (C .loop))
        (happly (USym Z) (_ ↦ USym Z) (usym_hom Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)))
          (x ↦ usym_hom Z Z (int_inversion_hom C) (usym_hom Z Z (int_inversion_hom C) x))
          (usym_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (C .loop))
        (concat (USym Z) (usym_hom Z Z (int_inversion_hom C) (usym_hom Z Z (int_inversion_hom C) (C .loop))) (C .loop)
          (usym_hom Z Z (group_hom_id Z) (C .loop))
          (int_inversion_involutive_usym C (C .loop))
          (inverse (USym Z) (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop) (usym_hom_id Z (C .loop)))))

def int_inversion_function_equiv (C : CircleSignature) : Equiv (C .carrier) (C .carrier)
  ≔ let Z ≔ circle_group C in let Bι ≔ hom_function Z Z (int_inversion_hom C) in
    let h ≔ happly (C .carrier) (_ ↦ C .carrier) (x ↦ Bι (Bι x)) (x ↦ x)
      (group_hom_function_path Z Z (group_hom_compose Z Z Z (int_inversion_hom C) (int_inversion_hom C)) (group_hom_id Z)
        (int_inversion_compose_id C)) in
    quasi_inverse_equiv (C .carrier) (C .carrier) Bι Bι h h

{` Multiplication by m = −(n+1). `}
def matrix1_neg_hom (C : CircleSignature) (n : Nat) : GroupHom (circle_group C) (circle_group C)
  ≔ group_hom_compose (circle_group C) (circle_group C) (circle_group C) (int_inversion_hom C) (matrix1_hom C n)

def matrix1_neg_hom_path (C : CircleSignature) (n : Nat)
  : Id (GroupHom (circle_group C) (circle_group C)) (matrix1_neg_hom C n) (circle_multiplication_hom C (neg. n))
  ≔ let Z ≔ circle_group C in let m ≔ usym_hom Z Z (matrix1_hom C n) in
    pbg_circle_hom_ext C Z (matrix1_neg_hom C n) (circle_multiplication_hom C (neg. n))
      (calc
        usym_hom Z Z (matrix1_neg_hom C n) (circle_group_loop C)
        = m (usym_hom Z Z (int_inversion_hom C) (C .loop))
          by happly (USym Z) (_ ↦ USym Z) (usym_hom Z Z (matrix1_neg_hom C n)) (x ↦ m (usym_hom Z Z (int_inversion_hom C) x))
               (usym_hom_compose Z Z Z (int_inversion_hom C) (matrix1_hom C n)) (C .loop)
        = m (usym_inv Z (C .loop)) by refl m (int_inversion_loop C)
        = usym_inv Z (m (C .loop)) by usym_hom_inv Z Z (matrix1_hom C n) (C .loop)
        = usym_inv Z (usym_power Z (C .loop) (suc. n)) by refl (usym_inv Z) (circle_multiplication_loop C (pos. (suc. n)))
        = usym_power Z (usym_inv Z (C .loop)) (suc. n)
          by inverse (USym Z) (usym_power Z (usym_inv Z (C .loop)) (suc. n)) (usym_inv Z (usym_power Z (C .loop) (suc. n)))
               (usym_power_inv Z (C .loop) (suc. n))
        = usym_hom Z Z (circle_multiplication_hom C (neg. n)) (circle_group_loop C)
          by inverse (USym Z) (usym_hom Z Z (circle_multiplication_hom C (neg. n)) (C .loop)) (usym_power Z (usym_inv Z (C .loop)) (suc. n))
               (circle_multiplication_loop C (neg. n)) ∎)

def matrix1_neg_hom_mono (C : CircleSignature) (n : Nat)
  : IsGroupMono (circle_group C) (circle_group C) (matrix1_neg_hom C n)
  ≔ let Z ≔ circle_group C in let ι ≔ usym_hom Z Z (int_inversion_hom C) in let m ≔ usym_hom Z Z (matrix1_hom C n) in
    path_reflecting_set_embedding (USym Z) (USym Z) (usym_set Z) (usym_hom Z Z (matrix1_neg_hom C n))
      (x y e ↦
        let e' : Id (USym Z) (m (ι x)) (m (ι y))
          ≔ concat (USym Z) (m (ι x)) (usym_hom Z Z (matrix1_neg_hom C n) x) (m (ι y))
              (inverse (USym Z) (usym_hom Z Z (matrix1_neg_hom C n) x) (m (ι x))
                (happly (USym Z) (_ ↦ USym Z) (usym_hom Z Z (matrix1_neg_hom C n)) (z ↦ m (ι z))
                  (usym_hom_compose Z Z Z (int_inversion_hom C) (matrix1_hom C n)) x))
              (concat (USym Z) (usym_hom Z Z (matrix1_neg_hom C n) x) (usym_hom Z Z (matrix1_neg_hom C n) y) (m (ι y)) e
                (happly (USym Z) (_ ↦ USym Z) (usym_hom Z Z (matrix1_neg_hom C n)) (z ↦ m (ι z))
                  (usym_hom_compose Z Z Z (int_inversion_hom C) (matrix1_hom C n)) y)) in
        let r : Id (USym Z) (ι x) (ι y) ≔ embedding_reflects_paths (USym Z) (USym Z) m (matrix1_mono C n) (ι x) (ι y) e' in
        calc
          x = ι (ι x) by inverse (USym Z) (ι (ι x)) x (int_inversion_involutive_usym C x)
          = ι (ι y) by refl ι r
          = y by int_inversion_involutive_usym C y ∎)

def matrix1_neg_mono (C : CircleSignature) (n : Nat)
  : IsGroupMono (circle_group C) (circle_group C) (circle_multiplication_hom C (neg. n))
  ≔ transport (GroupHom (circle_group C) (circle_group C)) (IsGroupMono (circle_group C) (circle_group C))
      (matrix1_neg_hom C n) (circle_multiplication_hom C (neg. n)) (matrix1_neg_hom_path C n) (matrix1_neg_hom_mono C n)

{` The cokernel at the shape: the fiber of B(m ∘ ι) = deg_{n+1} ∘ Bι is the
   fiber of deg_{n+1} (Bι an equivalence), i.e. Fin (n+1). `}
def matrix1_neg_hom_cokernel_card (C : CircleSignature) (n : Nat)
  : Equiv (gset_underlying (circle_group C) (cokernel (circle_group C) (circle_group C) (matrix1_neg_hom C n))) (Fin (suc. n))
  ≔ let Z ≔ circle_group C in
    let F ≔ HomFiber Z Z (matrix1_neg_hom C n) (shape Z) in
    let F1 ≔ HomFiber Z Z (matrix1_hom C n) (shape Z) in
    let e : Equiv F F1 ≔ preequivalence_fiber_equiv (C .carrier) (C .carrier) (C .carrier) (int_inversion_function_equiv C)
      (hom_function Z Z (matrix1_hom C n)) (shape Z) in
    let hF : isSet F ≔ hlevel_two_to_set F (hlevel_equiv (suc. (suc. zero.)) F1 F (canonical_inverse_equiv F F1 e)
      (set_to_hlevel_two F1 (matrix1_fiber_set C n))) in
    compose_equiv (SetTrunc F) F (Fin (suc. n)) (set_trunc_of_set_equiv F hF)
      (compose_equiv F F1 (Fin (suc. n)) e (canonical_inverse_equiv (Fin (suc. n)) F1 (matrix1_fiber_equiv C n)))

def matrix1_neg_cokernel_card (C : CircleSignature) (n : Nat)
  : Equiv (gset_underlying (circle_group C) (cokernel (circle_group C) (circle_group C) (circle_multiplication_hom C (neg. n)))) (Fin (suc. n))
  ≔ transport (GroupHom (circle_group C) (circle_group C))
      (h ↦ Equiv (gset_underlying (circle_group C) (cokernel (circle_group C) (circle_group C) h)) (Fin (suc. n)))
      (matrix1_neg_hom C n) (circle_multiplication_hom C (neg. n)) (matrix1_neg_hom_path C n) (matrix1_neg_hom_cokernel_card C n)
