export "1051-order-p-subgroup-count"

{` Chapter 10, the example at fingp.tex 27-33: "when n > 5 ...
   the subgroups of order 3 are no longer all conjugate".

   For n = m + 6 (Fin n has the six outer points 0, ..., 5 and the inner
   copy of Fin m), c = (0 1 2) and d = (0 1 2)(3 4 5) generate subgroups of
   order 3 of Σ_n that are not conjugate (sigma_n_order_three_not_conjugate):
   a conjugate g c g⁻¹ moves exactly as many points as c (3), while every
   element ≠ e of ⟨d⟩ is d or d², which move 6 points. The number of moved
   points is the cardinality of MovedPoints, computed by explicit
   equivalences with Fin 3 and Fin 6 (the inner points are fixed). `}

def MovedPoints (A : Type) (f : A → A) : Type ≔ Σ A (x ↦ Not (Id A (f x) x))

def moved_points_pointwise (A : Type) (f f' : A → A) (h : (x : A) → Id A (f x) (f' x))
  : Equiv (MovedPoints A f) (MovedPoints A f')
  ≔ family_equiv A (x ↦ Not (Id A (f x) x)) (x ↦ Not (Id A (f' x) x))
      (x ↦ iff_equiv (Not (Id A (f x) x)) (Not (Id A (f' x) x)) (negation_prop (Id A (f x) x)) (negation_prop (Id A (f' x) x))
        (n e ↦ n (concat A (f x) (f' x) x (h x) e))
        (n e ↦ n (concat A (f' x) (f x) x (inverse A (f x) (f' x) (h x)) e)))

{` Permutation actions: g⁻¹ undoes g, and conjugates move as many points. `}
def perm_action_inv_left (S : SetTypes) (g : USym (permutation_group S)) (y : S .fst)
  : Id (S .fst) (permutation_action S (usym_inv (permutation_group S) g) (permutation_action S g y)) y
  ≔ let G ≔ permutation_group S in
    calc
      permutation_action S (usym_inv G g) (permutation_action S g y)
      = permutation_action S (usym_mul G (usym_inv G g) g) y
        by inverse (S .fst) (permutation_action S (usym_mul G (usym_inv G g) g) y)
             (permutation_action S (usym_inv G g) (permutation_action S g y)) (permutation_action_mul S (usym_inv G g) g y)
      = permutation_action S (usym_unit G) y
        by refl ((s ↦ permutation_action S s y) : USym G → S .fst) (concat_inverse_right (BG G .carrier) (shape G) (shape G) g)
      = y by permutation_action_unit S y ∎

def perm_action_inv_right (S : SetTypes) (g : USym (permutation_group S)) (y : S .fst)
  : Id (S .fst) (permutation_action S g (permutation_action S (usym_inv (permutation_group S) g) y)) y
  ≔ let G ≔ permutation_group S in
    calc
      permutation_action S g (permutation_action S (usym_inv G g) y)
      = permutation_action S (usym_mul G g (usym_inv G g)) y
        by inverse (S .fst) (permutation_action S (usym_mul G g (usym_inv G g)) y)
             (permutation_action S g (permutation_action S (usym_inv G g) y)) (permutation_action_mul S g (usym_inv G g) y)
      = permutation_action S (usym_unit G) y
        by refl ((s ↦ permutation_action S s y) : USym G → S .fst) (concat_inverse_left (BG G .carrier) (shape G) (shape G) g)
      = y by permutation_action_unit S y ∎

def perm_conjugate (S : SetTypes) (g t : USym (permutation_group S)) : USym (permutation_group S)
  ≔ usym_mul (permutation_group S) g (usym_mul (permutation_group S) t (usym_inv (permutation_group S) g))

def perm_conjugate_action (S : SetTypes) (g t : USym (permutation_group S)) (z : S .fst)
  : Id (S .fst) (permutation_action S (perm_conjugate S g t) z)
      (permutation_action S g (permutation_action S t (permutation_action S (usym_inv (permutation_group S) g) z)))
  ≔ let G ≔ permutation_group S in let gi ≔ usym_inv G g in
    concat (S .fst) (permutation_action S (perm_conjugate S g t) z)
      (permutation_action S g (permutation_action S (usym_mul G t gi) z))
      (permutation_action S g (permutation_action S t (permutation_action S gi z)))
      (permutation_action_mul S g (usym_mul G t gi) z)
      (refl (permutation_action S g) (permutation_action_mul S t gi z))

def perm_conjugate_moved_equiv (S : SetTypes) (g t : USym (permutation_group S))
  : Equiv (MovedPoints (S .fst) (permutation_action S t)) (MovedPoints (S .fst) (permutation_action S (perm_conjugate S g t)))
  ≔ let G ≔ permutation_group S in let gi ≔ usym_inv G g in
    let X ≔ S .fst in
    let a ≔ permutation_action S in
    let tc ≔ perm_conjugate S g t in
    let fwd : MovedPoints X (a t) → MovedPoints X (a tc)
      ≔ u ↦ (a g (u .fst), q ↦ u .snd
          (calc
            a t (u .fst)
            = a gi (a g (a t (u .fst))) by inverse X (a gi (a g (a t (u .fst)))) (a t (u .fst)) (perm_action_inv_left S g (a t (u .fst)))
            = a gi (a g (a t (a gi (a g (u .fst)))))
              by refl (x ↦ a gi (a g (a t x))) (inverse X (a gi (a g (u .fst))) (u .fst) (perm_action_inv_left S g (u .fst)))
            = a gi (a tc (a g (u .fst)))
              by refl (a gi) (inverse X (a tc (a g (u .fst))) (a g (a t (a gi (a g (u .fst))))) (perm_conjugate_action S g t (a g (u .fst))))
            = a gi (a g (u .fst)) by refl (a gi) q
            = u .fst by perm_action_inv_left S g (u .fst) ∎)) in
    let bwd : MovedPoints X (a tc) → MovedPoints X (a t)
      ≔ u ↦ (a gi (u .fst), q ↦ u .snd
          (calc
            a tc (u .fst) = a g (a t (a gi (u .fst))) by perm_conjugate_action S g t (u .fst)
            = a g (a gi (u .fst)) by refl (a g) q
            = u .fst by perm_action_inv_right S g (u .fst) ∎)) in
    quasi_inverse_equiv (MovedPoints X (a t)) (MovedPoints X (a tc)) fwd bwd
      (u ↦ subtype_equal X (x ↦ Not (Id X (a t x) x)) (x ↦ negation_prop (Id X (a t x) x)) (bwd (fwd u)) u
             (perm_action_inv_left S g (u .fst)))
      (u ↦ subtype_equal X (x ↦ Not (Id X (a tc x) x)) (x ↦ negation_prop (Id X (a tc x) x)) (fwd (bwd u)) u
             (perm_action_inv_right S g (u .fst)))

{` The permutations c = (0 1 2) and d = (0 1 2)(3 4 5) of Fin (m + 6). `}
def sn6_c (m : Nat) : Fin (add m 6) → Fin (add m 6) ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. x)) ↦ inl. (inl. (inl. x)) ]

def sn6_d (m : Nat) : Fin (add m 6) → Fin (add m 6) ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. y))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. y))))) ]

def sn6_c_cube (m : Nat) : (x : Fin (add m 6)) → Id (Fin (add m 6)) (sn6_c m (sn6_c m (sn6_c m x))) x ≔ [
  | inr. u ↦ refl (inr. u : Fin (add m 6))
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin (add m 6))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin (add m 6))
  | inl. (inl. (inl. x)) ↦ refl (inl. (inl. (inl. x)) : Fin (add m 6)) ]

def sn6_d_cube (m : Nat) : (x : Fin (add m 6)) → Id (Fin (add m 6)) (sn6_d m (sn6_d m (sn6_d m x))) x ≔ [
  | inr. u ↦ refl (inr. u : Fin (add m 6))
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin (add m 6))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin (add m 6))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin (add m 6))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin (add m 6))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin (add m 6))
  | inl. (inl. (inl. (inl. (inl. (inl. y))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. y))))) : Fin (add m 6)) ]

def sn6_ne (m : Nat) (x y : Fin (add m 6))
  (e : Id Bool (decision_bool (Id (Fin (add m 6)) x y) (fin_decidable_equality (add m 6) x y)) false.)
  : Not (Id (Fin (add m 6)) x y)
  ≔ nat_decision_false_reflect (Id (Fin (add m 6)) x y) (fin_decidable_equality (add m 6) x y) e

{` The moved points of c, d and d^2. `}
def sn6_c_moved_fin (m : Nat) : Equiv (MovedPoints (Fin (add m 6)) (sn6_c m)) (Fin 3)
  ≔ let F ≔ Fin (add m 6) in
    let M ≔ MovedPoints F (sn6_c m) in
    let p0 : F ≔ inr. star. in let p1 : F ≔ inl. (inr. star.) in let p2 : F ≔ inl. (inl. (inr. star.)) in
    let to : (x : F) → Not (Id F (sn6_c m x) x) → Fin 3 ≔ [
      | inr. star. ↦ _ ↦ inr. star.
      | inl. (inr. star.) ↦ _ ↦ inl. (inr. star.)
      | inl. (inl. (inr. star.)) ↦ _ ↦ inl. (inl. (inr. star.))
      | inl. (inl. (inl. x)) ↦ n ↦ match n (refl (inl. (inl. (inl. x)) : F)) [] ] in
    let from : Fin 3 → M ≔ [
      | inr. star. ↦ (p0, sn6_ne m p1 p0 (refl (false. : Bool)))
      | inl. (inr. star.) ↦ (p1, sn6_ne m p2 p1 (refl (false. : Bool)))
      | inl. (inl. (inr. star.)) ↦ (p2, sn6_ne m p0 p2 (refl (false. : Bool)))
      | inl. (inl. (inl. e)) ↦ match e [] ] in
    let back : (x : F) → (n : Not (Id F (sn6_c m x) x)) → Id M (from (to x n)) (x, n) ≔ [
      | inr. star. ↦ n ↦ subtype_equal F (x ↦ Not (Id F (sn6_c m x) x)) (x ↦ negation_prop (Id F (sn6_c m x) x))
          (from (to (inr. star.) n)) (inr. star., n) (refl (inr. star. : F))
      | inl. (inr. star.) ↦ n ↦ subtype_equal F (x ↦ Not (Id F (sn6_c m x) x)) (x ↦ negation_prop (Id F (sn6_c m x) x))
          (from (to (inl. (inr. star.)) n)) (inl. (inr. star.), n) (refl (inl. (inr. star.) : F))
      | inl. (inl. (inr. star.)) ↦ n ↦ subtype_equal F (x ↦ Not (Id F (sn6_c m x) x)) (x ↦ negation_prop (Id F (sn6_c m x) x))
          (from (to (inl. (inl. (inr. star.))) n)) (inl. (inl. (inr. star.)), n) (refl (inl. (inl. (inr. star.)) : F))
      | inl. (inl. (inl. x)) ↦ n ↦ match n (refl (inl. (inl. (inl. x)) : F)) [] ] in
    quasi_inverse_equiv M (Fin 3) (u ↦ to (u .fst) (u .snd)) from (u ↦ back (u .fst) (u .snd))
      [ inr. star. ↦ refl (inr. star. : Fin 3)
      | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Fin 3)
      | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Fin 3)
      | inl. (inl. (inl. e)) ↦ match e [] ]

def sn6_d_moved_fin (m : Nat) (f : Fin (add m 6) → Fin (add m 6))
  (inner : (y : Fin m) → Id (Fin (add m 6)) (f (inl. (inl. (inl. (inl. (inl. (inl. y))))))) (inl. (inl. (inl. (inl. (inl. (inl. y)))))))
  (n0 : Not (Id (Fin (add m 6)) (f (inr. star.)) (inr. star.)))
  (n1 : Not (Id (Fin (add m 6)) (f (inl. (inr. star.))) (inl. (inr. star.))))
  (n2 : Not (Id (Fin (add m 6)) (f (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.)))))
  (n3 : Not (Id (Fin (add m 6)) (f (inl. (inl. (inl. (inr. star.))))) (inl. (inl. (inl. (inr. star.))))))
  (n4 : Not (Id (Fin (add m 6)) (f (inl. (inl. (inl. (inl. (inr. star.)))))) (inl. (inl. (inl. (inl. (inr. star.)))))))
  (n5 : Not (Id (Fin (add m 6)) (f (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))
  : Equiv (MovedPoints (Fin (add m 6)) f) (Fin 6)
  ≔ let F ≔ Fin (add m 6) in
    let M ≔ MovedPoints F f in
    let P : F → Type ≔ x ↦ Not (Id F (f x) x) in
    let to : (x : F) → P x → Fin 6 ≔ [
      | inr. star. ↦ _ ↦ inr. star.
      | inl. (inr. star.) ↦ _ ↦ inl. (inr. star.)
      | inl. (inl. (inr. star.)) ↦ _ ↦ inl. (inl. (inr. star.))
      | inl. (inl. (inl. (inr. star.))) ↦ _ ↦ inl. (inl. (inl. (inr. star.)))
      | inl. (inl. (inl. (inl. (inr. star.)))) ↦ _ ↦ inl. (inl. (inl. (inl. (inr. star.))))
      | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ _ ↦ inl. (inl. (inl. (inl. (inl. (inr. star.)))))
      | inl. (inl. (inl. (inl. (inl. (inl. y))))) ↦ n ↦ match n (inner y) [] ] in
    let from : Fin 6 → M ≔ [
      | inr. star. ↦ (inr. star., n0)
      | inl. (inr. star.) ↦ (inl. (inr. star.), n1)
      | inl. (inl. (inr. star.)) ↦ (inl. (inl. (inr. star.)), n2)
      | inl. (inl. (inl. (inr. star.))) ↦ (inl. (inl. (inl. (inr. star.))), n3)
      | inl. (inl. (inl. (inl. (inr. star.)))) ↦ (inl. (inl. (inl. (inl. (inr. star.)))), n4)
      | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ (inl. (inl. (inl. (inl. (inl. (inr. star.))))), n5)
      | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ] in
    let back : (x : F) → (n : P x) → Id M (from (to x n)) (x, n) ≔ [
      | inr. star. ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x)) (from (to (inr. star.) n)) (inr. star., n) (refl (inr. star. : F))
      | inl. (inr. star.) ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x))
          (from (to (inl. (inr. star.)) n)) (inl. (inr. star.), n) (refl (inl. (inr. star.) : F))
      | inl. (inl. (inr. star.)) ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x))
          (from (to (inl. (inl. (inr. star.))) n)) (inl. (inl. (inr. star.)), n) (refl (inl. (inl. (inr. star.)) : F))
      | inl. (inl. (inl. (inr. star.))) ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x))
          (from (to (inl. (inl. (inl. (inr. star.)))) n)) (inl. (inl. (inl. (inr. star.))), n) (refl (inl. (inl. (inl. (inr. star.))) : F))
      | inl. (inl. (inl. (inl. (inr. star.)))) ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x))
          (from (to (inl. (inl. (inl. (inl. (inr. star.))))) n)) (inl. (inl. (inl. (inl. (inr. star.)))), n)
          (refl (inl. (inl. (inl. (inl. (inr. star.)))) : F))
      | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ n ↦ subtype_equal F P (x ↦ negation_prop (Id F (f x) x))
          (from (to (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) n)) (inl. (inl. (inl. (inl. (inl. (inr. star.))))), n)
          (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : F))
      | inl. (inl. (inl. (inl. (inl. (inl. y))))) ↦ n ↦ match n (inner y) [] ] in
    quasi_inverse_equiv M (Fin 6) (u ↦ to (u .fst) (u .snd)) from (u ↦ back (u .fst) (u .snd))
      [ inr. star. ↦ refl (inr. star. : Fin 6)
      | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Fin 6)
      | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Fin 6)
      | inl. (inl. (inl. (inr. star.))) ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin 6)
      | inl. (inl. (inl. (inl. (inr. star.)))) ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin 6)
      | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin 6)
      | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def sn6_d_moved (m : Nat) : Equiv (MovedPoints (Fin (add m 6)) (sn6_d m)) (Fin 6)
  ≔ let o0 : Fin (add m 6) ≔ inr. star. in
    let o1 : Fin (add m 6) ≔ inl. (inr. star.) in
    let o2 : Fin (add m 6) ≔ inl. (inl. (inr. star.)) in
    let o3 : Fin (add m 6) ≔ inl. (inl. (inl. (inr. star.))) in
    let o4 : Fin (add m 6) ≔ inl. (inl. (inl. (inl. (inr. star.)))) in
    let o5 : Fin (add m 6) ≔ inl. (inl. (inl. (inl. (inl. (inr. star.))))) in
    sn6_d_moved_fin m (sn6_d m) (y ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. y))))) : Fin (add m 6)))
      (sn6_ne m o1 o0 (refl (false. : Bool))) (sn6_ne m o2 o1 (refl (false. : Bool))) (sn6_ne m o0 o2 (refl (false. : Bool)))
      (sn6_ne m o4 o3 (refl (false. : Bool))) (sn6_ne m o5 o4 (refl (false. : Bool))) (sn6_ne m o3 o5 (refl (false. : Bool)))

def sn6_d2_moved (m : Nat) : Equiv (MovedPoints (Fin (add m 6)) (x ↦ sn6_d m (sn6_d m x))) (Fin 6)
  ≔ let o0 : Fin (add m 6) ≔ inr. star. in
    let o1 : Fin (add m 6) ≔ inl. (inr. star.) in
    let o2 : Fin (add m 6) ≔ inl. (inl. (inr. star.)) in
    let o3 : Fin (add m 6) ≔ inl. (inl. (inl. (inr. star.))) in
    let o4 : Fin (add m 6) ≔ inl. (inl. (inl. (inl. (inr. star.)))) in
    let o5 : Fin (add m 6) ≔ inl. (inl. (inl. (inl. (inl. (inr. star.))))) in
    sn6_d_moved_fin m (x ↦ sn6_d m (sn6_d m x)) (y ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. y))))) : Fin (add m 6)))
      (sn6_ne m o2 o0 (refl (false. : Bool))) (sn6_ne m o0 o1 (refl (false. : Bool))) (sn6_ne m o1 o2 (refl (false. : Bool)))
      (sn6_ne m o5 o3 (refl (false. : Bool))) (sn6_ne m o3 o4 (refl (false. : Bool))) (sn6_ne m o4 o5 (refl (false. : Bool)))

{` The subgroups ⟨c⟩ and ⟨d⟩ of order 3 of Σ_(m+6). `}
def sn6_set (m : Nat) : SetTypes ≔ standard_set (add m 6)

def sn6_c_sym (m : Nat) : USym (symmetric_group (add m 6))
  ≔ permutation_symmetry (sn6_set m) (perm3_equiv (Fin (add m 6)) (sn6_c m) (sn6_c_cube m))

def sn6_d_sym (m : Nat) : USym (symmetric_group (add m 6))
  ≔ permutation_symmetry (sn6_set m) (perm3_equiv (Fin (add m 6)) (sn6_d m) (sn6_d_cube m))

def sn6_c_ne (m : Nat) : Not (Id (USym (symmetric_group (add m 6))) (sn6_c_sym m) (usym_unit (symmetric_group (add m 6))))
  ≔ perm_symmetry_ne_unit (sn6_set m) (perm3_equiv (Fin (add m 6)) (sn6_c m) (sn6_c_cube m)) (inr. star.)
      (sn6_ne m (inl. (inr. star.)) (inr. star.) (refl (false. : Bool)))

def sn6_d_ne (m : Nat) : Not (Id (USym (symmetric_group (add m 6))) (sn6_d_sym m) (usym_unit (symmetric_group (add m 6))))
  ≔ perm_symmetry_ne_unit (sn6_set m) (perm3_equiv (Fin (add m 6)) (sn6_d m) (sn6_d_cube m)) (inr. star.)
      (sn6_ne m (inl. (inr. star.)) (inr. star.) (refl (false. : Bool)))

def sn6_cyclic_subgroup (m : Nat) (s : USym (symmetric_group (add m 6)))
  (h : Id (USym (symmetric_group (add m 6))) (usym_power (symmetric_group (add m 6)) s 3) (usym_unit (symmetric_group (add m 6))))
  (ne : Not (Id (USym (symmetric_group (add m 6))) s (usym_unit (symmetric_group (add m 6)))))
  : FiniteOrderSubgroups (symmetric_group (add m 6)) 3
  ≔ generated_order_p_subgroup 2 nat_prime_three (symmetric_group (add m 6)) (s, (h, ne))

def sn6_c_subgroup (m : Nat) : FiniteOrderSubgroups (symmetric_group (add m 6)) 3
  ≔ sn6_cyclic_subgroup m (sn6_c_sym m) (perm3_symmetry_cube (sn6_set m) (sn6_c m) (sn6_c_cube m)) (sn6_c_ne m)

def sn6_d_subgroup (m : Nat) : FiniteOrderSubgroups (symmetric_group (add m 6)) 3
  ≔ sn6_cyclic_subgroup m (sn6_d_sym m) (perm3_symmetry_cube (sn6_set m) (sn6_d m) (sn6_d_cube m)) (sn6_d_ne m)

{` A conjugate of ⟨c⟩ is not ⟨d⟩. `}
def sn6_card_three_six (A : Type) (h : IsFinite A) (e3 : Equiv A (Fin 3)) (e6 : Equiv A (Fin 6)) : Empty
  ≔ nat_decision_false_reflect (Id Nat 3 6) (nat_dec_eq 3 6) (refl (false. : Bool))
      (concat Nat 3 (cardinality A h) 6
        (inverse Nat (cardinality A h) 3 (cardinality_equiv A (Fin 3) e3 h (fin_is_finite 3)))
        (cardinality_equiv A (Fin 6) e6 h (fin_is_finite 6)))

{` An element t of ⟨d⟩ is d^k with k < 3; t ≠ e moving 3 points is impossible. `}
def sn6_power_cases (m : Nat) (t : USym (symmetric_group (add m 6)))
  (hM : IsFinite (MovedPoints (Fin (add m 6)) (permutation_action (sn6_set m) t)))
  (ccount : Equiv (MovedPoints (Fin (add m 6)) (permutation_action (sn6_set m) t)) (Fin 3))
  (ne_t : Not (Id (USym (symmetric_group (add m 6))) t (usym_unit (symmetric_group (add m 6)))))
  (k : Nat) (lt : BookLt k 3)
  (p : Id (USym (symmetric_group (add m 6))) t (usym_power (symmetric_group (add m 6)) (sn6_d_sym m) k)) : Empty
  ≔ let G ≔ symmetric_group (add m 6) in let S ≔ sn6_set m in let F ≔ Fin (add m 6) in
    let Mt ≔ MovedPoints F (permutation_action S t) in
    let mp : (j : Nat) → Id (USym G) t (usym_power G (sn6_d_sym m) j) → Equiv Mt (MovedPoints F (iterate F (sn6_d m) j))
      ≔ j q ↦ moved_points_pointwise F (permutation_action S t) (iterate F (sn6_d m) j)
          (z ↦ concat F (permutation_action S t z) (permutation_action S (usym_power G (sn6_d_sym m) j) z) (iterate F (sn6_d m) j z)
                 (refl ((s ↦ permutation_action S s z) : USym G → F) q)
                 (perm_symmetry_power_action S (perm3_equiv F (sn6_d m) (sn6_d_cube m)) j z)) in
    match k [
    | zero. ↦ ne_t p
    | suc. zero. ↦ sn6_card_three_six Mt hM ccount
        (compose_equiv Mt (MovedPoints F (sn6_d m)) (Fin 6) (mp 1 p) (sn6_d_moved m))
    | suc. (suc. zero.) ↦ sn6_card_three_six Mt hM ccount
        (compose_equiv Mt (MovedPoints F (x ↦ sn6_d m (sn6_d m x))) (Fin 6) (mp 2 p) (sn6_d2_moved m))
    | suc. (suc. (suc. j)) ↦
      lt .snd .fst (nat_add_zero_right_part (lt .fst) j
        (refl ((z ↦ match z [ zero. ↦ zero. | suc. z ↦ match z [ zero. ↦ zero. | suc. z ↦ match z [ zero. ↦ zero. | suc. z ↦ z ] ] ]) : Nat → Nat)
          (lt .snd .snd))) ]

def sigma_n_order_three_not_conjugate (m : Nat) (g : USym (symmetric_group (add m 6)))
  (e : Id (Subgroups (symmetric_group (add m 6))) (subgroup_conjugate (symmetric_group (add m 6)) g (sn6_c_subgroup m .fst))
         (sn6_d_subgroup m .fst)) : Empty
  ≔ let G ≔ symmetric_group (add m 6) in
    let S ≔ sn6_set m in
    let F ≔ Fin (add m 6) in
    let c ≔ sn6_c_sym m in let d ≔ sn6_d_sym m in
    let C ≔ sn6_c_subgroup m .fst in let D ≔ sn6_d_subgroup m .fst in
    let X ≔ C .gset in let x ≔ C .point in
    let gi ≔ usym_inv G g in
    let t ≔ perm_conjugate S g c in
    let cmem : SubgroupHasMember G C c
      ≔ generated_subgroup_member 2 nat_prime_three G (c, (perm3_symmetry_cube S (sn6_c m) (sn6_c_cube m), sn6_c_ne m)) in
    let tmemT : SubgroupHasMember G (subgroup_conjugate G g C) t
      ≔ calc
          gset_usym_act G X t (gset_usym_act G X g x)
          = gset_usym_act G X g (gset_usym_act G X (usym_mul G c gi) (gset_usym_act G X g x))
            by gset_act_mul G X g (usym_mul G c gi) (gset_usym_act G X g x)
          = gset_usym_act G X g (gset_usym_act G X c (gset_usym_act G X gi (gset_usym_act G X g x)))
            by refl (gset_usym_act G X g) (gset_act_mul G X c gi (gset_usym_act G X g x))
          = gset_usym_act G X g (gset_usym_act G X c x)
            by refl (u ↦ gset_usym_act G X g (gset_usym_act G X c u)) (gset_act_inv_left G X g x)
          = gset_usym_act G X g x by refl (gset_usym_act G X g) cmem ∎ in
    let tmem : SubgroupHasMember G D t
      ≔ transport (Subgroups G) (T ↦ SubgroupHasMember G T t) (subgroup_conjugate G g C) D e tmemT in
    let ccount : Equiv (MovedPoints F (permutation_action S t)) (Fin 3)
      ≔ compose_equiv (MovedPoints F (permutation_action S t)) (MovedPoints F (permutation_action S c)) (Fin 3)
          (canonical_inverse_equiv (MovedPoints F (permutation_action S c)) (MovedPoints F (permutation_action S t))
            (perm_conjugate_moved_equiv S g c))
          (sn6_c_moved_fin m) in
    let hM : IsFinite (MovedPoints F (permutation_action S t))
      ≔ finite_of_equiv (MovedPoints F (permutation_action S t)) (Fin 3) ccount (fin_is_finite 3) in
    let ne_t : Not (Id (USym G) t (usym_unit G))
      ≔ q ↦ sn6_ne m (sn6_c m (inr. star.)) (inr. star.) (refl (false. : Bool))
          (calc
            sn6_c m (inr. star.)
            = permutation_action S gi (permutation_action S g (sn6_c m (inr. star.)))
              by inverse F (permutation_action S gi (permutation_action S g (sn6_c m (inr. star.)))) (sn6_c m (inr. star.))
                   (perm_action_inv_left S g (sn6_c m (inr. star.)))
            = permutation_action S gi (permutation_action S g (sn6_c m (permutation_action S gi (permutation_action S g (inr. star.)))))
              by refl (u ↦ permutation_action S gi (permutation_action S g (sn6_c m u)))
                   (inverse F (permutation_action S gi (permutation_action S g (inr. star.))) (inr. star.) (perm_action_inv_left S g (inr. star.)))
            = permutation_action S gi (permutation_action S t (permutation_action S g (inr. star.)))
              by refl (permutation_action S gi)
                   (inverse F (permutation_action S t (permutation_action S g (inr. star.)))
                     (permutation_action S g (sn6_c m (permutation_action S gi (permutation_action S g (inr. star.)))))
                     (perm_conjugate_action S g c (permutation_action S g (inr. star.))))
            = permutation_action S gi (permutation_action S (usym_unit G) (permutation_action S g (inr. star.)))
              by refl (u ↦ permutation_action S gi (permutation_action S u (permutation_action S g (inr. star.)))) q
            = permutation_action S gi (permutation_action S g (inr. star.))
              by refl (permutation_action S gi) (permutation_action_unit S (permutation_action S g (inr. star.)))
            = inr. star. by perm_action_inv_left S g (inr. star.) ∎) in
    mere_rec (Σ Nat (k ↦ Product (BookLt k 3) (Id (USym G) t (usym_power G d k)))) Empty empty_prop
      (w ↦ sn6_power_cases m t hM ccount ne_t (w .fst) (w .snd .fst) (w .snd .snd))
      (cyclic_subgroup_member_power 2 G d (perm3_symmetry_cube S (sn6_d m) (sn6_d_cube m))
        (prime_order_powers_nontrivial 3 nat_prime_three G d (perm3_symmetry_cube S (sn6_d m) (sn6_d_cube m)) (sn6_d_ne m)) t tmem)

def sigma_n_order_three_not_all_conjugate (m : Nat)
  (all : (S T : FiniteOrderSubgroups (symmetric_group (add m 6)) 3)
         → Mere (Σ (USym (symmetric_group (add m 6))) (g ↦ Id (Subgroups (symmetric_group (add m 6)))
              (subgroup_conjugate (symmetric_group (add m 6)) g (S .fst)) (T .fst))))
  : Empty
  ≔ mere_rec (Σ (USym (symmetric_group (add m 6))) (g ↦ Id (Subgroups (symmetric_group (add m 6)))
        (subgroup_conjugate (symmetric_group (add m 6)) g (sn6_c_subgroup m .fst)) (sn6_d_subgroup m .fst)))
      Empty empty_prop (u ↦ sigma_n_order_three_not_conjugate m (u .fst) (u .snd)) (all (sn6_c_subgroup m) (sn6_d_subgroup m))
