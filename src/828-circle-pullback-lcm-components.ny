export "824-integer-intersection"
export "826-circle-pullback-components"

{` Chapter 8 (congp.tex), ex:pullbackandgcd (line 355), the stronger claims:
   each component of P = S¹ ×_{S¹} S¹ (pullback of z ↦ z^a and w ↦ w^b,
   a, b > 0) is a circle on which the composite map P → S¹,
   (z, w) ↦ z^a, is the lcm(a,b)-fold covering; and P ≃ S¹ × Fin(gcd(a,b))
   over that composite.

   Route. The component of ((base, base), δ) is the classifying type of the
   pullback group of the homomorphisms ℤ → ℤ given by (-)^a (pointed by
   the boundary identification) and (-)^b (pointed by that path followed
   by δ); both send loop to loop^a resp. loop^b, so module 824 gives an
   isomorphism φ : ℤ ≅ (that group) with (incl ∘ φ) = multiplication by
   L = lcm(a,b), whose underlying map is the degree map (-)^L. Every
   component contains such a point. `}

def cpl_power_hom (C : CircleSignature) (a1 : Nat) : GroupHom (circle_group C) (circle_group C)
  ≔ circle_multiplication_hom C (pos. (suc. a1))

{` The multiplication homomorphism has the degree map as underlying map. `}
def cpl_power_hom_function (C : CircleSignature) (a1 : Nat)
  : Id (C .carrier → C .carrier) (hom_function (circle_group C) (circle_group C) (cpl_power_hom C a1))
      (circle_degree_map C (suc. a1))
  ≔ refl (circle_degree_map C (suc. a1))

{` In the circle, conjugation of loops is trivial; moving the pointing path
   of a conjugation. `}
def cpl_circle_conjugate_trivial (C : CircleSignature) (u x : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base)) (pointed_loop_conjugate (C .carrier) (C .base) (C .base) u x) x
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    calc
      concat S o o o u (concat S o o o x (inverse S o o u))
      = concat S o o o u (concat S o o o (inverse S o o u) x)
        by refl (concat S o o o u) (circle_loops_commute C x (inverse S o o u))
      = concat S o o o (concat S o o o u (inverse S o o u)) x
        by inverse (Id S o o) (concat S o o o (concat S o o o u (inverse S o o u)) x)
          (concat S o o o u (concat S o o o (inverse S o o u) x)) (concat_assoc S o o o o u (inverse S o o u) x)
      = concat S o o o (refl o) x by refl ((t ↦ concat S o o o t x) : Id S o o → Id S o o) (concat_inverse_right S o o u)
      = x by concat_1p S o o x ∎

def cpl_conjugate_move (A : Type) (a y : A) (p q : Id A a y) (l : Id A y y)
  : Id (Id A a a) (pointed_loop_conjugate A a y p l)
      (pointed_loop_conjugate A a a (concat A a y a p (inverse A a y q)) (pointed_loop_conjugate A a y q l))
  ≔ J A a
      (y q ↦ (p : Id A a y) (l : Id A y y) → Id (Id A a a) (pointed_loop_conjugate A a y p l)
        (pointed_loop_conjugate A a a (concat A a y a p (inverse A a y q)) (pointed_loop_conjugate A a y q l)))
      (p l ↦ calc
        pointed_loop_conjugate A a a p l
        = pointed_loop_conjugate A a a (concat A a a a p (inverse A a a (refl a))) l
          by refl ((t ↦ pointed_loop_conjugate A a a t l) : Id A a a → Id A a a)
            (inverse (Id A a a) (concat A a a a p (inverse A a a (refl a))) p
              (concat (Id A a a) (concat A a a a p (inverse A a a (refl a))) (concat A a a a p (refl a)) p
                (refl (concat A a a a p) (inverse_refl A a)) (concat_p1 A a a p)))
        = pointed_loop_conjugate A a a (concat A a a a p (inverse A a a (refl a))) (pointed_loop_conjugate A a a (refl a) l)
          by refl (pointed_loop_conjugate A a a (concat A a a a p (inverse A a a (refl a))))
            (inverse (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l (loop_conjugate_at_refl A a l)) ∎)
      y q p l

{` The second homomorphism for the component of ((base, base), δ). `}
def cpl_twisted_hom (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : GroupHom (circle_group C) (circle_group C)
  ≔ mkhom (circle_group C) (circle_group C)
      (circle_degree_map C (suc. b1),
       concat (C .carrier) (C .base) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base))
         (hom_point (circle_group C) (circle_group C) (cpl_power_hom C a1)) d)

def cpl_twisted_hom_loop (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : CircleHomLoop C (cpl_twisted_hom C a1 b1 d) (pos. (suc. b1))
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    let y ≔ circle_degree_map C (suc. b1) o in
    let p ≔ hom_point (circle_group C) (circle_group C) (cpl_twisted_hom C a1 b1 d) in
    let q ≔ hom_point (circle_group C) (circle_group C) (cpl_power_hom C b1) in
    let l ≔ refl (circle_degree_map C (suc. b1)) (C .loop) in
    calc
      pointed_loop_conjugate S o y p l
      = pointed_loop_conjugate S o o (concat S o y o p (inverse S o y q)) (pointed_loop_conjugate S o y q l)
        by cpl_conjugate_move S o y p q l
      = pointed_loop_conjugate S o y q l
        by cpl_circle_conjugate_trivial C (concat S o y o p (inverse S o y q)) (pointed_loop_conjugate S o y q l)
      = circle_power C (pos. (suc. b1)) by circle_multiplication_loop C (pos. (suc. b1)) ∎

{` The pullback group at the point ((base, base), p_a⁻¹ (p_a δ)). Its
   classifying type is the component of that point in P (judgmentally). `}
def cpl_component_group (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base))) : Group
  ≔ CircleHomIntersection C a1 b1 (cpl_power_hom C a1) (cpl_twisted_hom C a1 b1 d)
      (circle_multiplication_loop C (pos. (suc. a1))) (cpl_twisted_hom_loop C a1 b1 d)

def cpl_point (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : CirclePowerPullback C (suc. a1) (suc. b1)
  ≔ pbg_point (circle_group C) (circle_group C) (circle_group C) (cpl_power_hom C a1) (cpl_twisted_hom C a1 b1 d)

def cpl_component_group_classifying (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : Id Type (BG (cpl_component_group C a1 b1 d) .carrier)
      (NativeComponent (CirclePowerPullback C (suc. a1) (suc. b1)) (cpl_point C a1 b1 d))
  ≔ refl (BG (cpl_component_group C a1 b1 d) .carrier)

{` The component of cpl_point d is a copy of the L-fold covering: an
   equivalence S¹ ≃ component under which (z, w) ↦ z^a becomes z ↦ z^L. `}
def cpl_component_lcm_cover (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : Σ (BookEquiv (C .carrier) (NativeComponent (CirclePowerPullback C (suc. a1) (suc. b1)) (cpl_point C a1 b1 d)))
      (e ↦ Id (C .carrier → C .carrier) (x ↦ circle_degree_map C (suc. a1) (e .map x .fst .fst .fst))
        (circle_degree_map C (nat_lcm (suc. a1) (suc. b1))))
  ≔ let Z ≔ circle_group C in
    let f ≔ cpl_power_hom C a1 in
    let f' ≔ cpl_twisted_hom C a1 b1 d in
    let hf ≔ circle_multiplication_loop C (pos. (suc. a1)) in
    let hf' ≔ cpl_twisted_hom_loop C a1 b1 d in
    let P ≔ cpl_component_group C a1 b1 d in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    ((hom_function Z P phi, circle_hom_intersection_map_iso C a1 b1 f f' hf hf'),
     group_hom_function_path Z Z
       (group_hom_compose Z P Z phi (circle_hom_intersection_mono C a1 b1 f f' hf hf' .snd .fst))
       (circle_multiplication_hom C (pos. (nat_lcm (suc. a1) (suc. b1))))
       (circle_hom_intersection_triangle C a1 b1 f f' hf hf'))

{` Every component of P contains a point cpl_point d. `}
def cpl_move_to_base (C : CircleSignature) (a b : Nat) (z : C .carrier) (r : Id (C .carrier) (C .base) z)
  (w : C .carrier) (s : Id (C .carrier) (C .base) w)
  (p : Id (C .carrier) (circle_degree_map C a z) (circle_degree_map C b w))
  : Σ (Id (C .carrier) (circle_degree_map C a (C .base)) (circle_degree_map C b (C .base)))
      (d ↦ Id (CirclePowerPullback C a b) ((C .base, C .base), d) ((z, w), p))
  ≔ J (C .carrier) (C .base)
      (z r ↦ (w : C .carrier) (s : Id (C .carrier) (C .base) w)
        (p : Id (C .carrier) (circle_degree_map C a z) (circle_degree_map C b w))
        → Σ (Id (C .carrier) (circle_degree_map C a (C .base)) (circle_degree_map C b (C .base)))
            (d ↦ Id (CirclePowerPullback C a b) ((C .base, C .base), d) ((z, w), p)))
      (w s ↦ J (C .carrier) (C .base)
        (w s ↦ (p : Id (C .carrier) (circle_degree_map C a (C .base)) (circle_degree_map C b w))
          → Σ (Id (C .carrier) (circle_degree_map C a (C .base)) (circle_degree_map C b (C .base)))
              (d ↦ Id (CirclePowerPullback C a b) ((C .base, C .base), d) ((C .base, w), p)))
        (p ↦ (p, refl (((C .base, C .base), p) : CirclePowerPullback C a b))) w s)
      z r w s p

def cpl_twist_cancel (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : Id (CirclePowerPullback C (suc. a1) (suc. b1)) (cpl_point C a1 b1 d) ((C .base, C .base), d)
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    let y ≔ circle_degree_map C (suc. a1) o in let y' ≔ circle_degree_map C (suc. b1) o in
    let pa ≔ hom_point (circle_group C) (circle_group C) (cpl_power_hom C a1) in
    (refl ((o, o) : Product S S), calc
      concat S y o y' (inverse S o y pa) (concat S o y y' pa d)
      = concat S y y y' (concat S y o y (inverse S o y pa) pa) d
        by inverse (Id S y y') (concat S y y y' (concat S y o y (inverse S o y pa) pa) d)
          (concat S y o y' (inverse S o y pa) (concat S o y y' pa d)) (concat_assoc S y o y y' (inverse S o y pa) pa d)
      = concat S y y y' (refl y) d by refl ((t ↦ concat S y y y' t d) : Id S y y → Id S y y') (concat_inverse_left S o y pa)
      = d by concat_1p S y y' d ∎)

def CplComponent (C : CircleSignature) (a b : Nat) (c : SetTrunc (CirclePowerPullback C a b)) : Type
  ≔ BookFiber (CirclePowerPullback C a b) (SetTrunc (CirclePowerPullback C a b)) (set_trunc (CirclePowerPullback C a b)) c

def cpl_component_has_point (C : CircleSignature) (a1 b1 : Nat) (c : SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
  : Mere (Σ (Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
      (d ↦ Id (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) c
        (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpl_point C a1 b1 d))))
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let T ≔ Σ (Id S (circle_degree_map C (suc. a1) o) (circle_degree_map C (suc. b1) o))
      (d ↦ Id (SetTrunc P) c (set_trunc P (cpl_point C a1 b1 d))) in
    mere_rec (CplComponent C (suc. a1) (suc. b1) c) (Mere T) (mere_isprop T)
      (u ↦ mere_rec (Id S o (u .fst .fst .fst)) (Mere T) (mere_isprop T)
        (r ↦ mere_rec (Id S o (u .fst .fst .snd)) (Mere T) (mere_isprop T)
          (s ↦ let m ≔ cpl_move_to_base C (suc. a1) (suc. b1) (u .fst .fst .fst) r (u .fst .fst .snd) s (u .fst .snd) in
            mere T (m .fst, calc
              c = set_trunc P (u .fst) by u .snd
              = set_trunc P ((o, o), m .fst)
                by refl (set_trunc P) (inverse P ((o, o), m .fst) (u .fst) (m .snd))
              = set_trunc P (cpl_point C a1 b1 (m .fst))
                by refl (set_trunc P) (inverse P (cpl_point C a1 b1 (m .fst)) ((o, o), m .fst) (cpl_twist_cancel C a1 b1 (m .fst))) ∎))
          (native_circle_connected C .snd o (u .fst .fst .snd)))
        (native_circle_connected C .snd o (u .fst .fst .fst)))
      (set_trunc_surjective P c)

{` A component in the sense of the set truncation is the native component
   of any of its points (over P). `}
def cpl_component_native_equiv (X : Type) (x0 : X) (c : SetTrunc X) (h : Id (SetTrunc X) c (set_trunc X x0))
  : Equiv (NativeComponent X x0) (BookFiber X (SetTrunc X) (set_trunc X) c)
  ≔ family_equiv X (y ↦ Mere (Id X x0 y)) (y ↦ Id (SetTrunc X) c (set_trunc X y))
      (y ↦ iff_equiv (Mere (Id X x0 y)) (Id (SetTrunc X) c (set_trunc X y)) (mere_isprop (Id X x0 y))
        (set_trunc_set X c (set_trunc X y))
        (m ↦ concat (SetTrunc X) c (set_trunc X x0) (set_trunc X y) h
          (equiv_inverse_map (Id (SetTrunc X) (set_trunc X x0) (set_trunc X y)) (Mere (Id X x0 y)) (set_trunc_paths X x0 y) m))
        (k ↦ set_trunc_paths X x0 y .map
          (concat (SetTrunc X) (set_trunc X x0) c (set_trunc X y) (inverse (SetTrunc X) c (set_trunc X x0) h) k)))

{` ex:pullbackandgcd, last sentence: every component of P is a copy of the
   lcm(a,b)-fold covering — merely, an equivalence S¹ ≃ component under
   which the composite (z, w) ↦ z^a is z ↦ z^{lcm(a,b)}. `}
def CplLcmCover (C : CircleSignature) (a1 b1 : Nat) (c : SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) : Type
  ≔ Σ (BookEquiv (C .carrier) (CplComponent C (suc. a1) (suc. b1) c))
      (e ↦ Id (C .carrier → C .carrier) (x ↦ circle_degree_map C (suc. a1) (e .map x .fst .fst .fst))
        (circle_degree_map C (nat_lcm (suc. a1) (suc. b1))))

def circle_pullback_component_lcm_cover (C : CircleSignature) (a1 b1 : Nat)
  (c : SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
  : Mere (CplLcmCover C a1 b1 c)
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    mere_rec (Σ (Id S (circle_degree_map C (suc. a1) o) (circle_degree_map C (suc. b1) o))
        (d ↦ Id (SetTrunc P) c (set_trunc P (cpl_point C a1 b1 d))))
      (Mere (CplLcmCover C a1 b1 c)) (mere_isprop (CplLcmCover C a1 b1 c))
      (t ↦ let k ≔ cpl_component_lcm_cover C a1 b1 (t .fst) in
        let e2 ≔ cpl_component_native_equiv P (cpl_point C a1 b1 (t .fst)) c (t .snd) in
        mere (CplLcmCover C a1 b1 c)
          (book_equivalence S (CplComponent C (suc. a1) (suc. b1) c)
             (compose_equiv S (NativeComponent P (cpl_point C a1 b1 (t .fst))) (CplComponent C (suc. a1) (suc. b1) c)
               (native_equivalence S (NativeComponent P (cpl_point C a1 b1 (t .fst))) (k .fst)) e2),
           k .snd))
      (cpl_component_has_point C a1 b1 c)

{` ex:pullbackandgcd, the displayed pullback: P ≃ S¹ × Fin(gcd(a,b))
   (Fin d standing for the underlying set of C_d), merely, such that the
   composite (z, w) ↦ z^a becomes (x, k) ↦ x^{lcm(a,b)}. The components
   are enumerated by circle_power_pullback_components_fin; on each a copy of
   the lcm-fold covering is chosen (finite choice over Fin d). `}
def cpl_component_index (C : CircleSignature) (a1 b1 : Nat)
  : CirclePowerPullback C (suc. a1) (suc. b1) → Fin (nat_gcd (suc. a1) (suc. b1))
  ≔ x ↦ circle_power_pullback_components_fin C a1 b1 .map (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) x)

def cpl_fiber_component_equiv (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : Equiv (CplComponent C (suc. a1) (suc. b1)
            (equiv_inverse_map (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
              (circle_power_pullback_components_fin C a1 b1) k))
      (BookFiber (CirclePowerPullback C (suc. a1) (suc. b1)) (Fin (nat_gcd (suc. a1) (suc. b1))) (cpl_component_index C a1 b1) k)
  ≔ let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let F ≔ Fin (nat_gcd (suc. a1) (suc. b1)) in
    let e ≔ circle_power_pullback_components_fin C a1 b1 in
    let ck ≔ equiv_inverse_map (SetTrunc P) F e k in
    family_equiv P (y ↦ Id (SetTrunc P) ck (set_trunc P y)) (y ↦ Id F k (cpl_component_index C a1 b1 y))
      (y ↦ iff_equiv (Id (SetTrunc P) ck (set_trunc P y)) (Id F k (cpl_component_index C a1 b1 y))
        (set_trunc_set P ck (set_trunc P y)) (fin_set (nat_gcd (suc. a1) (suc. b1)) k (cpl_component_index C a1 b1 y))
        (q ↦ concat F k (e .map ck) (cpl_component_index C a1 b1 y)
          (inverse F (e .map ck) k (equiv_counit (SetTrunc P) F e k)) (refl (e .map) q))
        (q ↦ concat (SetTrunc P) ck (equiv_inverse_map (SetTrunc P) F e (e .map (set_trunc P y))) (set_trunc P y)
          (refl (equiv_inverse_map (SetTrunc P) F e) q)
          (inverse (SetTrunc P) (set_trunc P y) (equiv_inverse_map (SetTrunc P) F e (e .map (set_trunc P y)))
            (equiv_unit (SetTrunc P) F e (set_trunc P y)))))

def CplProductDecomposition (C : CircleSignature) (a1 b1 : Nat) : Type
  ≔ Σ (Equiv (Product (C .carrier) (Fin (nat_gcd (suc. a1) (suc. b1)))) (CirclePowerPullback C (suc. a1) (suc. b1)))
      (E ↦ Id (Product (C .carrier) (Fin (nat_gcd (suc. a1) (suc. b1))) → C .carrier)
        (t ↦ circle_degree_map C (suc. a1) (E .map t .fst .fst))
        (t ↦ circle_degree_map C (nat_lcm (suc. a1) (suc. b1)) (t .fst)))

def cpl_product_from_choice (C : CircleSignature) (a1 b1 : Nat)
  (ch : (k : Fin (nat_gcd (suc. a1) (suc. b1))) → CplLcmCover C a1 b1
         (equiv_inverse_map (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
           (circle_power_pullback_components_fin C a1 b1) k))
  : CplProductDecomposition C a1 b1
  ≔ let S ≔ C .carrier in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let F ≔ Fin (nat_gcd (suc. a1) (suc. b1)) in
    let e ≔ circle_power_pullback_components_fin C a1 b1 in
    let ix ≔ cpl_component_index C a1 b1 in
    let Fib : F → Type ≔ k ↦ BookFiber P F ix k in
    let E ≔ compose_equiv (Product S F) (Σ F (_ ↦ S)) P
      (quasi_inverse_equiv (Product S F) (Σ F (_ ↦ S)) (t ↦ (t .snd, t .fst)) (t ↦ (t .snd, t .fst)) (t ↦ refl t) (t ↦ refl t))
      (compose_equiv (Σ F (_ ↦ S)) (Σ F Fib) P
        (family_equiv F (_ ↦ S) Fib
          (k ↦ compose_equiv S (CplComponent C (suc. a1) (suc. b1) (equiv_inverse_map (SetTrunc P) F e k)) (Fib k)
            (native_equivalence S (CplComponent C (suc. a1) (suc. b1) (equiv_inverse_map (SetTrunc P) F e k)) (ch k .fst))
            (cpl_fiber_component_equiv C a1 b1 k)))
        (sum_of_fibers_equiv P F ix)) in
    (E, funext (Product S F) (_ ↦ S) (t ↦ circle_degree_map C (suc. a1) (E .map t .fst .fst))
          (t ↦ circle_degree_map C (nat_lcm (suc. a1) (suc. b1)) (t .fst))
          (t ↦ ch (t .snd) .snd (refl (t .fst))))

def circle_pullback_product_decomposition (C : CircleSignature) (a1 b1 : Nat) : Mere (CplProductDecomposition C a1 b1)
  ≔ let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let F ≔ Fin (nat_gcd (suc. a1) (suc. b1)) in
    let e ≔ circle_power_pullback_components_fin C a1 b1 in
    mere_rec ((k : F) → CplLcmCover C a1 b1 (equiv_inverse_map (SetTrunc P) F e k))
      (Mere (CplProductDecomposition C a1 b1)) (mere_isprop (CplProductDecomposition C a1 b1))
      (ch ↦ mere (CplProductDecomposition C a1 b1) (cpl_product_from_choice C a1 b1 ch))
      (finite_choice F (fin_is_finite (nat_gcd (suc. a1) (suc. b1)))
        (k ↦ CplLcmCover C a1 b1 (equiv_inverse_map (SetTrunc P) F e k))
        (k ↦ circle_pullback_component_lcm_cover C a1 b1 (equiv_inverse_map (SetTrunc P) F e k)))

{` "The pair (z^{b'}, z^{a'}) is in the pullback": a map S¹ → P whose
   coordinates are the degree maps z ↦ z^{L/a} and z ↦ z^{L/b}
   (L = lcm(a,b) = (L/a)·a = (L/b)·b; the book's b' = b/d and a' = a/d are
   these quotients). It is the underlying map of φ above, for any δ. `}
def circle_pullback_pair_map (C : CircleSignature) (a1 b1 : Nat)
  (d : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
  : Σ (C .carrier → CirclePowerPullback C (suc. a1) (suc. b1))
      (h ↦ Product
        (Id (C .carrier → C .carrier) (z ↦ h z .fst .fst) (circle_degree_map C (pbg_lcm_quotient_left a1 b1 .fst)))
        (Id (C .carrier → C .carrier) (z ↦ h z .fst .snd) (circle_degree_map C (pbg_lcm_quotient_right a1 b1 .fst))))
  ≔ let Z ≔ circle_group C in
    let f ≔ cpl_power_hom C a1 in
    let f' ≔ cpl_twisted_hom C a1 b1 d in
    let hf ≔ circle_multiplication_loop C (pos. (suc. a1)) in
    let hf' ≔ cpl_twisted_hom_loop C a1 b1 d in
    let P ≔ cpl_component_group C a1 b1 d in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    ((z ↦ hom_function Z P phi z .fst),
     (group_hom_function_path Z Z (group_hom_compose Z P Z phi (pullback_group_proj_left Z Z Z f f'))
        (circle_multiplication_hom C (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
        (circle_hom_intersection_proj_left C a1 b1 f f' hf hf'),
      group_hom_function_path Z Z (group_hom_compose Z P Z phi (pullback_group_proj_right Z Z Z f f'))
        (circle_multiplication_hom C (pos. (pbg_lcm_quotient_right a1 b1 .fst)))
        (circle_hom_intersection_proj_right C a1 b1 f f' hf hf')))
