export "828-circle-pullback-lcm-components"
export "1001-divisibility-lemmas"

{` Chapter 8 (congp.tex), ex:pullbackandgcd (line 355), the displayed
   pullback square as an explicit equivalence: for a, b > 0,
   d = gcd(a,b), a = d a', b = d b',
     S¹ × Fin d ≃ S¹ ×_{S¹} S¹   (pullback of z ↦ z^a and w ↦ w^b)
   whose two coordinates are z ↦ z^{b'} and z ↦ z^{a'} on every copy
   (the book's ζ^k z^{b'} is homotopic to z^{b'}; the rotation by ζ^k is
   recorded in the third, path, component), and on which (z,w) ↦ z^a is
   z ↦ z^{lcm(a,b)}. Module 828 had this only merely (finite choice of one
   point per component). Here the points are explicit:
     pt_n = (base, x_n), x_n the transport back along the boundary path of
     the degree map of m^n(y0), m the deck transformation of the b-fold
     covering and y0 its base point,
   and the component equivalence of module 826 sends pt_n to the class of n
   in ℤ/dℤ (cpx_point_class, by unfolding its five steps); n ↦ [n] is an
   explicit bijection Fin d ≃ ℤ/dℤ (division with remainder), so every
   component k gets the explicit point pt_{j(k)}, which is moved to the
   points cpl_point δ of module 828 whose components are explicit circles.
   Also the arithmetic of the example: lcm(a,b)/a = b', lcm(a,b)/b = a',
   lcm(a,b) = a'b = da'b' = ab'. `}

{` Arithmetic. `}
def cpx_mul_swap (x y z : Nat) : Id Nat (mul x (mul y z)) (mul y (mul x z))
  ≔ calc
      mul x (mul y z) = mul (mul x y) z by inverse Nat (mul (mul x y) z) (mul x (mul y z)) (mul_assoc x y z)
      = mul (mul y x) z by refl ((u ↦ mul u z) : Nat → Nat) (mul_comm x y)
      = mul y (mul x z) by mul_assoc y x z ∎

def cpx_positive (n m : Nat) (p : Id Nat n (suc. m)) : Lt zero. n
  ≔ transport Nat (x ↦ Lt zero. x) (suc. m) n (inverse Nat n (suc. m) p) star.

{` With d = gcd(a,b), a = d a', b = d b': lcm(a,b)/a = b'. `}
def cpx_quotient_left_eq (a1 b1 a' b' : Nat)
  (ha : Id Nat (suc. a1) (mul (nat_gcd (suc. a1) (suc. b1)) a'))
  (hb : Id Nat (suc. b1) (mul (nat_gcd (suc. a1) (suc. b1)) b'))
  : Id Nat (pbg_lcm_quotient_left a1 b1 .fst) b'
  ≔ let A : Nat ≔ suc. a1 in let B : Nat ≔ suc. b1 in
    let G ≔ nat_gcd A B in let L ≔ nat_lcm A B in
    let q ≔ pbg_lcm_quotient_left a1 b1 .fst in
    let hq : Id Nat L (mul q A) ≔ pbg_lcm_quotient_left a1 b1 .snd in
    let r ≔ pbg_lcm_quotient_right a1 b1 .fst in
    let hr : Id Nat L (mul r B) ≔ pbg_lcm_quotient_right a1 b1 .snd in
    let Gp : Lt zero. G ≔ cpx_positive G (cpp_gcd_positive a1 b1 .fst) (cpp_gcd_positive a1 b1 .snd) in
    let qp : Lt zero. q ≔ cpx_positive q (pbg_lcm_quotient_left_positive a1 b1 .fst) (pbg_lcm_quotient_left_positive a1 b1 .snd) in
    let e1 : Id Nat (mul A b') (mul B a') ≔ calc
        mul A b' = mul (mul G a') b' by refl ((x ↦ mul x b') : Nat → Nat) ha
        = mul G (mul a' b') by mul_assoc G a' b'
        = mul G (mul b' a') by refl (mul G) (mul_comm a' b')
        = mul (mul G b') a' by inverse Nat (mul (mul G b') a') (mul G (mul b' a')) (mul_assoc G b' a')
        = mul B a' by refl ((x ↦ mul x a') : Nat → Nat) (inverse Nat B (mul G b') hb) ∎ in
    let d1 : NatDivides L (mul A b')
      ≔ nat_lcm_least A B (mul A b') (nat_divides_intro A (mul A b') b' (mul_comm A b'))
          (nat_divides_intro B (mul A b') a' (concat Nat (mul A b') (mul B a') (mul a' B) e1 (mul_comm B a'))) in
    let d2 : NatDivides q b'
      ≔ nat_divides_mul_cancel_positive A q b' star.
          (transport Nat (x ↦ NatDivides x (mul b' A)) L (mul q A) hq
            (transport Nat (y ↦ NatDivides L y) (mul A b') (mul b' A) (mul_comm A b') d1)) in
    mere_rec (Σ Nat (t ↦ Id Nat b' (mul t q))) (Id Nat q b') (nat_set q b')
      (w ↦
        let t ≔ w .fst in let hb' ≔ w .snd in
        let eq : Id Nat (mul a' (mul G q)) (mul (mul r t) (mul G q)) ≔ calc
            mul a' (mul G q) = mul G (mul a' q) by cpx_mul_swap a' G q
            = mul G (mul q a') by refl (mul G) (mul_comm a' q)
            = mul q (mul G a') by cpx_mul_swap G q a'
            = mul q A by refl (mul q) (inverse Nat A (mul G a') ha)
            = L by inverse Nat L (mul q A) hq
            = mul r B by hr
            = mul r (mul G b') by refl (mul r) hb
            = mul r (mul G (mul t q)) by refl ((x ↦ mul r (mul G x)) : Nat → Nat) hb'
            = mul r (mul t (mul G q)) by refl (mul r) (cpx_mul_swap G t q)
            = mul (mul r t) (mul G q) by inverse Nat (mul (mul r t) (mul G q)) (mul r (mul t (mul G q))) (mul_assoc r t (mul G q)) ∎ in
        let ha' : Id Nat a' (mul r t) ≔ nat_mul_cancel_positive (mul G q) a' (mul r t) (nat_mul_positive G q Gp qp) eq in
        let dA : NatDivides (mul G t) A ≔ nat_divides_intro (mul G t) A r (calc
            A = mul G a' by ha
            = mul G (mul r t) by refl (mul G) ha'
            = mul r (mul G t) by cpx_mul_swap G r t ∎) in
        let dB : NatDivides (mul G t) B ≔ nat_divides_intro (mul G t) B q (calc
            B = mul G b' by hb
            = mul G (mul t q) by refl (mul G) hb'
            = mul G (mul q t) by refl (mul G) (mul_comm t q)
            = mul q (mul G t) by cpx_mul_swap G q t ∎) in
        let dG ≔ nat_gcd_greatest A B (mul G t) dA dB in
        let t1 : Id Nat t (suc. zero.)
          ≔ mere_rec (Σ Nat (k ↦ Id Nat G (mul k (mul G t)))) (Id Nat t (suc. zero.)) (nat_set t (suc. zero.))
              (v ↦ let k ≔ v .fst in
                let one : Id Nat (suc. zero.) (mul k t)
                  ≔ nat_mul_cancel_positive G (suc. zero.) (mul k t) Gp (calc
                      mul (suc. zero.) G = G by mul_one_left G
                      = mul k (mul G t) by v .snd
                      = mul k (mul t G) by refl (mul k) (mul_comm G t)
                      = mul (mul k t) G by inverse Nat (mul (mul k t) G) (mul k (mul t G)) (mul_assoc k t G) ∎) in
                nat_divides_antisym t (suc. zero.) (nat_divides_intro t (suc. zero.) k one)
                  (nat_divides_intro (suc. zero.) t t (inverse Nat (mul t (suc. zero.)) t (mul_one_right t))))
              dG in
        calc
          q = mul (suc. zero.) q by inverse Nat (mul (suc. zero.) q) q (mul_one_left q)
          = mul t q by refl ((x ↦ mul x q) : Nat → Nat) (inverse Nat t (suc. zero.) t1)
          = b' by inverse Nat b' (mul t q) hb' ∎)
      d2

{` lcm(a,b)/b = a', and the identities lcm(a,b) = a'b = da'b' = ab'. `}
def cpx_quotient_right_eq (a1 b1 a' b' : Nat)
  (ha : Id Nat (suc. a1) (mul (nat_gcd (suc. a1) (suc. b1)) a'))
  (hb : Id Nat (suc. b1) (mul (nat_gcd (suc. a1) (suc. b1)) b'))
  : Id Nat (pbg_lcm_quotient_right a1 b1 .fst) a'
  ≔ let A : Nat ≔ suc. a1 in let B : Nat ≔ suc. b1 in
    let G ≔ nat_gcd A B in let L ≔ nat_lcm A B in
    let q ≔ pbg_lcm_quotient_left a1 b1 .fst in
    let r ≔ pbg_lcm_quotient_right a1 b1 .fst in
    let qb ≔ cpx_quotient_left_eq a1 b1 a' b' ha hb in
    nat_mul_cancel_positive B r a' star. (calc
      mul r B = L by inverse Nat L (mul r B) (pbg_lcm_quotient_right a1 b1 .snd)
      = mul q A by pbg_lcm_quotient_left a1 b1 .snd
      = mul b' A by refl ((x ↦ mul x A) : Nat → Nat) qb
      = mul b' (mul G a') by refl (mul b') ha
      = mul G (mul b' a') by cpx_mul_swap b' G a'
      = mul G (mul a' b') by refl (mul G) (mul_comm b' a')
      = mul a' (mul G b') by cpx_mul_swap G a' b'
      = mul a' B by refl (mul a') (inverse Nat B (mul G b') hb) ∎)

def cpx_lcm_identities (a1 b1 a' b' : Nat)
  (ha : Id Nat (suc. a1) (mul (nat_gcd (suc. a1) (suc. b1)) a'))
  (hb : Id Nat (suc. b1) (mul (nat_gcd (suc. a1) (suc. b1)) b'))
  : Product (Id Nat (nat_lcm (suc. a1) (suc. b1)) (mul a' (suc. b1)))
      (Product (Id Nat (nat_lcm (suc. a1) (suc. b1)) (mul (nat_gcd (suc. a1) (suc. b1)) (mul a' b')))
        (Id Nat (nat_lcm (suc. a1) (suc. b1)) (mul (suc. a1) b')))
  ≔ let A : Nat ≔ suc. a1 in let B : Nat ≔ suc. b1 in
    let G ≔ nat_gcd A B in let L ≔ nat_lcm A B in
    let r ≔ pbg_lcm_quotient_right a1 b1 .fst in
    let ra ≔ cpx_quotient_right_eq a1 b1 a' b' ha hb in
    let l1 : Id Nat L (mul a' B) ≔ calc
        L = mul r B by pbg_lcm_quotient_right a1 b1 .snd
        = mul a' B by refl ((x ↦ mul x B) : Nat → Nat) ra
        = mul a' B by refl (mul a' B) ∎ in
    let l2 : Id Nat L (mul G (mul a' b')) ≔ calc
        L = mul a' B by l1
        = mul a' (mul G b') by refl (mul a') hb
        = mul G (mul a' b') by cpx_mul_swap a' G b' ∎ in
    let l3 : Id Nat L (mul A b') ≔ calc
        L = mul G (mul a' b') by l2
        = mul (mul G a') b' by inverse Nat (mul (mul G a') b') (mul G (mul a' b')) (mul_assoc G a' b')
        = mul A b' by refl ((x ↦ mul x b') : Nat → Nat) (inverse Nat A (mul G a') ha) ∎ in
    (l1, (l2, l3))

{` Transport commutes with a fiberwise map; transport cancels its inverse. `}
def cpx_transport_natural (X : Type) (F O : X → Type) (c : (x : X) → F x → O x) (x y : X) (p : Id X x y) (u : F x)
  : Id (O y) (transport X O x y p (c x u)) (c y (transport X F x y p u))
  ≔ J X x (y p ↦ Id (O y) (transport X O x y p (c x u)) (c y (transport X F x y p u)))
      (concat (O x) (transport X O x x (refl x) (c x u)) (c x u) (c x (transport X F x x (refl x) u))
        (transport_refl X O x (c x u))
        (refl (c x) (inverse (F x) (transport X F x x (refl x) u) u (transport_refl X F x u))))
      y p

def cpx_transport_section (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B y)
  : Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b
  ≔ J A x (y p ↦ (b : B y) → Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b)
      (b ↦ calc
        transport A B x x (refl x) (transport A B x x (inverse A x x (refl x)) b)
        = transport A B x x (inverse A x x (refl x)) b by transport_refl A B x (transport A B x x (inverse A x x (refl x)) b)
        = transport A B x x (refl x) b
          by refl ((q ↦ transport A B x x q b) : Id A x x → B x) (inverse_refl A x)
        = b by transport_refl A B x b ∎)
      y p b

def cpx_set_trunc_class (A B : Type) (E : Equiv A B) (t : A)
  : Id (SetTrunc B) (cpp_set_trunc_equiv A B E .map (set_trunc A t)) (set_trunc B (E .map t))
  ≔ concat (SetTrunc B) (cpp_set_trunc_equiv A B E .map (set_trunc A t))
      (transport Type SetTrunc A B (ua A B E) (set_trunc A t)) (set_trunc B (E .map t))
      (id_to_equiv_transport (SetTrunc A) (SetTrunc B) (refl SetTrunc (ua A B E)) (set_trunc A t))
      (cpx_transport_natural Type (T ↦ T) SetTrunc set_trunc A B (ua A B E) t)

{` Classes of orbits move along free-loop identifications by transport. `}
def cpx_orbit_class (C : CircleSignature) (b : Nat) (t : FreeLoop (C .carrier)) (x : cpp_fam C b (t .fst))
  : cpp_free_loop_orbits C b t
  ≔ quotient_class (cpp_fam C b (t .fst))
      (orbit_relation (cpp_fam C b (t .fst))
        (transport_equiv (cpp_fam C b (t .fst)) (cpp_fam C b (t .fst)) (refl (cpp_fam C b) (t .snd)))) x

def cpx_free_loop_class (C : CircleSignature) (b : Nat) (t t' : FreeLoop (C .carrier))
  (p : Id (FreeLoop (C .carrier)) t t') (x : cpp_fam C b (t .fst))
  : Id (cpp_free_loop_orbits C b t')
      (id_to_equiv (cpp_free_loop_orbits C b t) (cpp_free_loop_orbits C b t') (refl (cpp_free_loop_orbits C b) p) .map
        (cpx_orbit_class C b t x))
      (cpx_orbit_class C b t' (transport (C .carrier) (cpp_fam C b) (t .fst) (t' .fst) (p .fst) x))
  ≔ concat (cpp_free_loop_orbits C b t')
      (id_to_equiv (cpp_free_loop_orbits C b t) (cpp_free_loop_orbits C b t') (refl (cpp_free_loop_orbits C b) p) .map
        (cpx_orbit_class C b t x))
      (transport (FreeLoop (C .carrier)) (cpp_free_loop_orbits C b) t t' p (cpx_orbit_class C b t x))
      (cpx_orbit_class C b t' (transport (C .carrier) (cpp_fam C b) (t .fst) (t' .fst) (p .fst) x))
      (id_to_equiv_transport (cpp_free_loop_orbits C b t) (cpp_free_loop_orbits C b t') (refl (cpp_free_loop_orbits C b) p)
        (cpx_orbit_class C b t x))
      (cpx_transport_natural (FreeLoop (C .carrier)) (s ↦ cpp_fam C b (s .fst)) (cpp_free_loop_orbits C b)
        (cpx_orbit_class C b) t t' p x)

{` First coordinates of fiber elements are kept by transport and by the deck transformation. `}
def cpx_fib_transport_fst (C : CircleSignature) (b : Nat) (y y' : C .carrier) (p : Id (C .carrier) y y') (u : cpp_fam C b y)
  : Id (C .carrier) (transport (C .carrier) (cpp_fam C b) y y' p u .fst) (u .fst)
  ≔ J (C .carrier) y (y' p ↦ Id (C .carrier) (transport (C .carrier) (cpp_fam C b) y y' p u .fst) (u .fst))
      (refl ((v ↦ v .fst) : cpp_fam C b y → C .carrier) (transport_refl (C .carrier) (cpp_fam C b) y u)) y' p

def cpx_iterate_invariant (A B : Type) (h : A → B) (f : A → A) (hf : (u : A) → Id B (h (f u)) (h u)) (n : Nat) (u : A)
  : Id B (h (iterate A f n u)) (h u)
  ≔ match n [
    | zero. ↦ refl (h u)
    | suc. k ↦ concat B (h (f (iterate A f k u))) (h (iterate A f k u)) (h u) (hf (iterate A f k u))
        (cpx_iterate_invariant A B h f hf k u) ]

def cpx_perm_invariant (A B : Type) (h : A → B) (e : Equiv A A) (he : (u : A) → Id B (h (e .map u)) (h u)) (z : Int) (u : A)
  : Id B (h (permutation_power A e z u)) (h u)
  ≔ let inv ≔ equiv_inverse_map A A e in
    let hi : (v : A) → Id B (h (inv v)) (h v)
      ≔ v ↦ concat B (h (inv v)) (h (e .map (inv v))) (h v) (inverse B (h (e .map (inv v))) (h (inv v)) (he (inv v)))
             (refl h (equiv_counit A A e v)) in
    match z [
    | pos. n ↦ cpx_iterate_invariant A B h (e .map) he n u
    | neg. n ↦ cpx_iterate_invariant A B h inv hi (suc. n) u ]

{` The explicit points pt_n of P (a = a1+1, b = b1+1). `}
def cpx_y0 (C : CircleSignature) (b1 : Nat) : cpp_fam C (suc. b1) (C .base)
  ≔ degree_cover_base_point C (suc. b1) (lt_to_book zero. (suc. b1) star.)

def cpx_fiber_point (C : CircleSignature) (a1 b1 : Nat) (n : Int)
  : cpp_fam C (suc. b1) (circle_degree_map C (suc. a1) (C .base))
  ≔ transport (C .carrier) (cpp_fam C (suc. b1)) (C .base) (circle_degree_map C (suc. a1) (C .base))
      (inverse (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (C .base) (circle_degree_boundary C (suc. a1) .fst))
      (permutation_power (cpp_fam C (suc. b1) (C .base)) (cpp_cycle C b1 .fst .snd) n (cpx_y0 C b1))

def cpx_point (C : CircleSignature) (a1 b1 : Nat) (n : Int) : CirclePowerPullback C (suc. a1) (suc. b1)
  ≔ ((C .base, cpx_fiber_point C a1 b1 n .fst), cpx_fiber_point C a1 b1 n .snd)

def cpx_point_w (C : CircleSignature) (a1 b1 : Nat) (n : Int)
  : Id (C .carrier) (cpx_fiber_point C a1 b1 n .fst) (C .base)
  ≔ let S ≔ C .carrier in let o ≔ C .base in
    let Fb ≔ cpp_fam C (suc. b1) in
    let y ≔ permutation_power (Fb o) (cpp_cycle C b1 .fst .snd) n (cpx_y0 C b1) in
    concat S (cpx_fiber_point C a1 b1 n .fst) (y .fst) o
      (cpx_fib_transport_fst C (suc. b1) o (circle_degree_map C (suc. a1) o)
        (inverse S (circle_degree_map C (suc. a1) o) o (circle_degree_boundary C (suc. a1) .fst)) y)
      (cpx_perm_invariant (Fb o) S (v ↦ v .fst) (cpp_cycle C b1 .fst .snd)
        (u ↦ cpx_fib_transport_fst C (suc. b1) o o (C .loop) u) n (cpx_y0 C b1))

{` The component equivalence of module 826 sends pt_n to the class of n. `}
def cpx_point_class (C : CircleSignature) (a1 b1 : Nat) (n : Int)
  : Id (SubgroupQuotient (Multiples (nat_gcd (suc. a1) (suc. b1))) (multiples_laws (nat_gcd (suc. a1) (suc. b1))))
      (circle_power_pullback_components C a1 b1 .map
        (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 n)))
      (subgroup_class (Multiples (nat_gcd (suc. a1) (suc. b1))) (multiples_laws (nat_gcd (suc. a1) (suc. b1))) n)
  ≔ let a : Nat ≔ suc. a1 in let b : Nat ≔ suc. b1 in
    let S ≔ C .carrier in let o ≔ C .base in
    let P ≔ CirclePowerPullback C a b in
    let R ≔ cpp_family C a b in
    let Y ≔ cpp_fam C b o in
    let D ≔ SubgroupQuotient (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b)) in
    let c ≔ cpp_cycle C b1 in
    let O ≔ OrbitQuotient Y (cpp_monodromy_power C a b) in
    let stE ≔ cpp_set_trunc_equiv P (Σ S R) (cpp_total_equiv C a b) in
    let coE ≔ circle_components_orbits_equiv C R in
    let trE ≔ cpp_orbits_transport C a b in
    let cpoe ≔ cycle_power_orbits_equiv Y (c .fst .fst .snd) (c .fst .snd) (c .snd) (cpx_y0 C b1) a b
                 (cpp_cycle_per C b1) (cpp_cycle_rep C b1) (cpp_monodromy_power C a b) (cpp_monodromy_power_he C a b1) in
    let inv ≔ equiv_inverse_map D O cpoe in
    let x ≔ cpx_fiber_point C a1 b1 n in
    let y ≔ permutation_power Y (c .fst .snd) n (cpx_y0 C b1) in
    let bnd ≔ circle_degree_boundary C a in
    calc
      inv (trE .map (coE .map (stE .map (set_trunc P (cpx_point C a1 b1 n)))))
      = inv (trE .map (coE .map (set_trunc (Σ S R) (o, x))))
        by refl ((u ↦ inv (trE .map (coE .map u))) : SetTrunc (Σ S R) → D)
             (cpx_set_trunc_class P (Σ S R) (cpp_total_equiv C a b) (cpx_point C a1 b1 n))
      = inv (trE .map (cpx_orbit_class C b (circle_eval C S (circle_degree_map C a)) x))
        by refl ((u ↦ inv (trE .map u)) : OrbitQuotient (R o) (family_monodromy C R) → D)
             (circle_components_orbits_beta C R x)
      = inv (cpx_orbit_class C b (o, cpp_power_loop C a) (transport S (cpp_fam C b) (circle_degree_map C a o) o (bnd .fst) x))
        by refl inv (cpx_free_loop_class C b (circle_eval C S (circle_degree_map C a)) (o, cpp_power_loop C a) bnd x)
      = inv (cpx_orbit_class C b (o, cpp_power_loop C a) y)
        by refl ((u ↦ inv (cpx_orbit_class C b (o, cpp_power_loop C a) u)) : Y → D)
             (cpx_transport_section S (cpp_fam C b) (circle_degree_map C a o) o (bnd .fst) y)
      = subgroup_class (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b)) n
        by equiv_retraction D O cpoe (subgroup_class (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b)) n) ∎

{` Fin m ≃ ℤ/mℤ, j ↦ [j], for m > 0 (division with remainder, module 56). `}
def cpx_iota (m : Nat) (j : Fin m) : Int ≔ pos. (fin_book_below_equiv m .map j .fst)

def cpx_fin_class (m : Nat) (j : Fin m) : SubgroupQuotient (Multiples m) (multiples_laws m)
  ≔ subgroup_class (Multiples m) (multiples_laws m) (cpx_iota m j)

def cpx_fin_class_injective (m : Nat) (positive : BookLt zero. m)
  : PathReflecting (Fin m) (SubgroupQuotient (Multiples m) (multiples_laws m)) (cpx_fin_class m)
  ≔ j j' h ↦
    let R ≔ subgroup_relation (Multiples m) (multiples_laws m) in
    let x ≔ cpx_iota m j in let x' ≔ cpx_iota m j' in
    mere_rec (MultipleWitness m (int_sub x x')) (Id (Fin m) j j') (fin_set m j j')
      (w ↦ refl ((pr ↦ pr .fst) : Product (Fin m) Int → Fin m)
        (equivalence_injective (Product (Fin m) Int) Int
          (native_equivalence (Product (Fin m) Int) Int (integer_radix_equiv m positive)) (j, int_zero) (j', w .fst)
          (calc
            int_add x (int_mul (pos. m) int_zero) = x
              by refl (int_add x) (concat Int (int_mul (pos. m) int_zero) (int_mul int_zero (pos. m)) int_zero
                   (int_mul_comm (pos. m) int_zero) (int_mul_zero_left_pos m))
            = int_add (int_sub x x') x' by inverse Int (int_add (int_sub x x') x') x (int_sub_add x x')
            = int_add (int_mul (w .fst) (pos. m)) x' by refl ((z ↦ int_add z x') : Int → Int) (w .snd)
            = int_add x' (int_mul (w .fst) (pos. m)) by int_add_comm (int_mul (w .fst) (pos. m)) x'
            = int_add x' (int_mul (pos. m) (w .fst)) by refl (int_add x') (int_mul_comm (w .fst) (pos. m)) ∎)))
      (quotient_effective Int R x x' .map h)

def cpx_fin_class_surjective (m : Nat) (positive : BookLt zero. m)
  : Surjective (Fin m) (SubgroupQuotient (Multiples m) (multiples_laws m)) (cpx_fin_class m)
  ≔ z ↦
    let Q ≔ SubgroupQuotient (Multiples m) (multiples_laws m) in
    let R ≔ subgroup_relation (Multiples m) (multiples_laws m) in
    let T ≔ BookFiber (Fin m) Q (cpx_fin_class m) z in
    mere_rec (BookFiber Int Q (subgroup_class (Multiples m) (multiples_laws m)) z) (Mere T) (mere_isprop T)
      (u ↦ let n ≔ u .fst in
        let dg ≔ integer_radix_digits m positive n in
        let x ≔ cpx_iota m (dg .fst) in
        mere T (dg .fst,
          concat Q z (subgroup_class (Multiples m) (multiples_laws m) n) (cpx_fin_class m (dg .fst)) (u .snd)
            (quotient_encode Int R n x
              (mere (MultipleWitness m (int_sub n x)) (dg .snd, calc
                int_sub n x = int_sub (integer_radix_value m dg) x
                  by refl ((y ↦ int_sub y x) : Int → Int)
                       (inverse Int (integer_radix_value m dg) n (integer_radix_recompose m positive n))
                = int_mul (pos. m) (dg .snd) by int_sub_sum_left x (int_mul (pos. m) (dg .snd))
                = int_mul (dg .snd) (pos. m) by int_mul_comm (pos. m) (dg .snd) ∎)))))
      (quotient_surjective Int R z)

def cpx_fin_quotient_equiv (m : Nat) (positive : BookLt zero. m)
  : Equiv (Fin m) (SubgroupQuotient (Multiples m) (multiples_laws m))
  ≔ set_bijection_equiv (Fin m) (SubgroupQuotient (Multiples m) (multiples_laws m))
      (subgroup_quotient_set (Multiples m) (multiples_laws m)) (cpx_fin_class m)
      (cpx_fin_class_injective m positive) (cpx_fin_class_surjective m positive)

{` For every component index k an explicit point of that component. `}
def cpx_gcd_book_positive (a1 b1 : Nat) : BookLt zero. (nat_gcd (suc. a1) (suc. b1))
  ≔ transport Nat (x ↦ BookLt zero. x) (suc. (cpp_gcd_positive a1 b1 .fst)) (nat_gcd (suc. a1) (suc. b1))
      (inverse Nat (nat_gcd (suc. a1) (suc. b1)) (suc. (cpp_gcd_positive a1 b1 .fst)) (cpp_gcd_positive a1 b1 .snd))
      (lt_to_book zero. (suc. (cpp_gcd_positive a1 b1 .fst)) star.)

def cpx_index_point (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1))) : Int
  ≔ let G ≔ nat_gcd (suc. a1) (suc. b1) in
    let Q ≔ SubgroupQuotient (Multiples G) (multiples_laws G) in
    cpx_iota G (equiv_inverse_map (Fin G) Q (cpx_fin_quotient_equiv G (cpx_gcd_book_positive a1 b1))
      (equiv_inverse_map Q (Fin G) (cpp_multiples_quotient_fin_any G (cpp_gcd_positive a1 b1 .fst) (cpp_gcd_positive a1 b1 .snd)) k))

def cpx_index_hits (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : Id (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
      (equiv_inverse_map (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
        (circle_power_pullback_components_fin C a1 b1) k)
      (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 (cpx_index_point C a1 b1 k)))
  ≔ let G ≔ nat_gcd (suc. a1) (suc. b1) in
    let F ≔ Fin G in
    let Q ≔ SubgroupQuotient (Multiples G) (multiples_laws G) in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let e ≔ circle_power_pullback_components_fin C a1 b1 in
    let e2 ≔ cpp_multiples_quotient_fin_any G (cpp_gcd_positive a1 b1 .fst) (cpp_gcd_positive a1 b1 .snd) in
    let gE ≔ cpx_fin_quotient_equiv G (cpx_gcd_book_positive a1 b1) in
    let n ≔ cpx_index_point C a1 b1 k in
    let pt ≔ set_trunc P (cpx_point C a1 b1 n) in
    let h1 : Id F (e .map pt) k ≔ calc
        e .map pt = e2 .map (subgroup_class (Multiples G) (multiples_laws G) n)
          by refl (e2 .map) (cpx_point_class C a1 b1 n)
        = e2 .map (equiv_inverse_map Q F e2 k)
          by refl (e2 .map) (equiv_counit F Q gE (equiv_inverse_map Q F e2 k))
        = k by equiv_counit Q F e2 k ∎ in
    concat (SetTrunc P) (equiv_inverse_map (SetTrunc P) F e k) (equiv_inverse_map (SetTrunc P) F e (e .map pt)) pt
      (refl (equiv_inverse_map (SetTrunc P) F e) (inverse F (e .map pt) k h1))
      (equiv_retraction (SetTrunc P) F e pt)

{` Moving pt_n to a point cpl_point δ of module 828. `}
def cpx_delta (C : CircleSignature) (a1 b1 : Nat) (n : Int)
  : Σ (Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base)))
      (d ↦ Id (CirclePowerPullback C (suc. a1) (suc. b1)) ((C .base, C .base), d) (cpx_point C a1 b1 n))
  ≔ cpl_move_to_base C (suc. a1) (suc. b1) (C .base) (refl (C .base)) (cpx_fiber_point C a1 b1 n .fst)
      (inverse (C .carrier) (cpx_fiber_point C a1 b1 n .fst) (C .base) (cpx_point_w C a1 b1 n))
      (cpx_fiber_point C a1 b1 n .snd)

def cpx_choice_delta (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : Id (C .carrier) (circle_degree_map C (suc. a1) (C .base)) (circle_degree_map C (suc. b1) (C .base))
  ≔ cpx_delta C a1 b1 (cpx_index_point C a1 b1 k) .fst

def cpx_choice_hits (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : Id (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
      (equiv_inverse_map (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
        (circle_power_pullback_components_fin C a1 b1) k)
      (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpl_point C a1 b1 (cpx_choice_delta C a1 b1 k)))
  ≔ let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let n ≔ cpx_index_point C a1 b1 k in
    let dv ≔ cpx_delta C a1 b1 n in
    concat (SetTrunc P) (equiv_inverse_map (SetTrunc P) (Fin (nat_gcd (suc. a1) (suc. b1))) (circle_power_pullback_components_fin C a1 b1) k)
      (set_trunc P (cpx_point C a1 b1 n)) (set_trunc P (cpl_point C a1 b1 (dv .fst)))
      (cpx_index_hits C a1 b1 k)
      (refl (set_trunc P) (inverse P (cpl_point C a1 b1 (dv .fst)) (cpx_point C a1 b1 n)
        (concat P (cpl_point C a1 b1 (dv .fst)) ((C .base, C .base), dv .fst) (cpx_point C a1 b1 n)
          (cpl_twist_cancel C a1 b1 (dv .fst)) (dv .snd))))

{` The explicit choice of a copy of the lcm-fold covering on every component. `}
def cpx_choice (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : CplLcmCover C a1 b1
      (equiv_inverse_map (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
        (circle_power_pullback_components_fin C a1 b1) k)
  ≔ let S ≔ C .carrier in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let c ≔ equiv_inverse_map (SetTrunc P) (Fin (nat_gcd (suc. a1) (suc. b1))) (circle_power_pullback_components_fin C a1 b1) k in
    let d ≔ cpx_choice_delta C a1 b1 k in
    let K ≔ cpl_component_lcm_cover C a1 b1 d in
    let e2 ≔ cpl_component_native_equiv P (cpl_point C a1 b1 d) c (cpx_choice_hits C a1 b1 k) in
    (book_equivalence S (CplComponent C (suc. a1) (suc. b1) c)
       (compose_equiv S (NativeComponent P (cpl_point C a1 b1 d)) (CplComponent C (suc. a1) (suc. b1) c)
         (native_equivalence S (NativeComponent P (cpl_point C a1 b1 d)) (K .fst)) e2),
     K .snd)

{` ex:pullbackandgcd: P ≃ S¹ × Fin(gcd(a,b)), explicitly, with (z,w) ↦ z^a becoming (x,k) ↦ x^{lcm}. `}
def circle_pullback_explicit_decomposition (C : CircleSignature) (a1 b1 : Nat) : CplProductDecomposition C a1 b1
  ≔ cpl_product_from_choice C a1 b1 (cpx_choice C a1 b1)

{` Its coordinates on the copy k are the degree maps z ↦ z^{L/a} and z ↦ z^{L/b}. `}
def circle_pullback_explicit_coordinates (C : CircleSignature) (a1 b1 : Nat) (k : Fin (nat_gcd (suc. a1) (suc. b1)))
  : Product
      (Id (C .carrier → C .carrier) (z ↦ circle_pullback_explicit_decomposition C a1 b1 .fst .map (z, k) .fst .fst)
        (circle_degree_map C (pbg_lcm_quotient_left a1 b1 .fst)))
      (Id (C .carrier → C .carrier) (z ↦ circle_pullback_explicit_decomposition C a1 b1 .fst .map (z, k) .fst .snd)
        (circle_degree_map C (pbg_lcm_quotient_right a1 b1 .fst)))
  ≔ circle_pullback_pair_map C a1 b1 (cpx_choice_delta C a1 b1 k) .snd

{` The displayed square in the book's terms: with d = gcd(a,b), a = d a',
   b = d b', an explicit equivalence S¹ × Fin d ≃ P whose coordinates on
   every copy are z ↦ z^{b'} and z ↦ z^{a'}, and on which (z,w) ↦ z^a is
   (x,k) ↦ x^{lcm(a,b)}. `}
def circle_pullback_explicit_square (C : CircleSignature) (a1 b1 a' b' : Nat)
  (ha : Id Nat (suc. a1) (mul (nat_gcd (suc. a1) (suc. b1)) a'))
  (hb : Id Nat (suc. b1) (mul (nat_gcd (suc. a1) (suc. b1)) b'))
  : Σ (Equiv (Product (C .carrier) (Fin (nat_gcd (suc. a1) (suc. b1)))) (CirclePowerPullback C (suc. a1) (suc. b1))) (E ↦
      Product
        ((k : Fin (nat_gcd (suc. a1) (suc. b1)))
         → Product (Id (C .carrier → C .carrier) (z ↦ E .map (z, k) .fst .fst) (circle_degree_map C b'))
                   (Id (C .carrier → C .carrier) (z ↦ E .map (z, k) .fst .snd) (circle_degree_map C a')))
        (Id (Product (C .carrier) (Fin (nat_gcd (suc. a1) (suc. b1))) → C .carrier)
          (t ↦ circle_degree_map C (suc. a1) (E .map t .fst .fst))
          (t ↦ circle_degree_map C (nat_lcm (suc. a1) (suc. b1)) (t .fst))))
  ≔ let S ≔ C .carrier in
    let E ≔ circle_pullback_explicit_decomposition C a1 b1 in
    (E .fst,
     (k ↦ (concat (S → S) (z ↦ E .fst .map (z, k) .fst .fst) (circle_degree_map C (pbg_lcm_quotient_left a1 b1 .fst))
             (circle_degree_map C b')
             (circle_pullback_explicit_coordinates C a1 b1 k .fst)
             (refl (circle_degree_map C) (cpx_quotient_left_eq a1 b1 a' b' ha hb)),
           concat (S → S) (z ↦ E .fst .map (z, k) .fst .snd) (circle_degree_map C (pbg_lcm_quotient_right a1 b1 .fst))
             (circle_degree_map C a')
             (circle_pullback_explicit_coordinates C a1 b1 k .snd)
             (refl (circle_degree_map C) (cpx_quotient_right_eq a1 b1 a' b' ha hb))),
      E .snd))

{` The book's "(ζ^k z, w) lies in the same component as (z, w) iff d | k",
   synthetically (with the roles of a and b exchanged, as in module 826):
   the points pt_n, built from m^n(y0) for the deck transformation m of the
   b-fold covering, lie in the same component iff d divides n − n'. `}
def cpx_same_component_iff (C : CircleSignature) (a1 b1 : Nat) (n n' : Int)
  : Product
      (Id (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
          (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 n))
          (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 n'))
        → Multiples (nat_gcd (suc. a1) (suc. b1)) (int_sub n n') .fst)
      (Multiples (nat_gcd (suc. a1) (suc. b1)) (int_sub n n') .fst
        → Id (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
            (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 n))
            (set_trunc (CirclePowerPullback C (suc. a1) (suc. b1)) (cpx_point C a1 b1 n')))
  ≔ let G ≔ nat_gcd (suc. a1) (suc. b1) in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let Q ≔ SubgroupQuotient (Multiples G) (multiples_laws G) in
    let R ≔ subgroup_relation (Multiples G) (multiples_laws G) in
    let e1 ≔ circle_power_pullback_components C a1 b1 in
    let cl ≔ subgroup_class (Multiples G) (multiples_laws G) in
    let p ≔ set_trunc P (cpx_point C a1 b1 n) in let p' ≔ set_trunc P (cpx_point C a1 b1 n') in
    (h ↦ quotient_effective Int R n n' .map (calc
        cl n = e1 .map p by inverse Q (e1 .map p) (cl n) (cpx_point_class C a1 b1 n)
        = e1 .map p' by refl (e1 .map) h
        = cl n' by cpx_point_class C a1 b1 n' ∎),
     r ↦ equivalence_injective (SetTrunc P) Q e1 p p' (calc
        e1 .map p = cl n by cpx_point_class C a1 b1 n
        = cl n' by quotient_encode Int R n n' r
        = e1 .map p' by inverse Q (e1 .map p') (cl n') (cpx_point_class C a1 b1 n') ∎))
