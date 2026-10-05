export "822-pullback-group-symmetries"
export "435-circle-group-homomorphisms"
export "418-cyclic-group-images"
export "710-hom-delooping"
export "686-category-of-groups"
export "148-order-gcd-lcm"
export "145-order-quotient-images"
export "81-circle-degree-coverings"
export "825-cycle-power-orbits"

{` Chapter 8 (congp.tex), the example at line 471: for natural numbers
   a, b with least common multiple L, Lℤ is the intersection aℤ ∩ bℤ of the
   subgroups aℤ and bℤ of ℤ. Here ℤ ≔ circle_group C for an arbitrary
   circle C, and aℤ ↪ ℤ is the homomorphism ℤ → ℤ sending the generator
   loop to loop^a (multiplication by a). We take a, b > 0: multiplication
   by 0 is not a monomorphism (circle_multiplication_zero_not_mono), so
   0ℤ is not a subgroup in the sense of monomorphisms and the pullback of
   0 and b is not an intersection. `}

{` A homomorphism whose action on symmetries is an equivalence is an
   isomorphism (via the delooping lem:homomabstrconcr of module 710: the
   inverse of USym f is an abstract homomorphism, its delooping is the
   inverse of f in the category of groups). `}
def pbg_inverse_abstract_hom (G H : Group) (f : GroupHom G H) (g : USym H → USym G)
  (sect : (y : USym H) → Id (USym H) (usym_hom G H f (g y)) y)
  (retr : (x : USym G) → Id (USym G) (g (usym_hom G H f x)) x)
  : AbstractHom (abstr H) (abstr G)
  ≔ (g, s s' ↦ calc
      g (usym_mul H s s') = g (usym_hom G H f (usym_mul G (g s) (g s')))
        by refl g (calc
          usym_mul H s s' = usym_mul H (usym_hom G H f (g s)) (usym_hom G H f (g s'))
            by refl (usym_mul H) (inverse (USym H) (usym_hom G H f (g s)) s (sect s))
              (inverse (USym H) (usym_hom G H f (g s')) s' (sect s'))
          = usym_hom G H f (usym_mul G (g s) (g s'))
            by inverse (USym H) (usym_hom G H f (usym_mul G (g s) (g s')))
              (usym_mul H (usym_hom G H f (g s)) (usym_hom G H f (g s'))) (usym_hom_mul G H f (g s) (g s')) ∎)
      = usym_mul G (g s) (g s') by retr (usym_mul G (g s) (g s')) ∎)

def pbg_hom_ext_usym (G H : Group) (h h' : GroupHom G H)
  (e : (x : USym G) → Id (USym H) (usym_hom G H h x) (usym_hom G H h' x))
  : Id (GroupHom G H) h h'
  ≔ equivalence_injective (GroupHom G H) (AbstractHom (abstr G) (abstr H)) (abstr_hom_equiv G H) h h'
      (subtype_equal (USym G → USym H) (IsAbstractHom (abstr G) (abstr H)) (is_abstract_hom_prop (abstr G) (abstr H))
        (abstr_hom G H h) (abstr_hom G H h')
        (funext (USym G) (_ ↦ USym H) (usym_hom G H h) (usym_hom G H h') e))

def pbg_group_iso_from_usym_inverse (G H : Group) (f : GroupHom G H) (g : USym H → USym G)
  (sect : (y : USym H) → Id (USym H) (usym_hom G H f (g y)) y)
  (retr : (x : USym G) → Id (USym G) (g (usym_hom G H f x)) x)
  : IsGroupIso G H f
  ≔ let psi ≔ deloop_hom H G (pbg_inverse_abstract_hom G H f g sect retr) in
    let psi_usym : (y : USym H) → Id (USym G) (usym_hom H G psi y) (g y)
      ≔ y ↦ refl ((t ↦ t .fst y) : AbstractHom (abstr H) (abstr G) → USym G)
               (deloop_hom_section H G (pbg_inverse_abstract_hom G H f g sect retr)) in
    group_cat_is_iso_to_group_iso G H f
      ((psi, pbg_hom_ext_usym H H (group_hom_compose H G H psi f) (group_hom_id H) (y ↦ calc
          usym_hom H H (group_hom_compose H G H psi f) y = usym_hom G H f (usym_hom H G psi y)
            by usym_hom_compose H G H psi f (refl y)
          = usym_hom G H f (g y) by refl (usym_hom G H f) (psi_usym y)
          = y by sect y
          = usym_hom H H (group_hom_id H) y by inverse (USym H) (usym_hom H H (group_hom_id H) y) y (usym_hom_id H y) ∎)),
       (psi, pbg_hom_ext_usym G G (group_hom_compose G H G f psi) (group_hom_id G) (x ↦ calc
          usym_hom G G (group_hom_compose G H G f psi) x = usym_hom H G psi (usym_hom G H f x)
            by usym_hom_compose G H G f psi (refl x)
          = g (usym_hom G H f x) by psi_usym (usym_hom G H f x)
          = x by retr x
          = usym_hom G G (group_hom_id G) x by inverse (USym G) (usym_hom G G (group_hom_id G) x) x (usym_hom_id G x) ∎)))

def pbg_group_iso_from_usym_equiv (G H : Group) (f : GroupHom G H) (e : Equiv (USym G) (USym H))
  (he : (x : USym G) → Id (USym H) (e .map x) (usym_hom G H f x))
  : IsGroupIso G H f
  ≔ pbg_group_iso_from_usym_inverse G H f (equiv_inverse_map (USym G) (USym H) e)
      (y ↦ concat (USym H) (usym_hom G H f (equiv_inverse_map (USym G) (USym H) e y))
        (e .map (equiv_inverse_map (USym G) (USym H) e y)) y
        (inverse (USym H) (e .map (equiv_inverse_map (USym G) (USym H) e y))
          (usym_hom G H f (equiv_inverse_map (USym G) (USym H) e y)) (he (equiv_inverse_map (USym G) (USym H) e y)))
        (equiv_counit (USym G) (USym H) e y))
      (x ↦ concat (USym G) (equiv_inverse_map (USym G) (USym H) e (usym_hom G H f x))
        (equiv_inverse_map (USym G) (USym H) e (e .map x)) x
        (refl (equiv_inverse_map (USym G) (USym H) e)
          (inverse (USym H) (e .map x) (usym_hom G H f x) (he x)))
        (inverse (USym G) x (equiv_inverse_map (USym G) (USym H) e (e .map x)) (equiv_unit (USym G) (USym H) e x)))

{` Homomorphisms ℤ → G are equal when they agree on the generator
   (ex:Zinitial, module 435). `}
def pbg_circle_hom_ext (C : CircleSignature) (G : Group) (h h' : GroupHom (circle_group C) G)
  (e : Id (USym G) (usym_hom (circle_group C) G h (circle_group_loop C)) (usym_hom (circle_group C) G h' (circle_group_loop C)))
  : Id (GroupHom (circle_group C) G) h h'
  ≔ equivalence_injective (GroupHom (circle_group C) G) (USym G) (circle_group_hom_ev C G) h h' e

{` Multiplication by z : ℤ, the homomorphism ℤ → ℤ with loop ↦ loop^z. `}
def circle_multiplication_hom (C : CircleSignature) (z : Int) : GroupHom (circle_group C) (circle_group C)
  ≔ circle_group_hom_from_symmetry C (circle_group C) (circle_power C z)

def pbg_winding_injective (C : CircleSignature) (g g' : USym (circle_group C))
  (h : Id Int (circle_winding C g) (circle_winding C g')) : Id (USym (circle_group C)) g g'
  ≔ calc
      g = circle_power C (circle_winding C g)
        by inverse (USym (circle_group C)) (circle_power C (circle_winding C g)) g (circle_power_winding C g)
      = circle_power C (circle_winding C g') by refl (circle_power C) h
      = g' by circle_power_winding C g' ∎

{` A homomorphism ℤ → ℤ sending loop to loop^z multiplies windings by z. `}
def CircleHomLoop (C : CircleSignature) (f : GroupHom (circle_group C) (circle_group C)) (z : Int) : Type
  ≔ Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) f (circle_group_loop C)) (circle_power C z)

def circle_hom_winding (C : CircleSignature) (z : Int) (f : GroupHom (circle_group C) (circle_group C))
  (hf : CircleHomLoop C f z) (g : USym (circle_group C))
  : Id Int (circle_winding C (usym_hom (circle_group C) (circle_group C) f g)) (int_mul (circle_winding C g) z)
  ≔ let Z ≔ circle_group C in
    let m ≔ f in
    let k ≔ circle_winding C g in
    calc
      circle_winding C (usym_hom Z Z m g) = circle_winding C (usym_hom Z Z m (circle_power C k))
        by refl ((x ↦ circle_winding C (usym_hom Z Z m x)) : USym Z → Int)
          (inverse (USym Z) (circle_power C k) g (circle_power_winding C g))
      = circle_winding C (loop_power (C .carrier) (C .base) (usym_hom Z Z m (circle_group_loop C)) k)
        by refl (circle_winding C) (loops_map_power (BG Z) (BG Z) (hom_B Z Z m) (circle_group_loop C) k)
      = circle_winding C (loop_power (C .carrier) (C .base) (circle_power C z) k)
        by refl ((x ↦ circle_winding C (loop_power (C .carrier) (C .base) x k)) : USym Z → Int) hf
      = int_mul (circle_winding C (circle_power C z)) k by circle_winding_power_arbitrary C (circle_power C z) k
      = int_mul z k by refl ((x ↦ int_mul x k) : Int → Int) (circle_winding_power C z)
      = int_mul k z by int_mul_comm z k ∎

def circle_multiplication_loop (C : CircleSignature) (z : Int)
  : Id (USym (circle_group C))
      (usym_hom (circle_group C) (circle_group C) (circle_multiplication_hom C z) (circle_group_loop C)) (circle_power C z)
  ≔ circle_group_hom_from_symmetry_loop C (circle_group C) (circle_power C z)

def circle_multiplication_winding (C : CircleSignature) (z : Int) (g : USym (circle_group C))
  : Id Int (circle_winding C (usym_hom (circle_group C) (circle_group C) (circle_multiplication_hom C z) g))
      (int_mul (circle_winding C g) z)
  ≔ circle_hom_winding C z (circle_multiplication_hom C z) (circle_multiplication_loop C z) g

{` For n > 0 multiplication by n is a monomorphism (aℤ is a subgroup). `}
def circle_hom_reflects (C : CircleSignature) (n : Nat) (f : GroupHom (circle_group C) (circle_group C))
  (hf : CircleHomLoop C f (pos. (suc. n)))
  : PathReflecting (USym (circle_group C)) (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) f)
  ≔ let Z ≔ circle_group C in
    let m ≔ f in
    g g' h ↦ pbg_winding_injective C g g'
      (int_mul_cancel_pos n (circle_winding C g) (circle_winding C g') (calc
        int_mul (circle_winding C g) (pos. (suc. n)) = circle_winding C (usym_hom Z Z m g)
          by inverse Int (circle_winding C (usym_hom Z Z m g)) (int_mul (circle_winding C g) (pos. (suc. n)))
            (circle_hom_winding C (pos. (suc. n)) f hf g)
        = circle_winding C (usym_hom Z Z m g') by refl (circle_winding C) h
        = int_mul (circle_winding C g') (pos. (suc. n)) by circle_hom_winding C (pos. (suc. n)) f hf g' ∎))

def circle_hom_mono (C : CircleSignature) (n : Nat) (f : GroupHom (circle_group C) (circle_group C))
  (hf : CircleHomLoop C f (pos. (suc. n)))
  : IsGroupMono (circle_group C) (circle_group C) f
  ≔ path_reflecting_set_embedding (USym (circle_group C)) (USym (circle_group C)) (usym_set (circle_group C))
      (usym_hom (circle_group C) (circle_group C) f) (circle_hom_reflects C n f hf)

def circle_multiplication_mono (C : CircleSignature) (n : Nat)
  : IsGroupMono (circle_group C) (circle_group C) (circle_multiplication_hom C (pos. (suc. n)))
  ≔ circle_hom_mono C n (circle_multiplication_hom C (pos. (suc. n))) (circle_multiplication_loop C (pos. (suc. n)))

def circle_multiplication_mono_object (C : CircleSignature) (n : Nat) : GroupMonos (circle_group C)
  ≔ (circle_group C, (circle_multiplication_hom C (pos. (suc. n)), circle_multiplication_mono C n))

{` Multiplication by 0 is not a monomorphism: it sends loop and refl to
   refl, and loop ≠ refl (their windings are 1 and 0). `}
def circle_multiplication_zero_not_mono (C : CircleSignature)
  (h : IsGroupMono (circle_group C) (circle_group C) (circle_multiplication_hom C (pos. zero.))) : Empty
  ≔ let Z ≔ circle_group C in
    let m ≔ circle_multiplication_hom C (pos. zero.) in
    let r ≔ embedding_reflects_paths (USym Z) (USym Z) (usym_hom Z Z m) h (circle_group_loop C) (usym_unit Z)
      (concat (USym Z) (usym_hom Z Z m (circle_group_loop C)) (circle_power C (pos. zero.)) (usym_hom Z Z m (usym_unit Z))
        (circle_multiplication_loop C (pos. zero.))
        (inverse (USym Z) (usym_hom Z Z m (usym_unit Z)) (usym_unit Z) (usym_hom_unit Z Z m))) in
    pbg_one_not_zero (calc
      (pos. (suc. zero.) : Int) = circle_winding C (circle_power C (pos. (suc. zero.)))
        by inverse Int (circle_winding C (circle_power C (pos. (suc. zero.)))) (pos. (suc. zero.))
          (circle_winding_power C (pos. (suc. zero.)))
      = circle_winding C (circle_group_loop C)
        by refl (circle_winding C) (concat_1p (C .carrier) (C .base) (C .base) (C .loop))
      = circle_winding C (usym_unit Z) by refl (circle_winding C) r
      = pos. zero. by circle_winding_power C (pos. zero.) ∎)

{` Exact quotients L = q·a for a > 0 (unique, so extracted from the mere
   divisibility witness). `}
def pbg_pos_injective (m n : Nat) (p : Id Int (pos. m) (pos. n)) : Id Nat m n
  ≔ refl ((z ↦ match z [ pos. k ↦ k | neg. _ ↦ zero. ]) : Int → Nat) p

def pbg_exact_quotient_prop (a1 L : Nat) : isProp (Σ Nat (q ↦ Id Nat L (mul q (suc. a1))))
  ≔ u v ↦ subtype_equal Nat (q ↦ Id Nat L (mul q (suc. a1))) (q ↦ nat_set L (mul q (suc. a1))) u v
      (pbg_pos_injective (u .fst) (v .fst) (int_mul_cancel_pos a1 (pos. (u .fst)) (pos. (v .fst)) (calc
        int_mul (pos. (u .fst)) (pos. (suc. a1)) = pos. (mul (u .fst) (suc. a1))
          by inverse Int (pos. (mul (u .fst) (suc. a1))) (int_mul (pos. (u .fst)) (pos. (suc. a1)))
            (int_mul_naturals (u .fst) (suc. a1))
        = pos. L by refl ((k ↦ pos. k) : Nat → Int) (inverse Nat L (mul (u .fst) (suc. a1)) (u .snd))
        = pos. (mul (v .fst) (suc. a1)) by refl ((k ↦ pos. k) : Nat → Int) (v .snd)
        = int_mul (pos. (v .fst)) (pos. (suc. a1)) by int_mul_naturals (v .fst) (suc. a1) ∎)))

def pbg_exact_quotient (a1 L : Nat) (h : NatDivides (suc. a1) L) : Σ Nat (q ↦ Id Nat L (mul q (suc. a1)))
  ≔ mere_rec (Σ Nat (q ↦ Id Nat L (mul q (suc. a1)))) (Σ Nat (q ↦ Id Nat L (mul q (suc. a1))))
      (pbg_exact_quotient_prop a1 L) (t ↦ t) h

{` The setting of the example: a = a1+1, b = b1+1, L = lcm(a,b) = qa·a = qb·b. `}
def pbg_lcm_quotient_left (a1 b1 : Nat) : Σ Nat (q ↦ Id Nat (nat_lcm (suc. a1) (suc. b1)) (mul q (suc. a1)))
  ≔ pbg_exact_quotient a1 (nat_lcm (suc. a1) (suc. b1)) (nat_lcm_multiple_left (suc. a1) (suc. b1))

def pbg_lcm_quotient_right (a1 b1 : Nat) : Σ Nat (q ↦ Id Nat (nat_lcm (suc. a1) (suc. b1)) (mul q (suc. b1)))
  ≔ pbg_exact_quotient b1 (nat_lcm (suc. a1) (suc. b1)) (nat_lcm_multiple_right (suc. a1) (suc. b1))

def CircleHomIntersection (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1))) : Group
  ≔ pullback_group (circle_group C) (circle_group C) (circle_group C)
      (f) (f')

{` Generic form: f, f' : ℤ → ℤ with f(loop) = loop^a, f'(loop) = loop^b
   (a, b > 0). The intersection as an element of Mono(ℤ). `}
def circle_hom_intersection_mono (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1))) : GroupMonos (circle_group C)
  ≔ group_mono_intersection (circle_group C) (circle_group C, (f, circle_hom_mono C a1 f hf)) (circle_group C, (f', circle_hom_mono C b1 f' hf'))

{` Windings of the homomorphisms applied to powers. `}
def pbg_hom_power_winding (C : CircleSignature) (z : Int) (f : GroupHom (circle_group C) (circle_group C))
  (hf : CircleHomLoop C f z) (k : Int)
  : Id Int (circle_winding C (usym_hom (circle_group C) (circle_group C) f (circle_power C k))) (int_mul k z)
  ≔ concat Int (circle_winding C (usym_hom (circle_group C) (circle_group C) f (circle_power C k)))
      (int_mul (circle_winding C (circle_power C k)) z) (int_mul k z)
      (circle_hom_winding C z f hf (circle_power C k))
      (refl ((x ↦ int_mul x z) : Int → Int) (circle_winding_power C k))

def circle_hom_intersection_generator_data (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : PullbackUSym (circle_group C) (circle_group C) (circle_group C)
      (f) (f')
  ≔ let qa ≔ pbg_lcm_quotient_left a1 b1 in
    let qb ≔ pbg_lcm_quotient_right a1 b1 in
    let L ≔ nat_lcm (suc. a1) (suc. b1) in
    let Z ≔ circle_group C in
    ((circle_power C (pos. (qa .fst)), circle_power C (pos. (qb .fst))),
     pbg_winding_injective C
       (usym_hom Z Z (f) (circle_power C (pos. (qa .fst))))
       (usym_hom Z Z (f') (circle_power C (pos. (qb .fst)))) (calc
         circle_winding C (usym_hom Z Z (f) (circle_power C (pos. (qa .fst))))
         = int_mul (pos. (qa .fst)) (pos. (suc. a1)) by pbg_hom_power_winding C (pos. (suc. a1)) f hf (pos. (qa .fst))
         = pos. (mul (qa .fst) (suc. a1))
           by inverse Int (pos. (mul (qa .fst) (suc. a1))) (int_mul (pos. (qa .fst)) (pos. (suc. a1)))
             (int_mul_naturals (qa .fst) (suc. a1))
         = pos. L by refl ((k ↦ pos. k) : Nat → Int) (inverse Nat L (mul (qa .fst) (suc. a1)) (qa .snd))
         = pos. (mul (qb .fst) (suc. b1)) by refl ((k ↦ pos. k) : Nat → Int) (qb .snd)
         = int_mul (pos. (qb .fst)) (pos. (suc. b1)) by int_mul_naturals (qb .fst) (suc. b1)
         = circle_winding C (usym_hom Z Z (f') (circle_power C (pos. (qb .fst))))
           by inverse Int (circle_winding C (usym_hom Z Z (f')
               (circle_power C (pos. (qb .fst)))))
             (int_mul (pos. (qb .fst)) (pos. (suc. b1))) (pbg_hom_power_winding C (pos. (suc. b1)) f' hf' (pos. (qb .fst))) ∎))

def circle_hom_intersection_generator (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1))) : USym (CircleHomIntersection C a1 b1 f f' hf hf')
  ≔ let Z ≔ circle_group C in
    equiv_inverse_map (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
      (PullbackUSym Z Z Z (f) (f'))
      (pullback_group_usym_equiv Z Z Z (f) (f'))
      (circle_hom_intersection_generator_data C a1 b1 f f' hf hf')

{` φ : ℤ → aℤ ∩ bℤ, loop ↦ the generator (loop^{L/a}, loop^{L/b}). `}
def circle_hom_intersection_map (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1))) : GroupHom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf')
  ≔ circle_group_hom_from_symmetry C (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_generator C a1 b1 f f' hf hf')

def pbg_hom_generator_left (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Id (USym (circle_group C))
      (usym_hom (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C)
        (pullback_group_proj_left (circle_group C) (circle_group C) (circle_group C)
          (f) (f'))
        (circle_hom_intersection_generator C a1 b1 f f' hf hf'))
      (circle_power C (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
  ≔ let Z ≔ circle_group C in
    refl ((t ↦ t .fst .fst) : PullbackUSym Z Z Z (f)
            (f') → USym Z)
      (equiv_counit (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
        (PullbackUSym Z Z Z (f) (f'))
        (pullback_group_usym_equiv Z Z Z (f) (f'))
        (circle_hom_intersection_generator_data C a1 b1 f f' hf hf'))

{` prj_{aℤ} ∘ φ is multiplication by L/a. `}
def circle_hom_intersection_proj_left (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Id (GroupHom (circle_group C) (circle_group C))
      (group_hom_compose (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C) (circle_hom_intersection_map C a1 b1 f f' hf hf')
        (pullback_group_proj_left (circle_group C) (circle_group C) (circle_group C)
          (f) (f')))
      (circle_multiplication_hom C (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let p1 ≔ pullback_group_proj_left Z Z Z (f) (f') in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    pbg_circle_hom_ext C Z (group_hom_compose Z P Z phi p1) (circle_multiplication_hom C (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
      (calc
        usym_hom Z Z (group_hom_compose Z P Z phi p1) (circle_group_loop C)
        = usym_hom P Z p1 (usym_hom Z P phi (circle_group_loop C)) by usym_hom_compose Z P Z phi p1 (refl (circle_group_loop C))
        = usym_hom P Z p1 (circle_hom_intersection_generator C a1 b1 f f' hf hf')
          by refl (usym_hom P Z p1) (circle_group_hom_from_symmetry_loop C P (circle_hom_intersection_generator C a1 b1 f f' hf hf'))
        = circle_power C (pos. (pbg_lcm_quotient_left a1 b1 .fst)) by pbg_hom_generator_left C a1 b1 f f' hf hf'
        = usym_hom Z Z (circle_multiplication_hom C (pos. (pbg_lcm_quotient_left a1 b1 .fst))) (circle_group_loop C)
          by inverse (USym Z) (usym_hom Z Z (circle_multiplication_hom C (pos. (pbg_lcm_quotient_left a1 b1 .fst))) (circle_group_loop C))
            (circle_power C (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
            (circle_multiplication_loop C (pos. (pbg_lcm_quotient_left a1 b1 .fst))) ∎)

def pbg_hom_generator_right (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Id (USym (circle_group C))
      (usym_hom (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C)
        (pullback_group_proj_right (circle_group C) (circle_group C) (circle_group C)
          (f) (f'))
        (circle_hom_intersection_generator C a1 b1 f f' hf hf'))
      (circle_power C (pos. (pbg_lcm_quotient_right a1 b1 .fst)))
  ≔ let Z ≔ circle_group C in
    refl ((t ↦ t .fst .snd) : PullbackUSym Z Z Z (f)
            (f') → USym Z)
      (equiv_counit (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
        (PullbackUSym Z Z Z (f) (f'))
        (pullback_group_usym_equiv Z Z Z (f) (f'))
        (circle_hom_intersection_generator_data C a1 b1 f f' hf hf'))

{` prj_{bℤ} ∘ φ is multiplication by L/b. `}
def circle_hom_intersection_proj_right (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Id (GroupHom (circle_group C) (circle_group C))
      (group_hom_compose (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C) (circle_hom_intersection_map C a1 b1 f f' hf hf')
        (pullback_group_proj_right (circle_group C) (circle_group C) (circle_group C)
          (f) (f')))
      (circle_multiplication_hom C (pos. (pbg_lcm_quotient_right a1 b1 .fst)))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let p2 ≔ pullback_group_proj_right Z Z Z (f) (f') in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    pbg_circle_hom_ext C Z (group_hom_compose Z P Z phi p2) (circle_multiplication_hom C (pos. (pbg_lcm_quotient_right a1 b1 .fst)))
      (calc
        usym_hom Z Z (group_hom_compose Z P Z phi p2) (circle_group_loop C)
        = usym_hom P Z p2 (usym_hom Z P phi (circle_group_loop C)) by usym_hom_compose Z P Z phi p2 (refl (circle_group_loop C))
        = usym_hom P Z p2 (circle_hom_intersection_generator C a1 b1 f f' hf hf')
          by refl (usym_hom P Z p2) (circle_group_hom_from_symmetry_loop C P (circle_hom_intersection_generator C a1 b1 f f' hf hf'))
        = circle_power C (pos. (pbg_lcm_quotient_right a1 b1 .fst)) by pbg_hom_generator_right C a1 b1 f f' hf hf'
        = usym_hom Z Z (circle_multiplication_hom C (pos. (pbg_lcm_quotient_right a1 b1 .fst))) (circle_group_loop C)
          by inverse (USym Z) (usym_hom Z Z (circle_multiplication_hom C (pos. (pbg_lcm_quotient_right a1 b1 .fst))) (circle_group_loop C))
            (circle_power C (pos. (pbg_lcm_quotient_right a1 b1 .fst)))
            (circle_multiplication_loop C (pos. (pbg_lcm_quotient_right a1 b1 .fst))) ∎)

{` The inclusion of the intersection composed with φ is multiplication by L:
   the triangle ℤ --φ--> aℤ ∩ bℤ --(a ∘ prj)--> ℤ equals Lℤ ↪ ℤ. `}
def circle_hom_intersection_triangle (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Id (GroupHom (circle_group C) (circle_group C))
      (group_hom_compose (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C) (circle_hom_intersection_map C a1 b1 f f' hf hf')
        (circle_hom_intersection_mono C a1 b1 f f' hf hf' .snd .fst))
      (circle_multiplication_hom C (pos. (nat_lcm (suc. a1) (suc. b1))))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let ma ≔ f in
    let p1 ≔ pullback_group_proj_left Z Z Z ma (f') in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    let qa ≔ pbg_lcm_quotient_left a1 b1 in
    let L ≔ nat_lcm (suc. a1) (suc. b1) in
    pbg_circle_hom_ext C Z (group_hom_compose Z P Z phi (group_hom_compose P Z Z p1 ma)) (circle_multiplication_hom C (pos. L))
      (pbg_winding_injective C (usym_hom Z Z (group_hom_compose Z P Z phi (group_hom_compose P Z Z p1 ma)) (circle_group_loop C))
        (usym_hom Z Z (circle_multiplication_hom C (pos. L)) (circle_group_loop C))
        (calc
          circle_winding C (usym_hom Z Z (group_hom_compose Z P Z phi (group_hom_compose P Z Z p1 ma)) (circle_group_loop C))
          = circle_winding C (usym_hom Z Z ma (usym_hom P Z p1 (usym_hom Z P phi (circle_group_loop C))))
            by refl (circle_winding C) (calc
              usym_hom Z Z (group_hom_compose Z P Z phi (group_hom_compose P Z Z p1 ma)) (circle_group_loop C)
              = usym_hom P Z (group_hom_compose P Z Z p1 ma) (usym_hom Z P phi (circle_group_loop C))
                by usym_hom_compose Z P Z phi (group_hom_compose P Z Z p1 ma) (refl (circle_group_loop C))
              = usym_hom Z Z ma (usym_hom P Z p1 (usym_hom Z P phi (circle_group_loop C)))
                by usym_hom_compose P Z Z p1 ma (refl (usym_hom Z P phi (circle_group_loop C))) ∎)
          = circle_winding C (usym_hom Z Z ma (circle_power C (pos. (qa .fst))))
            by refl ((x ↦ circle_winding C (usym_hom Z Z ma x)) : USym Z → Int) (calc
              usym_hom P Z p1 (usym_hom Z P phi (circle_group_loop C)) = usym_hom P Z p1 (circle_hom_intersection_generator C a1 b1 f f' hf hf')
                by refl (usym_hom P Z p1) (circle_group_hom_from_symmetry_loop C P (circle_hom_intersection_generator C a1 b1 f f' hf hf'))
              = circle_power C (pos. (qa .fst)) by pbg_hom_generator_left C a1 b1 f f' hf hf' ∎)
          = int_mul (pos. (qa .fst)) (pos. (suc. a1)) by pbg_hom_power_winding C (pos. (suc. a1)) f hf (pos. (qa .fst))
          = pos. (mul (qa .fst) (suc. a1))
            by inverse Int (pos. (mul (qa .fst) (suc. a1))) (int_mul (pos. (qa .fst)) (pos. (suc. a1)))
              (int_mul_naturals (qa .fst) (suc. a1))
          = pos. L by refl ((k ↦ pos. k) : Nat → Int) (inverse Nat L (mul (qa .fst) (suc. a1)) (qa .snd))
          = circle_winding C (circle_power C (pos. L))
            by inverse Int (circle_winding C (circle_power C (pos. L))) (pos. L) (circle_winding_power C (pos. L))
          = circle_winding C (usym_hom Z Z (circle_multiplication_hom C (pos. L)) (circle_group_loop C))
            by refl (circle_winding C)
              (inverse (USym Z) (usym_hom Z Z (circle_multiplication_hom C (pos. L)) (circle_group_loop C))
                (circle_power C (pos. L)) (circle_multiplication_loop C (pos. L))) ∎))

{` φ is an isomorphism ℤ ≅ aℤ ∩ bℤ. Injectivity: prj_{aℤ} ∘ φ is
   multiplication by L/a > 0. Surjectivity: a symmetry ω of the
   intersection has components (α, β) with a·w(α) = b·w(β) =: x, so
   x ∈ aℤ ∩ bℤ = Lℤ (nat_lcm_intersection, module 148), x = kL, and
   ω = φ(loop^k) since prj_{aℤ} is a monomorphism. `}
def pbg_quotient_positive (a1 l q : Nat) : Id Nat (suc. l) (mul q (suc. a1)) → Σ Nat (n ↦ Id Nat q (suc. n))
  ≔ match q [
  | zero. ↦ e ↦ absurd (Σ Nat (n ↦ Id Nat zero. (suc. n)))
      (pbg_suc_ne_zero l (concat Nat (suc. l) (mul zero. (suc. a1)) zero. e (mul_zero_left (suc. a1))))
  | suc. n ↦ _ ↦ (n, refl (suc. n : Nat)) ]

def pbg_lcm_quotient_left_positive (a1 b1 : Nat) : Σ Nat (n ↦ Id Nat (pbg_lcm_quotient_left a1 b1 .fst) (suc. n))
  ≔ pbg_quotient_positive a1 (lcm_positive_search a1 b1 .fst) (pbg_lcm_quotient_left a1 b1 .fst)
      (pbg_lcm_quotient_left a1 b1 .snd)

def pbg_hom_proj_phi_winding (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1))) (g : USym (circle_group C))
  : Id Int
      (circle_winding C (usym_hom (CircleHomIntersection C a1 b1 f f' hf hf') (circle_group C)
        (pullback_group_proj_left (circle_group C) (circle_group C) (circle_group C)
          (f) (f'))
        (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf') g)))
      (int_mul (circle_winding C g) (pos. (pbg_lcm_quotient_left a1 b1 .fst)))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let p1 ≔ pullback_group_proj_left Z Z Z (f) (f') in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    let qa ≔ pbg_lcm_quotient_left a1 b1 .fst in
    calc
      circle_winding C (usym_hom P Z p1 (usym_hom Z P phi g))
      = circle_winding C (usym_hom Z Z (group_hom_compose Z P Z phi p1) g)
        by refl (circle_winding C) (inverse (USym Z) (usym_hom Z Z (group_hom_compose Z P Z phi p1) g)
          (usym_hom P Z p1 (usym_hom Z P phi g)) (usym_hom_compose Z P Z phi p1 (refl g)))
      = circle_winding C (usym_hom Z Z (circle_multiplication_hom C (pos. qa)) g)
        by refl ((h ↦ circle_winding C (usym_hom Z Z h g)) : GroupHom Z Z → Int) (circle_hom_intersection_proj_left C a1 b1 f f' hf hf')
      = int_mul (circle_winding C g) (pos. qa) by circle_multiplication_winding C (pos. qa) g ∎

def circle_hom_intersection_map_reflects (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : PathReflecting (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
      (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf'))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let p1 ≔ pullback_group_proj_left Z Z Z (f) (f') in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    let qa ≔ pbg_lcm_quotient_left a1 b1 .fst in
    let n ≔ pbg_lcm_quotient_left_positive a1 b1 .fst in
    let en : Id Int (pos. qa) (pos. (suc. n)) ≔ refl ((k ↦ pos. k) : Nat → Int) (pbg_lcm_quotient_left_positive a1 b1 .snd) in
    g g' h ↦ pbg_winding_injective C g g'
      (int_mul_cancel_pos n (circle_winding C g) (circle_winding C g') (calc
        int_mul (circle_winding C g) (pos. (suc. n)) = int_mul (circle_winding C g) (pos. qa)
          by refl (int_mul (circle_winding C g)) (inverse Int (pos. qa) (pos. (suc. n)) en)
        = circle_winding C (usym_hom P Z p1 (usym_hom Z P phi g))
          by inverse Int (circle_winding C (usym_hom P Z p1 (usym_hom Z P phi g))) (int_mul (circle_winding C g) (pos. qa))
            (pbg_hom_proj_phi_winding C a1 b1 f f' hf hf' g)
        = circle_winding C (usym_hom P Z p1 (usym_hom Z P phi g'))
          by refl ((x ↦ circle_winding C (usym_hom P Z p1 x)) : USym P → Int) h
        = int_mul (circle_winding C g') (pos. qa) by pbg_hom_proj_phi_winding C a1 b1 f f' hf hf' g'
        = int_mul (circle_winding C g') (pos. (suc. n)) by refl (int_mul (circle_winding C g')) en ∎))

def circle_hom_intersection_map_surjective (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Surjective (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
      (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf'))
  ≔ let Z ≔ circle_group C in
    let P ≔ CircleHomIntersection C a1 b1 f f' hf hf' in
    let ma ≔ f in
    let mb ≔ f' in
    let p1 ≔ pullback_group_proj_left Z Z Z ma mb in
    let p2 ≔ pullback_group_proj_right Z Z Z ma mb in
    let phi ≔ circle_hom_intersection_map C a1 b1 f f' hf hf' in
    let qa ≔ pbg_lcm_quotient_left a1 b1 in
    let L ≔ nat_lcm (suc. a1) (suc. b1) in
    let F : USym P → Type ≔ w ↦ BookFiber (USym Z) (USym P) (usym_hom Z P phi) w in
    w ↦
      let al ≔ usym_hom P Z p1 w in
      let be ≔ usym_hom P Z p2 w in
      let x ≔ circle_winding C (usym_hom Z Z ma al) in
      let xa : Multiples (suc. a1) x .fst
        ≔ mere (MultipleWitness (suc. a1) x) (circle_winding C al, circle_hom_winding C (pos. (suc. a1)) f hf al) in
      let xb : Multiples (suc. b1) x .fst
        ≔ mere (MultipleWitness (suc. b1) x) (circle_winding C be,
             concat Int x (circle_winding C (usym_hom Z Z mb be)) (int_mul (circle_winding C be) (pos. (suc. b1)))
               (refl (circle_winding C) (pullback_group_usym_square Z Z Z ma mb w))
               (circle_hom_winding C (pos. (suc. b1)) f' hf' be)) in
      let xL : Multiples L x .fst
        ≔ transport (Subtypes Int) (H ↦ H x .fst) (SubgroupIntersection (Multiples (suc. a1)) (Multiples (suc. b1)))
            (Multiples L) (nat_lcm_intersection (suc. a1) (suc. b1)) (xa, xb) in
      mere_rec (MultipleWitness L x) (Mere (F w)) (mere_isprop (F w))
        (kw ↦ mere (F w) (circle_power C (kw .fst),
          pullback_group_proj_left_reflects Z Z Z ma mb (circle_hom_mono C b1 f' hf') w
            (usym_hom Z P phi (circle_power C (kw .fst)))
            (pbg_winding_injective C al (usym_hom P Z p1 (usym_hom Z P phi (circle_power C (kw .fst))))
              (calc
                circle_winding C al = int_mul (kw .fst) (pos. (qa .fst))
                  by int_mul_cancel_pos a1 (circle_winding C al) (int_mul (kw .fst) (pos. (qa .fst))) (calc
                    int_mul (circle_winding C al) (pos. (suc. a1)) = x
                      by inverse Int x (int_mul (circle_winding C al) (pos. (suc. a1)))
                        (circle_hom_winding C (pos. (suc. a1)) f hf al)
                    = int_mul (kw .fst) (pos. L) by kw .snd
                    = int_mul (kw .fst) (pos. (mul (qa .fst) (suc. a1)))
                      by refl ((k ↦ int_mul (kw .fst) (pos. k)) : Nat → Int) (qa .snd)
                    = int_mul (int_mul (kw .fst) (pos. (qa .fst))) (pos. (suc. a1))
                      by int_mul_pos_mul (kw .fst) (qa .fst) (suc. a1) ∎)
                = int_mul (circle_winding C (circle_power C (kw .fst))) (pos. (qa .fst))
                  by refl ((k ↦ int_mul k (pos. (qa .fst))) : Int → Int)
                    (inverse Int (circle_winding C (circle_power C (kw .fst))) (kw .fst) (circle_winding_power C (kw .fst)))
                = circle_winding C (usym_hom P Z p1 (usym_hom Z P phi (circle_power C (kw .fst))))
                  by inverse Int (circle_winding C (usym_hom P Z p1 (usym_hom Z P phi (circle_power C (kw .fst)))))
                    (int_mul (circle_winding C (circle_power C (kw .fst))) (pos. (qa .fst)))
                    (pbg_hom_proj_phi_winding C a1 b1 f f' hf hf' (circle_power C (kw .fst))) ∎))))
        xL

def circle_hom_intersection_usym_equiv (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Equiv (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
  ≔ native_equivalence (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
      (native_embedding_surjection_equiv (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
        (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf'))
        (path_reflecting_set_embedding (USym (circle_group C)) (USym (CircleHomIntersection C a1 b1 f f' hf hf'))
          (usym_set (CircleHomIntersection C a1 b1 f f' hf hf'))
          (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf'))
          (circle_hom_intersection_map_reflects C a1 b1 f f' hf hf'))
        (circle_hom_intersection_map_surjective C a1 b1 f f' hf hf'))

def circle_hom_intersection_map_iso (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : IsGroupIso (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf')
  ≔ pbg_group_iso_from_usym_equiv (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf')
      (circle_hom_intersection_usym_equiv C a1 b1 f f' hf hf')
      (g ↦ refl (usym_hom (circle_group C) (CircleHomIntersection C a1 b1 f f' hf hf') (circle_hom_intersection_map C a1 b1 f f' hf hf') g))

{` The example (line 471): for a, b > 0 with L = lcm(a,b), there is a group
   isomorphism φ : ℤ ≅ aℤ ∩ bℤ under which the inclusion of the
   intersection becomes Lℤ ↪ ℤ (multiplication by L). `}
def circle_hom_intersection_lcm (C : CircleSignature) (a1 b1 : Nat) (f f' : GroupHom (circle_group C) (circle_group C)) (hf : CircleHomLoop C f (pos. (suc. a1))) (hf' : CircleHomLoop C f' (pos. (suc. b1)))
  : Σ (GroupIso (circle_group C) (circle_hom_intersection_mono C a1 b1 f f' hf hf' .fst))
      (phi ↦ Id (GroupHom (circle_group C) (circle_group C))
        (group_hom_compose (circle_group C) (circle_hom_intersection_mono C a1 b1 f f' hf hf' .fst) (circle_group C) (phi .fst)
          (circle_hom_intersection_mono C a1 b1 f f' hf hf' .snd .fst))
        (circle_multiplication_hom C (pos. (nat_lcm (suc. a1) (suc. b1)))))
  ≔ ((circle_hom_intersection_map C a1 b1 f f' hf hf', circle_hom_intersection_map_iso C a1 b1 f f' hf hf'), circle_hom_intersection_triangle C a1 b1 f f' hf hf')

{` The example (line 471), instances at the multiplication homomorphisms. `}
def IntegerIntersection (C : CircleSignature) (a1 b1 : Nat) : Group
  ≔ CircleHomIntersection C a1 b1 (circle_multiplication_hom C (pos. (suc. a1))) (circle_multiplication_hom C (pos. (suc. b1)))
      (circle_multiplication_loop C (pos. (suc. a1))) (circle_multiplication_loop C (pos. (suc. b1)))

{` aℤ ∩ bℤ as an element of Mono(ℤ) (def:intersectionofgroups). `}
def integer_intersection_mono (C : CircleSignature) (a1 b1 : Nat) : GroupMonos (circle_group C)
  ≔ circle_hom_intersection_mono C a1 b1 (circle_multiplication_hom C (pos. (suc. a1))) (circle_multiplication_hom C (pos. (suc. b1)))
      (circle_multiplication_loop C (pos. (suc. a1))) (circle_multiplication_loop C (pos. (suc. b1)))

{` For a, b > 0 with L = lcm(a,b) there is a group isomorphism
   φ : ℤ ≅ aℤ ∩ bℤ under which the inclusion of the intersection becomes
   Lℤ ↪ ℤ (multiplication by L). `}
def integer_intersection_lcm (C : CircleSignature) (a1 b1 : Nat)
  : Σ (GroupIso (circle_group C) (integer_intersection_mono C a1 b1 .fst))
      (phi ↦ Id (GroupHom (circle_group C) (circle_group C))
        (group_hom_compose (circle_group C) (integer_intersection_mono C a1 b1 .fst) (circle_group C) (phi .fst)
          (integer_intersection_mono C a1 b1 .snd .fst))
        (circle_multiplication_hom C (pos. (nat_lcm (suc. a1) (suc. b1)))))
  ≔ circle_hom_intersection_lcm C a1 b1 (circle_multiplication_hom C (pos. (suc. a1))) (circle_multiplication_hom C (pos. (suc. b1)))
      (circle_multiplication_loop C (pos. (suc. a1))) (circle_multiplication_loop C (pos. (suc. b1)))
