export "1503-algebraic-elements"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   preliminaries. Every homomorphism of fields is injective
   (field_hom_injective, constructive: φ(x − y) = 0 makes x − y
   non-invertible, hence 0 in the field K), fields have no zero divisors
   (field_no_zero_divisors, constructive), and a few identities of
   commutative rings used for synthetic division (module 1521). `}

{` x + (−y) = 0 implies x = y. `}
def ring_sub_zero_eq (R : AbstractRing) (x y : R .carrier)
  (p : Id (R .carrier) (R .add x (R .neg y)) (R .zero)) : Id (R .carrier) x y
  ≔ let A ≔ R .carrier in
    calc
      x = R .add x (R .zero) by inverse A (R .add x (R .zero)) x (R .add_laws .unit_right x)
      = R .add x (R .add (R .neg y) y)
        by refl (R .add x) (inverse A (R .add (R .neg y) y) (R .zero) (ag_inv_left (ring_additive_group R) y))
      = R .add (R .add x (R .neg y)) y by R .add_laws .assoc x (R .neg y) y
      = R .add (R .zero) y by refl ((t ↦ R .add t y) : A → A) p
      = y by R .add_laws .unit_left y ∎

{` If φ(d) = 0 for a ring homomorphism into a field, d is not invertible. `}
def field_hom_kernel_not_invertible (K L : Field) (φ : RingHom (K .fst) (L .fst)) (d : K .fst .carrier)
  (h : Id (L .fst .carrier) (φ .fst .fst d) (L .fst .zero)) : Not (IsInvertible (K .fst) d)
  ≔ let R ≔ K .fst in let S ≔ L .fst in let B ≔ S .carrier in let f ≔ φ .fst .fst in
    t ↦ mere_rec (InverseWitness R d) Empty empty_prop
      (w ↦ ring_one_ne_zero S (L .snd .fst .snd)
        (calc
           S .one = f (R .one) by inverse B (f (R .one)) (S .one) (φ .snd .fst)
           = f (R .mul d (w .fst)) by refl f (inverse (R .carrier) (R .mul d (w .fst)) (R .one) (w .snd .fst))
           = S .mul (f d) (f (w .fst)) by φ .snd .snd d (w .fst)
           = S .mul (S .zero) (f (w .fst)) by refl ((u ↦ S .mul u (f (w .fst))) : B → B) h
           = S .zero by ring_mul_zero_left S (f (w .fst)) ∎))
      t

{` Homomorphisms of fields are injective (the book's injectivity, since the
   carriers are sets). `}
def field_hom_injective (K L : Field) (φ : RingHom (K .fst) (L .fst))
  : PathReflecting (K .fst .carrier) (L .fst .carrier) (φ .fst .fst)
  ≔ x y e ↦
    let R ≔ K .fst in let S ≔ L .fst in let B ≔ S .carrier in let f ≔ φ .fst .fst in
    let d ≔ R .add x (R .neg y) in
    let fd : Id B (f d) (S .zero)
      ≔ calc
          f d = S .add (f x) (f (R .neg y)) by φ .fst .snd x (R .neg y)
          = S .add (f x) (S .neg (f y))
            by refl (S .add (f x)) (abstract_hom_preserves_inv (ring_additive_group R) (ring_additive_group S) f (φ .fst .snd) y)
          = S .add (f y) (S .neg (f y)) by refl ((u ↦ S .add u (S .neg (f y))) : B → B) e
          = S .zero by S .add_laws .inv_right (f y) ∎ in
    ring_sub_zero_eq R x y (field_non_invertible_zero R (K .snd) d (field_hom_kernel_not_invertible K L φ d fd))

{` Fields have no zero divisors: x ≠ 0 and x · y = 0 imply y = 0. `}
def field_no_zero_divisors (K : Field) (x y : K .fst .carrier) (nx : Not (Id (K .fst .carrier) x (K .fst .zero)))
  (p : Id (K .fst .carrier) (K .fst .mul x y) (K .fst .zero)) : Id (K .fst .carrier) y (K .fst .zero)
  ≔ let R ≔ K .fst in let A ≔ R .carrier in
    field_non_invertible_zero R (K .snd) y
      (t ↦ mere_rec (InverseWitness R y) Empty empty_prop
        (w ↦ nx
          (calc
             x = R .mul x (R .one) by inverse A (R .mul x (R .one)) x (ring_mul_one_right R x)
             = R .mul x (R .mul y (w .fst)) by refl (R .mul x) (inverse A (R .mul y (w .fst)) (R .one) (w .snd .fst))
             = R .mul (R .mul x y) (w .fst) by ring_mul_assoc R x y (w .fst)
             = R .mul (R .zero) (w .fst) by refl ((u ↦ R .mul u (w .fst)) : A → A) p
             = R .zero by ring_mul_zero_left R (w .fst) ∎))
        t)

{` x ≠ y implies x + (−y) ≠ 0. `}
def field_sub_nonzero (R : AbstractRing) (x y : R .carrier) (ne : Not (Id (R .carrier) x y))
  : Not (Id (R .carrier) (R .add x (R .neg y)) (R .zero))
  ≔ p ↦ ne (ring_sub_zero_eq R x y p)

{` (a + b) + (c + d) = (a + c) + (b + d). `}
def ring_add_interchange (R : AbstractRing) (a b c d : R .carrier)
  : Id (R .carrier) (R .add (R .add a b) (R .add c d)) (R .add (R .add a c) (R .add b d))
  ≔ let A ≔ R .carrier in let p ≔ R .add in
    calc
      p (p a b) (p c d) = p a (p b (p c d)) by inverse A (p a (p b (p c d))) (p (p a b) (p c d)) (R .add_laws .assoc a b (p c d))
      = p a (p (p b c) d) by refl (p a) (R .add_laws .assoc b c d)
      = p a (p (p c b) d) by refl ((u ↦ p a (p u d)) : A → A) (ring_add_comm R b c)
      = p a (p c (p b d)) by refl (p a) (inverse A (p c (p b d)) (p (p c b) d) (R .add_laws .assoc c b d))
      = p (p a c) (p b d) by R .add_laws .assoc a c (p b d) ∎

{` b + (c + (−b)) = c. `}
def ring_add_cancel_mid (R : AbstractRing) (b c : R .carrier)
  : Id (R .carrier) (R .add b (R .add c (R .neg b))) c
  ≔ let A ≔ R .carrier in let p ≔ R .add in
    calc
      p b (p c (R .neg b)) = p (p c (R .neg b)) b by ring_add_comm R b (p c (R .neg b))
      = p c (p (R .neg b) b) by inverse A (p c (p (R .neg b) b)) (p (p c (R .neg b)) b) (R .add_laws .assoc c (R .neg b) b)
      = p c (R .zero) by refl (p c) (ag_inv_left (ring_additive_group R) b)
      = c by R .add_laws .unit_right c ∎

{` (x + (−c)) · z = x z + (−(c z)). `}
def ring_sub_rdistr (R : AbstractRing) (x c z : R .carrier)
  : Id (R .carrier) (R .mul (R .add x (R .neg c)) z) (R .add (R .mul x z) (R .neg (R .mul c z)))
  ≔ concat (R .carrier) (R .mul (R .add x (R .neg c)) z) (R .add (R .mul x z) (R .mul (R .neg c) z))
      (R .add (R .mul x z) (R .neg (R .mul c z)))
      (ring_rdistr R x (R .neg c) z) (refl (R .add (R .mul x z)) (ring_mul_neg_left R c z))

{` (c + (−c)) · z = 0. `}
def ring_sub_self_mul (R : AbstractRing) (c z : R .carrier)
  : Id (R .carrier) (R .mul (R .add c (R .neg c)) z) (R .zero)
  ≔ concat (R .carrier) (R .mul (R .add c (R .neg c)) z) (R .mul (R .zero) z) (R .zero)
      (refl ((u ↦ R .mul u z) : R .carrier → R .carrier) (R .add_laws .inv_right c)) (ring_mul_zero_left R z)
