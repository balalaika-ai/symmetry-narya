export "1310-integer-ring"
export "430-pointwise-abstract-groups"

{` Chapter 13 (fields.tex), exa:ring-Z-polynomials (line 89), first step:
   the ring R[[x]] of formal power series over an abstract ring R, i.e.
   coefficient sequences Nat → R with pointwise addition (the group
   pointwise_abstract_group of module 430) and the Cauchy product, defined
   by structural recursion on the index:
     (f g)_0 = f_0 g_0,   (f g)_(n+1) = f_0 g_(n+1) + ((shift f) g)_n,
   where (shift f)_k = f_(k+1); this is Σ_(i+j=n) f_i g_j unfolded. The
   ring laws are proved coefficientwise by induction on n, generalising
   over the sequences; tail(f g) = f_0 · shift g + (shift f) g holds
   judgmentally. R[[x]] is commutative when R is. `}

def series_shift (R : AbstractRing) (f : Nat → R .carrier) : Nat → R .carrier ≔ k ↦ f (suc. k)

def series_add (R : AbstractRing) (f g : Nat → R .carrier) : Nat → R .carrier ≔ k ↦ R .add (f k) (g k)

def series_scale (R : AbstractRing) (c : R .carrier) (f : Nat → R .carrier) : Nat → R .carrier
  ≔ k ↦ R .mul c (f k)

def series_one (R : AbstractRing) : Nat → R .carrier ≔ [ zero. ↦ R .one | suc. _ ↦ R .zero ]

{` The Cauchy product. `}
def series_mul (R : AbstractRing) (f g : Nat → R .carrier) (n : Nat) : R .carrier
  ≔ match n [
  | zero. ↦ R .mul (f zero.) (g zero.)
  | suc. n ↦ R .add (R .mul (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n) ]

def series_mul_zero_left (R : AbstractRing) (f g : Nat → R .carrier)
  (hf : (k : Nat) → Id (R .carrier) (f k) (R .zero)) (n : Nat)
  : Id (R .carrier) (series_mul R f g n) (R .zero)
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let z ≔ R .zero in
    match n [
  | zero. ↦ concat S (m (f zero.) (g zero.)) (m z (g zero.)) z
      (refl ((x ↦ m x (g zero.)) : S → S) (hf zero.)) (ring_mul_zero_left R (g zero.))
  | suc. n ↦ calc
      R .add (m (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n) = R .add z z
        by refl (R .add)
          (concat S (m (f zero.) (g (suc. n))) (m z (g (suc. n))) z
            (refl ((x ↦ m x (g (suc. n))) : S → S) (hf zero.)) (ring_mul_zero_left R (g (suc. n))))
          (series_mul_zero_left R (series_shift R f) g (k ↦ hf (suc. k)) n)
      = z by R .add_laws .unit_right z ∎ ]

def series_mul_zero_right (R : AbstractRing) (f g : Nat → R .carrier)
  (hg : (k : Nat) → Id (R .carrier) (g k) (R .zero)) (n : Nat)
  : Id (R .carrier) (series_mul R f g n) (R .zero)
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let z ≔ R .zero in
    match n [
  | zero. ↦ concat S (m (f zero.) (g zero.)) (m (f zero.) z) z
      (refl (m (f zero.)) (hg zero.)) (ring_mul_zero_right R (f zero.))
  | suc. n ↦ calc
      R .add (m (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n) = R .add z z
        by refl (R .add)
          (concat S (m (f zero.) (g (suc. n))) (m (f zero.) z) z
            (refl (m (f zero.)) (hg (suc. n))) (ring_mul_zero_right R (f zero.)))
          (series_mul_zero_right R (series_shift R f) g hg n)
      = z by R .add_laws .unit_right z ∎ ]

{` (f + g) h = f h + g h, coefficientwise. `}
def series_mul_add_left (R : AbstractRing) (f g h : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R (series_add R f g) h n) (R .add (series_mul R f h n) (series_mul R g h n))
  ≔ let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ ring_rdistr R (f zero.) (g zero.) (h zero.)
  | suc. n ↦ calc
      p (m (p (f zero.) (g zero.)) (h (suc. n))) (series_mul R (series_add R (series_shift R f) (series_shift R g)) h n)
      = p (p (m (f zero.) (h (suc. n))) (m (g zero.) (h (suc. n))))
          (p (series_mul R (series_shift R f) h n) (series_mul R (series_shift R g) h n))
        by refl p (ring_rdistr R (f zero.) (g zero.) (h (suc. n)))
          (series_mul_add_left R (series_shift R f) (series_shift R g) h n)
      = p (p (m (f zero.) (h (suc. n))) (series_mul R (series_shift R f) h n))
          (p (m (g zero.) (h (suc. n))) (series_mul R (series_shift R g) h n))
        by abstract_abelian_interchange (ring_additive_group R) (ring_additive_abelian R)
          (m (f zero.) (h (suc. n))) (m (g zero.) (h (suc. n)))
          (series_mul R (series_shift R f) h n) (series_mul R (series_shift R g) h n) ∎ ]

{` f (g + h) = f g + f h, coefficientwise. `}
def series_mul_add_right (R : AbstractRing) (f g h : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R f (series_add R g h) n) (R .add (series_mul R f g n) (series_mul R f h n))
  ≔ let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ ring_ldistr R (f zero.) (g zero.) (h zero.)
  | suc. n ↦ calc
      p (m (f zero.) (p (g (suc. n)) (h (suc. n)))) (series_mul R (series_shift R f) (series_add R g h) n)
      = p (p (m (f zero.) (g (suc. n))) (m (f zero.) (h (suc. n))))
          (p (series_mul R (series_shift R f) g n) (series_mul R (series_shift R f) h n))
        by refl p (ring_ldistr R (f zero.) (g (suc. n)) (h (suc. n)))
          (series_mul_add_right R (series_shift R f) g h n)
      = p (p (m (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n))
          (p (m (f zero.) (h (suc. n))) (series_mul R (series_shift R f) h n))
        by abstract_abelian_interchange (ring_additive_group R) (ring_additive_abelian R)
          (m (f zero.) (g (suc. n))) (m (f zero.) (h (suc. n)))
          (series_mul R (series_shift R f) g n) (series_mul R (series_shift R f) h n) ∎ ]

{` (c · f) h = c · (f h), coefficientwise. `}
def series_mul_scale_left (R : AbstractRing) (c : R .carrier) (f h : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R (series_scale R c f) h n) (R .mul c (series_mul R f h n))
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ inverse S (m c (m (f zero.) (h zero.))) (m (m c (f zero.)) (h zero.)) (ring_mul_assoc R c (f zero.) (h zero.))
  | suc. n ↦ calc
      p (m (m c (f zero.)) (h (suc. n))) (series_mul R (series_scale R c (series_shift R f)) h n)
      = p (m c (m (f zero.) (h (suc. n)))) (m c (series_mul R (series_shift R f) h n))
        by refl p (inverse S (m c (m (f zero.) (h (suc. n)))) (m (m c (f zero.)) (h (suc. n)))
             (ring_mul_assoc R c (f zero.) (h (suc. n))))
          (series_mul_scale_left R c (series_shift R f) h n)
      = m c (p (m (f zero.) (h (suc. n))) (series_mul R (series_shift R f) h n))
        by inverse S (m c (p (m (f zero.) (h (suc. n))) (series_mul R (series_shift R f) h n)))
          (p (m c (m (f zero.) (h (suc. n)))) (m c (series_mul R (series_shift R f) h n)))
          (ring_ldistr R c (m (f zero.) (h (suc. n))) (series_mul R (series_shift R f) h n)) ∎ ]

{` The Cauchy product unfolded from the other end:
   (f g)_(n+1) = (f (shift g))_n + f_(n+1) g_0. `}
def series_mul_suc_right (R : AbstractRing) (f g : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R f g (suc. n))
      (R .add (series_mul R f (series_shift R g) n) (R .mul (f (suc. n)) (g zero.)))
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ refl (p (m (f zero.) (g 1)) (m (f 1) (g zero.)))
  | suc. n ↦ calc
      p (m (f zero.) (g (suc. (suc. n)))) (series_mul R (series_shift R f) g (suc. n))
      = p (m (f zero.) (g (suc. (suc. n))))
          (p (series_mul R (series_shift R f) (series_shift R g) n) (m (f (suc. (suc. n))) (g zero.)))
        by refl (p (m (f zero.) (g (suc. (suc. n))))) (series_mul_suc_right R (series_shift R f) g n)
      = p (p (m (f zero.) (g (suc. (suc. n)))) (series_mul R (series_shift R f) (series_shift R g) n))
          (m (f (suc. (suc. n))) (g zero.))
        by ring_add_assoc R (m (f zero.) (g (suc. (suc. n))))
          (series_mul R (series_shift R f) (series_shift R g) n) (m (f (suc. (suc. n))) (g zero.)) ∎ ]

{` Associativity in the orientation of AssocLaw: f (g h) = (f g) h. `}
def series_mul_assoc (R : AbstractRing) (f g h : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R f (series_mul R g h) n) (series_mul R (series_mul R f g) h n)
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ ring_mul_assoc R (f zero.) (g zero.) (h zero.)
  | suc. n ↦
    let a ≔ m (f zero.) (m (g zero.) (h (suc. n))) in
    let b ≔ m (f zero.) (series_mul R (series_shift R g) h n) in
    let c ≔ series_mul R (series_mul R (series_shift R f) g) h n in
    calc
      p (m (f zero.) (p (m (g zero.) (h (suc. n))) (series_mul R (series_shift R g) h n)))
        (series_mul R (series_shift R f) (series_mul R g h) n)
      = p (p a b) c
        by refl p (ring_ldistr R (f zero.) (m (g zero.) (h (suc. n))) (series_mul R (series_shift R g) h n))
          (series_mul_assoc R (series_shift R f) g h n)
      = p a (p b c) by inverse S (p a (p b c)) (p (p a b) c) (ring_add_assoc R a b c)
      = p (m (m (f zero.) (g zero.)) (h (suc. n)))
          (p (series_mul R (series_scale R (f zero.) (series_shift R g)) h n) c)
        by refl p (ring_mul_assoc R (f zero.) (g zero.) (h (suc. n)))
          (refl ((x ↦ p x c) : S → S)
            (inverse S (series_mul R (series_scale R (f zero.) (series_shift R g)) h n) b
              (series_mul_scale_left R (f zero.) (series_shift R g) h n)))
      = p (m (m (f zero.) (g zero.)) (h (suc. n)))
          (series_mul R (series_add R (series_scale R (f zero.) (series_shift R g)) (series_mul R (series_shift R f) g)) h n)
        by refl (p (m (m (f zero.) (g zero.)) (h (suc. n))))
          (inverse S
            (series_mul R (series_add R (series_scale R (f zero.) (series_shift R g)) (series_mul R (series_shift R f) g)) h n)
            (p (series_mul R (series_scale R (f zero.) (series_shift R g)) h n) c)
            (series_mul_add_left R (series_scale R (f zero.) (series_shift R g)) (series_mul R (series_shift R f) g) h n)) ∎ ]

def series_mul_one_left (R : AbstractRing) (f : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R (series_one R) f n) (f n)
  ≔ match n [
  | zero. ↦ ring_mul_one_left R (f zero.)
  | suc. n ↦ calc
      R .add (R .mul (R .one) (f (suc. n))) (series_mul R (series_shift R (series_one R)) f n)
      = R .add (f (suc. n)) (R .zero)
        by refl (R .add) (ring_mul_one_left R (f (suc. n)))
          (series_mul_zero_left R (series_shift R (series_one R)) f (_ ↦ refl (R .zero)) n)
      = f (suc. n) by R .add_laws .unit_right (f (suc. n)) ∎ ]

def series_mul_one_right (R : AbstractRing) (f : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R f (series_one R) n) (f n)
  ≔ match n [
  | zero. ↦ ring_mul_one_right R (f zero.)
  | suc. n ↦ calc
      series_mul R f (series_one R) (suc. n)
      = R .add (series_mul R f (series_shift R (series_one R)) n) (R .mul (f (suc. n)) (R .one))
        by series_mul_suc_right R f (series_one R) n
      = R .add (R .zero) (f (suc. n))
        by refl (R .add) (series_mul_zero_right R f (series_shift R (series_one R)) (_ ↦ refl (R .zero)) n)
          (ring_mul_one_right R (f (suc. n)))
      = f (suc. n) by R .add_laws .unit_left (f (suc. n)) ∎ ]

def series_mul_comm (R : AbstractRing) (hc : IsCommutativeRing R) (f g : Nat → R .carrier) (n : Nat)
  : Id (R .carrier) (series_mul R f g n) (series_mul R g f n)
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    match n [
  | zero. ↦ hc (f zero.) (g zero.)
  | suc. n ↦ calc
      p (m (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n)
      = p (series_mul R (series_shift R f) g n) (m (f zero.) (g (suc. n)))
        by ring_add_comm R (m (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n)
      = p (series_mul R g (series_shift R f) n) (m (g (suc. n)) (f zero.))
        by refl p (series_mul_comm R hc (series_shift R f) g n) (hc (f zero.) (g (suc. n)))
      = series_mul R g f (suc. n)
        by inverse S (series_mul R g f (suc. n)) (p (series_mul R g (series_shift R f) n) (m (g (suc. n)) (f zero.)))
          (series_mul_suc_right R g f n) ∎ ]

{` R[[x]] = (Nat → R, pointwise 0, +, -, series_one, Cauchy product). `}
def power_series_ring (R : AbstractRing) : AbstractRing
  ≔ let G ≔ pointwise_abstract_group (ring_additive_group R) Nat in
    let S ≔ R .carrier in
    (Nat → S, G .unit, G .mul, G .inv, G .laws, series_one R, series_mul R,
     (G .laws .carrier_set,
      (f ↦ (funext Nat (_ ↦ S) (series_mul R f (series_one R)) f (series_mul_one_right R f),
            funext Nat (_ ↦ S) (series_mul R (series_one R) f) f (series_mul_one_left R f)),
       f g h ↦ funext Nat (_ ↦ S) (series_mul R f (series_mul R g h)) (series_mul R (series_mul R f g) h)
         (series_mul_assoc R f g h))),
     (f g h ↦ funext Nat (_ ↦ S) (series_mul R f (series_add R g h)) (series_add R (series_mul R f g) (series_mul R f h))
        (series_mul_add_right R f g h),
      f g h ↦ funext Nat (_ ↦ S) (series_mul R (series_add R f g) h) (series_add R (series_mul R f h) (series_mul R g h))
        (series_mul_add_left R f g h)))

def power_series_ring_commutative (R : AbstractRing) (hc : IsCommutativeRing R)
  : IsCommutativeRing (power_series_ring R)
  ≔ f g ↦ funext Nat (_ ↦ R .carrier) (series_mul R f g) (series_mul R g f) (series_mul_comm R hc f g)

{` The variable x = (0, 1, 0, 0, …). `}
def series_variable (R : AbstractRing) : Nat → R .carrier
  ≔ [ zero. ↦ R .zero | suc. zero. ↦ R .one | suc. (suc. _) ↦ R .zero ]

{` Litmus in ℤ[[x]]: (1 - x)(1 + x + x² + …) = 1, checked on the
   coefficients 0 to 3 by computation, and x · x = x² (coefficient 2 is 1,
   coefficient 1 is 0). `}
def int_one_minus_x : Nat → Int ≔ [ zero. ↦ int_one | suc. zero. ↦ neg. 0 | suc. (suc. _) ↦ int_zero ]

def int_geometric_series : Nat → Int ≔ _ ↦ int_one

def power_series_litmus_geometric
  : Id (Product Int (Product Int (Product Int Int)))
      (power_series_ring integer_ring .mul int_one_minus_x int_geometric_series 0,
       (power_series_ring integer_ring .mul int_one_minus_x int_geometric_series 1,
        (power_series_ring integer_ring .mul int_one_minus_x int_geometric_series 2,
         power_series_ring integer_ring .mul int_one_minus_x int_geometric_series 3)))
      (int_one, (int_zero, (int_zero, int_zero)))
  ≔ refl ((int_one, (int_zero, (int_zero, int_zero))) : Product Int (Product Int (Product Int Int)))

def power_series_litmus_x_squared
  : Id (Product Int (Product Int Int))
      (power_series_ring integer_ring .mul (series_variable integer_ring) (series_variable integer_ring) 1,
       (power_series_ring integer_ring .mul (series_variable integer_ring) (series_variable integer_ring) 2,
        power_series_ring integer_ring .mul (series_variable integer_ring) (series_variable integer_ring) 3))
      (int_zero, (int_one, int_zero))
  ≔ refl ((int_zero, (int_one, int_zero)) : Product Int (Product Int Int))
