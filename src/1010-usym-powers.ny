export "404-group-examples"
export "1000-prime-numbers"
export "288-chapter-three-text-claims"
export "282-explicit-power-degree"

{` Chapter 10 (fingp.tex), supporting material: natural-number powers g^n of
   a symmetry g : USym G and their laws; homomorphisms preserve powers;
   periods (g^m = e); the least positive period divides every period; and
   the prime case: if p is prime, g^p = e and g ≠ e, then g^k ≠ e for
   0 < k < p (used for Cauchy's theorem, thm:cauchys).

   g^n is loop_power_nat (module 26) at the shape of G, so g^0 = e and
   g^(n+1) = g · g^n (usym_mul G g (g^n) = concat (g^n) g) hold by definition.
   usym_hom_power is the USym form of loops_map_power_nat (module 418); it is
   proved here directly so that this module only imports the precompiled base.
   Reused: loop_power_nat_trivial (module 288), loop_power_nat_inverse
   (module 282), Euclidean division (module 48), least numbers (module 47). `}

def usym_power (G : Group) (g : USym G) (n : Nat) : USym G
  ≔ loop_power_nat (BG G .carrier) (shape G) g n

def usym_power_zero (G : Group) (g : USym G) : Id (USym G) (usym_power G g zero.) (usym_unit G)
  ≔ refl (usym_unit G)

def usym_power_suc (G : Group) (g : USym G) (n : Nat)
  : Id (USym G) (usym_power G g (suc. n)) (usym_mul G g (usym_power G g n))
  ≔ refl (usym_power G g (suc. n))

def usym_power_one (G : Group) (g : USym G) : Id (USym G) (usym_power G g (suc. zero.)) g
  ≔ concat_1p (BG G .carrier) (shape G) (shape G) g

{` g^(m+n) = g^n · g^m (in concatenation order: first g^m, then g^n). `}
def usym_power_add (G : Group) (g : USym G) (m n : Nat)
  : Id (USym G) (usym_power G g (add m n)) (usym_mul G (usym_power G g n) (usym_power G g m))
  ≔ match n [
  | zero. ↦ inverse (USym G) (usym_mul G (usym_power G g zero.) (usym_power G g m)) (usym_power G g m)
      (concat_p1 (BG G .carrier) (shape G) (shape G) (usym_power G g m))
  | suc. n ↦ calc
      usym_power G g (suc. (add m n))
      = concat (BG G .carrier) (shape G) (shape G) (shape G)
          (concat (BG G .carrier) (shape G) (shape G) (shape G) (usym_power G g m) (usym_power G g n)) g
        by refl ((r ↦ concat (BG G .carrier) (shape G) (shape G) (shape G) r g) : USym G → USym G)
          (usym_power_add G g m n)
      = concat (BG G .carrier) (shape G) (shape G) (shape G) (usym_power G g m)
          (concat (BG G .carrier) (shape G) (shape G) (shape G) (usym_power G g n) g)
        by concat_assoc (BG G .carrier) (shape G) (shape G) (shape G) (shape G) (usym_power G g m) (usym_power G g n) g ∎ ]

{` Powers of g commute with each other. `}
def usym_power_commute (G : Group) (g : USym G) (m n : Nat)
  : Id (USym G) (usym_mul G (usym_power G g m) (usym_power G g n)) (usym_mul G (usym_power G g n) (usym_power G g m))
  ≔ calc
      usym_mul G (usym_power G g m) (usym_power G g n)
      = usym_power G g (add n m)
        by inverse (USym G) (usym_power G g (add n m)) (usym_mul G (usym_power G g m) (usym_power G g n))
          (usym_power_add G g n m)
      = usym_power G g (add m n) by refl (usym_power G g) (add_comm n m)
      = usym_mul G (usym_power G g n) (usym_power G g m) by usym_power_add G g m n ∎

{` g^(m+n) = g^m · g^n, the book's g^(m+n) = g^m g^n. `}
def usym_power_add_left (G : Group) (g : USym G) (m n : Nat)
  : Id (USym G) (usym_power G g (add m n)) (usym_mul G (usym_power G g m) (usym_power G g n))
  ≔ concat (USym G) (usym_power G g (add m n)) (usym_mul G (usym_power G g n) (usym_power G g m))
      (usym_mul G (usym_power G g m) (usym_power G g n))
      (usym_power_add G g m n) (usym_power_commute G g n m)

{` g^(m·n) = (g^m)^n. `}
def usym_power_mul (G : Group) (g : USym G) (m n : Nat)
  : Id (USym G) (usym_power G g (mul m n)) (usym_power G (usym_power G g m) n)
  ≔ match n [
  | zero. ↦ refl (usym_unit G)
  | suc. n ↦ calc
      usym_power G g (add (mul m n) m)
      = usym_mul G (usym_power G g m) (usym_power G g (mul m n)) by usym_power_add G g (mul m n) m
      = usym_mul G (usym_power G g m) (usym_power G (usym_power G g m) n)
        by refl (usym_mul G (usym_power G g m)) (usym_power_mul G g m n) ∎ ]

{` e^n = e. `}
def usym_power_unit (G : Group) (n : Nat) : Id (USym G) (usym_power G (usym_unit G) n) (usym_unit G)
  ≔ loop_power_nat_trivial (BG G .carrier) (shape G) (usym_unit G) (refl (usym_unit G)) n

{` (g⁻¹)^n = (g^n)⁻¹. `}
def usym_power_inv (G : Group) (g : USym G) (n : Nat)
  : Id (USym G) (usym_power G (usym_inv G g) n) (usym_inv G (usym_power G g n))
  ≔ inverse (USym G) (usym_inv G (usym_power G g n)) (usym_power G (usym_inv G g) n)
      (loop_power_nat_inverse (BG G .carrier) (shape G) g n)

{` Homomorphisms preserve powers: f(g^n) = f(g)^n. `}
def usym_hom_power (G H : Group) (f : GroupHom G H) (g : USym G) (n : Nat)
  : Id (USym H) (usym_hom G H f (usym_power G g n)) (usym_power H (usym_hom G H f g) n)
  ≔ match n [
  | zero. ↦ usym_hom_unit G H f
  | suc. n ↦ concat (USym H) (usym_hom G H f (usym_mul G g (usym_power G g n)))
      (usym_mul H (usym_hom G H f g) (usym_hom G H f (usym_power G g n)))
      (usym_mul H (usym_hom G H f g) (usym_power H (usym_hom G H f g) n))
      (usym_hom_mul G H f g (usym_power G g n))
      (refl (usym_mul H (usym_hom G H f g)) (usym_hom_power G H f g n)) ]

{` Periods. If g^m = e, then g^(q·m) = e and g^(k + q·m) = g^k = g^(q·m + k). `}
def usym_power_multiple_unit (G : Group) (g : USym G) (m : Nat)
  (h : Id (USym G) (usym_power G g m) (usym_unit G)) (q : Nat)
  : Id (USym G) (usym_power G g (mul q m)) (usym_unit G)
  ≔ calc
      usym_power G g (mul q m) = usym_power G g (mul m q) by refl (usym_power G g) (mul_comm q m)
      = usym_power G (usym_power G g m) q by usym_power_mul G g m q
      = usym_unit G by loop_power_nat_trivial (BG G .carrier) (shape G) (usym_power G g m) h q ∎

def usym_power_period (G : Group) (g : USym G) (m : Nat)
  (h : Id (USym G) (usym_power G g m) (usym_unit G)) (k q : Nat)
  : Id (USym G) (usym_power G g (add k (mul q m))) (usym_power G g k)
  ≔ calc
      usym_power G g (add k (mul q m))
      = usym_mul G (usym_power G g (mul q m)) (usym_power G g k) by usym_power_add G g k (mul q m)
      = usym_mul G (usym_unit G) (usym_power G g k)
        by refl ((x ↦ usym_mul G x (usym_power G g k)) : USym G → USym G) (usym_power_multiple_unit G g m h q)
      = usym_power G g k by concat_p1 (BG G .carrier) (shape G) (shape G) (usym_power G g k) ∎

def usym_power_period_left (G : Group) (g : USym G) (m : Nat)
  (h : Id (USym G) (usym_power G g m) (usym_unit G)) (q k : Nat)
  : Id (USym G) (usym_power G g (add (mul q m) k)) (usym_power G g k)
  ≔ calc
      usym_power G g (add (mul q m) k)
      = usym_mul G (usym_power G g k) (usym_power G g (mul q m)) by usym_power_add G g (mul q m) k
      = usym_mul G (usym_power G g k) (usym_unit G)
        by refl (usym_mul G (usym_power G g k)) (usym_power_multiple_unit G g m h q)
      = usym_power G g k by concat_1p (BG G .carrier) (shape G) (shape G) (usym_power G g k) ∎

{` Positive periods of g, and the least one (the order of g). `}
def UsymPositivePeriod (G : Group) (g : USym G) (n : Nat) : Type
  ≔ Product (BookLt zero. n) (Id (USym G) (usym_power G g n) (usym_unit G))

def usym_positive_period_prop (G : Group) (g : USym G) (n : Nat) : isProp (UsymPositivePeriod G g n)
  ≔ product_prop (BookLt zero. n) (Id (USym G) (usym_power G g n) (usym_unit G))
      (book_lt_prop zero. n) (usym_set G (usym_power G g n) (usym_unit G))

def usym_book_le_lt_absurd (d r : Nat) (le : BookLe d r) (lt : BookLt r d) : Empty
  ≔ lt_irrefl d (le_lt_trans d r d (le_from_book d r le) (lt_from_book r d lt))

{` The least positive period d divides every m with g^m = e (Euclidean
   division: m = q·d + r with r < d and g^r = e, so r = 0 by minimality). `}
def usym_order_divides (G : Group) (g : USym G) (d : Nat) (min : IsMinimum (UsymPositivePeriod G g) d)
  (m : Nat) (h : Id (USym G) (usym_power G g m) (usym_unit G)) : NatDivides d m
  ≔ let u ≔ euclidean_division m d (min .fst .fst) in
    let q ≔ u .fst .fst in let r ≔ u .fst .snd in
    let hr : Id (USym G) (usym_power G g r) (usym_unit G) ≔ calc
        usym_power G g r = usym_power G g (add (mul q d) r)
          by inverse (USym G) (usym_power G g (add (mul q d) r)) (usym_power G g r)
            (usym_power_period_left G g d (min .fst .snd) q r)
        = usym_power G g m by refl (usym_power G g) (inverse Nat m (add (mul q d) r) (u .snd .snd))
        = usym_unit G by h ∎ in
    match nat_dec_eq r zero. [
    | inl. r0 ↦ mere (Σ Nat (q' ↦ Id Nat m (mul q' d)))
        (q, concat Nat m (add (mul q d) r) (mul q d) (u .snd .snd) (refl (add (mul q d)) r0))
    | inr. rnz ↦ absurd (NatDivides d m)
        (usym_book_le_lt_absurd d r (min .snd r ((r, (rnz, refl r)), hr)) (u .snd .fst)) ]

def usym_positive_period_decidable (G : Group) (g : USym G)
  (dec : (n : Nat) → Decidable (Id (USym G) (usym_power G g n) (usym_unit G))) (n : Nat)
  : Decidable (UsymPositivePeriod G g n)
  ≔ match book_lt_decidable zero. n [
  | inl. pos ↦ match dec n [
    | inl. e ↦ inl. (pos, e)
    | inr. ne ↦ inr. (w ↦ ne (w .snd)) ]
  | inr. npos ↦ inr. (w ↦ npos (w .fst)) ]

{` With decidable g^n = e, a positive period yields the least one. `}
def usym_least_period (G : Group) (g : USym G)
  (dec : (n : Nat) → Decidable (Id (USym G) (usym_power G g n) (usym_unit G)))
  (n : Nat) (w : UsymPositivePeriod G g n) : Σ Nat (IsMinimum (UsymPositivePeriod G g))
  ≔ minimum_from_witness (UsymPositivePeriod G g) (usym_positive_period_decidable G g dec) n w

def usym_least_period_deceq (G : Group) (deq : DecidableEquality (USym G)) (g : USym G)
  (n : Nat) (w : UsymPositivePeriod G g n) : Σ Nat (IsMinimum (UsymPositivePeriod G g))
  ≔ usym_least_period G g (k ↦ deq (usym_power G g k) (usym_unit G)) n w

{` In a finite group equality of symmetries is decidable. `}
def usym_least_period_finite (G : Group) (hG : IsFiniteGroup G) (g : USym G)
  (n : Nat) (w : UsymPositivePeriod G g n) : Σ Nat (IsMinimum (UsymPositivePeriod G g))
  ≔ usym_least_period_deceq G (finite_decidable_equality (USym G) hG) g n w

{` The prime case, by descent on k: write p = q·k + r with r < k; then
   g^r = e. If r = 0, then k | p, so k = 1 (k < p) and g = g^1 = e; otherwise
   0 < r < k and we recurse. No decidability of g^k = e is needed. `}
def usym_prime_period_descent (p : Nat) (hp : NatIsPrime p) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g p) (usym_unit G)) (fuel : Nat)
  : (k : Nat) → Lt k fuel → BookLt zero. k → BookLt k p → Id (USym G) (usym_power G g k) (usym_unit G)
    → Id (USym G) g (usym_unit G)
  ≔ match fuel [
  | zero. ↦ k hk hk0 hkp hgk ↦ absurd (Id (USym G) g (usym_unit G)) hk
  | suc. fuel ↦ k hk hk0 hkp hgk ↦
      let u ≔ euclidean_division p k hk0 in
      let q ≔ u .fst .fst in let r ≔ u .fst .snd in
      let hgr : Id (USym G) (usym_power G g r) (usym_unit G) ≔ calc
          usym_power G g r = usym_power G g (add (mul q k) r)
            by inverse (USym G) (usym_power G g (add (mul q k) r)) (usym_power G g r)
              (usym_power_period_left G g k hgk q r)
          = usym_power G g p by refl (usym_power G g) (inverse Nat p (add (mul q k) r) (u .snd .snd))
          = usym_unit G by h ∎ in
      match nat_dec_eq r zero. [
      | inl. r0 ↦
          match hp .snd k (mere (Σ Nat (q' ↦ Id Nat p (mul q' k)))
            (q, concat Nat p (add (mul q k) r) (mul q k) (u .snd .snd) (refl (add (mul q k)) r0))) [
          | inl. k1 ↦ calc
              g = usym_power G g (suc. zero.)
                by inverse (USym G) (usym_power G g (suc. zero.)) g (usym_power_one G g)
              = usym_power G g k by refl (usym_power G g) (inverse Nat k (suc. zero.) k1)
              = usym_unit G by hgk ∎
          | inr. kp ↦ absurd (Id (USym G) g (usym_unit G)) (lt_not_equal k p (lt_from_book k p hkp) kp) ]
      | inr. rnz ↦ usym_prime_period_descent p hp G g h fuel r
          (lt_le_trans r k fuel (lt_from_book r k (u .snd .fst)) hk)
          (r, (rnz, refl r)) (book_lt_trans r k p (u .snd .fst) hkp) hgr ] ]

{` p prime, g^p = e and g ≠ e imply g^k ≠ e for every 0 < k < p. `}
def prime_order_powers_nontrivial (p : Nat) (hp : NatIsPrime p) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g p) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  (k : Nat) (hk0 : BookLt zero. k) (hkp : BookLt k p)
  : Id (USym G) (usym_power G g k) (usym_unit G) → Empty
  ≔ hgk ↦ ne (usym_prime_period_descent p hp G g h (suc. k) k (le_refl k) hk0 hkp hgk)

{` A positive n with g^n = e and g^k ≠ e for 0 < k < n is the least positive
   period, and conversely. `}
def usym_minimum_of_nontrivial_below (G : Group) (g : USym G) (n : Nat) (pos : BookLt zero. n)
  (h : Id (USym G) (usym_power G g n) (usym_unit G))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k n → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  : IsMinimum (UsymPositivePeriod G g) n
  ≔ ((pos, h),
     (m w ↦ match le_total n m [
       | inl. le ↦ le_to_book n m le
       | inr. ge ↦ match le_split m n ge [
         | inl. lt ↦ absurd (BookLe n m) (hyp m (w .fst) (lt_to_book m n lt) (w .snd))
         | inr. eq ↦ le_to_book n m (le_from_equal n m (inverse Nat m n eq)) ] ]))

def usym_minimum_nontrivial_below (G : Group) (g : USym G) (n : Nat) (min : IsMinimum (UsymPositivePeriod G g) n)
  (k : Nat) (hk0 : BookLt zero. k) (hk : BookLt k n) : Id (USym G) (usym_power G g k) (usym_unit G) → Empty
  ≔ e ↦ usym_book_le_lt_absurd n k (min .snd k (hk0, e)) hk

{` If g^k ≠ e for 0 < k < n, then g^i = g^j with i, j < n forces i = j. `}
def usym_power_injective_le (G : Group) (g : USym G) (n : Nat)
  (hyp : (k : Nat) → BookLt zero. k → BookLt k n → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (i j : Nat) (hj : BookLt j n) (le : BookLe i j) (e : Id (USym G) (usym_power G g i) (usym_power G g j))
  : Id Nat i j
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    let d ≔ le .fst in
    let e' : Id (USym G) (concat A a a a (usym_power G g i) (refl a)) (concat A a a a (usym_power G g i) (usym_power G g d))
      ≔ calc
        concat A a a a (usym_power G g i) (refl a) = usym_power G g i by concat_p1 A a a (usym_power G g i)
        = usym_power G g j by e
        = usym_power G g (add i d)
          by refl (usym_power G g) (concat Nat j (add d i) (add i d) (inverse Nat (add d i) j (le .snd)) (add_comm d i))
        = concat A a a a (usym_power G g i) (usym_power G g d) by usym_power_add G g i d ∎ in
    let gd : Id (USym G) (usym_unit G) (usym_power G g d)
      ≔ concat_cancel_left A a a a (usym_power G g i) (refl a) (usym_power G g d) e' in
    match nat_dec_eq d zero. [
    | inl. d0 ↦ calc
        i = add zero. i by inverse Nat (add zero. i) i (add_zero_left i)
        = add d i by refl ((x ↦ add x i) : Nat → Nat) (inverse Nat d zero. d0)
        = j by le .snd ∎
    | inr. dnz ↦ absurd (Id Nat i j)
        (hyp d (d, (dnz, refl d))
          (lt_to_book d n (le_lt_trans d j n (le_from_book d j (i, concat Nat (add i d) (add d i) j (add_comm i d) (le .snd)))
            (lt_from_book j n hj)))
          (inverse (USym G) (usym_unit G) (usym_power G g d) gd)) ]

def usym_power_injective_below (G : Group) (g : USym G) (n : Nat)
  (hyp : (k : Nat) → BookLt zero. k → BookLt k n → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (i j : Nat) (hi : BookLt i n) (hj : BookLt j n) (e : Id (USym G) (usym_power G g i) (usym_power G g j))
  : Id Nat i j
  ≔ match le_total i j [
  | inl. le ↦ usym_power_injective_le G g n hyp i j hj (le_to_book i j le) e
  | inr. ge ↦ inverse Nat j i
      (usym_power_injective_le G g n hyp j i hi (le_to_book j i ge)
        (inverse (USym G) (usym_power G g i) (usym_power G g j) e)) ]

{` Hence p is the least positive period (the order) of such a g. `}
def usym_prime_order_minimum (p : Nat) (hp : NatIsPrime p) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g p) (usym_unit G)) (ne : Id (USym G) g (usym_unit G) → Empty)
  : IsMinimum (UsymPositivePeriod G g) p
  ≔ usym_minimum_of_nontrivial_below G g p (lt_to_book zero. p (lt_trans zero. (suc. zero.) p star. (hp .fst))) h
      (prime_order_powers_nontrivial p hp G g h ne)

{` Litmus checks in C_3 = cyclic_group 3 with the symmetry sigma_3 = (s⁻¹, !)
   of module 180 (evaluation at 0 is the predecessor): sigma_3^2 evaluates to
   1, sigma_3 and sigma_3^2 are nontrivial, sigma_3^3 = e, so 3 is the least
   positive period, and every period of sigma_3 is a multiple of 3. `}
def usym_power_litmus_eval (k : Nat)
  : Id (Remainder (suc. (suc. (suc. zero.))))
      (cyc_loop_equiv (suc. (suc. zero.)) .map (usym_power (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.))) k))
      (iterate (Remainder (suc. (suc. (suc. zero.)))) (modular_predecessor (suc. (suc. zero.))) k
        (remainder_at (suc. (suc. zero.)) zero. star.))
  ≔ let b : Nat ≔ suc. (suc. zero.) in
    concat (Remainder (suc. b)) (cyc_loop_equiv b .map (usym_power (cyclic_group (suc. b)) (cyc_generator b) k))
      (iterate (Remainder (suc. b)) (modular_predecessor b) k (cyc_loop_equiv b .map (refl (principal_component_point (suc. b)))))
      (iterate (Remainder (suc. b)) (modular_predecessor b) k (remainder_at b zero. star.))
      (cyc_loop_power b k)
      (refl (iterate (Remainder (suc. b)) (modular_predecessor b) k) (cyc_loop_refl b))

def usym_power_litmus_square
  : Id Nat (cyc_loop_equiv (suc. (suc. zero.)) .map
      (usym_power (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.))) (suc. (suc. zero.))) .fst)
      (suc. zero.)
  ≔ usym_power_litmus_eval (suc. (suc. zero.)) .fst

def usym_power_litmus_value (k : Nat)
  (e : Id (USym (cyclic_group (suc. (suc. (suc. zero.)))))
    (usym_power (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.))) k)
    (usym_unit (cyclic_group (suc. (suc. (suc. zero.))))))
  : Id Nat (iterate (Remainder (suc. (suc. (suc. zero.)))) (modular_predecessor (suc. (suc. zero.))) k
      (remainder_at (suc. (suc. zero.)) zero. star.) .fst) zero.
  ≔ let b : Nat ≔ suc. (suc. zero.) in
    let C3 ≔ cyclic_group (suc. b) in
    let s ≔ cyc_generator b in
    calc
      iterate (Remainder (suc. b)) (modular_predecessor b) k (remainder_at b zero. star.) .fst
      = cyc_loop_equiv b .map (usym_power C3 s k) .fst
        by inverse Nat (cyc_loop_equiv b .map (usym_power C3 s k) .fst)
          (iterate (Remainder (suc. b)) (modular_predecessor b) k (remainder_at b zero. star.) .fst)
          (usym_power_litmus_eval k .fst)
      = cyc_loop_equiv b .map (usym_unit C3) .fst
        by refl ((t ↦ cyc_loop_equiv b .map t .fst) : USym C3 → Nat) e
      = zero. by cyc_loop_refl b .fst ∎

def usym_power_litmus_order
  : IsMinimum (UsymPositivePeriod (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.))))
      (suc. (suc. (suc. zero.)))
  ≔ let C3 ≔ cyclic_group (suc. (suc. (suc. zero.))) in
    let s ≔ cyc_generator (suc. (suc. zero.)) in
    ((lt_to_book zero. (suc. (suc. (suc. zero.))) star.,
      inverse (USym C3) (usym_unit C3) (usym_power C3 s (suc. (suc. (suc. zero.))))
        (cyc_generator_order (suc. (suc. zero.)))),
     (m ↦ match m [
       | zero. ↦ w ↦ absurd (BookLe (suc. (suc. (suc. zero.))) zero.) (lt_from_book zero. zero. (w .fst))
       | suc. zero. ↦ w ↦ absurd (BookLe (suc. (suc. (suc. zero.))) (suc. zero.))
           (nat_zero_ne_suc (suc. zero.)
             (inverse Nat (suc. (suc. zero.)) zero. (usym_power_litmus_value (suc. zero.) (w .snd))))
       | suc. (suc. zero.) ↦ w ↦ absurd (BookLe (suc. (suc. (suc. zero.))) (suc. (suc. zero.)))
           (nat_zero_ne_suc zero.
             (inverse Nat (suc. zero.) zero. (usym_power_litmus_value (suc. (suc. zero.)) (w .snd))))
       | suc. (suc. (suc. m)) ↦ w ↦ le_to_book (suc. (suc. (suc. zero.))) (suc. (suc. (suc. m))) star. ]))

def usym_power_litmus_divides (m : Nat)
  (h : Id (USym (cyclic_group (suc. (suc. (suc. zero.)))))
    (usym_power (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.))) m)
    (usym_unit (cyclic_group (suc. (suc. (suc. zero.))))))
  : NatDivides (suc. (suc. (suc. zero.))) m
  ≔ usym_order_divides (cyclic_group (suc. (suc. (suc. zero.)))) (cyc_generator (suc. (suc. zero.)))
      (suc. (suc. (suc. zero.))) usym_power_litmus_order m h
