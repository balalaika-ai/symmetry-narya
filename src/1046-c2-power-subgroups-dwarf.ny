export "1045-c2-power-subgroups-lower-bound"

{` Chapter 10, the remark at fingp.tex 105: the order
   |C_2^n| = 2^n (cyclic_two_power_card, module 1012) is dwarfed by the
   number of decidable subgroups: for every k there is N such that
   k · 2^n ≤ |decidable subgroups of C_2^n| for all n ≥ N
   (c2_power_decidable_subgroups_dwarf, any finiteness proofs; N = 4k + 1).
   Proof: |decidable subgroups of C_2^(m+1)| ≥ 3^m (module 1045) and
   (m + 2) · 2^m ≤ 2 · 3^m (c2arith_growth), so 4k ≤ m + 2 gives
   k · 2^(m+1) ≤ 3^m. `}

def c2arith_le_rewrite (x y x' y' : Nat) (ex : Id Nat x x') (ey : Id Nat y y') (h : Le x y) : Le x' y'
  ≔ transport Nat (z ↦ Le x' z) y y' ey (transport Nat (z ↦ Le z y) x x' ex h)

{` 2^m ≤ 3^m. `}
def c2arith_pow_le (m : Nat) : Le (nat_power two m) (nat_power c2tri_three m)
  ≔ match m [
    | zero. ↦ le_refl (suc. zero.)
    | suc. k ↦
      le_trans (mul (nat_power two k) two) (mul (nat_power c2tri_three k) two) (mul (nat_power c2tri_three k) c2tri_three)
        (le_mul_right (nat_power two k) (nat_power c2tri_three k) two (c2arith_pow_le k))
        (le_add_base (mul (nat_power c2tri_three k) two) (nat_power c2tri_three k)) ]

{` (m + 2) · 2^m ≤ 2 · 3^m. `}
def c2arith_growth (m : Nat) : Le (mul (nat_power two m) (suc. (suc. m))) (mul (nat_power c2tri_three m) two)
  ≔ match m [
    | zero. ↦ le_refl (mul (suc. zero.) two)
    | suc. k ↦
      let a ≔ nat_power two k in
      let b ≔ nat_power c2tri_three k in
      let K : Nat ≔ suc. (suc. k) in
      let eqX : Id Nat (mul (mul a K) two) (mul (mul a two) K)
        ≔ calc
            mul (mul a K) two = mul a (mul K two) by mul_assoc a K two
            = mul a (mul two K) by map_path Nat Nat (mul a) (mul K two) (mul two K) (mul_comm K two)
            = mul (mul a two) K by inverse Nat (mul (mul a two) K) (mul a (mul two K)) (mul_assoc a two K) ∎ in
      let leX : Le (mul (mul a two) K) (mul b (mul two two))
        ≔ c2arith_le_rewrite (mul (mul a K) two) (mul (mul b two) two) (mul (mul a two) K) (mul b (mul two two))
            eqX (mul_assoc b two two) (le_mul_right (mul a K) (mul b two) two (c2arith_growth k)) in
      let leY : Le (mul a two) (mul b two) ≔ le_mul_right a b two (c2arith_pow_le k) in
      let eqR : Id Nat (add (mul b (mul two two)) (mul b two)) (mul (mul b c2tri_three) two)
        ≔ concat Nat (add (mul b (mul two two)) (mul b two)) (mul b (mul c2tri_three two)) (mul (mul b c2tri_three) two)
            (inverse Nat (mul b (add (mul two two) two)) (add (mul b (mul two two)) (mul b two))
              (mul_add_left b (mul two two) two))
            (inverse Nat (mul (mul b c2tri_three) two) (mul b (mul c2tri_three two)) (mul_assoc b c2tri_three two)) in
      c2arith_le_rewrite (add (mul (mul a two) K) (mul a two)) (add (mul b (mul two two)) (mul b two))
        (mul (mul a two) (suc. K)) (mul (mul b c2tri_three) two)
        (refl (mul (mul a two) (suc. K))) eqR
        (le_add_both (mul (mul a two) K) (mul b (mul two two)) (mul a two) (mul b two) leX leY) ]

{` Cancelling a factor 2. `}
def c2arith_le_total (x y : Nat) : Sum (Le x y) (Le (suc. y) x)
  ≔ match x, y [
    | zero., y ↦ inl. star.
    | suc. x, zero. ↦ inr. star.
    | suc. x, suc. y ↦ c2arith_le_total x y ]

def c2arith_double_step (y : Nat) : Le (suc. (mul y two)) (mul (suc. y) two)
  ≔ le_add_right (add zero. y) (suc. (add zero. y)) y (le_step (add zero. y) (add zero. y) (le_refl (add zero. y)))

def c2arith_double_cancel (x y : Nat) (h : Le (mul x two) (mul y two)) : Le x y
  ≔ match c2arith_le_total x y [
    | inl. l ↦ l
    | inr. g ↦ absurd (Le x y)
        (lt_irrefl (mul y two)
          (le_trans (suc. (mul y two)) (mul (suc. y) two) (mul y two) (c2arith_double_step y)
            (le_trans (mul (suc. y) two) (mul x two) (mul y two) (le_mul_right (suc. y) x two g) h))) ]

{` 4k ≤ m + 2 implies k · 2^(m+1) ≤ 3^m. `}
def c2arith_bound (k m : Nat) (h : Le (mul k (mul two two)) (suc. (suc. m)))
  : Le (mul k (nat_power two (suc. m))) (nat_power c2tri_three m)
  ≔ let a ≔ nat_power two m in
    let b ≔ nat_power c2tri_three m in
    let le1 : Le (mul a (mul k (mul two two))) (mul b two)
      ≔ le_trans (mul a (mul k (mul two two))) (mul a (suc. (suc. m))) (mul b two)
          (le_mul_left a (mul k (mul two two)) (suc. (suc. m)) h) (c2arith_growth m) in
    let eq : Id Nat (mul a (mul k (mul two two))) (mul (mul k (mul a two)) two)
      ≔ calc
          mul a (mul k (mul two two))
          = mul (mul a k) (mul two two) by inverse Nat (mul (mul a k) (mul two two)) (mul a (mul k (mul two two))) (mul_assoc a k (mul two two))
          = mul (mul k a) (mul two two) by map_path Nat Nat (x ↦ mul x (mul two two)) (mul a k) (mul k a) (mul_comm a k)
          = mul k (mul a (mul two two)) by mul_assoc k a (mul two two)
          = mul k (mul (mul a two) two)
            by map_path Nat Nat (mul k) (mul a (mul two two)) (mul (mul a two) two)
              (inverse Nat (mul (mul a two) two) (mul a (mul two two)) (mul_assoc a two two))
          = mul (mul k (mul a two)) two
            by inverse Nat (mul (mul k (mul a two)) two) (mul k (mul (mul a two) two)) (mul_assoc k (mul a two) two) ∎ in
    c2arith_double_cancel (mul k (mul a two)) b
      (c2arith_le_rewrite (mul a (mul k (mul two two))) (mul b two) (mul (mul k (mul a two)) two) (mul b two)
        eq (refl (mul b two)) le1)

{` The remark at fingp.tex 105. `}
def c2_power_dwarf_at (k n : Nat) (l : Le (suc. (mul k (mul two two))) n)
  (h : IsFinite (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))))
  : Le (mul k (nat_power two n)) (cardinality (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))) h)
  ≔ match n [
    | zero. ↦ match l [ ]
    | suc. m ↦
      le_trans (mul k (nat_power two (suc. m))) (nat_power c2tri_three m)
        (cardinality (Σ (Subgroups (c2pow_group (suc. m))) (IsDecidableSubgroup (c2pow_group (suc. m)))) h)
        (c2arith_bound k m
          (le_trans (mul k (mul two two)) m (suc. (suc. m)) l (le_step m (suc. m) (le_step m m (le_refl m)))))
        (c2_power_decidable_subgroups_lower_bound m h) ]

def c2_power_decidable_subgroups_dwarf (k : Nat)
  : Σ Nat (N ↦ (n : Nat) → Le N n
      → (h : IsFinite (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))))
      → Le (mul k (nat_power two n)) (cardinality (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))) h))
  ≔ (suc. (mul k (mul two two)), n l h ↦ c2_power_dwarf_at k n l h)

{` In the form "finite for every n, and eventually ≥ k · 2^n". `}
def c2_power_decidable_subgroups_dwarf_package
  : Σ ((n : Nat) → IsFinite (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))))
      (fin ↦ (k : Nat) → Mere (Σ Nat (N ↦ (n : Nat) → Le N n
         → Le (mul k (nat_power two n)) (cardinality (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))) (fin n)))))
  ≔ let fin : (n : Nat) → IsFinite (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n)))
      ≔ n ↦ decidable_subgroups_finite (c2pow_group n) (cyclic_two_power_finite n) in
    (fin,
     k ↦ mere (Σ Nat (N ↦ (n : Nat) → Le N n
         → Le (mul k (nat_power two n)) (cardinality (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))) (fin n))))
       (c2_power_decidable_subgroups_dwarf k .fst, n l ↦ c2_power_decidable_subgroups_dwarf k .snd n l (fin n)))
