export "1315-standard-vector-space"

{` Chapter 14, section "The icosahedron" (geometry.tex 292-308): the twelve
   vertices are the cyclic permutations of (0, ±1, ±φ). The vertex list is
   defined for any coordinate type S with 0, 1, negation and an element φ
   (module 1442 uses S = K, φ the golden ratio). Litmus over the ring
   ℤ[φ] = ℤ ⊕ ℤφ with φ² = φ + 1 (pairs of integers, multiplication
   (a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ), computed by refl: all 12
   vertices are distinct; among the 132 ordered pairs of distinct vertices,
   60 are at squared distance 4 (the 30 edges of length 2), 60 at 4φ² =
   4 + 4φ and 12 (antipodal) at 4 + 4φ² = 8 + 4φ; every vertex has exactly 5
   neighbours at distance 2. `}

{` Vertices are indexed by a cyclic shift k : Fin 3 and two signs. `}
def IcosaIndex : Type ≔ Product (Fin 3) (Product Bool Bool)

def triple_vector (S : Type) (a b c : S) : Fin 3 → S
  ≔ [ inl. (inl. _) ↦ a | inl. (inr. _) ↦ b | inr. _ ↦ c ]

def icosa_sign (S : Type) (ng : S → S) (b : Bool) (x : S) : S ≔ match b [ true. ↦ x | false. ↦ ng x ]

{` k = 0: (0, ±1, ±φ); k = 1: (±φ, 0, ±1); k = 2: (±1, ±φ, 0). `}
def icosa_vertex (S : Type) (z o : S) (ng : S → S) (φ : S) (i : IcosaIndex) : Fin 3 → S
  ≔ let a ≔ z in let b ≔ icosa_sign S ng (i .snd .fst) o in let c ≔ icosa_sign S ng (i .snd .snd) φ in
    match i .fst [
    | inl. (inl. _) ↦ triple_vector S a b c
    | inl. (inr. _) ↦ triple_vector S c a b
    | inr. _ ↦ triple_vector S b c a ]

{` ℤ[φ]. `}
def GoldenInt : Type ≔ Product Int Int

def golden_add (x y : GoldenInt) : GoldenInt ≔ (int_add (x .fst) (y .fst), int_add (x .snd) (y .snd))

def golden_neg (x : GoldenInt) : GoldenInt ≔ (int_neg (x .fst), int_neg (x .snd))

def golden_mul (x y : GoldenInt) : GoldenInt
  ≔ (int_add (int_mul (x .fst) (y .fst)) (int_mul (x .snd) (y .snd)),
     int_add (int_add (int_mul (x .fst) (y .snd)) (int_mul (x .snd) (y .fst))) (int_mul (x .snd) (y .snd)))

def golden_zero : GoldenInt ≔ (pos. zero., pos. zero.)
def golden_one : GoldenInt ≔ (pos. (suc. zero.), pos. zero.)
def golden_phi : GoldenInt ≔ (pos. zero., pos. (suc. zero.))

{` Litmus: φ² = φ + 1 in ℤ[φ]. `}
def golden_phi_square : Id GoldenInt (golden_mul golden_phi golden_phi) (golden_add golden_phi golden_one)
  ≔ refl (golden_add golden_phi golden_one)

def golden_dec_eq (x y : GoldenInt) : Decidable (Id GoldenInt x y)
  ≔ match int_dec_eq (x .fst) (y .fst) [
    | inr. no ↦ inr. (p ↦ no (refl ((u ↦ u .fst) : GoldenInt → Int) p))
    | inl. p ↦ match int_dec_eq (x .snd) (y .snd) [
      | inr. no ↦ inr. (q ↦ no (refl ((u ↦ u .snd) : GoldenInt → Int) q))
      | inl. q ↦ inl. (refl ((a b ↦ (a, b)) : Int → Int → GoldenInt) p q) ] ]

def golden_vertex (i : IcosaIndex) : Fin 3 → GoldenInt
  ≔ icosa_vertex GoldenInt golden_zero golden_one golden_neg golden_phi i

def golden_square (x : GoldenInt) : GoldenInt ≔ golden_mul x x

def golden_sq_distance (u v : Fin 3 → GoldenInt) : GoldenInt
  ≔ let d ≔ (j : Fin 3) ↦ golden_add (u j) (golden_neg (v j)) in
    golden_add (golden_add (golden_square (d (inl. (inl. (inr. star.))))) (golden_square (d (inl. (inr. star.)))))
      (golden_square (d (inr. star.)))

def golden_indicator (x y : GoldenInt) : Nat ≔ match golden_dec_eq x y [ inl. _ ↦ 1 | inr. _ ↦ 0 ]

def sum_over_bool (f : Bool → Nat) : Nat ≔ add (f true.) (f false.)

def sum_over_icosa_index (f : IcosaIndex → Nat) : Nat
  ≔ let g ≔ (k : Fin 3) ↦ sum_over_bool (b ↦ sum_over_bool (c ↦ f (k, (b, c)))) in
    add (add (g (inl. (inl. (inr. star.)))) (g (inl. (inr. star.)))) (g (inr. star.))

def icosa_pair_count (t : GoldenInt) : Nat
  ≔ sum_over_icosa_index (i ↦ sum_over_icosa_index (j ↦ golden_indicator (golden_sq_distance (golden_vertex i) (golden_vertex j)) t))

def icosa_degree (i : IcosaIndex) : Nat
  ≔ sum_over_icosa_index (j ↦ golden_indicator (golden_sq_distance (golden_vertex i) (golden_vertex j)) (pos. 4, pos. zero.))

def icosa_count_zero : Id Nat (icosa_pair_count golden_zero) 12 ≔ refl (12 : Nat)
def icosa_count_edges : Id Nat (icosa_pair_count (pos. 4, pos. zero.)) 60 ≔ refl (60 : Nat)
def icosa_count_second : Id Nat (icosa_pair_count (pos. 4, pos. 4)) 60 ≔ refl (60 : Nat)
def icosa_count_antipodal : Id Nat (icosa_pair_count (pos. 8, pos. 4)) 12 ≔ refl (12 : Nat)

{` Every vertex has exactly five neighbours at distance 2. `}
def icosa_degree_five_cases (k : Fin 3) (b c : Bool) : Id Nat (icosa_degree (k, (b, c))) 5
  ≔ match k [
    | inl. (inl. (inl. e)) ↦ match e [ ]
    | inl. (inl. (inr. star.)) ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ]
    | inl. (inr. star.) ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ]
    | inr. star. ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ] ]

def icosa_degree_five (i : IcosaIndex) : Id Nat (icosa_degree i) 5
  ≔ icosa_degree_five_cases (i .fst) (i .snd .fst) (i .snd .snd)

{` The remark's pair: (0, 1, φ) and (1, φ, 0) are at squared distance 4. `}
def icosa_remark_pair_golden
  : Id GoldenInt
      (golden_sq_distance (golden_vertex (inl. (inl. (inr. star.)), (true., true.)))
        (golden_vertex (inr. star., (true., true.))))
      (pos. 4, pos. zero.)
  ≔ refl ((pos. 4, pos. zero.) : GoldenInt)
