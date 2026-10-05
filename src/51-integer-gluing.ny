export "50-integer-quotient"

def nat_head (P : Nat → Type) (f : (n : Nat) → P n) : P zero. ≔ f zero.
def nat_tail (P : Nat → Type) (f : (n : Nat) → P n) : (n : Nat) → P (suc. n) ≔ n ↦ f (suc. n)
def nat_prepend (P : Nat → Type) (a : P zero.) (f : (n : Nat) → P (suc. n)) (n : Nat) : P n
  ≔ match n [ zero. ↦ a | suc. n ↦ f n ]

def nat_head_homotopy (P : Nat → Type) (a : P zero.)
  (u : BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a)
  (n : Nat) : Id (P n) (nat_prepend P a (nat_tail P (u .fst)) n) (u .fst n)
  ≔ match n [ zero. ↦ u .snd | suc. n ↦ refl (u .fst (suc. n)) ]

def nat_head_rebuild (P : Nat → Type) (a : P zero.)
  (u : BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a)
  : Id (BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a)
      (nat_prepend P a (nat_tail P (u .fst)), refl a) u
  ≔ let k ≔ nat_prepend P a (nat_tail P (u .fst)) in
    let H ≔ nat_head_homotopy P a u in
    let r ≔ funext Nat P k (u .fst) H in
    equiv_inverse_map
      (Id (BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a) (k, refl a) u)
      (BookFiber (Id ((n : Nat) → P n) k (u .fst)) (Id (P zero.) a (u .fst zero.))
        (map_path ((n : Nat) → P n) (P zero.) (nat_head P) k (u .fst)) (u .snd))
      (ap_fiber_equiv ((n : Nat) → P n) (P zero.) (nat_head P) k (u .fst) (u .snd))
      (r, funext_beta Nat P k (u .fst) H zero.)

def nat_head_book_fiber_equiv (P : Nat → Type) (a : P zero.)
  : Equiv (BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a) ((n : Nat) → P (suc. n))
  ≔ quasi_inverse_equiv (BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a) ((n : Nat) → P (suc. n))
      (u ↦ nat_tail P (u .fst)) (f ↦ (nat_prepend P a f, refl a)) (nat_head_rebuild P a) (f ↦ refl f)

def nat_head_fiber_equiv (P : Nat → Type) (a : P zero.)
  : Equiv (Fiber ((n : Nat) → P n) (P zero.) (nat_head P) a) ((n : Nat) → P (suc. n))
  ≔ compose_equiv (Fiber ((n : Nat) → P n) (P zero.) (nat_head P) a)
      (BookFiber ((n : Nat) → P n) (P zero.) (nat_head P) a) ((n : Nat) → P (suc. n))
      (fiber_conventions_equiv ((n : Nat) → P n) (P zero.) (nat_head P) a) (nat_head_book_fiber_equiv P a)

def int_nonpositive (n : Nat) : Int ≔ match n [ zero. ↦ pos. zero. | suc. n ↦ neg. n ]
def int_zero_glue : Id Int (int_nonpositive zero.) (int_of_nat zero.) ≔ refl int_zero

{` The dependent gluing data of def:zet. Both zero endpoints are represented
   by int_zero here; the gluing path is reflexivity. `}
def IntegerBoundary (P : Int → Type) : Type
  ≔ Σ ((n : Nat) → P (int_of_nat n)) (g ↦
      Σ ((n : Nat) → P (int_nonpositive n)) (h ↦ Id (P int_zero) (h zero.) (g zero.)))

def integer_boundary_pair (P : Int → Type)
  : Equiv (IntegerBoundary P)
      (Product ((n : Nat) → P (pos. n)) ((n : Nat) → P (neg. n)))
  ≔ family_equiv ((n : Nat) → P (pos. n))
      (g ↦ Fiber ((n : Nat) → P (int_nonpositive n)) (P int_zero)
        (nat_head (n ↦ P (int_nonpositive n))) (g zero.))
      (_ ↦ (n : Nat) → P (neg. n))
      (g ↦ nat_head_fiber_equiv (n ↦ P (int_nonpositive n)) (g zero.))

def integer_boundary_evaluate (P : Int → Type) (f : (z : Int) → P z) : IntegerBoundary P
  ≔ ((n ↦ f (pos. n)), ((n ↦ f (int_nonpositive n)), refl (f int_zero)))

def integer_boundary_rec (P : Int → Type) (d : IntegerBoundary P) (z : Int) : P z
  ≔ match z [ pos. n ↦ d .fst n | neg. n ↦ d .snd .fst (suc. n) ]

def integer_boundary_beta (P : Int → Type) (d : IntegerBoundary P)
  : Id (IntegerBoundary P) (integer_boundary_evaluate P (integer_boundary_rec P d)) d
  ≔ equivalence_injective (IntegerBoundary P) (Product ((n : Nat) → P (pos. n)) ((n : Nat) → P (neg. n)))
      (integer_boundary_pair P) (integer_boundary_evaluate P (integer_boundary_rec P d)) d
      (refl (d .fst, (n ↦ d .snd .fst (suc. n))))

def integer_boundary_eta (P : Int → Type) (f : (z : Int) → P z)
  : Id ((z : Int) → P z) (integer_boundary_rec P (integer_boundary_evaluate P f)) f
  ≔ funext Int P (integer_boundary_rec P (integer_boundary_evaluate P f)) f
      [ pos. n ↦ refl (f (pos. n)) | neg. n ↦ refl (f (neg. n)) ]

def integer_gluing_universal_property (P : Int → Type)
  : BookEquiv ((z : Int) → P z) (IntegerBoundary P)
  ≔ book_quasi_inverse_equiv ((z : Int) → P z) (IntegerBoundary P)
      (integer_boundary_evaluate P) (integer_boundary_rec P) (integer_boundary_eta P) (integer_boundary_beta P)

def integer_gluing_positive_beta (P : Int → Type) (d : IntegerBoundary P) (n : Nat)
  : Id (P (pos. n)) (integer_boundary_rec P d (pos. n)) (d .fst n) ≔ refl (d .fst n)

{` At the shared zero this law uses the specified gluing path. It is not a
   judgmental negative-zero beta rule. The full coherence is integer_boundary_beta. `}
def integer_gluing_negative_beta (P : Int → Type) (d : IntegerBoundary P) (n : Nat)
  : Id (P (int_nonpositive n)) (integer_boundary_rec P d (int_nonpositive n)) (d .snd .fst n)
  ≔ match n [ zero. ↦ inverse (P int_zero) (d .snd .fst zero.) (d .fst zero.) (d .snd .snd)
             | suc. n ↦ refl (d .snd .fst (suc. n)) ]

def integer_gluing_pathover (P : Int → Type) (d : IntegerBoundary P)
  : Id P int_zero_glue (d .snd .fst zero.) (d .fst zero.) ≔ d .snd .snd
