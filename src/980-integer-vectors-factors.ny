export "981-integer-determinant"
export "966-integer-matrix-diagonal"

{` Chapter 9 (subgroups.tex 1186), the general n × n integer-matrix
   example: lists of factors of a self-map of Int^n (unimodular, or
   diagonal with nonzero entries), their composite and the product of the
   absolute values of the diagonal entries. Integer vectors, matrices,
   finite sums, A · x, additive and unimodular maps and the determinant are
   in module 981 (which only needs the integers, module 1310). Modules
   982-985 factor A · x into such a list with |det A| = card, modules
   986-987 turn additive self-maps of Int^n into homomorphisms Z^n → Z^n,
   module 988 combines both. `}

def IntMatFactor (n : Nat) : Type
  ≔ Sum (Σ ((Fin n → Int) → Fin n → Int) (IntVecUnimodular n))
      (Σ (Fin n → Int) (d ↦ (i : Fin n) → IntNonzero (d i)))

def int_mat_factor_map (n : Nat) (f : IntMatFactor n) : (Fin n → Int) → Fin n → Int
  ≔ match f [ inl. u ↦ u .fst | inr. d ↦ int_diag_map n (d .fst) ]

def int_mat_factor_card (n : Nat) (f : IntMatFactor n) : Nat
  ≔ match f [ inl. _ ↦ suc. zero. | inr. d ↦ fin_nat_prod n (i ↦ int_abs_nat (d .fst i)) ]

{` The composite of a list of factors, the head applied last. `}
def int_mat_factors_eval (n : Nat) (l : List (IntMatFactor n)) (x : Fin n → Int) : Fin n → Int
  ≔ match l [ nil. ↦ x | cons. f l ↦ int_mat_factor_map n f (int_mat_factors_eval n l x) ]

def int_mat_factors_card (n : Nat) (l : List (IntMatFactor n)) : Nat
  ≔ match l [ nil. ↦ suc. zero. | cons. f l ↦ mul (int_mat_factor_card n f) (int_mat_factors_card n l) ]

