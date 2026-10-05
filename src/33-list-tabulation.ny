export "32-finite-cardinality"

{` xca:tabulation. The head index is inr star; inl shifts a tail index.
   This is the numbering used by fin_below_equiv: head is 0, shift is successor. `}
def Table (A : Type) : Type ≔ Σ Nat (n ↦ Fin n → A)

def table_cons (A : Type) (a : A) (t : Table A) : Table A
  ≔ (suc. (t .fst), [ inl. i ↦ t .snd i | inr. u ↦ a ])

def lookup (A : Type) (xs : List A) : Table A
  ≔ match xs [ nil. ↦ (zero., x ↦ match x [])
             | cons. a xs ↦ table_cons A a (lookup A xs) ]

def tabulate (A : Type) (n : Nat) (f : Fin n → A) : List A
  ≔ match n [ zero. ↦ nil.
             | suc. n ↦ cons. (f (inr. star.)) (tabulate A n (i ↦ f (inl. i))) ]

def tabulate_lookup (A : Type) (xs : List A)
  : Id (List A) (tabulate A (lookup A xs .fst) (lookup A xs .snd)) xs
  ≔ match xs [ nil. ↦ refl (nil. : List A)
             | cons. a xs ↦ cons. (refl a) (tabulate_lookup A xs) ]

def lookup_tabulate (A : Type) (n : Nat) (f : Fin n → A)
  : Id (Table A) (lookup A (tabulate A n f)) (n, f)
  ≔ match n [
  | zero. ↦ (refl zero., funext Empty (_ ↦ A) (lookup A nil. .snd) f (x ↦ match x []))
  | suc. n ↦ concat (Table A) (lookup A (tabulate A (suc. n) f))
      (table_cons A (f (inr. star.)) (n, i ↦ f (inl. i))) (suc. n, f)
      (map_path (Table A) (Table A) (table_cons A (f (inr. star.)))
        (lookup A (tabulate A n (i ↦ f (inl. i)))) (n, i ↦ f (inl. i))
        (lookup_tabulate A n (i ↦ f (inl. i))))
      (refl (suc. n), funext (Fin (suc. n)) (_ ↦ A)
        (table_cons A (f (inr. star.)) (n, i ↦ f (inl. i)) .snd) f
        [ inl. i ↦ refl (f (inl. i))
        | inr. u ↦ match u [ star. ↦ refl (f (inr. star.)) ] ]) ]

def lookup_equiv (A : Type) : BookEquiv (List A) (Table A)
  ≔ book_quasi_inverse_equiv (List A) (Table A) (lookup A)
      (t ↦ tabulate A (t .fst) (t .snd)) (tabulate_lookup A)
      (t ↦ lookup_tabulate A (t .fst) (t .snd))

def lookup_length (A : Type) (xs : List A) : Id Nat (lookup A xs .fst) (length A xs)
  ≔ match xs [ nil. ↦ refl zero. | cons. a xs ↦ suc. (lookup_length A xs) ]

def lookup_head (A : Type) (a : A) (xs : List A)
  : Id A (lookup A (cons. a xs) .snd (inr. star.)) a ≔ refl a

def lookup_tail (A : Type) (a : A) (xs : List A) (i : Fin (lookup A xs .fst))
  : Id A (lookup A (cons. a xs) .snd (inl. i)) (lookup A xs .snd i)
  ≔ refl (lookup A xs .snd i)

def fin_head_index (n : Nat)
  : Id Nat (fin_below_equiv (suc. n) .map (inr. star.) .fst) zero. ≔ refl zero.

def fin_shift_index (n : Nat) (i : Fin n)
  : Id Nat (fin_below_equiv (suc. n) .map (inl. i) .fst)
      (suc. (fin_below_equiv n .map i .fst)) ≔ refl (suc. (fin_below_equiv n .map i .fst))
