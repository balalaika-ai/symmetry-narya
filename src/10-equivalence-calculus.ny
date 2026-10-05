export "08-quasi-inverses"
export "01-inductive"

def equiv_retraction (A B : Type) (e : Equiv A B) (a : A)
  : Id A (equiv_inverse_map A B e (e .map a)) a
  ≔ inverse A a (equiv_inverse_map A B e (e .map a)) (equiv_unit A B e a)

{` xca:equivalence-invers, with the expected underlying inverse map. `}
def canonical_inverse_equiv (A B : Type) (e : Equiv A B) : Equiv B A
  ≔ quasi_inverse_equiv B A (equiv_inverse_map A B e) (e .map)
      (equiv_counit A B e) (equiv_retraction A B e)

{` xca:equivalence-comp `}
def compose_equiv (A B C : Type) (e : Equiv A B) (d : Equiv B C) : Equiv A C
  ≔ let ge ≔ equiv_inverse_map A B e in
    let gd ≔ equiv_inverse_map B C d in
    quasi_inverse_equiv A C (a ↦ d .map (e .map a)) (c ↦ ge (gd c))
      (a ↦ concat A (ge (gd (d .map (e .map a)))) (ge (e .map a)) a
        (refl ge (equiv_retraction B C d (e .map a))) (equiv_retraction A B e a))
      (c ↦ concat C (d .map (e .map (ge (gd c)))) (d .map (gd c)) c
        (refl (d .map) (equiv_counit A B e (gd c))) (equiv_counit B C d c))

{` xca:Xequiv1toX `}
def unit_function_equiv (A : Type) : Equiv A (Unit → A)
  ≔ quasi_inverse_equiv A (Unit → A) (a _ ↦ a) (f ↦ f star.)
      (a ↦ refl a)
      (f ↦ funext Unit (_ ↦ A) (_ ↦ f star.) f [ star. ↦ refl (f star.) ])

{` xca:XequivXtimes1 `}
def unit_product_equiv (A : Type) : Equiv A (Product A Unit)
  ≔ quasi_inverse_equiv A (Product A Unit) (a ↦ (a, star.)) (p ↦ p .fst)
      (a ↦ refl a) (p ↦ (refl (p .fst), unit_prop star. (p .snd)))

{` Products preserve equivalences (auxiliary). `}
def product_equiv (A B X Y : Type) (e : Equiv A X) (d : Equiv B Y)
  : Equiv (Product A B) (Product X Y)
  ≔ quasi_inverse_equiv (Product A B) (Product X Y)
      (p ↦ (e .map (p .fst), d .map (p .snd)))
      (p ↦ (equiv_inverse_map A X e (p .fst), equiv_inverse_map B Y d (p .snd)))
      (p ↦ (equiv_retraction A X e (p .fst), equiv_retraction B Y d (p .snd)))
      (p ↦ (equiv_counit A X e (p .fst), equiv_counit B Y d (p .snd)))

{` Coproducts preserve equivalences (auxiliary). `}
def sum_equiv (A B X Y : Type) (e : Equiv A X) (d : Equiv B Y)
  : Equiv (Sum A B) (Sum X Y)
  ≔ quasi_inverse_equiv (Sum A B) (Sum X Y)
      [ inl. a ↦ inl. (e .map a) | inr. b ↦ inr. (d .map b) ]
      [ inl. x ↦ inl. (equiv_inverse_map A X e x)
      | inr. y ↦ inr. (equiv_inverse_map B Y d y) ]
      [ inl. a ↦ inl. (equiv_retraction A X e a)
      | inr. b ↦ inr. (equiv_retraction B Y d b) ]
      [ inl. x ↦ inl. (equiv_counit A X e x)
      | inr. y ↦ inr. (equiv_counit B Y d y) ]

{` The associativity equivalence used at ft:Sigma-assoc. `}
def sigma_assoc (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  : Equiv (Σ (Σ A B) (p ↦ C (p .fst) (p .snd))) (Σ A (a ↦ Σ (B a) (C a)))
  ≔ quasi_inverse_equiv
      (Σ (Σ A B) (p ↦ C (p .fst) (p .snd))) (Σ A (a ↦ Σ (B a) (C a)))
      (p ↦ (p .fst .fst, (p .fst .snd, p .snd)))
      (p ↦ ((p .fst, p .snd .fst), p .snd .snd))
      (p ↦ refl p) (p ↦ refl p)

{` xca:Sigma-distrib `}
def sigma_distrib (A B : Type) (C : A → Type)
  : Equiv (Σ A (a ↦ Product (C a) B)) (Product (Σ A C) B)
  ≔ quasi_inverse_equiv (Σ A (a ↦ Product (C a) B)) (Product (Σ A C) B)
      (p ↦ ((p .fst, p .snd .fst), p .snd .snd))
      (p ↦ (p .fst .fst, (p .fst .snd, p .snd)))
      (p ↦ refl p) (p ↦ refl p)

{` xca:Sigma-comm `}
def sigma_comm (A B : Type) (C : A → B → Type)
  : Equiv (Σ A (a ↦ Σ B (b ↦ C a b))) (Σ B (b ↦ Σ A (a ↦ C a b)))
  ≔ quasi_inverse_equiv (Σ A (a ↦ Σ B (b ↦ C a b))) (Σ B (b ↦ Σ A (a ↦ C a b)))
      (p ↦ (p .snd .fst, (p .fst, p .snd .snd)))
      (p ↦ (p .snd .fst, (p .fst, p .snd .snd)))
      (p ↦ refl p) (p ↦ refl p)

{` The orientations printed in xca:Xequiv1toX and xca:XequivXtimes1. `}
def unit_evaluation_equiv (A : Type) : Equiv (Unit → A) A
  ≔ quasi_inverse_equiv (Unit → A) A (f ↦ f star.) (a _ ↦ a)
      (f ↦ funext Unit (_ ↦ A) (_ ↦ f star.) f [ star. ↦ refl (f star.) ])
      (a ↦ refl a)

def unit_projection_equiv (A : Type) : Equiv (Σ A (_ ↦ Unit)) A
  ≔ quasi_inverse_equiv (Σ A (_ ↦ Unit)) A (p ↦ p .fst) (a ↦ (a, star.))
      (p ↦ (refl (p .fst), unit_prop star. (p .snd))) (a ↦ refl a)

{` The precise factor ordering printed in xca:Sigma-distrib. `}
def sigma_distrib_left (X Y : Type) (Z : Y → Type)
  : Equiv (Product X (Σ Y Z)) (Σ Y (y ↦ Product X (Z y)))
  ≔ quasi_inverse_equiv (Product X (Σ Y Z)) (Σ Y (y ↦ Product X (Z y)))
      (p ↦ (p .snd .fst, (p .fst, p .snd .snd)))
      (p ↦ (p .snd .fst, (p .fst, p .snd .snd)))
      (p ↦ refl p) (p ↦ refl p)

def BoolFamily (X Y : Type) : Bool → Type ≔ [ false. ↦ X | true. ↦ Y ]

def bool_pi_pair (X Y : Type) (f : (b : Bool) → BoolFamily X Y b) : Product X Y
  ≔ (f false., f true.)

def bool_pair_pi (X Y : Type) (p : Product X Y) : (b : Bool) → BoolFamily X Y b
  ≔ [ false. ↦ p .fst | true. ↦ p .snd ]

{` xca:binary-prod-equiv, exactly the Boolean-indexed product statement. `}
def bool_product_equiv (X Y : Type) : Equiv ((b : Bool) → BoolFamily X Y b) (Product X Y)
  ≔ quasi_inverse_equiv ((b : Bool) → BoolFamily X Y b) (Product X Y)
      (bool_pi_pair X Y) (bool_pair_pi X Y)
      (f ↦ funext Bool (BoolFamily X Y) (bool_pair_pi X Y (bool_pi_pair X Y f)) f
        [ false. ↦ refl (f false.) | true. ↦ refl (f true.) ])
      (p ↦ refl p)

def bool_sum_sigma (X Y : Type) : Sum X Y → Σ Bool (BoolFamily X Y)
  ≔ [ inl. x ↦ (false., x) | inr. y ↦ (true., y) ]

def bool_sigma_sum_at (X Y : Type) (b : Bool) (v : BoolFamily X Y b) : Sum X Y
  ≔ match b [ false. ↦ inl. v | true. ↦ inr. v ]

def bool_sigma_sum (X Y : Type) (p : Σ Bool (BoolFamily X Y)) : Sum X Y
  ≔ bool_sigma_sum_at X Y (p .fst) (p .snd)

def bool_sigma_roundtrip (X Y : Type) (b : Bool) (v : BoolFamily X Y b)
  : Id (Σ Bool (BoolFamily X Y)) (bool_sum_sigma X Y (bool_sigma_sum_at X Y b v)) (b, v)
  ≔ match b [ false. ↦ refl (false., v) | true. ↦ refl (true., v) ]

{` xca:binary-sum-equiv, exactly the Boolean-indexed sum statement. `}
def bool_sum_equiv (X Y : Type) : Equiv (Sum X Y) (Σ Bool (BoolFamily X Y))
  ≔ quasi_inverse_equiv (Sum X Y) (Σ Bool (BoolFamily X Y))
      (bool_sum_sigma X Y) (bool_sigma_sum X Y)
      [ inl. x ↦ refl (inl. x : Sum X Y) | inr. y ↦ refl (inr. y : Sum X Y) ]
      (p ↦ bool_sigma_roundtrip X Y (p .fst) (p .snd))
