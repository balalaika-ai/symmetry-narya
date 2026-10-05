export "109-connected-map-sections"

{` def:n-truncated for every n>=-2, indexed by h-level n+2. This
   definition needs no constructor for higher truncations. `}
def TruncatedMap (level : Nat) (A B : Type) (f : A → B) : Type
  ≔ (b : B) → HLevel level (BookFiber A B f b)

def truncated_map_prop (level : Nat) (A B : Type) (f : A → B) : isProp (TruncatedMap level A B f)
  ≔ pi_prop B (b ↦ HLevel level (BookFiber A B f b))
      (b ↦ hlevel_isprop level (BookFiber A B f b))

def truncated_map_raise (level : Nat) (A B : Type) (f : A → B) (h : TruncatedMap level A B f)
  : TruncatedMap (suc. level) A B f ≔ b ↦ hlevel_raise level (BookFiber A B f b) (h b)

def minus_two_truncated_map_equiv (A B : Type) (f : A → B)
  : Equiv (TruncatedMap zero. A B f) (BookIsEquiv A B f)
  ≔ iff_equiv (TruncatedMap zero. A B f) (BookIsEquiv A B f)
      (truncated_map_prop zero. A B f) (book_isequiv_isprop A B f)
      (h b ↦ book_contraction (BookFiber A B f b) (h b))
      (h b ↦ native_contraction (BookFiber A B f b) (h b))

def minus_one_truncated_map_equiv (A B : Type) (f : A → B)
  : Equiv (TruncatedMap (suc. zero.) A B f) (IsEmbedding A B f)
  ≔ iff_equiv (TruncatedMap (suc. zero.) A B f) (IsEmbedding A B f)
      (truncated_map_prop (suc. zero.) A B f)
      (pi_prop B (b ↦ isProp (BookFiber A B f b)) (b ↦ isprop_isprop (BookFiber A B f b)))
      (h b ↦ hlevel_one_to_prop (BookFiber A B f b) (h b))
      (h b ↦ prop_to_hlevel_one (BookFiber A B f b) (h b))

def zero_truncated_map_equiv (A B : Type) (f : A → B)
  : Equiv (TruncatedMap (suc. (suc. zero.)) A B f) (IsCovering A B f)
  ≔ iff_equiv (TruncatedMap (suc. (suc. zero.)) A B f) (IsCovering A B f)
      (truncated_map_prop (suc. (suc. zero.)) A B f) (covering_property_prop B (A, f))
      (h b ↦ hlevel_two_to_set (BookFiber A B f b) (h b))
      (h b ↦ set_to_hlevel_two (BookFiber A B f b) (h b))

def MinusOneConnectedMap (A B : Type) (f : A → B) : Type
  ≔ (b : B) → BookIsContr (Mere (BookFiber A B f b))

def minus_one_connected_map_equiv (A B : Type) (f : A → B)
  : Equiv (MinusOneConnectedMap A B f) (Surjective A B f)
  ≔ iff_equiv (MinusOneConnectedMap A B f) (Surjective A B f)
      (pi_prop B (b ↦ BookIsContr (Mere (BookFiber A B f b)))
        (b ↦ book_iscontr_isprop (Mere (BookFiber A B f b)))) (surjective_property_prop A B f)
      (h b ↦ h b .center) (h b ↦ (h b, mere_isprop (BookFiber A B f b) (h b)))

{` def:type-of-factorizations, keeping the specified triangular equality. `}
def Factorizations (A B : Type) (f : A → B) : Type ≔ ImageFactorizationTriangles A B f

def ZeroFactorizationProperties (A B : Type) (f : A → B) (t : Factorizations A B f) : Type
  ≔ Product (ZeroConnectedMap A (t .fst) (t .snd .fst)) (IsCovering (t .fst) B (t .snd .snd .fst))

def zero_factorization_regroup (A B : Type) (f : A → B)
  : Equiv (ZeroImageFactorizations A B f) (Σ (Factorizations A B f) (ZeroFactorizationProperties A B f))
  ≔ quasi_inverse_equiv (ZeroImageFactorizations A B f)
      (Σ (Factorizations A B f) (ZeroFactorizationProperties A B f))
      (t ↦ ((t .fst, (t .snd .fst, (t .snd .snd .fst, t .snd .snd .snd .fst))), t .snd .snd .snd .snd))
      (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd .fst, (t .fst .snd .snd .snd, t .snd)))))
      (t ↦ refl t) (t ↦ refl t)

def set_trunc_of_set_equiv (S : Type) (hs : isSet S) : Equiv (SetTrunc S) S
  ≔ quasi_inverse_equiv (SetTrunc S) S (set_trunc_rec S S hs (identity S)) (set_trunc S)
      (z ↦ surjection_function_ext S (SetTrunc S) (SetTrunc S) (set_trunc S) (set_trunc_surjective S)
        (set_trunc_set S) (compose (SetTrunc S) S (SetTrunc S) (set_trunc S) (set_trunc_rec S S hs (identity S)))
        (identity (SetTrunc S)) (refl (set_trunc S)) (refl z)) (s ↦ refl s)

{` The version used in the proof of thm:n-im-univ-prop: when the base
   is a set, only the summands need truncating. `}
def truncated_sum_set_base_equiv (X : Type) (hx : isSet X) (Y : X → Type)
  : Equiv (SetTrunc (Σ X Y)) (Σ X (x ↦ SetTrunc (Y x)))
  ≔ compose_equiv (SetTrunc (Σ X Y)) (SetTrunc (Σ X (x ↦ SetTrunc (Y x))))
      (Σ X (x ↦ SetTrunc (Y x))) (truncated_sum_equiv X Y)
      (set_trunc_of_set_equiv (Σ X (x ↦ SetTrunc (Y x)))
        (sigma_set X (x ↦ SetTrunc (Y x)) hx (x ↦ set_trunc_set (Y x))))
