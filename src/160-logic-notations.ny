export "136-roots-of-infinite-cycles"

{` def:neg-eq-ne. Negation is formed for a proposition and equations for
   elements of a set; both are packaged with their proposition proofs. `}
def Negation (P : PropTypes) : PropTypes ≔ (Not (P .fst), negation_prop (P .fst))

def Equation (A : SetTypes) (a b : A .fst) : PropTypes ≔ (Id (A .fst) a b, A .snd a b)

def Unequal (A : SetTypes) (a b : A .fst) : PropTypes ≔ Negation (Equation A a b)

{` rem:diagram. A square of functions is filled by an identification
   g∘p = q∘f; when the sink is a set this is a proposition. A square of
   identifications is filled by an identification of the two composites. `}
def SquareFiller (X Y S T : Type) (f : X → Y) (p : X → S) (q : Y → T) (g : S → T) : Type
  ≔ Id (X → T) (compose X S T g p) (compose X Y T q f)

def square_filler_prop (X Y S T : Type) (f : X → Y) (p : X → S) (q : Y → T) (g : S → T)
  (hT : isSet T) : isProp (SquareFiller X Y S T f p q g)
  ≔ pi_set X (_ ↦ T) (_ ↦ hT) (compose X S T g p) (compose X Y T q f)

def PathSquareFiller (W : Type) (x y s t : W) (f : Id W x y) (p : Id W x s) (q : Id W y t)
  (g : Id W s t) : Type
  ≔ Id (Id W x t) (concat W x s t p g) (concat W x y t f q)

def path_square_filler_prop (W : Type) (x y s t : W) (f : Id W x y) (p : Id W x s) (q : Id W y t)
  (g : Id W s t) (h : isSet (Id W x t)) : isProp (PathSquareFiller W x y s t f p q g)
  ≔ h (concat W x s t p g) (concat W x y t f q)

{` def:non-empty, relative to a truncation signature and for the
   constructed impredicative truncation. `}
def IsNonEmpty (T : TruncationSignature) (A : Type) : Type ≔ T .carrier A

def NonEmpty (A : Type) : Type ≔ IsNonEmpty native_truncation A

def negation_empty_path (A : Type) (n : Not A) : Id Type A Empty
  ≔ ua A Empty (n, e ↦ match e [])

{` The footnote to def:non-empty: not being empty, ¬(T = ∅), is
   equivalent to ¬¬T. `}
def not_empty_double_negation (A : Type) : Equiv (Not (Id Type A Empty)) (Not (Not A))
  ≔ iff_equiv (Not (Id Type A Empty)) (Not (Not A))
      (negation_prop (Id Type A Empty)) (negation_prop (Not A))
      (h n ↦ h (negation_empty_path A n))
      (h p ↦ h (a ↦ p .trr a))

{` The unnumbered definitions of disjunction, existence and unique
   existence, as propositions. The first two are the native instances of
   Or and Exists from 12-logic; the last one needs no truncation. `}
def Disjunction (P Q : PropTypes) : PropTypes
  ≔ (Mere (Sum (P .fst) (Q .fst)), mere_isprop (Sum (P .fst) (Q .fst)))

def Existence (X : Type) (P : X → PropTypes) : PropTypes
  ≔ (Mere (Σ X (x ↦ P x .fst)), mere_isprop (Σ X (x ↦ P x .fst)))

def UniqueExistence (X : Type) (P : X → PropTypes) : PropTypes
  ≔ (ExistsUnique X (x ↦ P x .fst), book_iscontr_isprop (Σ X (x ↦ P x .fst)))

def disjunction_native_or (P Q : PropTypes)
  : Id Type (Disjunction P Q .fst) (Or native_truncation (P .fst) (Q .fst))
  ≔ refl (Disjunction P Q .fst)

def existence_native_exists (X : Type) (P : X → PropTypes)
  : Id Type (Existence X P .fst) (Exists native_truncation X (x ↦ P x .fst))
  ≔ refl (Existence X P .fst)

{` xca:inj-sets. The book injection has propositional book fibers; the
   second notion reflects paths. The first map needs no set hypothesis. `}
def embedding_reflects_paths (A B : Type) (f : A → B) (h : IsEmbedding A B f)
  : PathReflecting A B f
  ≔ a a' p ↦ h (f a') (a, inverse B (f a) (f a') p) (a', refl (f a')) .fst

def path_reflecting_set_embedding (A B : Type) (setB : isSet B) (f : A → B)
  (inj : PathReflecting A B f) : IsEmbedding A B f
  ≔ b ↦ retract_prop (Fiber A B f b) (BookFiber A B f b)
      (fiber_prop_of_injective A B setB f inj b)
      (fiber_to_book A B f b) (fiber_from_book A B f b)
      (t ↦ (refl (t .fst), inverse_inverse B b (f (t .fst)) (t .snd)))

def boolean_set_point : Unit → SetTypes ≔ _ ↦ boolean_set

{` The set-level swap with first component exactly bool_swap. `}
def boolean_set_swap_pair : Id SetTypes boolean_set boolean_set
  ≔ (bool_swap, pathover_of_eq Type isSet Bool Bool bool_swap bool_set bool_set
      (isset_isprop Bool (transport Type isSet Bool Bool bool_swap bool_set) bool_set))

{` The requested function from True to Set that is not injective. `}
def boolean_set_point_not_embedding (h : IsEmbedding Unit SetTypes boolean_set_point) : Empty
  ≔ let e ≔ native_equivalence (Id Unit star. star.) (Id SetTypes boolean_set boolean_set)
      (embedding_on_paths Unit SetTypes boolean_set_point h star. star.) in
    let loops_prop : isProp (Id SetTypes boolean_set boolean_set)
      ≔ retract_prop (Id Unit star. star.) (Id SetTypes boolean_set boolean_set)
          (unit_set star. star.) (e .map)
          (equiv_inverse_map (Id Unit star. star.) (Id SetTypes boolean_set boolean_set) e)
          (equiv_counit (Id Unit star. star.) (Id SetTypes boolean_set boolean_set) e) in
    bool_swap_nontrivial
      (refl ((l ↦ l .fst) : Id SetTypes boolean_set boolean_set → Id Type Bool Bool)
        (loops_prop boolean_set_swap_pair (refl boolean_set)))

{` xca:decidability, with yes read as true. `}
def bool_true_decidable (b : Bool) : Decidable (Id Bool b true.)
  ≔ match b [ true. ↦ inl. (refl (true. : Bool)) | false. ↦ inr. (bool_encode false. true.) ]

def bool_value_predicate (T : Type) (f : T → Bool) : DecidablePredicate T
  ≔ (t ↦ (Id Bool (f t) true., bool_set (f t) true.), t ↦ bool_true_decidable (f t))

def decidable_proposition_classification (P : Type) (hP : isProp P) (d : Decidable P)
  : Sum (Equiv P Unit) (Equiv P Empty)
  ≔ match d [
  | inl. p ↦ inl. (iff_equiv P Unit hP unit_prop (_ ↦ star.) (_ ↦ p))
  | inr. n ↦ inr. (iff_equiv P Empty hP empty_prop n (e ↦ match e [])) ]
