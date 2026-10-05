export "285-chapter-three-completions"

{` Claims made in the running text of chapter 2 (intro-uf.tex), outside the
   numbered environments, that had no declaration of their own.  Each group
   is preceded by the book line and a short quote of the claim. `}

{` intro-uf.tex:228, "(h ∘ g) ∘ f and h ∘ (g ∘ f) are the same by
   definition", and intro-uf.tex:236, "f ∘ id_X is the same by definition as
   a ↦ f(a), which ... is to be regarded as the same as f.  A similar
   computation applies to id_Y ∘ f".  Narya has eta for functions, so all
   three are checked by refl. `}
def compose_assoc_definitional (X Y Z W : Type) (f : X → Y) (g : Y → Z) (h : Z → W)
  : Id (X → W) (compose X Y W (compose Y Z W h g) f) (compose X Z W h (compose X Y Z g f))
  ≔ refl (compose X Z W h (compose X Y Z g f))

def compose_identity_right_definitional (X Y : Type) (f : X → Y)
  : Id (X → Y) (compose X X Y f (identity X)) f ≔ refl f

def compose_identity_left_definitional (X Y : Type) (f : X → Y)
  : Id (X → Y) (compose X Y Y (identity Y) f) f ≔ refl f

{` intro-uf.tex:397, "Alternatively (and equivalently) we may use iteration of
   functions to define addition and multiplication, by setting n+m ≔ Succ^m(n)
   and m·n ≔ (i ↦ i+n)^m(0)".  The book's n+m (by induction on m) is add n m;
   the book's m·n (by induction on m: 0·n ≔ 0, Succ(m)·n ≔ (m·n)+n) is
   mul n m.  Both agreements are inductions on m, written with nat_ind. `}
def add_iterate_suc (n m : Nat) : Id Nat (add n m) (iterate Nat (x ↦ suc. x) m n)
  ≔ nat_ind (k ↦ Id Nat (add n k) (iterate Nat (x ↦ suc. x) k n)) (refl n) (k ih ↦ suc. ih) m

def mul_iterate_add (m n : Nat) : Id Nat (mul n m) (iterate Nat (i ↦ add i n) m zero.)
  ≔ nat_ind (k ↦ Id Nat (mul n k) (iterate Nat (i ↦ add i n) k zero.)) (refl (zero. : Nat))
      (k ih ↦ refl ((i ↦ add i n) : Nat → Nat) ih) m

{` intro-uf.tex:470, "Consider the identity type fact(2) = 2 ... we see from
   rule E2 that refl_{Succ(Succ(0))} serves as an element of it"; and
   fact(3) ≡ 6 from the definition of fact (intro-uf.tex:400). `}
def factorial_two_refl : Id Nat (factorial (suc. (suc. zero.))) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)

def factorial_three_refl
  : Id Nat (factorial (suc. (suc. (suc. zero.))))
      (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ refl (suc. (suc. (suc. (suc. (suc. (suc. zero.))))) : Nat)

{` intro-uf.tex:821, footnote to def:ptw, "one could define ptw_{f,g}(p,x) ≔
   ap_{ev_x}(p).  The functions provided by these two definitions are not
   equal by definition, but they can be identified".  ptw is happly; in
   Narya the two definitions happen to agree definitionally. `}
def happly_evaluation_ap (X : Type) (Y : X → Type) (f g : (x : X) → Y x)
  (p : Id ((x : X) → Y x) f g) (x : X)
  : Id (Id (Y x) (f x) (g x)) (happly X Y f g p x)
      (map_path ((x : X) → Y x) (Y x) (h ↦ h x) f g p)
  ≔ refl (happly X Y f g p x)

{` intro-uf.tex:1187, "By path composition, one sees that any element x : X
   can serve as the center of a contraction of a contractible type X". `}
def book_contraction_at (X : Type) (h : BookIsContr X) (x : X) : BookIsContr X
  ≔ (x, a ↦ concat X x (h .center) a (inverse X (h .center) x (h .contract x)) (h .contract a))

{` intro-uf.tex:1333, footnote ft:Sigma-assoc, "we construct for any
   contractible type X and for any family of types Y(x) ... an equivalence
   between Σ_{x:X} Y(x) and Y(c), where c is the center of contraction".
   Since c = x is contractible, Y(x) ≃ (c = x) × Y(x); then contract away. `}
def contractible_base_sigma_equiv (X : Type) (Y : X → Type) (h : isContr X)
  : Equiv (Σ X Y) (Y (h .center))
  ≔ let c ≔ h .center in
    compose_equiv (Σ X Y) (Σ X (x ↦ Product (Id X c x) (Y x))) (Y c)
      (family_equiv X Y (x ↦ Product (Id X c x) (Y x))
        (x ↦ canonical_inverse_equiv (Product (Id X c x) (Y x)) (Y x)
          (compose_equiv (Product (Id X c x) (Y x)) (Product (Y x) (Id X c x)) (Y x)
            (product_swap_equiv (Id X c x) (Y x))
            (contractible_fiber_projection (Y x) (_ ↦ Id X c x)
              (_ ↦ prop_paths_contractible X (contractible_prop X h) c x)))))
      (contract_away_simple X c Y)

def book_contractible_base_sigma_equiv (X : Type) (Y : X → Type) (h : BookIsContr X)
  : Equiv (Σ X Y) (Y (h .center))
  ≔ contractible_base_sigma_equiv X Y (native_contraction X h)

{` intro-uf.tex:1695, "we let f × f′ denote the map of type (X × X′) →
   (Y × Y′) that sends (x,x′) to (f(x),f′(x′))".  The map of the auxiliary
   product_equiv is f × f′ by definition, and f × f′ is an equivalence when
   f and f′ are. `}
def product_map (X Y X' Y' : Type) (f : X → Y) (f' : X' → Y') : Product X X' → Product Y Y'
  ≔ u ↦ (f (u .fst), f' (u .snd))

def product_equiv_map (X Y X' Y' : Type) (e : Equiv X Y) (e' : Equiv X' Y')
  : Id (Product X X' → Product Y Y') (product_equiv X X' Y Y' e e' .map)
      (product_map X Y X' Y' (e .map) (e' .map))
  ≔ refl (product_map X Y X' Y' (e .map) (e' .map))

def product_map_book_equiv (X Y X' Y' : Type) (f : X → Y) (f' : X' → Y')
  (hf : BookIsEquiv X Y f) (hf' : BookIsEquiv X' Y' f')
  : BookIsEquiv (Product X X') (Product Y Y') (product_map X Y X' Y' f f')
  ≔ book_equivalence (Product X X') (Product Y Y')
      (product_equiv X X' Y Y' (native_equivalence X Y (f, hf)) (native_equivalence X' Y' (f', hf')))
      .equiv

{` intro-uf.tex:1806, "The definition of P(b) is motivated by the expectation
   that we will be able to construct an equivalence between P(b) and
   yes = b", with P(yes) ≔ 1, P(no) ≔ 0; this P is BoolCode true.
   intro-uf.tex:1815, the same for P(i) and 0 = i, with P(0) ≔ 1,
   P(Succ(m)) ≔ 0; this P is NatCode zero.  The general encode-decode
   equivalences also serve intro-uf.tex:3720 below. `}
def bool_encode_decode (a b : Bool) (c : BoolCode a b)
  : Id (BoolCode a b) (bool_encode a b (bool_decode a b c)) c
  ≔ bool_code_prop a b (bool_encode a b (bool_decode a b c)) c

def bool_path_equiv (a b : Bool) : Equiv (Id Bool a b) (BoolCode a b)
  ≔ quasi_inverse_equiv (Id Bool a b) (BoolCode a b) (bool_encode a b) (bool_decode a b)
      (bool_decode_encode a b) (bool_encode_decode a b)

def bool_true_path_code_equiv (b : Bool) : Equiv (Id Bool true. b) (BoolCode true. b)
  ≔ bool_path_equiv true. b

def nat_encode_decode (m n : Nat) (c : NatCode m n)
  : Id (NatCode m n) (nat_encode m n (nat_decode m n c)) c
  ≔ nat_code_prop m n (nat_encode m n (nat_decode m n c)) c

def nat_path_equiv (m n : Nat) : Equiv (Id Nat m n) (NatCode m n)
  ≔ quasi_inverse_equiv (Id Nat m n) (NatCode m n) (nat_encode m n) (nat_decode m n)
      (nat_decode_encode m n) (nat_encode_decode m n)

def nat_zero_path_code_equiv (i : Nat) : Equiv (Id Nat zero. i) (NatCode zero. i)
  ≔ nat_path_equiv zero. i

{` intro-uf.tex:3720, footnote to thm:isset-inductive-types, "A variation can
   be used to give a complete characterization of the identity types of
   inductive types".  Sums (sum_path_equiv), lists (list_path_equiv) and pairs
   were done before; Bool and ℕ are bool_path_equiv and nat_path_equiv
   above; the unit type and the unary sum Copy follow. `}
def unit_path_equiv (x y : Unit) : Equiv (Id Unit x y) Unit
  ≔ iff_equiv (Id Unit x y) Unit (unit_set x y) unit_prop (_ ↦ star.) (_ ↦ unit_prop x y)

def copy_path_equiv (A : Type) (a b : A) : Equiv (Id (Copy A) (copy. a) (copy. b)) (Id A a b)
  ≔ equivalence_on_paths (Copy A) A (copy_equiv A) (copy. a) (copy. b)

{` intro-uf.tex:1931, "Note that Copy(X) can alternatively be defined as
   Σ_{z:1} X". `}
def copy_unit_sigma_equiv (X : Type) : Equiv (Copy X) (Σ Unit (_ ↦ X))
  ≔ quasi_inverse_equiv (Copy X) (Σ Unit (_ ↦ X)) [ copy. x ↦ (star., x) ] (u ↦ copy. (u .snd))
      [ copy. x ↦ refl (copy. x : Copy X) ] (u ↦ (unit_prop star. (u .fst), refl (u .snd)))

{` intro-uf.tex:2037, "there are no general functions producing the head and
   tail of an arbitrary list, since the empty list has neither head nor
   tail.  However, we can use binary sums with 1 to define hd : X* → X ⨿ 1,
   tl : X* → X* ⨿ 1" (with the displayed computation rules, by definition). `}
def no_general_list_head (h : (X : Type) → List X → X) : Empty ≔ h Empty nil.

def nil_no_head_tail (X : Type) (u : Σ X (x ↦ Σ (List X) (t ↦ Id (List X) nil. (cons. x t))))
  : Empty
  ≔ list_encode X nil. (cons. (u .fst) (u .snd .fst)) (u .snd .snd)

def list_hd (X : Type) (l : List X) : Sum X Unit
  ≔ match l [ nil. ↦ inr. star. | cons. x _ ↦ inl. x ]

def list_tl (X : Type) (l : List X) : Sum (List X) Unit
  ≔ match l [ nil. ↦ inr. star. | cons. _ rest ↦ inl. rest ]

{` intro-uf.tex:2535, "1 ⨿ 1 has two distinct elements inl(triv) and
   inr(triv), and is therefore not a proposition"; the same for Bool. `}
def unit_sum_elements_distinct (p : Id (Sum Unit Unit) (inl. star.) (inr. star.)) : Empty
  ≔ sum_encode Unit Unit (inl. star.) (inr. star.) p

def unit_sum_not_prop (h : isProp (Sum Unit Unit)) : Empty
  ≔ unit_sum_elements_distinct (h (inl. star.) (inr. star.))

def bool_not_prop (h : isProp Bool) : Empty ≔ bool_encode false. true. (h false. true.)

{` intro-uf.tex:2537, "Σ_{n:ℕ} 1 has infinitely many distinct elements
   (n,triv) and is not a proposition": n ↦ (n,triv) reflects paths. `}
def nat_unit_sigma_injective : PathReflecting Nat (Σ Nat (_ ↦ Unit)) (n ↦ (n, star.))
  ≔ m n p ↦ p .fst

def nat_unit_sigma_not_prop (h : isProp (Σ Nat (_ ↦ Unit))) : Empty
  ≔ nat_zero_ne_suc zero. (h (zero., star.) (suc. zero., star.) .fst)

{` intro-uf.tex:2817, "Note that the empty type ∅ is not connected". `}
def empty_not_connected (T : TruncationSignature) (h : IsConnected T Empty) : Empty
  ≔ trunc_rec T Empty Empty empty_prop (identity Empty) (h .fst)

def native_empty_not_connected (h : Connected Empty) : Empty
  ≔ empty_not_connected native_truncation h

{` intro-uf.tex:2861, "Consider the function f : 1 → 2 that is constant 0 ...
   The latter fiber [at 1] is not contractible ... Hence f is not an
   equivalence.  Observe that both fibers are propositions", and
   intro-uf.tex:2872, "As a function between sets f is an injection
   (one-to-one), but not a surjection".  The elements 0 and 1 of
   Fin 2 = Fin 1 ⨿ 1 are inl(0) and inr(triv) (def:finiteset). `}
def fin_two_zero : Fin (suc. (suc. zero.)) ≔ inl. (inr. star.)

def fin_two_one : Fin (suc. (suc. zero.)) ≔ inr. star.

def fin_one_prop : isProp (Fin (suc. zero.))
  ≔ retract_prop Unit (Fin (suc. zero.)) unit_prop (u ↦ inr. u) (fin_one_equiv .map)
      [ inl. e ↦ match e [] | inr. u ↦ refl (inr. u : Fin (suc. zero.)) ]

def fin_one_to_two_zero : Fin (suc. zero.) → Fin (suc. (suc. zero.))
  ≔ constant (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_two_zero

def fin_one_to_two_zero_fiber_one_empty
  (u : BookFiber (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_one_to_two_zero fin_two_one)
  : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit (inr. star.) (inl. (inr. star.)) (u .snd)

def fin_one_to_two_zero_not_equiv
  (h : BookIsEquiv (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_one_to_two_zero) : Empty
  ≔ fin_one_to_two_zero_fiber_one_empty (h fin_two_one .center)

def fin_one_to_two_zero_embedding
  : IsEmbedding (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_one_to_two_zero
  ≔ b ↦ sigma_prop (Fin (suc. zero.)) (x ↦ Id (Fin (suc. (suc. zero.))) b (fin_one_to_two_zero x))
      fin_one_prop (x ↦ fin_set (suc. (suc. zero.)) b (fin_one_to_two_zero x))

def fin_one_to_two_zero_not_surjective
  (h : Surjective (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_one_to_two_zero) : Empty
  ≔ mere_rec (BookFiber (Fin (suc. zero.)) (Fin (suc. (suc. zero.))) fin_one_to_two_zero fin_two_one)
      Empty empty_prop fin_one_to_two_zero_fiber_one_empty (h fin_two_one)

{` intro-uf.tex:2920, footnote to lem:inj+surj, "This argument applies
   generally: Any non-empty proposition is contractible". `}
def nonempty_prop_contractible (T : TruncationSignature) (P : Type) (hP : isProp P)
  (n : IsNonEmpty T P) : BookIsContr P
  ≔ let c : P ≔ trunc_rec T P P hP (identity P) n in (c, x ↦ hP c x)

def native_nonempty_prop_contractible (P : Type) (hP : isProp P) (n : NonEmpty P) : BookIsContr P
  ≔ nonempty_prop_contractible native_truncation P hP n

{` intro-uf.tex:3299, "we can define χ_P : T → Bool by ... case distinction on
   d(t) : P(t) ⨿ ¬P(t) ... In this way, decidable predicates on a type T
   correspond to their characteristic functions T → Bool": the map P ↦ χ_P
   is an equivalence, with inverse f ↦ (t ↦ (f(t) = yes)) of intro-uf.tex:3292
   (bool_value_predicate). `}
def characteristic_function (T : Type) (P : DecidablePredicate T) : T → Bool
  ≔ t ↦ decision_bool (P .fst t .fst) (P .snd t)

def characteristic_function_section (T : Type) (f : T → Bool)
  : Id (T → Bool) (characteristic_function T (bool_value_predicate T f)) f
  ≔ funext T (_ ↦ Bool) (characteristic_function T (bool_value_predicate T f)) f
      (t ↦ decision_bool_value (f t) (bool_true_decidable (f t)))

def characteristic_function_retraction (T : Type) (P : DecidablePredicate T)
  : Id (DecidablePredicate T) (bool_value_predicate T (characteristic_function T P)) P
  ≔ let Q ≔ bool_value_predicate T (characteristic_function T P) in
    equiv_inverse_map (Id (DecidablePredicate T) Q P) (Id (Subtypes T) (Q .fst) (P .fst))
      (subtype_path_equiv (Subtypes T) (R ↦ (t : T) → Decidable (R t .fst))
        (R ↦ pi_prop T (t ↦ Decidable (R t .fst)) (t ↦ decidability_prop (R t .fst) (R t .snd)))
        Q P)
      (inclusion_antisym T (Q .fst) (P .fst)
        (t e ↦ decision_bool_reflect (P .fst t .fst) (P .snd t) e)
        (t p ↦ decision_bool_true (P .fst t .fst) (P .snd t) p))

def characteristic_function_book_equiv (T : Type)
  : BookIsEquiv (DecidablePredicate T) (T → Bool) (characteristic_function T)
  ≔ book_quasi_inverse_equiv (DecidablePredicate T) (T → Bool) (characteristic_function T)
      (bool_value_predicate T) (characteristic_function_retraction T) (characteristic_function_section T)
      .equiv

def decidable_predicates_bool_equiv (T : Type) : Equiv (DecidablePredicate T) (T → Bool)
  ≔ quasi_inverse_equiv (DecidablePredicate T) (T → Bool) (characteristic_function T)
      (bool_value_predicate T) (characteristic_function_retraction T) (characteristic_function_section T)

{` intro-uf.tex:3292, "we can form the predicate P(t) ≔ (f(t) = yes) ...
   However, not every predicate can be given through a f : T → Bool, since
   Prop and Bool are only equivalent if LEM holds".  A predicate P is given
   through f if P = (t ↦ (f(t) = yes)) in T → Prop.  This happens for some f
   (necessarily unique) exactly when P is decidable, and every predicate on
   every type is so given exactly when LEM holds. `}
def bool_predicate_map (T : Type) (f : T → Bool) : Subtypes T ≔ bool_value_predicate T f .fst

def bool_true_iff_path (a b : Bool) (u : Id Bool a true. → Id Bool b true.)
  (v : Id Bool b true. → Id Bool a true.) : Id Bool a b
  ≔ match a, b [
  | true., true. ↦ refl (true. : Bool)
  | false., false. ↦ refl (false. : Bool)
  | true., false. ↦ absurd (Id Bool true. false.) (bool_encode false. true. (u (refl (true. : Bool))))
  | false., true. ↦ absurd (Id Bool false. true.) (bool_encode false. true. (v (refl (true. : Bool)))) ]

def bool_predicate_map_injective (T : Type) : PathReflecting (T → Bool) (Subtypes T) (bool_predicate_map T)
  ≔ f g p ↦ funext T (_ ↦ Bool) f g (t ↦
      let q ≔ p (refl t) .fst in
      bool_true_iff_path (f t) (g t) (x ↦ q .trr x) (y ↦ q .trl y))

def BooleanPredicate (T : Type) (P : Subtypes T) : Type
  ≔ BookFiber (T → Bool) (Subtypes T) (bool_predicate_map T) P

def boolean_predicate_prop (T : Type) (P : Subtypes T) : isProp (BooleanPredicate T P)
  ≔ path_reflecting_set_embedding (T → Bool) (Subtypes T) (subtypes_set T) (bool_predicate_map T)
      (bool_predicate_map_injective T) P

def boolean_predicate_decidable (T : Type) (P : Subtypes T) (b : BooleanPredicate T P) (t : T)
  : Decidable (P t .fst)
  ≔ let q ≔ b .snd (refl t) .fst in
    decidable_iff (Id Bool (b .fst t) true.) (P t .fst) (bool_true_decidable (b .fst t))
      (y ↦ q .trl y) (x ↦ q .trr x)

def boolean_predicate_of_decidable (T : Type) (P : Subtypes T) (d : (t : T) → Decidable (P t .fst))
  : BooleanPredicate T P
  ≔ (characteristic_function T (P, d),
     inclusion_antisym T P (bool_predicate_map T (characteristic_function T (P, d)))
       (t p ↦ decision_bool_true (P t .fst) (d t) p)
       (t e ↦ decision_bool_reflect (P t .fst) (d t) e))

def boolean_predicate_decidable_equiv (T : Type) (P : Subtypes T)
  : Equiv (BooleanPredicate T P) ((t : T) → Decidable (P t .fst))
  ≔ iff_equiv (BooleanPredicate T P) ((t : T) → Decidable (P t .fst))
      (boolean_predicate_prop T P)
      (pi_prop T (t ↦ Decidable (P t .fst)) (t ↦ decidability_prop (P t .fst) (P t .snd)))
      (boolean_predicate_decidable T P) (boolean_predicate_of_decidable T P)

def AllPredicatesBoolean : Type ≔ (T : Type) (P : Subtypes T) → BooleanPredicate T P

def all_predicates_boolean_excluded_middle (h : AllPredicatesBoolean) : ExcludedMiddle
  ≔ P hP ↦ boolean_predicate_decidable Unit (_ ↦ (P, hP)) (h Unit (_ ↦ (P, hP))) star.

def excluded_middle_all_predicates_boolean (lem : ExcludedMiddle) : AllPredicatesBoolean
  ≔ T P ↦ boolean_predicate_of_decidable T P (t ↦ lem (P t .fst) (P t .snd))

def all_predicates_boolean_excluded_middle_equiv : Equiv AllPredicatesBoolean ExcludedMiddle
  ≔ iff_equiv AllPredicatesBoolean ExcludedMiddle
      (pi_prop Type (T ↦ (P : Subtypes T) → BooleanPredicate T P)
        (T ↦ pi_prop (Subtypes T) (P ↦ BooleanPredicate T P) (P ↦ boolean_predicate_prop T P)))
      excluded_middle_prop all_predicates_boolean_excluded_middle excluded_middle_all_predicates_boolean

{` intro-uf.tex:3389, footnote ft:caution-subtype, "The identity types
   P =_{Sub(T)} Q and T_P =_U T_Q are in general not equivalent!".
   Counterexample: T = Bool, P = (– = true), Q = (– = false).  Both T_P and
   T_Q are contractible, hence identified, but P ≠ Q. `}
def bool_true_subtype : Subtypes Bool ≔ t ↦ (Id Bool t true., bool_set t true.)

def bool_false_subtype : Subtypes Bool ≔ t ↦ (Id Bool t false., bool_set t false.)

def bool_true_false_subtypes_distinct
  (p : Id (Subtypes Bool) bool_true_subtype bool_false_subtype) : Empty
  ≔ bool_encode true. false. (p (refl (true. : Bool)) .fst .trr (refl (true. : Bool)))

def bool_true_false_carriers_path
  : Id Type (SubtypeCarrier Bool bool_true_subtype) (SubtypeCarrier Bool bool_false_subtype)
  ≔ ua (SubtypeCarrier Bool bool_true_subtype) (SubtypeCarrier Bool bool_false_subtype)
      (compose_equiv (SubtypeCarrier Bool bool_true_subtype) Unit (SubtypeCarrier Bool bool_false_subtype)
        (contractible_unit_equiv (SubtypeCarrier Bool bool_true_subtype) (path_to_contractible Bool true.))
        (canonical_inverse_equiv (SubtypeCarrier Bool bool_false_subtype) Unit
          (contractible_unit_equiv (SubtypeCarrier Bool bool_false_subtype)
            (path_to_contractible Bool false.))))

def bool_subtype_paths_not_carrier_paths
  (e : Equiv (Id (Subtypes Bool) bool_true_subtype bool_false_subtype)
    (Id Type (SubtypeCarrier Bool bool_true_subtype) (SubtypeCarrier Bool bool_false_subtype)))
  : Empty
  ≔ bool_true_false_subtypes_distinct
      (equiv_inverse_map (Id (Subtypes Bool) bool_true_subtype bool_false_subtype)
        (Id Type (SubtypeCarrier Bool bool_true_subtype) (SubtypeCarrier Bool bool_false_subtype))
        e bool_true_false_carriers_path)

def SubtypePathsCarrierPaths : Type
  ≔ (T : Type) (P Q : Subtypes T)
    → Equiv (Id (Subtypes T) P Q) (Id Type (SubtypeCarrier T P) (SubtypeCarrier T Q))

def subtype_paths_not_carrier_paths (h : SubtypePathsCarrierPaths) : Empty
  ≔ bool_subtype_paths_not_carrier_paths (h Bool bool_true_subtype bool_false_subtype)

{` intro-uf.tex:3463, footnote ft:incl-vs-inj, "the identity type of Inj^U(T)
   identifies precisely the triples defining the same subset": paths of
   triples (S,i,p) are paths of their fiber predicates t ↦ i⁻¹(t), and
   pointwise equivalences of the fibers. `}
def injections_path_equiv (T : Type) (u v : InjectionsInto T)
  : Equiv (Id (InjectionsInto T) u v)
      (Id (Subtypes T) (injection_fiber_predicate T u) (injection_fiber_predicate T v))
  ≔ equivalence_on_paths (InjectionsInto T) (Subtypes T) (injection_fiber_predicate_equiv T) u v

def injections_path_fiberwise_equiv (T : Type) (u v : InjectionsInto T)
  : Equiv (Id (InjectionsInto T) u v)
      ((t : T) → Equiv (BookFiber (u .fst) T (u .snd .fst) t) (BookFiber (v .fst) T (v .snd .fst) t))
  ≔ let P ≔ injection_fiber_predicate T u in
    let Q ≔ injection_fiber_predicate T v in
    iff_equiv (Id (InjectionsInto T) u v) ((t : T) → Equiv (P t .fst) (Q t .fst))
      (injections_into_set T u v)
      (pi_prop T (t ↦ Equiv (P t .fst) (Q t .fst)) (t ↦ equivalences_prop (P t .fst) (Q t .fst) (Q t .snd)))
      (p t ↦ proposition_paths_equiv (P t) (Q t) .map (refl (injection_fiber_predicate T) p (refl t)))
      (h ↦ equiv_inverse_map (Id (InjectionsInto T) u v) (Id (Subtypes T) P Q) (injections_path_equiv T u v)
        (funext T (_ ↦ PropTypes) P Q (t ↦
          equiv_inverse_map (Id PropTypes (P t) (Q t)) (Equiv (P t .fst) (Q t .fst))
            (proposition_paths_equiv (P t) (Q t)) (h t))))

{` intro-uf.tex:3827, footnote on higher truncations, "Sometimes it is
   convenient to consider contractible types as −2-types, with constant
   truncation operator ‖T‖_{−2} ≔ 1 and constructor |t|_{−2} ≔ triv",
   satisfying the universal property: this is MinusTwoTrunc and
   minus_two_trunc_unit of module 285; maps from ‖T‖_{−2} into a (−2)-type
   are maps from T. `}
def minus_two_trunc_definition (T : Type) : Id Type (MinusTwoTrunc T) Unit ≔ refl Unit

def minus_two_trunc_unit_definition (T : Type) (t : T)
  : Id Unit (minus_two_trunc_unit T t) star. ≔ refl (star. : Unit)

def minus_two_trunc_level (T : Type) : HLevel zero. (MinusTwoTrunc T) ≔ unit_contractible

def minus_two_trunc_universal_property (T S : Type) (hS : HLevel zero. S)
  : BookIsEquiv (MinusTwoTrunc T → S) (T → S)
      (g ↦ compose T (MinusTwoTrunc T) S g (minus_two_trunc_unit T))
  ≔ b ↦ contractible_map_book_fiber (MinusTwoTrunc T → S) (T → S)
      (g ↦ compose T (MinusTwoTrunc T) S g (minus_two_trunc_unit T))
      (book_contraction (MinusTwoTrunc T → S) (pi_contractible (MinusTwoTrunc T) (_ ↦ S) (_ ↦ hS)))
      (book_contraction (T → S) (pi_contractible T (_ ↦ S) (_ ↦ hS))) b

{` intro-uf.tex:4902, footnote to the (−1)-image, "Since the unit type 1 is
   the unique (−2)-type, we have ‖X‖_{−2} = 1 for any type X": every
   (−2)-type is identified with 1, the type of (−2)-types is contractible,
   and ‖X‖_{−2} ≃ 1. `}
def minus_two_type_unit_path (X : Type) (h : HLevel zero. X) : Id Type X Unit
  ≔ ua X Unit (contractible_unit_equiv X h)

def minus_two_types_contractible : isContr (Σ Type isContr)
  ≔ ((Unit, unit_contractible), u ↦
      equiv_inverse_map (Id (Σ Type isContr) u (Unit, unit_contractible)) (Id Type (u .fst) Unit)
        (subtype_path_equiv Type isContr iscontr_isprop u (Unit, unit_contractible))
        (minus_two_type_unit_path (u .fst) (u .snd)))

def minus_two_trunc_unit_equiv (X : Type) : Equiv (MinusTwoTrunc X) Unit ≔ identity_equiv Unit

{` intro-uf.tex:3865, "a constant map, which can be identified with one of the
   form x ↦ b for some b : B.  Any constant map is indeed weakly constant". `}
def constant_weakly_constant (A B : Type) (b : B) : WeaklyConstant A B (constant A B b)
  ≔ x y ↦ refl b

def identified_constant_weakly_constant (A B : Type) (f : A → B) (b : B)
  (p : Id (A → B) f (constant A B b)) : WeaklyConstant A B f
  ≔ x y ↦ concat B (f x) b (f y) (p (refl x)) (inverse B (f y) b (p (refl y)))

{` intro-uf.tex:3919, "(Succ(w),Succ(d)) ... determines the same net worth as
   (w,d), and (Succ(w),Succ(d)) ≠ (w,d)".  Same net worth: Succ(w) + d =
   w + Succ(d). `}
def nat_ne_suc (n : Nat) (p : Id Nat n (suc. n)) : Empty
  ≔ lt_not_equal n (suc. n) (le_refl (suc. n)) p

def net_worth_same (w d : Nat) : Id Nat (add (suc. w) d) (add w (suc. d)) ≔ add_suc_left w d

def net_worth_pairs_distinct (w d : Nat) (p : Id (Product Nat Nat) (suc. w, suc. d) (w, d)) : Empty
  ≔ nat_ne_suc w (inverse Nat (suc. w) w (p .fst))

{` intro-uf.tex:4142, footnote to xca:map-induces-quotient, "If f is
   injective, then ap_f is an equivalence by lem:inj-ap, so that A/≃_f is
   essentially given by rem:set-trunc-as-quotient": for an injection f the
   relation ‖f(a) = f(a′)‖ is ‖a = a′‖, so A/≃_f is the set truncation. `}
def embedding_induced_relation_mere_paths (A B : Type) (f : A → B) (h : IsEmbedding A B f)
  : Id (A → A → PropTypes) (induced_relation A B f .predicate) (mere_path_relation A .predicate)
  ≔ funext A (_ ↦ A → PropTypes) (induced_relation A B f .predicate) (mere_path_relation A .predicate)
      (x ↦ funext A (_ ↦ PropTypes) (induced_relation A B f .predicate x) (mere_path_relation A .predicate x)
        (y ↦ proposition_extensionality (induced_relation A B f .predicate x y)
          (mere_path_relation A .predicate x y)
          (trunc_map native_truncation (Id B (f x) (f y)) (Id A x y) (embedding_reflects_paths A B f h x y))
          (trunc_map native_truncation (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))))

def embedding_induced_quotient_set_trunc (A B : Type) (f : A → B) (h : IsEmbedding A B f)
  : Id Type (InducedQuotient A B f) (SetTrunc A)
  ≔ refl ((R : A → A → PropTypes) ↦ Image A (A → PropTypes) R) (embedding_induced_relation_mere_paths A B f h)

{` intro-uf.tex:4445, "several examples of 2-element sets: Bool, 2, 1 ⨿ 1 that
   can easily be identified": 1 ⨿ 1 ≃ 2 ≃ Bool (fin_two_equiv). `}
def fin_one_sum_bool_equiv : Equiv (Sum (Fin (suc. zero.)) (Fin (suc. zero.))) Bool
  ≔ compose_equiv (Sum (Fin (suc. zero.)) (Fin (suc. zero.))) (Fin (suc. (suc. zero.))) Bool
      (sum_equiv (Fin (suc. zero.)) (Fin (suc. zero.)) (Fin (suc. zero.)) Unit
        (identity_equiv (Fin (suc. zero.))) fin_one_equiv)
      fin_two_equiv

{` intro-uf.tex:4485, footnote to cor:lists-truncated, "We need n ≥ 0, since
   for a contractible (−2-type) X we get an equivalence X* ≃ ℕ ... and ℕ is
   not contractible". `}
def nat_not_contractible (h : isContr Nat) : Empty
  ≔ nat_zero_ne_suc zero. (contractible_prop Nat h zero. (suc. zero.))

def list_of_contractible_not_contractible (X : Type) (hX : isContr X) (h : isContr (List X)) : Empty
  ≔ nat_not_contractible
      (contractible_retract (List X) Nat h (length X) (repeat X (hX .center)) (length_repeat X (hX .center)))
