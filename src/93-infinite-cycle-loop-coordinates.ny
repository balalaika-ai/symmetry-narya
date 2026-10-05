export "92-infinite-cycle-components"

{` lem:conn-eq-f-ap-f-x, both directions as an equivalence of propositions. `}
def connected_equivalence_loop_criterion (T : TruncationSignature) (A B : Type) (f : A → B)
  (connected_A : IsConnected T A) (connected_B : IsConnected T B) (a : A)
  : BookEquiv (BookIsEquiv A B f)
      (BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
  ≔ book_equivalence (BookIsEquiv A B f)
      (BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
      (iff_equiv (BookIsEquiv A B f)
        (BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
        (book_isequiv_isprop A B f)
        (book_isequiv_isprop (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
        (h ↦ book_equivalence (Id A a a) (Id B (f a) (f a))
          (equivalence_on_paths A B (native_equivalence A B (f, h)) a a) .equiv)
        (h ↦ connected_map_equiv_from_loops T A B f connected_A connected_B a h .equiv))

def carrier_path_evaluate (A : Type) (F : A → Type) (a b : A) (p : Id A a b) (x : F a) : F b
  ≔ refl F p .trr x

def carrier_path_evaluate_concat (A : Type) (F : A → Type) (a b c : A)
  (p : Id A a b) (q : Id A b c) (x : F a)
  : Id (F c) (carrier_path_evaluate A F a c (concat A a b c p q) x)
      (carrier_path_evaluate A F b c q (carrier_path_evaluate A F a b p x))
  ≔ concat (F c) (carrier_path_evaluate A F a c (concat A a b c p q) x)
      (concat Type (F a) (F b) (F c) (refl F p) (refl F q) .trr x)
      (carrier_path_evaluate A F b c q (carrier_path_evaluate A F a b p x))
      (refl ((r ↦ r .trr x) : Id Type (F a) (F c) → F c) (map_path_concat A Type F a b c p q))
      (transport_concat Type (X ↦ X) (F a) (F b) (F c) (refl F p) (refl F q) x)

def cycle_integer_loop_translation (p : Id Cycles infinite_cycle infinite_cycle) (z : Int)
  : Id Int (cycle_path_evaluate infinite_cycle infinite_cycle p z)
      (int_add z (cycle_path_evaluate infinite_cycle infinite_cycle p int_zero))
  ≔ let f ≔ cycle_paths_equiv infinite_cycle infinite_cycle .map p .fst .map in
    calc
      f z = f (int_add int_zero z) by refl f (int_add_zero_left z)
      = int_add (f int_zero) z by permutation_power_intertwine Int Int int_succ_equiv int_succ_equiv f
          (cycle_paths_equiv infinite_cycle infinite_cycle .map p .snd) z int_zero
      = int_add z (f int_zero) by int_add_comm (f int_zero) z ∎

def integer_translation_across (A B : Type) (e : Equiv A B) (f : A → Int → Int) (g : B → Int → Int)
  (agreement : (a : A) (z : Int) → Id Int (f a z) (g (e .map a) z))
  (translation : (a : A) (z : Int) → Id Int (f a z) (int_add z (f a int_zero))) (p : B) (z : Int)
  : Id Int (g p z) (int_add z (g p int_zero))
  ≔ let q ≔ equiv_inverse_map A B e p in
    calc
      g p z = g (e .map q) z by refl ((r ↦ g r z) : B → Int) (equiv_counit A B e p)
      = f q z by agreement q z
      = int_add z (f q int_zero) by translation q z
      = int_add z (g (e .map q) int_zero) by refl (int_add z) (agreement q int_zero)
      = int_add z (g p int_zero) by refl ((r ↦ int_add z (g r int_zero)) : B → Int) (equiv_counit A B e p) ∎

def endomorphism_integer_loop_translation (p : Id Endomorphisms integer_endomorphism integer_endomorphism) (z : Int)
  : Id Int (endomorphism_path_evaluate integer_endomorphism integer_endomorphism p z)
      (int_add z (endomorphism_path_evaluate integer_endomorphism integer_endomorphism p int_zero))
  ≔ integer_translation_across (Id Cycles infinite_cycle infinite_cycle)
      (Id Endomorphisms integer_endomorphism integer_endomorphism)
      (cycle_endomorphism_paths infinite_cycle infinite_cycle)
      (cycle_path_evaluate infinite_cycle infinite_cycle)
      (endomorphism_path_evaluate integer_endomorphism integer_endomorphism)
      (p z ↦ refl (p .fst .fst .fst .trr z)) cycle_integer_loop_translation p z

def infinite_cycle_loop_coordinate (p : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) : Int
  ≔ endomorphism_path_evaluate integer_endomorphism integer_endomorphism (p .fst) int_zero

def infinite_cycle_loop_coordinate_equiv
  : Equiv (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) Int
  ≔ compose_equiv (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (Id Endomorphisms integer_endomorphism integer_endomorphism) Int
      (subtype_path_equiv Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
        (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
        infinite_endomorphism_point infinite_endomorphism_point)
      (native_equivalence (Id Endomorphisms integer_endomorphism integer_endomorphism) Int
        (infinite_endomorphism_evaluation infinite_endomorphism_point))

def infinite_cycle_loop_coordinate_refl
  : Id Int (infinite_cycle_loop_coordinate (refl infinite_endomorphism_point)) int_zero
  ≔ transport_refl Type (X ↦ X) Int int_zero

def infinite_cycle_loop_coordinate_composition
  (p q : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
  : Id Int (infinite_cycle_loop_coordinate
      (concat InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point infinite_endomorphism_point p q))
      (int_add (infinite_cycle_loop_coordinate p) (infinite_cycle_loop_coordinate q))
  ≔ concat Int (infinite_cycle_loop_coordinate
      (concat InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point infinite_endomorphism_point p q))
      (endomorphism_path_evaluate integer_endomorphism integer_endomorphism (q .fst)
        (infinite_cycle_loop_coordinate p))
      (int_add (infinite_cycle_loop_coordinate p) (infinite_cycle_loop_coordinate q))
      (carrier_path_evaluate_concat InfiniteCycles (t ↦ t .fst .fst)
        infinite_endomorphism_point infinite_endomorphism_point infinite_endomorphism_point p q int_zero)
      (endomorphism_integer_loop_translation (q .fst) (infinite_cycle_loop_coordinate p))

def int_neg_additive (x y : Int) : Id Int (int_neg (int_add x y)) (int_add (int_neg x) (int_neg y))
  ≔ inverse Int (int_add (int_neg x) (int_neg y)) (int_neg (int_add x y))
      (int_neg_unique (int_add x y) (int_add (int_neg x) (int_neg y)) (calc
        int_add (int_add x y) (int_add (int_neg x) (int_neg y))
        = int_add x (int_add y (int_add (int_neg x) (int_neg y)))
          by int_add_assoc x y (int_add (int_neg x) (int_neg y))
        = int_add x (int_add (int_add y (int_neg x)) (int_neg y))
          by refl (int_add x) (int_add_assoc y (int_neg x) (int_neg y))
        = int_add x (int_add (int_add (int_neg x) y) (int_neg y))
          by refl ((z ↦ int_add x (int_add z (int_neg y))) : Int → Int) (int_add_comm y (int_neg x))
        = int_add x (int_add (int_neg x) (int_add y (int_neg y)))
          by refl (int_add x) (int_add_assoc (int_neg x) y (int_neg y))
        = int_add x (int_neg x) by refl ((z ↦ int_add x (int_add (int_neg x) z)) : Int → Int) (int_add_neg_right y)
        = int_zero by int_add_neg_right x ∎))
