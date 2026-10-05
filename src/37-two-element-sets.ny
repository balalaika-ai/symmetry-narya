export "36-cardinality-arithmetic"

def two : Nat ≔ suc. (suc. zero.)
def TwoElement (A : Type) : Type ≔ Mere (Id Type (Fin two) A)
def two_element_prop (A : Type) : isProp (TwoElement A) ≔ mere_isprop (Id Type (Fin two) A)
def fin_two_path : Id Type (Fin two) Bool ≔ ua (Fin two) Bool fin_two_equiv
def bool_two_element : TwoElement Bool ≔ mere (Id Type (Fin two) Bool) fin_two_path

def two_as_bool (A : Type) (h : TwoElement A) : Mere (Id Type Bool A)
  ≔ trunc_map native_truncation (Id Type (Fin two) A) (Id Type Bool A)
      (p ↦ concat Type Bool (Fin two) A (inverse Type (Fin two) Bool fin_two_path) p) h

def two_element_ind_prop (P : Type → Type) (hp : (A : Type) → isProp (P A))
  (base : P Bool) (A : Type) (h : TwoElement A) : P A
  ≔ mere_rec (Id Type Bool A) (P A) (hp A) (p ↦ transport Type P Bool A p base) (two_as_bool A h)

def two_element_finite (A : Type) (h : TwoElement A) : IsFinite A
  ≔ mere_rec (Id Type (Fin two) A) (IsFinite A) (isfinite_prop A)
      (p ↦ mere (Σ Nat (n ↦ Id Type A (Fin n))) (two, inverse Type (Fin two) A p)) h

def two_element_set (A : Type) (h : TwoElement A) : isSet A
  ≔ two_element_ind_prop isSet isset_isprop bool_set A h

{` The evaluation map is canonical. Only its proposition-valued equivalence
   proof is obtained by eliminating the mere identification with Bool. `}
def two_evaluate (A : Type) (e : Equiv Bool A) : A ≔ e .map false.

def TwoEvaluation (A : Type) : Type ≔ isEquiv (Equiv Bool A) A (two_evaluate A)

def two_evaluation_equiv (A : Type) (h : TwoElement A) : Equiv (Equiv Bool A) A
  ≔ (two_evaluate A,
      two_element_ind_prop TwoEvaluation
        (X ↦ isequiv_isprop (Equiv Bool X) X (two_evaluate X))
        (bool_automorphisms_equiv .equiv) A h)

def two_pointed_enumeration (A : Type) (h : TwoElement A) (a : A) : Equiv Bool A
  ≔ equiv_inverse_map (Equiv Bool A) A (two_evaluation_equiv A h) a

def two_pointed_enumeration_beta (A : Type) (h : TwoElement A) (a : A)
  : Id A (two_pointed_enumeration A h a .map false.) a
  ≔ equiv_counit (Equiv Bool A) A (two_evaluation_equiv A h) a

def two_paths_evaluation (A : Type) (h : TwoElement A) : Equiv (Id Type Bool A) A
  ≔ compose_equiv (Id Type Bool A) (Equiv Bool A) A
      (univalence_equiv Bool A) (two_evaluation_equiv A h)

{` xca:2-element-sets, first clause: the loop type is itself two-element. `}
def bool_loops_two_element : TwoElement (Id Type Bool Bool)
  ≔ mere (Id Type (Fin two) (Id Type Bool Bool))
      (concat Type (Fin two) Bool (Id Type Bool Bool) fin_two_path
        (inverse Type (Id Type Bool Bool) Bool (ua (Id Type Bool Bool) Bool bool_loops_equiv)))

def two_loops_two_element (A : Type) (h : TwoElement A) : TwoElement (Id Type A A)
  ≔ two_element_ind_prop (X ↦ TwoElement (Id Type X X))
      (X ↦ two_element_prop (Id Type X X)) bool_loops_two_element A h

{` Third clause: the identity loop supplies the point needed for a canonical enumeration. `}
def two_loops_enumeration (A : Type) (h : TwoElement A) : Equiv (Id Type A A) (Fin two)
  ≔ compose_equiv (Id Type A A) Bool (Fin two)
      (canonical_inverse_equiv Bool (Id Type A A)
        (two_pointed_enumeration (Id Type A A) (two_loops_two_element A h) (refl A)))
      (canonical_inverse_equiv (Fin two) Bool fin_two_equiv)

def two_loops_identification (A : Type) (h : TwoElement A) : Id Type (Id Type A A) (Fin two)
  ≔ ua (Id Type A A) (Fin two) (two_loops_enumeration A h)

{` Last clause: a point of A is equivalent to an actual identification Fin 2 = A. `}
def two_points_paths_equiv (A : Type) (h : TwoElement A) : Equiv A (Id Type (Fin two) A)
  ≔ compose_equiv A (Id Type Bool A) (Id Type (Fin two) A)
      (canonical_inverse_equiv (Id Type Bool A) A (two_paths_evaluation A h))
      (id_to_equiv (Id Type Bool A) (Id Type (Fin two) A)
        (map_path Type Type (X ↦ Id Type X A) Bool (Fin two)
          (inverse Type (Fin two) Bool fin_two_path)))

def two_points_paths_identification (A : Type) (h : TwoElement A) : Id Type A (Id Type (Fin two) A)
  ≔ ua A (Id Type (Fin two) A) (two_points_paths_equiv A h)

def TwoSets : Type ≔ FiniteSetsAt two
def two_sets_carrier (S : TwoSets) : Type ≔ S .fst .fst
def bool_two_set : TwoSets ≔ ((Bool, bool_set), bool_two_element)

def bool_set_swap : Id SetTypes (Bool, bool_set) (Bool, bool_set)
  ≔ (bool_swap, pathover_of_eq Type isSet Bool Bool bool_swap bool_set bool_set
      (isset_isprop Bool (transport Type isSet Bool Bool bool_swap bool_set) bool_set))

def bool_two_set_swap : Id TwoSets bool_two_set bool_two_set
  ≔ (bool_set_swap,
      pathover_of_eq SetTypes (S ↦ TwoElement (S .fst)) (Bool, bool_set) (Bool, bool_set)
        bool_set_swap bool_two_element bool_two_element
        (two_element_prop Bool
          (transport SetTypes (S ↦ TwoElement (S .fst)) (Bool, bool_set) (Bool, bool_set)
            bool_set_swap bool_two_element) bool_two_element))

def bool_not_no_fixed_point (b : Bool) : Id Bool (bool_not b) b → Empty
  ≔ match b [ false. ↦ bool_encode true. false. | true. ↦ bool_encode false. true. ]

{` A global point would be fixed by the swap loop of the bundled Boolean set. `}
def two_sets_no_global_point (s : (S : TwoSets) → two_sets_carrier S) : Empty
  ≔ bool_not_no_fixed_point (s bool_two_set)
      (pathover_transport_equiv TwoSets two_sets_carrier bool_two_set bool_two_set bool_two_set_swap
        (s bool_two_set) (s bool_two_set) .map (refl s bool_two_set_swap))

{` Second clause, with exactly the book's domain of bundled two-element sets. `}
def two_sets_no_global_identification
  (h : (S : TwoSets) → Id Type (two_sets_carrier S) (Fin two)) : Empty
  ≔ two_sets_no_global_point
      (S ↦ equiv_inverse_map (two_sets_carrier S) (Fin two)
        (id_to_equiv (two_sets_carrier S) (Fin two) (h S)) (inr. star.))

def two_sets_loops_identification (S : TwoSets)
  : Id Type (Id Type (two_sets_carrier S) (two_sets_carrier S)) (Fin two)
  ≔ two_loops_identification (two_sets_carrier S) (S .snd)

def two_sets_points_paths_identification (S : TwoSets)
  : Id Type (two_sets_carrier S) (Id Type (Fin two) (two_sets_carrier S))
  ≔ two_points_paths_identification (two_sets_carrier S) (S .snd)
