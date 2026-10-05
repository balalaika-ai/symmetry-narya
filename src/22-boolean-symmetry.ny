export "21-subtypes"

def equivalence_injective (A B : Type) (e : Equiv A B) (x y : A)
  (p : Id B (e .map x) (e .map y)) : Id A x y
  ≔ concat A x (equiv_inverse_map A B e (e .map x)) y (equiv_unit A B e x)
      (concat A (equiv_inverse_map A B e (e .map x)) (equiv_inverse_map A B e (e .map y)) y
        (refl (equiv_inverse_map A B e) p) (equiv_retraction A B e y))

def bool_not_equiv : Equiv Bool Bool
  ≔ quasi_inverse_equiv Bool Bool bool_not bool_not bool_not_involutive bool_not_involutive

def bool_automorphism : Bool → Equiv Bool Bool
  ≔ [ false. ↦ identity_equiv Bool | true. ↦ bool_not_equiv ]

def bool_automorphism_false (b : Bool) : Id Bool (bool_automorphism b .map false.) b
  ≔ match b [ false. ↦ false. | true. ↦ true. ]

def bool_automorphism_true (b : Bool) : Id Bool (bool_automorphism b .map true.) (bool_not b)
  ≔ match b [ false. ↦ true. | true. ↦ false. ]

def bool_distinct_other (x y : Bool) (h : Id Bool x y → Empty) : Id Bool y (bool_not x)
  ≔ match x, y [
  | false., false. ↦ absurd (Id Bool false. true.) (h (refl false.))
  | false., true. ↦ true.
  | true., false. ↦ false.
  | true., true. ↦ absurd (Id Bool true. false.) (h (refl true.)) ]

def bool_equiv_other (e : Equiv Bool Bool)
  : Id Bool (e .map true.) (bool_not (e .map false.))
  ≔ bool_distinct_other (e .map false.) (e .map true.)
      (p ↦ bool_encode false. true. (equivalence_injective Bool Bool e false. true. p))

def bool_automorphism_eta (e : Equiv Bool Bool)
  : Id (Equiv Bool Bool) (bool_automorphism (e .map false.)) e
  ≔ equiv_homotopy Bool Bool (bool_automorphism (e .map false.)) e
      [ false. ↦ bool_automorphism_false (e .map false.)
      | true. ↦ concat Bool (bool_automorphism (e .map false.) .map true.)
          (bool_not (e .map false.)) (e .map true.) (bool_automorphism_true (e .map false.))
          (inverse Bool (e .map true.) (bool_not (e .map false.)) (bool_equiv_other e)) ]

def bool_automorphisms_equiv : Equiv (Equiv Bool Bool) Bool
  ≔ quasi_inverse_equiv (Equiv Bool Bool) Bool (e ↦ e .map false.) bool_automorphism
      bool_automorphism_eta bool_automorphism_false

{` xca:C2: the entire type of universe loops at Bool has two elements. `}
def bool_loops_equiv : Equiv (Id Type Bool Bool) Bool
  ≔ compose_equiv (Id Type Bool Bool) (Equiv Bool Bool) Bool
      (univalence_equiv Bool Bool) bool_automorphisms_equiv

def bool_swap : Id Type Bool Bool ≔ ua Bool Bool bool_not_equiv

def bool_loops_equiv_refl : Id Bool (bool_loops_equiv .map (refl Bool)) false.
  ≔ concat Bool (bool_loops_equiv .map (refl Bool))
      (transport Type (T ↦ T) Bool Bool (refl Bool) false.) false.
      (id_to_equiv_transport Bool Bool (refl Bool) false.)
      (transport_refl Type (T ↦ T) Bool false.)

def bool_loops_equiv_swap : Id Bool (bool_loops_equiv .map bool_swap) true.
  ≔ id_to_equiv_transport Bool Bool bool_swap false.

def bool_swap_squared : Id (Id Type Bool Bool) (concat Type Bool Bool Bool bool_swap bool_swap) (refl Bool)
  ≔ calc
      concat Type Bool Bool Bool bool_swap bool_swap
      = ua Bool Bool (compose_equiv Bool Bool Bool bool_not_equiv bool_not_equiv)
        by ua_compose Bool Bool Bool bool_not_equiv bool_not_equiv
      = ua Bool Bool (identity_equiv Bool)
        by refl (ua Bool Bool)
          (equiv_homotopy Bool Bool (compose_equiv Bool Bool Bool bool_not_equiv bool_not_equiv)
            (identity_equiv Bool) bool_not_involutive)
      = refl Bool by ua_identity Bool ∎

def bool_loop_representative : Bool → Id Type Bool Bool
  ≔ [ false. ↦ refl Bool | true. ↦ bool_swap ]

def bool_ua_representative (b : Bool)
  : Id (Id Type Bool Bool) (ua Bool Bool (bool_automorphism b)) (bool_loop_representative b)
  ≔ match b [ false. ↦ ua_identity Bool | true. ↦ refl bool_swap ]

def bool_loop_classification (p : Id Type Bool Bool)
  : Id (Id Type Bool Bool) p (bool_loop_representative (bool_loops_equiv .map p))
  ≔ calc
      p
      = ua Bool Bool (id_to_equiv Bool Bool p) by ua_eta Bool Bool p
      = ua Bool Bool (bool_automorphism (id_to_equiv Bool Bool p .map false.))
        by refl (ua Bool Bool) (bool_automorphism_eta (id_to_equiv Bool Bool p))
      = bool_loop_representative (bool_loops_equiv .map p)
        by bool_ua_representative (bool_loops_equiv .map p) ∎

def bool_swap_nontrivial : Id (Id Type Bool Bool) bool_swap (refl Bool) → Empty
  ≔ p ↦ bool_encode true. false.
      (concat Bool true. (transport Type (T ↦ T) Bool Bool (refl Bool) false.) false.
        (refl ((q ↦ q .trr false.) : Id Type Bool Bool → Bool) p)
        (transport_refl Type (T ↦ T) Bool false.))
