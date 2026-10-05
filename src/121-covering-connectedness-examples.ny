export "120-two-boolean-circle-coverings"

def equivalence_covering (A B : Type) (e : Equiv A B) : IsCovering A B (e .map)
  ≔ b ↦ prop_is_set (BookFiber A B (e .map) b)
      (contractible_prop (BookFiber A B (e .map) b)
        (native_contraction (BookFiber A B (e .map) b) (book_equivalence A B e .equiv b)))

def connected_fiber_property_prop (A B : Type) (f : A → B) : isProp (ConnectedFibers A B f)
  ≔ pi_prop B (b ↦ Connected (BookFiber A B f b)) (b ↦ connected_isprop (BookFiber A B f b))

{` The alternative meaning 'all fibers are connected' is exactly an
   equivalence when f is a covering. It differs from connected total space. `}
def covering_connected_fibers_equiv (A B : Type) (f : A → B) (hf : IsCovering A B f)
  : Equiv (ConnectedFibers A B f) (BookIsEquiv A B f)
  ≔ iff_equiv (ConnectedFibers A B f) (BookIsEquiv A B f)
      (connected_fiber_property_prop A B f) (book_isequiv_isprop A B f)
      (h b ↦ native_connected_set_contractible (BookFiber A B f b) (h b) (hf b))
      (h b ↦ contractible_connected (BookFiber A B f b) (h b))

def boolean_not_contractible (h : BookIsContr Bool) : Empty
  ≔ bool_encode false. true. (contractible_prop Bool (native_contraction Bool h) false. true.)
def boolean_not_connected (h : Connected Bool) : Empty
  ≔ boolean_not_contractible (native_connected_set_contractible Bool h bool_set)
def boolean_identity_covering : IsCovering Bool Bool (identity Bool)
  ≔ equivalence_covering Bool Bool (identity_equiv Bool)

def swapping_boolean_cover (C : CircleSignature) : Coverings (C .carrier)
  ≔ let d ≔ setfamily_to_covering (C .carrier) (swapping_boolean_circle_family C) in
    (d .fst .fst, (d .fst .snd, d .snd))
def swapping_boolean_connected_cover (C : CircleSignature) : ConnectedCoverings (C .carrier)
  ≔ (swapping_boolean_cover C, swapping_boolean_total_connected C)

def swapping_boolean_cover_not_equivalence (C : CircleSignature)
  (h : BookIsEquiv (swapping_boolean_cover C .fst) (C .carrier) (swapping_boolean_cover C .snd .fst)) : Empty
  ≔ let R ≔ ((z ↦ swapping_boolean_circle_family C z .fst) : C .carrier → Type) in
    let F ≔ BookFiber (Σ (C .carrier) R) (C .carrier) (z ↦ z .fst) (C .base) in
    let hr ≔ book_contractibility_equiv F (R (C .base))
      (native_equivalence F (R (C .base)) (book_projection_fiber_equiv (C .carrier) R (C .base))) .map (h (C .base)) in
    boolean_not_contractible (transport Type BookIsContr (R (C .base)) Bool
      (circle_rec_beta C SetTypes (boolean_set, boolean_set_swap) .fst .fst) hr)

def equivalence_fibers_finite (A B : Type) (e : Equiv A B) (b : B)
  : IsFinite (BookFiber A B (e .map) b)
  ≔ finite_from_equiv (BookFiber A B (e .map) b) (suc. zero.)
      (compose_equiv (BookFiber A B (e .map) b) Unit (Fin (suc. zero.))
        (contractible_unit_equiv (BookFiber A B (e .map) b)
          (native_contraction (BookFiber A B (e .map) b) (book_equivalence A B e .equiv b)))
        (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv))

def circle_identity_covering (C : CircleSignature) : IsCovering (C .carrier) (C .carrier) (identity (C .carrier))
  ≔ equivalence_covering (C .carrier) (C .carrier) (identity_equiv (C .carrier))
def circle_identity_fibers_finite (C : CircleSignature) (z : C .carrier)
  : IsFinite (BookFiber (C .carrier) (C .carrier) (identity (C .carrier)) z)
  ≔ equivalence_fibers_finite (C .carrier) (C .carrier) (identity_equiv (C .carrier)) z

def circle_not_set (C : CircleSignature) (h : isSet (C .carrier)) : Empty
  ≔ let L ≔ Id (C .carrier) (C .base) (C .base) in
    let e ≔ native_equivalence L Int (circle_loop_integer_equiv C) in
    int_encode int_zero (pos. (suc. zero.))
      (retract_prop L Int (h (C .base) (C .base)) (e .map) (equiv_inverse_map L Int e)
        (equiv_counit L Int e) int_zero (pos. (suc. zero.)))
def circle_not_finite (C : CircleSignature) (h : IsFinite (C .carrier)) : Empty
  ≔ circle_not_set C (finite_sethood (C .carrier) h)
