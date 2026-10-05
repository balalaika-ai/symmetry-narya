export "118-covering-calculus"

def maps_between_sets_covering (A B : Type) (ha : isSet A) (hb : isSet B) (f : A → B) : IsCovering A B f
  ≔ b ↦ sigma_set A (a ↦ Id B b (f a)) ha (a ↦ prop_is_set (Id B b (f a)) (hb b (f a)))

{` xca:covering-utils, item 1, for any map into any contractible type. `}
def covering_into_contractible_equiv (A U : Type) (f : A → U) (hu : BookIsContr U)
  : Equiv (IsCovering A U f) (isSet A)
  ≔ let su ≔ prop_is_set U (contractible_prop U (native_contraction U hu)) in
    iff_equiv (IsCovering A U f) (isSet A) (covering_property_prop U (A, f)) (isset_isprop A)
      (hf ↦ covering_domain_set A U f hf su) (ha ↦ maps_between_sets_covering A U ha su f)

def finite_one_covering_equiv (A : Type) (f : A → Fin (suc. zero.))
  : Equiv (IsCovering A (Fin (suc. zero.)) f) (isSet A)
  ≔ covering_into_contractible_equiv A (Fin (suc. zero.)) f finite_one_contractible

def constant_unit_fiber_equiv (B : Type) (b c : B)
  : Equiv (BookFiber Unit B (constant Unit B b) c) (Id B c b)
  ≔ quasi_inverse_equiv (BookFiber Unit B (constant Unit B b) c) (Id B c b)
      (w ↦ w .snd) (q ↦ (star., q)) (w ↦ (unit_prop star. (w .fst), refl (w .snd))) (q ↦ refl q)

def target_path_spaces_set (B : Type) (b : B) (hb : isSet (Id B b b)) (c : B) : isSet (Id B c b)
  ≔ p q ↦ hlevel_two_to_set (Id B c b)
      (hlevel_equiv (suc. (suc. zero.)) (Id B b b) (Id B c b) (concat_left_equiv B c b b p)
        (set_to_hlevel_two (Id B b b) hb)) p q

def constant_unit_covering_from_loops (B : Type) (b : B) (hb : isSet (Id B b b))
  : IsCovering Unit B (constant Unit B b)
  ≔ c ↦ hlevel_two_to_set (BookFiber Unit B (constant Unit B b) c)
      (hlevel_equiv (suc. (suc. zero.)) (Id B c b) (BookFiber Unit B (constant Unit B b) c)
        (canonical_inverse_equiv (BookFiber Unit B (constant Unit B b) c) (Id B c b) (constant_unit_fiber_equiv B b c))
        (set_to_hlevel_two (Id B c b) (target_path_spaces_set B b hb c)))

def constant_unit_loops_from_covering (B : Type) (b : B) (hb : IsCovering Unit B (constant Unit B b))
  : isSet (Id B b b)
  ≔ hlevel_two_to_set (Id B b b)
      (hlevel_equiv (suc. (suc. zero.)) (BookFiber Unit B (constant Unit B b) b) (Id B b b)
        (constant_unit_fiber_equiv B b b) (set_to_hlevel_two (BookFiber Unit B (constant Unit B b) b) (hb b)))

def constant_unit_covering_equiv (B : Type) (b : B)
  : Equiv (IsCovering Unit B (constant Unit B b)) (isSet (Id B b b))
  ≔ iff_equiv (IsCovering Unit B (constant Unit B b)) (isSet (Id B b b))
      (covering_property_prop B (Unit, constant Unit B b)) (isset_isprop (Id B b b))
      (constant_unit_loops_from_covering B b) (constant_unit_covering_from_loops B b)

def coverings_preequivalence (A X B : Type) (e : Equiv A X) (f : X → B) (hf : IsCovering X B f)
  : IsCovering A B (compose A X B f (e .map))
  ≔ b ↦ hlevel_two_to_set (BookFiber A B (compose A X B f (e .map)) b)
      (preequivalence_truncated_map (suc. (suc. zero.)) A X B e f
        (b ↦ set_to_hlevel_two (BookFiber X B f b) (hf b)) b)

def coverings_cancel_preequivalence (A X B : Type) (e : Equiv A X) (f : X → B)
  (hf : IsCovering A B (compose A X B f (e .map))) : IsCovering X B f
  ≔ b ↦ hlevel_two_to_set (BookFiber X B f b)
      (cancel_preequivalence_truncated_map (suc. (suc. zero.)) A X B e f
        (b ↦ set_to_hlevel_two (BookFiber A B (compose A X B f (e .map)) b) (hf b)) b)

{` xca:covering-utils, item 2, in the literal Fin 1 presentation. `}
def constant_finite_one_covering_equiv (B : Type) (b : B)
  : Equiv (IsCovering (Fin (suc. zero.)) B (constant (Fin (suc. zero.)) B b)) (isSet (Id B b b))
  ≔ iff_equiv (IsCovering (Fin (suc. zero.)) B (constant (Fin (suc. zero.)) B b)) (isSet (Id B b b))
      (covering_property_prop B (Fin (suc. zero.), constant (Fin (suc. zero.)) B b)) (isset_isprop (Id B b b))
      (hf ↦ constant_unit_loops_from_covering B b
        (coverings_cancel_preequivalence (Fin (suc. zero.)) Unit B fin_one_equiv (constant Unit B b) hf))
      (hb ↦ coverings_preequivalence (Fin (suc. zero.)) Unit B fin_one_equiv (constant Unit B b)
        (constant_unit_covering_from_loops B b hb))
