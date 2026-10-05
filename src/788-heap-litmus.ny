export "787-heap-variety"
export "786-heap-concrete-groups"
export "413-group-motivation"

{` Litmus checks for sec:heaps (modules 780-787). `}

{` The ternary operation agrees with path_heap_op of rem:heap-preview
   (module 413), which brackets p q⁻¹ r as p (q⁻¹ r). `}
def heap_ternary_path_heap_op (H : Heap) (p q r : heap_usym H)
  : Id (heap_usym H) (heap_ternary H p q r) (path_heap_op (BHeap H) (heap_start_shape H) (heap_end_shape H) p q r)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    inverse (Id A a b) (concat A a a b (concat A a b a r (inverse A a b q)) p)
      (concat A a b b r (concat A b a b (inverse A a b q) p))
      (concat_assoc A a b a b r (inverse A a b q) p)

{` Composition order: in the doubled heap of Σ_3, the symmetry p q⁻¹ r with
   p = τ = (0 1), q = e, r = σ = (1 2) acts on 0 as τ(σ(0)) = 1 (first r,
   then q⁻¹, then p); the reverse order σ(τ(0)) would give 2. `}
def heap_sigma3_inverse_unit_action (x : Fin three)
  : Id (Fin three)
      (permutation_action (standard_set three) (usym_inv (symmetric_group three) (usym_unit (symmetric_group three))) x) x
  ≔ let G ≔ symmetric_group three in
    concat (Fin three) (permutation_action (standard_set three) (usym_inv G (usym_unit G)) x)
      (permutation_action (standard_set three) (usym_unit G) x) x
      (refl ((k ↦ permutation_action (standard_set three) k x) : USym G → Fin three) (inverse_refl (BG G .carrier) (shape G)))
      (permutation_action_unit (standard_set three) x)

def heap_sigma3_ternary_action
  : Id (Fin three)
      (permutation_action (standard_set three)
        (heap_ternary (group_heap (symmetric_group three)) sigma3_tau (usym_unit (symmetric_group three)) sigma3_sigma)
        fin3_zero)
      fin3_one
  ≔ let G ≔ symmetric_group three in
    let S ≔ standard_set three in
    let act ≔ permutation_action S in
    let ie ≔ usym_inv G (usym_unit G) in
    calc
      act (usym_mul G (usym_mul G sigma3_tau ie) sigma3_sigma) fin3_zero
      = act (usym_mul G sigma3_tau ie) (act sigma3_sigma fin3_zero)
        by permutation_action_mul S (usym_mul G sigma3_tau ie) sigma3_sigma fin3_zero
      = act sigma3_tau (act ie fin3_zero) by permutation_action_mul S sigma3_tau ie fin3_zero
      = act sigma3_tau fin3_zero by refl (act sigma3_tau) (heap_sigma3_inverse_unit_action fin3_zero)
      = fin3_one by refl fin3_one ∎

{` The doubled heap of the non-abelian group Σ_3 is not abelian. `}
def heap_sigma3_not_abelian (h : IsAbelianHeap (group_heap (symmetric_group three))) : Empty
  ≔ symmetric_group_three_not_abelian (heap_abelian_to_end (group_heap (symmetric_group three)) h)

{` The doubled heap of an abelian group is abelian, and its canonical
   isomorphism between the (equal) endpoint groups is the identity. `}
def heap_double_abelian (G : Group) (hab : IsAbelian G) : IsAbelianHeap (group_heap G)
  ≔ heap_end_abelian_to_heap (group_heap G) hab

def heap_double_canonical_identity (G : Group) (hab : IsAbelian G) (g : USym G)
  : Id (USym G) (heap_canonical_abstract_iso (group_heap G) (heap_double_abelian G hab) .fst .map g) g
  ≔ let K ≔ AbstractIso (abstr G) (abstr G) in
    concat (USym G) (heap_canonical_abstract_iso (group_heap G) (heap_double_abelian G hab) .fst .map g)
      (heap_conj_abstract_iso (group_heap G) (refl (shape G)) .fst .map g) g
      (refl ((ψ ↦ ψ .fst .map g) : K → USym G)
        (heap_canonical_abstract_iso_value (group_heap G) (heap_double_abelian G hab) (refl (shape G))))
      (conj_abelian_trivial G hab (refl (shape G)) g)

def heap_unit_group_abelian : IsAbelianHeap (group_heap unit_group)
  ≔ heap_double_abelian unit_group
      (g h ↦ concat (USym unit_group) (usym_mul unit_group g h) (unit_group_usym_contractible .center)
        (usym_mul unit_group h g)
        (inverse (USym unit_group) (unit_group_usym_contractible .center) (usym_mul unit_group g h)
          (unit_group_usym_contractible .contract (usym_mul unit_group g h)))
        (unit_group_usym_contractible .contract (usym_mul unit_group h g)))

{` xca:heap-variety: the empty set and the first projection on Bool carry no
   heap; the one-point set with the constant operation does. `}
def heap_empty_not_heap (t : Ternary Empty)
  (w : BookFiber Heap TernarySets heap_ternary_structure ((Empty, empty_set), t)) : Empty
  ≔ mere_rec Empty Empty empty_prop (x ↦ x) (heap_fiber_laws ((Empty, empty_set), t) w .fst)

def heap_bool_code : Bool → Type ≔ [ true. ↦ Unit | false. ↦ Empty ]

def heap_bool_projection : Ternary Bool ≔ u ↦ u .fst

def heap_bool_projection_not_heap
  (w : BookFiber Heap TernarySets heap_ternary_structure ((Bool, bool_set), heap_bool_projection)) : Empty
  ≔ transport Bool heap_bool_code true. false.
      (heap_fiber_laws ((Bool, bool_set), heap_bool_projection) w .snd .fst true. false.) star.

def heap_unit_ternary : Ternary Unit ≔ _ ↦ star.

def heap_unit_equations : HeapEquations Unit heap_unit_ternary
  ≔ (x y ↦ match y [ star. ↦ refl (star. : Unit) ],
     (x y ↦ match x [ star. ↦ refl (star. : Unit) ],
      x y z u v ↦ refl (star. : Unit)))

def heap_unit_heap : BookFiber Heap TernarySets heap_ternary_structure ((Unit, unit_set), heap_unit_ternary)
  ≔ heap_from_laws ((Unit, unit_set), heap_unit_ternary) (mere Unit star., heap_unit_equations)

{` The translation group of the doubled heap of Σ_3 is (identified with)
   Σ_3, as an abstract group and as a group. `}
def heap_sigma3_translation_end : Id Group (symmetric_group three)
    (heap_translation_concrete_group (group_heap (symmetric_group three)))
  ≔ heap_translation_concrete_end_path (group_heap (symmetric_group three))
