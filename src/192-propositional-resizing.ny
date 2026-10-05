export "191-small-closure"

{` pri:prop-resizing. The map P ↦ P : Prop_U → Prop_U', well typed by cumulativity. `}
def prop_inclusion (N : NestedUniverses) (P : PropU (N .lower)) : PropU (N .upper)
  ≔ ((P .fst .fst, N .cumulative (P .fst .fst) (P .fst .snd)), P .snd)

{` The principle, as a type (a proposition) used as a hypothesis. `}
def PropositionalResizing (N : NestedUniverses) : Type
  ≔ BookIsEquiv (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N)

def propositional_resizing_prop (N : NestedUniverses) : isProp (PropositionalResizing N)
  ≔ book_isequiv_isprop (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N)

def prop_inclusion_on_paths (N : NestedUniverses) (P Q : PropU (N .lower))
  : BookIsEquiv (Id (PropU (N .lower)) P Q) (Id (PropU (N .upper)) (prop_inclusion N P) (prop_inclusion N Q))
      (map_path (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N) P Q)
  ≔ let el ≔ prop_u_path_equiv (N .lower) P Q in
    let eu ≔ prop_u_path_equiv (N .upper) (prop_inclusion N P) (prop_inclusion N Q) in
    book_two_out_of_three_left (Id (PropU (N .lower)) P Q)
      (Id (PropU (N .upper)) (prop_inclusion N P) (prop_inclusion N Q)) (Id Type (P .fst .fst) (Q .fst .fst))
      (map_path (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N) P Q) (el .map) (eu .map)
      (refl (el .map))
      (book_equivalence (Id (PropU (N .lower)) P Q) (Id Type (P .fst .fst) (Q .fst .fst)) el .equiv)
      (book_equivalence (Id (PropU (N .upper)) (prop_inclusion N P) (prop_inclusion N Q))
        (Id Type (P .fst .fst) (Q .fst .fst)) eu .equiv)

def prop_inclusion_embedding (N : NestedUniverses)
  : IsEmbedding (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N)
  ≔ path_equivalences_embedding (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N) (prop_inclusion_on_paths N)

def resizing_fiber_small (N : NestedUniverses) (P : PropU (N .upper))
  (w : BookFiber (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N) P)
  : EssentiallySmall (N .lower) (P .fst .fst)
  ≔ (w .fst .fst, transport_equiv (P .fst .fst) (w .fst .fst .fst) (w .snd .fst .fst))

def small_resizing_fiber (N : NestedUniverses) (P : PropU (N .upper)) (h : EssentiallySmall (N .lower) (P .fst .fst))
  : BookFiber (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N) P
  ≔ let X ≔ h .fst in
    let Q : PropU (N .lower) ≔ (X, hlevel_one_to_prop (X .fst)
      (hlevel_equiv (suc. zero.) (P .fst .fst) (X .fst) (h .snd) (prop_to_hlevel_one (P .fst .fst) (P .snd)))) in
    (Q, subtype_equal (UniverseType (N .upper)) (Y ↦ isProp (Y .fst)) (Y ↦ isprop_isprop (Y .fst)) P (prop_inclusion N Q)
      (subtype_equal Type (N .upper .small) (N .upper .small_prop) (P .fst) (prop_inclusion N Q .fst)
        (ua (P .fst .fst) (X .fst) (h .snd))))

{` Resizing holds iff every U'-proposition is essentially U-small. `}
def resizing_equiv (N : NestedUniverses)
  : Equiv (PropositionalResizing N) ((P : PropU (N .upper)) → EssentiallySmall (N .lower) (P .fst .fst))
  ≔ iff_equiv (PropositionalResizing N) ((P : PropU (N .upper)) → EssentiallySmall (N .lower) (P .fst .fst))
      (propositional_resizing_prop N)
      (pi_prop (PropU (N .upper)) (P ↦ EssentiallySmall (N .lower) (P .fst .fst))
        (P ↦ essentially_small_prop (N .lower) (P .fst .fst)))
      (r P ↦ resizing_fiber_small N P (r P .center))
      (s P ↦ (small_resizing_fiber N P (s P),
        w ↦ prop_inclusion_embedding N P (small_resizing_fiber N P (s P)) w))

def small_resizing (N : NestedUniverses) (s : (P : PropU (N .upper)) → EssentiallySmall (N .lower) (P .fst .fst))
  : PropositionalResizing N
  ≔ equiv_inverse_map (PropositionalResizing N) ((P : PropU (N .upper)) → EssentiallySmall (N .lower) (P .fst .fst))
      (resizing_equiv N) s

{` xca:lem-prop-sizing. LEM for the propositions of U'. `}
def LEMFor (U : Universe) : Type ≔ (P : PropU U) → Decidable (P .fst .fst)

def excluded_middle_lem_for (lem : ExcludedMiddle) (U : Universe) : LEMFor U
  ≔ P ↦ lem (P .fst .fst) (P .snd)

def inhabited_prop_unit_equiv (P : Type) (hP : isProp P) (p : P) : Equiv P Unit
  ≔ quasi_inverse_equiv P Unit (_ ↦ star.) (_ ↦ p) (x ↦ hP p x) (u ↦ unit_prop star. u)

def refuted_empty_equiv (P : Type) (np : Not P) : Equiv P Empty
  ≔ quasi_inverse_equiv P Empty np (e ↦ absurd P e)
      (x ↦ absurd (Id P (absurd P (np x)) x) (np x)) (e ↦ absurd (Id Empty (np (absurd P e)) e) e)

def decided_prop_essentially_small (U : Universe) (P : Type) (hP : isProp P) (d : Decidable P)
  : EssentiallySmall U P
  ≔ match d [
  | inl. p ↦ ((Unit, U .unit_small), inhabited_prop_unit_equiv P hP p)
  | inr. np ↦ ((Empty, U .empty_small), refuted_empty_equiv P np) ]

def lem_resizing (N : NestedUniverses) (lem : LEMFor (N .upper)) : PropositionalResizing N
  ≔ small_resizing N (P ↦ decided_prop_essentially_small (N .lower) (P .fst .fst) (P .snd) (lem P))

def excluded_middle_resizing (lem : ExcludedMiddle) (N : NestedUniverses) : PropositionalResizing N
  ≔ lem_resizing N (excluded_middle_lem_for lem (N .upper))

{` Remark after the exercise on local smallness: resizing equivalently says
   that every proposition is essentially U-small; then every set is locally
   U-small. `}
def PropsEssentiallySmall (U : Universe) : Type ≔ (P : Type) → isProp P → EssentiallySmall U P

def props_small_resizing (N : NestedUniverses) (h : PropsEssentiallySmall (N .lower)) : PropositionalResizing N
  ≔ small_resizing N (P ↦ h (P .fst .fst) (P .snd))

def total_resizing_props_small (U : Universe) (r : PropositionalResizing (total_nested U)) : PropsEssentiallySmall U
  ≔ P hP ↦ resizing_equiv (total_nested U) .map r ((P, star.), hP)

def props_small_total_resizing_equiv (U : Universe)
  : Equiv (PropositionalResizing (total_nested U)) (PropsEssentiallySmall U)
  ≔ iff_equiv (PropositionalResizing (total_nested U)) (PropsEssentiallySmall U)
      (propositional_resizing_prop (total_nested U))
      (pi_prop Type (P ↦ isProp P → EssentiallySmall U P)
        (P ↦ pi_prop (isProp P) (_ ↦ EssentiallySmall U P) (_ ↦ essentially_small_prop U P)))
      (total_resizing_props_small U) (props_small_resizing (total_nested U))

def props_small_sets_locally_small (U : Universe) (h : PropsEssentiallySmall U) (A : Type) (hA : isSet A)
  : LocallySmall U A
  ≔ x y ↦ h (Id A x y) (hA x y)
