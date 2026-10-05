export "224-constructed-circle-checks"

{` The circle lies in every universe (circle.tex, def:circle: "S¹ : U").
   The constructed circle is the component of the infinite cycle (ℤ, succ)
   in the large type Cycles.  Cycles itself is not locally U-small (its
   carriers range over all of Type), but the subtype of cycles with a
   U-small carrier is: its identity types are the isomorphisms of cycles,
   built from U-small types.  Smallness of the carrier is a proposition, so
   the component of (ℤ, succ) in that subtype is the component in Cycles,
   and replacement (pri:replacement) makes it essentially U-small. `}

{` ℤ is U-small in every universe: ℤ ≃ ℕ + ℕ. `}
def nat_sum_to_int : Sum Nat Nat → Int ≔ [ inl. n ↦ pos. n | inr. n ↦ neg. n ]

def int_to_nat_sum : Int → Sum Nat Nat ≔ [ pos. n ↦ inl. n | neg. n ↦ inr. n ]

def nat_sum_int_equiv : Equiv (Sum Nat Nat) Int
  ≔ quasi_inverse_equiv (Sum Nat Nat) Int nat_sum_to_int int_to_nat_sum
      [ inl. n ↦ refl (inl. n : Sum Nat Nat) | inr. n ↦ refl (inr. n : Sum Nat Nat) ]
      [ pos. n ↦ refl (pos. n : Int) | neg. n ↦ refl (neg. n : Int) ]

def int_small_in_universe (U : Universe) : U .small Int
  ≔ small_equiv U (Sum Nat Nat) Int nat_sum_int_equiv (U .sum_small Nat Nat (U .nat_small) (U .nat_small))

{` Isomorphisms of permutations of U-small sets form a U-small type. `}
def permutation_isomorphisms_small (U : Universe) (p q : Permutations)
  (sp : U .small (p .fst .fst)) (sq : U .small (q .fst .fst))
  : U .small (PermutationIsomorphisms p q)
  ≔ U .sigma_small (Equiv (p .fst .fst) (q .fst .fst))
      (h ↦ Commutes (p .fst .fst) (q .fst .fst) (p .snd) (q .snd) (h .map))
      (equiv_small U (p .fst .fst) (q .fst .fst) sp sq)
      (h ↦ U .pi_small (p .fst .fst) (x ↦ Id (q .fst .fst) (h .map (p .snd .map x)) (q .snd .map (h .map x))) sp
        (x ↦ U .id_small (q .fst .fst) sq (h .map (p .snd .map x)) (q .snd .map (h .map x))))

{` Cycles whose underlying set is U-small. `}
def SmallCarrierCycles (U : Universe) : Type ≔ Σ Cycles (c ↦ U .small (c .fst .fst .fst))

def small_carrier_cycles_locally_small (U : Universe) : LocallySmall U (SmallCarrierCycles U)
  ≔ u v ↦
    let I ≔ PermutationIsomorphisms (u .fst .fst) (v .fst .fst) in
    let P ≔ Id (SmallCarrierCycles U) u v in
    essentially_small_equiv U I P
      (canonical_inverse_equiv P I
        (compose_equiv P (Id Cycles (u .fst) (v .fst)) I
          (subtype_path_equiv Cycles (c ↦ U .small (c .fst .fst .fst)) (c ↦ U .small_prop (c .fst .fst .fst)) u v)
          (cycle_paths_equiv (u .fst) (v .fst))))
      (small_essentially_small U I (permutation_isomorphisms_small U (u .fst .fst) (v .fst .fst) (u .snd) (v .snd)))

def small_carrier_infinite_cycle (U : Universe) : SmallCarrierCycles U ≔ (infinite_cycle, int_small_in_universe U)

{` def:circle, "S¹ : U": the constructed circle is essentially U-small in
   every universe U satisfying replacement. `}
def constructed_circle_essentially_small (U : Universe) (rep : Replacement U)
  : EssentiallySmall U (constructed_circle .carrier)
  ≔ essentially_small_equiv U (NativeComponent (SmallCarrierCycles U) (small_carrier_infinite_cycle U))
      (CycleComponent zero.)
      (component_subtype_equiv Cycles (c ↦ U .small (c .fst .fst .fst)) (c ↦ U .small_prop (c .fst .fst .fst))
        (small_carrier_infinite_cycle U))
      (component_essentially_small U rep (SmallCarrierCycles U) (small_carrier_cycles_locally_small U)
        (small_carrier_infinite_cycle U))

{` Since the smallness predicate is replete, the carrier itself is small,
   and the circle is an element of the universe. `}
def constructed_circle_small (U : Universe) (rep : Replacement U) : U .small (constructed_circle .carrier)
  ≔ essentially_small_is_small U (constructed_circle .carrier) (constructed_circle_essentially_small U rep)

def constructed_circle_code (U : Universe) (rep : Replacement U) : UniverseType U
  ≔ (constructed_circle .carrier, constructed_circle_small U rep)

def small_circle_signature (U : Universe) (rep : Replacement U) : Σ CircleSignature (C ↦ U .small (C .carrier))
  ≔ (constructed_circle, constructed_circle_small U rep)

{` Every circle is equivalent to the constructed one (thm:S1bysymmetries),
   hence every circle is essentially U-small. `}
def circle_carrier_essentially_small (U : Universe) (rep : Replacement U) (C : CircleSignature)
  : EssentiallySmall U (C .carrier)
  ≔ essentially_small_equiv U (CycleComponent zero.) (C .carrier)
      (compose_equiv (CycleComponent zero.) InfiniteCycles (C .carrier) infinite_cycle_forget_equiv
        (canonical_inverse_equiv (C .carrier) InfiniteCycles
          (native_equivalence (C .carrier) InfiniteCycles (circle_infinite_cycles_equiv C))))
      (constructed_circle_essentially_small U rep)

{` Instance: the universe of all types. `}
def total_constructed_circle_essentially_small : EssentiallySmall total_universe (constructed_circle .carrier)
  ≔ constructed_circle_essentially_small total_universe total_replacement
