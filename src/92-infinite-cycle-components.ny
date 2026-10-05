export "91-finite-covering-components"

def Endomorphisms : Type ≔ Σ Type (X ↦ X → X)
def integer_endomorphism : Endomorphisms ≔ (Int, int_succ)

def EndomorphismCycleStructure (t : Endomorphisms) : Type
  ≔ Σ (isSet (t .fst)) (_ ↦ Σ (isEquiv (t .fst) (t .fst) (t .snd))
      (h ↦ Cyclic (t .fst) (t .snd, h)))

def endomorphism_cycle_structure_prop (t : Endomorphisms) : isProp (EndomorphismCycleStructure t)
  ≔ sigma_prop (isSet (t .fst))
      (_ ↦ Σ (isEquiv (t .fst) (t .fst) (t .snd)) (h ↦ Cyclic (t .fst) (t .snd, h)))
      (isset_isprop (t .fst))
      (_ ↦ sigma_prop (isEquiv (t .fst) (t .fst) (t .snd)) (h ↦ Cyclic (t .fst) (t .snd, h))
        (isequiv_isprop (t .fst) (t .fst) (t .snd)) (h ↦ cyclic_prop (t .fst) (t .snd, h)))

def cycle_endomorphism (c : Cycles) : Endomorphisms ≔ (c .fst .fst .fst, c .fst .snd .map)
def cycle_endomorphism_structure (c : Cycles) : EndomorphismCycleStructure (cycle_endomorphism c)
  ≔ (c .fst .fst .snd, (c .fst .snd .equiv, c .snd))

def cycle_endomorphism_pack (c : Cycles) : Σ Endomorphisms EndomorphismCycleStructure
  ≔ (cycle_endomorphism c, cycle_endomorphism_structure c)
def cycle_endomorphism_unpack (t : Σ Endomorphisms EndomorphismCycleStructure) : Cycles
  ≔ (((t .fst .fst, t .snd .fst), (t .fst .snd, t .snd .snd .fst)), t .snd .snd .snd)

def cycles_endomorphism_subtype : Equiv Cycles (Σ Endomorphisms EndomorphismCycleStructure)
  ≔ quasi_inverse_equiv Cycles (Σ Endomorphisms EndomorphismCycleStructure)
      cycle_endomorphism_pack cycle_endomorphism_unpack (c ↦ refl c) (t ↦ refl t)

{` The map is literally ap of the forgetful map to endomorphisms. `}
def cycle_endomorphism_paths (c d : Cycles)
  : Equiv (Id Cycles c d) (Id Endomorphisms (cycle_endomorphism c) (cycle_endomorphism d))
  ≔ compose_equiv (Id Cycles c d)
      (Id (Σ Endomorphisms EndomorphismCycleStructure) (cycle_endomorphism_pack c) (cycle_endomorphism_pack d))
      (Id Endomorphisms (cycle_endomorphism c) (cycle_endomorphism d))
      (equivalence_on_paths Cycles (Σ Endomorphisms EndomorphismCycleStructure) cycles_endomorphism_subtype c d)
      (subtype_path_equiv Endomorphisms EndomorphismCycleStructure endomorphism_cycle_structure_prop
        (cycle_endomorphism_pack c) (cycle_endomorphism_pack d))

{` def:Cyc-components.  Zero denotes the infinite component; suc n denotes
   the component of the standard cycle with n+1 elements. `}
def CycleComponent (n : Nat) : Type ≔ NativeComponent Cycles (principal_cycle n)
def infinite_cycle_point : CycleComponent zero.
  ≔ (infinite_cycle, mere (Id Cycles infinite_cycle infinite_cycle) (refl infinite_cycle))

{` The book defines InfCyc in the universe of all endomorphisms. `}
def InfiniteCycles : Type ≔ NativeComponent Endomorphisms integer_endomorphism
def infinite_endomorphism_point : InfiniteCycles
  ≔ (integer_endomorphism, mere (Id Endomorphisms integer_endomorphism integer_endomorphism) (refl integer_endomorphism))

def infinite_cycle_forget_equiv : Equiv (CycleComponent zero.) InfiniteCycles
  ≔ compose_equiv (CycleComponent zero.)
      (NativeComponent (Σ Endomorphisms EndomorphismCycleStructure) (cycle_endomorphism_pack infinite_cycle))
      InfiniteCycles
      (component_equiv Cycles (Σ Endomorphisms EndomorphismCycleStructure) cycles_endomorphism_subtype infinite_cycle)
      (component_subtype_equiv Endomorphisms EndomorphismCycleStructure endomorphism_cycle_structure_prop
        (cycle_endomorphism_pack infinite_cycle))

def infinite_cycle_forget_base
  : Id InfiniteCycles (infinite_cycle_forget_equiv .map infinite_cycle_point) infinite_endomorphism_point
  ≔ subtype_equal Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
      (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
      (infinite_cycle_forget_equiv .map infinite_cycle_point) infinite_endomorphism_point (refl integer_endomorphism)

def infinite_endomorphism_structure (t : InfiniteCycles) : EndomorphismCycleStructure (t .fst)
  ≔ mere_transport native_truncation Endomorphisms EndomorphismCycleStructure endomorphism_cycle_structure_prop
      integer_endomorphism (t .fst) (t .snd) (cycle_endomorphism_structure infinite_cycle)

def infinite_endomorphism_cycle (t : InfiniteCycles) : Cycles
  ≔ cycle_endomorphism_unpack (t .fst, infinite_endomorphism_structure t)

def infinite_endomorphism_cycle_component (t : InfiniteCycles)
  : Mere (Id Cycles infinite_cycle (infinite_endomorphism_cycle t))
  ≔ trunc_map native_truncation (Id Endomorphisms integer_endomorphism (t .fst))
      (Id Cycles infinite_cycle (infinite_endomorphism_cycle t))
      (equiv_inverse_map (Id Cycles infinite_cycle (infinite_endomorphism_cycle t))
        (Id Endomorphisms integer_endomorphism (t .fst))
        (cycle_endomorphism_paths infinite_cycle (infinite_endomorphism_cycle t))) (t .snd)

def endomorphism_path_evaluate (s t : Endomorphisms) (p : Id Endomorphisms s t) (x : s .fst) : t .fst
  ≔ p .fst .trr x

{` Move a specified evaluation map across an equivalence of path types. `}
def evaluation_equiv_across (A B X : Type) (e : Equiv A B) (v : Equiv A X) (f : B → X)
  (agreement : (a : A) → Id X (v .map a) (f (e .map a))) : Equiv B X
  ≔ equiv_change_map B X (compose_equiv B A X (canonical_inverse_equiv A B e) v) f
      (b ↦ concat X (v .map (equiv_inverse_map A B e b)) (f (e .map (equiv_inverse_map A B e b))) (f b)
        (agreement (equiv_inverse_map A B e b)) (refl f (equiv_counit A B e b)))

{` lem:IdCisZet, in the book's actual endomorphism component, with evaluation
   given by transport of zero along the underlying type path. `}
def infinite_endomorphism_evaluation (t : InfiniteCycles)
  : BookEquiv (Id Endomorphisms integer_endomorphism (t .fst)) (t .fst .fst)
  ≔ book_equivalence (Id Endomorphisms integer_endomorphism (t .fst)) (t .fst .fst)
      (evaluation_equiv_across (Id Cycles infinite_cycle (infinite_endomorphism_cycle t))
        (Id Endomorphisms integer_endomorphism (t .fst)) (t .fst .fst)
        (cycle_endomorphism_paths infinite_cycle (infinite_endomorphism_cycle t))
        (native_equivalence (Id Cycles infinite_cycle (infinite_endomorphism_cycle t)) (t .fst .fst)
          (cycle_evaluation_from_component infinite_cycle (infinite_endomorphism_cycle t)
            (infinite_endomorphism_cycle_component t) int_zero))
        (p ↦ endomorphism_path_evaluate integer_endomorphism (t .fst) p int_zero)
        (p ↦ refl (p .fst .fst .fst .trr int_zero)))
