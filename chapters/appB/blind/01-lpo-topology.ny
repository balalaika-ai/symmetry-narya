import "../../../src/71-limited-omniscience"

{` Blind statements for appendix B (metamath.tex), sections "The Limited
   Principle of Omniscience" and "Topology". Statements only, no proofs. `}

{` Logical equivalence (a pair of maps). `}
def BlindIff (A B : Type) : Type ≔ Product (A → B) (B → A)

{` The book's 2 = Fin(2) (def:finiteset). Convention: Fin(S n) = Fin(n) + 1,
   the old elements 0..n-1 sit in the left summand and the new element n is
   inr; so 0 = inl (inr ★) and 1 = inr ★. (The book does not fix this; LPO
   for the other convention is equivalent, by composing with the swap.) `}
def BlindTwo : Type ≔ Fin 2
def blind_two_zero : BlindTwo ≔ inl. (inr. star.)
def blind_two_one : BlindTwo ≔ inr. star.

{` LPO (circle.tex, principle LPO, recalled in rem:LPO-solves-halting problem):
   for any P : N → 2, either there is a smallest n0 with P(n0) = 1, or P is
   the constant function with value 0. `}
def BlindLPOSmallestOne (P : Nat → BlindTwo) : Type
  ≔ Σ Nat (n0 ↦ Product (Id BlindTwo (P n0) blind_two_one)
      ((m : Nat) → Id BlindTwo (P m) blind_two_one → Le n0 m))

def BlindLPOConstantZero (P : Nat → BlindTwo) : Type
  ≔ Id (Nat → BlindTwo) P (_ ↦ blind_two_zero)

def BlindLPOInstance (P : Nat → BlindTwo) : Type
  ≔ Sum (BlindLPOSmallestOne P) (BlindLPOConstantZero P)

def BlindLPO : Type ≔ (P : Nat → BlindTwo) → BlindLPOInstance P

{` rem:LPO-solves-halting problem, internal content 1 ("It is clear that
   k ↦ T(e,n,k) is constant with value 0 iff M_e does not halt on n", with
   "M_e halts on n" read as ∃k. T(e,n,k) = 1): a function N → 2 is the
   constant 0 iff it never takes the value 1. `}
def blind_lpo_remark_constant_zero_iff_never_one : Type
  ≔ (P : Nat → BlindTwo)
    → BlindIff (BlindLPOConstantZero P) (Not (Σ Nat (k ↦ Id BlindTwo (P k) blind_two_one)))

{` rem:LPO-solves-halting problem, internal content 2: LPO applied to
   k ↦ T(e,n,k) decides, uniformly in e and n, whether T(e,n,-) ever takes
   the value 1 (the "halting problem" relative to any T : N → N → N → 2):
   there is H : N → N → 2 with H(e,n) = 1 iff ∃k. T(e,n,k) = 1, and
   H(e,n) = 0 iff k ↦ T(e,n,k) is the constant 0. That no such H is
   computable for Kleene's T, and that hence LPO has no closed axiom-free
   proof, is metatheoretic (see statements.json). `}
def blind_lpo_remark_halting_decider : Type
  ≔ BlindLPO → (T : Nat → Nat → Nat → BlindTwo)
    → Σ (Nat → Nat → BlindTwo) (H ↦ (e n : Nat)
        → Product
            (BlindIff (Id BlindTwo (H e n) blind_two_one) (Σ Nat (k ↦ Id BlindTwo (T e n k) blind_two_one)))
            (BlindIff (Id BlindTwo (H e n) blind_two_zero) (BlindLPOConstantZero (k ↦ T e n k))))

{` rem:LPO-solves-halting problem, the two cases of t(P) : L + R exclude each
   other (inl gives a value 1, inr gives constant 0). `}
def blind_lpo_remark_cases_exclusive : Type
  ≔ (P : Nat → BlindTwo) → BlindLPOSmallestOne P → BlindLPOConstantZero P → Empty

{` rem:LPO-solves-halting problem, footnote: "the argument must fail if we
   allow t to use LEM" — because LEM (pri:lem) proves LPO. `}
def blind_lpo_remark_lem_implies_lpo : Type ≔ ExcludedMiddle → BlindLPO

{` rem:injectionsurjectionisnotwhatyouthink. The real line is modelled by an
   arbitrary contractible type R ("all real numbers are identical"), the
   subspace {0,1} by any map f : 2 → R. `}

{` The preimage of any r : R (e.g. 3.25) contains both 0 and 1. `}
def blind_topology_remark_preimage_contains_both : Type
  ≔ (R : Type) → BookIsContr R → (f : BlindTwo → R) → (r : R)
    → Σ (BookFiber BlindTwo R f r) (u ↦ Σ (BookFiber BlindTwo R f r) (v ↦
        Product (Id BlindTwo (u .fst) blind_two_zero) (Id BlindTwo (v .fst) blind_two_one)))

{` ... so that preimage is not a proposition. `}
def blind_topology_remark_preimage_not_prop : Type
  ≔ (R : Type) → BookIsContr R → (f : BlindTwo → R) → (r : R)
    → Not (isProp (BookFiber BlindTwo R f r))

{` Hence "{0,1} ⊆ R" is not an injection in the sense of def:injection. `}
def blind_topology_remark_not_injection : Type
  ≔ (R : Type) → BookIsContr R → (f : BlindTwo → R) → Not (IsEmbedding BlindTwo R f)

{` "seemingly contradicting the next result": the next result is not printed
   (the remark was moved to the appendix). Our reading: the domain of an
   injection into a contractible type is a proposition (so, if inhabited,
   contractible and in particular connected), which {0,1} is not. `}
def blind_topology_remark_injection_into_contractible : Type
  ≔ (A R : Type) → BookIsContr R → (f : A → R) → IsEmbedding A R f → isProp A

{` {0,1} is not connected. `}
def blind_topology_remark_two_not_connected : Type ≔ Not (Connected BlindTwo)
