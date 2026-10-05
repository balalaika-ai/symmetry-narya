export "1101-graph-quotients"

{` Exercise at fggroups.tex:285: an equivalence relation R : A → A → Prop on a
   set A, regarded as the graph (A, R), has ‖A/R‖₀ ≃ A/R (the set quotient of
   def:quotient-set, module 41), for every graph quotient Q of (A, R).

   The maps are induced by the universal properties: ‖Q‖₀ → A/R sends |[a]| to
   the class of a (graph-quotient recursion into the set A/R, then set
   truncation recursion), A/R → ‖Q‖₀ sends the class of a to |[a]| (quotient
   recursion; R-related points are joined by an edge).  The hypothesis that A
   is a set is not needed. `}

def graph_set_quotient_to (A : Type) (R : EquivalenceRelation A) (Q : GraphQuotientSignature A (Rel A R))
  : SetTrunc (Q .carrier) → Quotient A R
  ≔ set_trunc_rec (Q .carrier) (Quotient A R) (quotient_set A R)
      (gq_rec A (Rel A R) Q (Quotient A R) (quotient_class A R, x y r ↦ quotient_encode A R x y r))

def graph_set_quotient_from (A : Type) (R : EquivalenceRelation A) (Q : GraphQuotientSignature A (Rel A R))
  : Quotient A R → SetTrunc (Q .carrier)
  ≔ quotient_rec A (SetTrunc (Q .carrier)) R (set_trunc_set (Q .carrier)) (a ↦ set_trunc (Q .carrier) (Q .vertex a))
      (x y r ↦ map_path (Q .carrier) (SetTrunc (Q .carrier)) (set_trunc (Q .carrier)) (Q .vertex x) (Q .vertex y) (Q .edge x y r))

def graph_set_quotient_to_from (A : Type) (R : EquivalenceRelation A) (Q : GraphQuotientSignature A (Rel A R))
  (z : Quotient A R)
  : Id (Quotient A R) (graph_set_quotient_to A R Q (graph_set_quotient_from A R Q z)) z
  ≔ mere_rec (BookFiber A (Quotient A R) (quotient_class A R) z)
      (Id (Quotient A R) (graph_set_quotient_to A R Q (graph_set_quotient_from A R Q z)) z)
      (quotient_set A R (graph_set_quotient_to A R Q (graph_set_quotient_from A R Q z)) z)
      (f ↦ transport (Quotient A R) (w ↦ Id (Quotient A R) (graph_set_quotient_to A R Q (graph_set_quotient_from A R Q w)) w)
          (quotient_class A R (f .fst)) z (inverse (Quotient A R) z (quotient_class A R (f .fst)) (f .snd))
          (gq_rec_vertex A (Rel A R) Q (Quotient A R) (quotient_class A R, x y r ↦ quotient_encode A R x y r) (f .fst)))
      (quotient_surjective A R z)

def graph_set_quotient_from_to (A : Type) (R : EquivalenceRelation A) (Q : GraphQuotientSignature A (Rel A R))
  (w : SetTrunc (Q .carrier))
  : Id (SetTrunc (Q .carrier)) (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q w)) w
  ≔ let T ≔ SetTrunc (Q .carrier) in
    set_trunc_induction (Q .carrier) (v ↦ Id T (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q v)) v)
      (v ↦ prop_is_set (Id T (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q v)) v)
        (set_trunc_set (Q .carrier) (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q v)) v))
      (gq_ind_prop A (Rel A R) Q
        (z ↦ Id T (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q (set_trunc (Q .carrier) z))) (set_trunc (Q .carrier) z))
        (z ↦ set_trunc_set (Q .carrier) (graph_set_quotient_from A R Q (graph_set_quotient_to A R Q (set_trunc (Q .carrier) z)))
          (set_trunc (Q .carrier) z))
        (a ↦ refl (graph_set_quotient_from A R Q)
          (gq_rec_vertex A (Rel A R) Q (Quotient A R) (quotient_class A R, x y r ↦ quotient_encode A R x y r) a)))
      w

def graph_set_quotient_equiv (A : Type) (R : EquivalenceRelation A) (Q : GraphQuotientSignature A (Rel A R))
  : Equiv (SetTrunc (Q .carrier)) (Quotient A R)
  ≔ quasi_inverse_equiv (SetTrunc (Q .carrier)) (Quotient A R)
      (graph_set_quotient_to A R Q) (graph_set_quotient_from A R Q)
      (graph_set_quotient_from_to A R Q) (graph_set_quotient_to_from A R Q)
