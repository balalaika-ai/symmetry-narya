export "1103-graph-quotient-steps"

{` fggroups.tex, definitions at lines 631 (subgraph) and 649 (spanning tree),
   and helpers for trees.

   Subgraph V E: a subtype h : U ↪ V of the vertices (a type U with an embedding)
   and, for all u, w in U, a subtype D(u,w) of E(h u, h w), given as a predicate
   (Subtypes = maps into PropTypes, the book's subtypes).  The subgraph is the
   graph (U, subgraph_edges).  "The embedding is decidable" (line 656 and
   lem:spanning-tree-step) is DecidableSubgraphVertices / DecidableSubgraphEdges.

   SpanningTree V E: a subgraph that is a tree (GraphTreeStructure, i.e. its
   graph quotient is contractible, module 1101) and whose vertex embedding is an
   equivalence (BookIsEquiv).

   discrete_signature: a graph with no edges has the vertex type itself as graph
   quotient.  unit_structure_tree: any graph-quotient structure on Unit (with
   any vertex and edge maps) is a tree structure. `}

def Subgraph (V : Type) (E : V → V → Type) : Type ≔ sig (
  vertices : Type,
  incl : vertices → V,
  incl_embedding : IsEmbedding vertices V incl,
  edges : (u w : vertices) → E (incl u) (incl w) → PropTypes )

def subgraph_edges (V : Type) (E : V → V → Type) (H : Subgraph V E) (u w : H .vertices) : Type
  ≔ Σ (E (H .incl u) (H .incl w)) (e ↦ H .edges u w e .fst)

def SubgraphEdgeTotal (V : Type) (E : V → V → Type) (H : Subgraph V E) : Type
  ≔ Σ (H .vertices) (u ↦ Σ (H .vertices) (w ↦ subgraph_edges V E H u w))

def DecidableSubgraphVertices (V : Type) (E : V → V → Type) (H : Subgraph V E) : Type
  ≔ (x : V) → Decidable (BookFiber (H .vertices) V (H .incl) x)

def DecidableSubgraphEdges (V : Type) (E : V → V → Type) (H : Subgraph V E) : Type
  ≔ (u w : H .vertices) (e : E (H .incl u) (H .incl w)) → Decidable (H .edges u w e .fst)

{` def. at line 649. `}
def SpanningTree (V : Type) (E : V → V → Type) : Type
  ≔ Σ (Subgraph V E) (H ↦
      Product (GraphTreeStructure (H .vertices) (subgraph_edges V E H))
        (BookIsEquiv (H .vertices) V (H .incl)))

{` ---------- Helpers ---------- `}

def set_injection_embedding (A B : Type) (hB : isSet B) (f : A → B) (inj : PathReflecting A B f)
  : IsEmbedding A B f
  ≔ b u v ↦
    let p ≔ inj (u .fst) (v .fst) (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)) in
    (p, pathover_of_eq A (a ↦ Id B b (f a)) (u .fst) (v .fst) p (u .snd) (v .snd)
          (hB b (f (v .fst)) (transport A (a ↦ Id B b (f a)) (u .fst) (v .fst) p (u .snd)) (v .snd)))

def embedding_injection (A B : Type) (f : A → B) (h : IsEmbedding A B f) : PathReflecting A B f
  ≔ x y q ↦ refl ((t : BookFiber A B f (f y)) ↦ t .fst)
      (h (f y) (x, inverse B (f x) (f y) q) (y, refl (f y)))

{` A graph with no edges: its vertex type is a graph quotient. `}
def NoEdges (V : Type) (x y : V) : Type ≔ Empty

def no_edges_edge (V : Type) (x y : V) (e : NoEdges V x y) : Id V x y ≔ match e []

def discrete_boundary_center (V : Type) (P : V → Type) (a : (x : V) → P x)
  : (x y : V) (e : NoEdges V x y) → Id P (no_edges_edge V x y e) (a x) (a y)
  ≔ x y e ↦ match e []

def discrete_boundary_contractible (V : Type) (P : V → Type) (a : (x : V) → P x)
  : isContr ((x y : V) (e : NoEdges V x y) → Id P (no_edges_edge V x y e) (a x) (a y))
  ≔ (discrete_boundary_center V P a,
     b ↦ funext3 V (_ ↦ V) (x y ↦ NoEdges V x y) (x y e ↦ Id P (no_edges_edge V x y e) (a x) (a y))
       b (discrete_boundary_center V P a) (x y e ↦ match e []))

def discrete_induction (V : Type)
  : GraphQuotientInduction V (NoEdges V) V (x ↦ x) (no_edges_edge V)
  ≔ gq_induction_of_isequiv V (NoEdges V) V (x ↦ x) (no_edges_edge V)
      (P ↦ isequiv_of_homotopic ((z : V) → P z) (GraphQuotientBoundary V (NoEdges V) V (x ↦ x) (no_edges_edge V) P)
        (canonical_inverse_equiv (GraphQuotientBoundary V (NoEdges V) V (x ↦ x) (no_edges_edge V) P) ((z : V) → P z)
          (contractible_fiber_projection ((z : V) → P z)
            (a ↦ (x y : V) (e : NoEdges V x y) → Id P (no_edges_edge V x y e) (a x) (a y))
            (a ↦ discrete_boundary_contractible V P a)))
        (graph_quotient_evaluate V (NoEdges V) V (x ↦ x) (no_edges_edge V) P)
        (h ↦ (refl h, inverse ((x y : V) (e : NoEdges V x y) → Id P (no_edges_edge V x y e) (h x) (h y))
            (graph_quotient_evaluate V (NoEdges V) V (x ↦ x) (no_edges_edge V) P h .snd)
            (discrete_boundary_center V P h)
            ((discrete_boundary_contractible V P h) .contract
              (graph_quotient_evaluate V (NoEdges V) V (x ↦ x) (no_edges_edge V) P h .snd)))))

def discrete_signature (V : Type) : GraphQuotientSignature V (NoEdges V)
  ≔ (V, x ↦ x, no_edges_edge V, discrete_induction V)

{` Any graph-quotient structure on Unit is a tree structure. `}
def UnitCocone (V : Type) (E : V → V → Type) : Type
  ≔ Σ (V → Unit) (vt ↦ (x y : V) → E x y → Id Unit (vt x) (vt y))

def unit_cocone_prop (V : Type) (E : V → V → Type) : isProp (UnitCocone V E)
  ≔ contractible_prop (UnitCocone V E)
      (sigma_contractible (V → Unit) (vt ↦ (x y : V) → E x y → Id Unit (vt x) (vt y))
        (pi_contractible V (_ ↦ Unit) (_ ↦ unit_contractible))
        (vt ↦ pi_contractible V (x ↦ (y : V) → E x y → Id Unit (vt x) (vt y)) (x ↦
          pi_contractible V (y ↦ E x y → Id Unit (vt x) (vt y)) (y ↦
            pi_contractible (E x y) (_ ↦ Id Unit (vt x) (vt y)) (_ ↦
              prop_paths_contractible Unit unit_prop (vt x) (vt y))))))

def unit_structure_tree (V : Type) (E : V → V → Type) (vt : V → Unit)
  (ed : (x y : V) → E x y → Id Unit (vt x) (vt y)) (ind : GraphQuotientInduction V E Unit vt ed)
  : GraphTreeStructure V E
  ≔ transport (UnitCocone V E) (c ↦ GraphQuotientInduction V E Unit (c .fst) (c .snd)) (vt, ed)
      (_ ↦ star., x y _ ↦ refl (star. : Unit))
      (unit_cocone_prop V E (vt, ed) (_ ↦ star., x y _ ↦ refl (star. : Unit))) ind
