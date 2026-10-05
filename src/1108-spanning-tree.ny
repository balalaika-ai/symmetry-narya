export "1107-spanning-tree-step"
export "1720-blass-counting"

{` lem:spanning-tree (fggroups.tex:750).  A connected graph (V, E) (for a graph
   quotient Q of it, Connected Q) whose vertex type is an n-element set (merely
   equal to Fin n) and whose edges E(x,y) are decidable sets (decidable
   equality) merely has a spanning tree with exactly n - 1 edges.

   The conclusion (SpanningTreeWithEdges) is a SpanningTree V E (def. at line
   649, module 1105) whose edge predicate is moreover decidable (the book's
   "very often we'll require that the edge embeddings are decidable", needed
   for Nielsen–Schreier), together with k and suc k = n and an equivalence of
   the total type of tree edges with Fin k ("exactly n - 1 edges"; n = 0 is
   impossible since connected graphs have a vertex).

   Proof as in the book: by induction on k there merely is a decidable subtree
   with k + 1 vertices and k edges (TreeGrowth k); the step uses
   lem:spanning-tree-step (module 1107) with a vertex outside U found by a finite
   search (finite_quantifiers); at k + 1 = n the injective vertex inclusion of an
   n-element set into an n-element set is surjective, hence an equivalence. `}

def subgraph_vertices_decidable_equality (V : Type) (E : V → V → Type) (decV : DecidableEquality V) (H : Subgraph V E)
  : DecidableEquality (H .vertices)
  ≔ u v ↦ match decV (H .incl u) (H .incl v) [
  | inl. p ↦ inl. (embedding_injection (H .vertices) V (H .incl) (H .incl_embedding) u v p)
  | inr. n ↦ inr. (q ↦ n (refl (H .incl) q)) ]

def transported_edge_decidable (A : Type) (hA : isSet A) (decA : DecidableEquality A) (B : A → Type)
  (decB : (a : A) → DecidableEquality (B a)) (a0 a : A) (e0 : B a0) (e : B a)
  : Decidable (Σ (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e))
  ≔ match decA a0 a [
  | inl. p ↦ match decB a (transport A B a0 a p e0) e [
    | inl. r ↦ inl. (p, r)
    | inr. n ↦ inr. (t ↦ n (transport (Id A a0 a) (q ↦ Id (B a) (transport A B a0 a q e0) e) (t .fst) p
        (hA a0 a (t .fst) p) (t .snd))) ]
  | inr. n ↦ inr. (t ↦ n (t .fst)) ]

def step_edges_fwd_decidable (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (decV : DecidableEquality V) (decE : (x y : V) → DecidableEquality (E x y))
  (H : Subgraph V E) (w : V) (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0))) (u : H .vertices) (e : E (H .incl u) w)
  : Decidable (step_edges_fwd V E hV hE H (step_crossing_data V E H w hw u0 c) u e .fst)
  ≔ match c [
  | inl. e0 ↦ transported_edge_decidable (H .vertices) (step_vertices_set V E H hV)
      (subgraph_vertices_decidable_equality V E decV H) (z ↦ E (H .incl z) w) (z ↦ decE (H .incl z) w) u0 u e0 e
  | inr. _ ↦ inr. (z ↦ z) ]

def step_edges_back_decidable (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (decV : DecidableEquality V) (decE : (x y : V) → DecidableEquality (E x y))
  (H : Subgraph V E) (w : V) (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0))) (u : H .vertices) (e : E w (H .incl u))
  : Decidable (step_edges_back V E hV hE H (step_crossing_data V E H w hw u0 c) u e .fst)
  ≔ match c [
  | inl. _ ↦ inr. (z ↦ z)
  | inr. e0 ↦ transported_edge_decidable (H .vertices) (step_vertices_set V E H hV)
      (subgraph_vertices_decidable_equality V E decV H) (z ↦ E w (H .incl z)) (z ↦ decE w (H .incl z)) u0 u e0 e ]

def step_edges_decidable (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (decV : DecidableEquality V) (decE : (x y : V) → DecidableEquality (E x y))
  (H : Subgraph V E) (hdecE : DecidableSubgraphEdges V E H) (d : StepData V E H)
  : DecidableSubgraphEdges V E (step_subgraph V E hV hE H d)
  ≔ a b e ↦ match a [
  | inl. u1 ↦ match b [
    | inl. u2 ↦ hdecE u1 u2 e
    | inr. _ ↦ step_edges_fwd_decidable V E hV hE decV decE H (d .new_vertex) (d .new_vertex_outside)
        (d .old_vertex) (d .crossing) u1 e ]
  | inr. _ ↦ match b [
    | inl. u2 ↦ step_edges_back_decidable V E hV hE decV decE H (d .new_vertex) (d .new_vertex_outside)
        (d .old_vertex) (d .crossing) u2 e
    | inr. _ ↦ inr. (z ↦ z) ] ]

{` ---------- The induction ---------- `}

def TreeGrowth (V : Type) (E : V → V → Type) (k : Nat) : Type
  ≔ Σ (Subgraph V E) (H ↦
      Product (DecidableSubgraphVertices V E H)
        (Product (DecidableSubgraphEdges V E H)
          (Product (GraphTreeStructure (H .vertices) (subgraph_edges V E H))
            (Product (Equiv (H .vertices) (Fin (suc. k))) (Equiv (SubgraphEdgeTotal V E H) (Fin k))))))

def initial_subgraph (V : Type) (E : V → V → Type) (hV : isSet V) (v : V) : Subgraph V E
  ≔ (Unit, _ ↦ v,
     set_injection_embedding Unit V hV (_ ↦ v) (x y _ ↦ unit_prop x y),
     _ _ _ ↦ false_prop_type)

def initial_tree (V : Type) (E : V → V → Type) (hV : isSet V) (v : V)
  : GraphTreeStructure Unit (subgraph_edges V E (initial_subgraph V E hV v))
  ≔ let D ≔ subgraph_edges V E (initial_subgraph V E hV v) in
    unit_structure_tree Unit D (x ↦ x) (x y e ↦ no_edges_edge Unit x y (e .snd))
      (gq_edge_transfer Unit D (NoEdges Unit) (x y ↦ empty_equiv (D x y) (e ↦ e .snd))
        Unit (x ↦ x) (no_edges_edge Unit) (discrete_induction Unit))

def initial_edges_total (V : Type) (E : V → V → Type) (hV : isSet V) (v : V)
  : Equiv (SubgraphEdgeTotal V E (initial_subgraph V E hV v)) (Fin zero.)
  ≔ empty_equiv (SubgraphEdgeTotal V E (initial_subgraph V E hV v)) (t ↦ t .snd .snd .snd)

def fin_one_unit_equiv : Equiv Unit (Fin (suc. zero.))
  ≔ quasi_inverse_equiv Unit (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ star.)
      (u ↦ match u [ star. ↦ refl (star. : Unit) ])
      (i ↦ match i [ inl. z ↦ match z [] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ])

def tree_growth_base (V : Type) (E : V → V → Type) (decV : DecidableEquality V) (v : V) : TreeGrowth V E zero.
  ≔ let hV ≔ decidable_set_is_set V (hedberg V decV) in
    (initial_subgraph V E hV v,
     (x ↦ match decV x v [ inl. p ↦ inl. (star., p) | inr. n ↦ inr. (t ↦ n (t .snd)) ],
      (_ _ _ ↦ inr. (z ↦ z),
       (initial_tree V E hV v,
        (fin_one_unit_equiv, initial_edges_total V E hV v)))))

def graph_vertex_merely (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  : Mere V
  ≔ mere_rec (Q .carrier) (Mere V) (mere_isprop V)
      (gq_ind_prop V E Q (_ ↦ Mere V) (_ ↦ mere_isprop V) (x ↦ mere V x)) (hc .fst)

{` A vertex outside a decidable subgraph with fewer vertices than V. `}
def outside_vertex_merely (V : Type) (E : V → V → Type) (n k : Nat) (hn : Mere (Id Type V (Fin n)))
  (H : Subgraph V E) (hdec : DecidableSubgraphVertices V E H) (eU : Equiv (H .vertices) (Fin (suc. k)))
  (hk : Lt (suc. k) n)
  : Mere (Σ V (v ↦ Not (BookFiber (H .vertices) V (H .incl) v)))
  ≔ let fin ≔ (mere_rec (Id Type V (Fin n)) (IsFinite V) (mere_isprop (Σ Nat (m ↦ Id Type V (Fin m))))
        (p ↦ mere (Σ Nat (m ↦ Id Type V (Fin m))) (n, p)) hn : IsFinite V) in
    let P ≔ (x : V) ↦ BookFiber (H .vertices) V (H .incl) x in
    let q ≔ finite_quantifiers V fin in
    let notP ≔ (x : V) ↦ Not (P x) in
    match (q notP (x ↦ negation_prop (P x)) (x ↦ match hdec x [ inl. f ↦ inr. (g ↦ g f) | inr. g ↦ inl. g ])) .snd [
    | inl. t ↦ t
    | inr. none ↦
      let all : (x : V) → P x
        ≔ x ↦ match hdec x [ inl. f ↦ f | inr. g ↦ match none (mere (Σ V notP) (x, g)) [] ] in
      let be ≔ native_embedding_surjection_equiv (H .vertices) V (H .incl) (H .incl_embedding)
          (x ↦ mere (P x) (all x)) in
      let eUV ≔ native_equivalence (H .vertices) V be in
      match mere_rec (Id Type V (Fin n)) Empty empty_prop
          (p ↦ lt_irrefl n (transport Nat (m ↦ Lt m n) (suc. k) n
            (fin_equiv_cardinality (suc. k) n
              (compose_equiv (Fin (suc. k)) (H .vertices) (Fin n)
                (canonical_inverse_equiv (H .vertices) (Fin (suc. k)) eU)
                (compose_equiv (H .vertices) V (Fin n) eUV (id_to_equiv V (Fin n) p)))) hk))
          hn [] ]

def lt_suc_weaken (k n : Nat) (h : Lt (suc. k) n) : Lt k n
  ≔ le_trans (suc. k) (suc. (suc. k)) n (le_step (suc. k) (suc. k) (le_refl (suc. k))) h

def tree_growth_step (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (decV : DecidableEquality V) (decE : (x y : V) → DecidableEquality (E x y))
  (n : Nat) (hn : Mere (Id Type V (Fin n))) (k : Nat) (hk : Lt (suc. k) n) (g : TreeGrowth V E k)
  : Mere (TreeGrowth V E (suc. k))
  ≔ let hV ≔ decidable_set_is_set V (hedberg V decV) in
    let hE ≔ (x y : V) ↦ decidable_set_is_set (E x y) (hedberg (E x y) (decE x y)) in
    let H ≔ g .fst in
    let hdec ≔ g .snd .fst in
    let hdecE ≔ g .snd .snd .fst in
    let t ≔ g .snd .snd .snd .fst in
    let eU ≔ g .snd .snd .snd .snd .fst in
    let eD ≔ g .snd .snd .snd .snd .snd in
    let u ≔ equiv_inverse_map (H .vertices) (Fin (suc. k)) eU (inr. star.) in
    mere_rec (Σ V (v ↦ Not (BookFiber (H .vertices) V (H .incl) v))) (Mere (TreeGrowth V E (suc. k)))
      (mere_isprop (TreeGrowth V E (suc. k)))
      (o ↦ mere_rec (SpanningTreeStepConclusion V E hV hE H) (Mere (TreeGrowth V E (suc. k)))
        (mere_isprop (TreeGrowth V E (suc. k)))
        (r ↦ let d ≔ r .fst in
          mere (TreeGrowth V E (suc. k))
            (step_subgraph V E hV hE H d,
             (step_vertices_decidable V E hV hE decV H hdec d,
              (step_edges_decidable V E hV hE decV decE H hdecE d,
               (step_tree V E hV hE H d t,
                (sum_equiv (H .vertices) Unit (Fin (suc. k)) Unit eU (identity_equiv Unit),
                 compose_equiv (SubgraphEdgeTotal V E (step_subgraph V E hV hE H d)) (Sum (SubgraphEdgeTotal V E H) Unit)
                   (Fin (suc. k)) (r .snd .fst)
                   (sum_equiv (SubgraphEdgeTotal V E H) Unit (Fin k) Unit eD (identity_equiv Unit))))))))
        (spanning_tree_step V E Q hc decV hE H hdec u (o .fst) (o .snd)))
      (outside_vertex_merely V E n k hn H hdec eU hk)

def tree_growth (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (decV : DecidableEquality V) (decE : (x y : V) → DecidableEquality (E x y))
  (n : Nat) (hn : Mere (Id Type V (Fin n))) (k : Nat) : Lt k n → Mere (TreeGrowth V E k)
  ≔ match k [
  | zero. ↦ _ ↦ mere_rec V (Mere (TreeGrowth V E zero.)) (mere_isprop (TreeGrowth V E zero.))
      (v ↦ mere (TreeGrowth V E zero.) (tree_growth_base V E decV v)) (graph_vertex_merely V E Q hc)
  | suc. k ↦ h ↦ mere_rec (TreeGrowth V E k) (Mere (TreeGrowth V E (suc. k))) (mere_isprop (TreeGrowth V E (suc. k)))
      (g ↦ tree_growth_step V E Q hc decV decE n hn k h g)
      (tree_growth V E Q hc decV decE n hn k (lt_suc_weaken k n h)) ]

{` ---------- Full trees ---------- `}

def fsg_map (U V : Type) (f : U → V) (n : Nat) (eU : Equiv U (Fin n)) (p : Id Type V (Fin n)) (j : Fin n) : Fin n
  ≔ id_to_equiv V (Fin n) p .map (f (equiv_inverse_map U (Fin n) eU j))

def fsg_injective (U V : Type) (f : U → V) (finj : PathReflecting U V f) (n : Nat) (eU : Equiv U (Fin n))
  (p : Id Type V (Fin n)) : PathReflecting (Fin n) (Fin n) (fsg_map U V f n eU p)
  ≔ j j' q ↦ fsc_inverse_map_injective U (Fin n) eU j j'
      (finj (equiv_inverse_map U (Fin n) eU j) (equiv_inverse_map U (Fin n) eU j')
        (equiv_path_reflecting V (Fin n) (id_to_equiv V (Fin n) p)
          (f (equiv_inverse_map U (Fin n) eU j)) (f (equiv_inverse_map U (Fin n) eU j')) q))

def fsg_fiber_from (U V : Type) (f : U → V) (n : Nat) (eU : Equiv U (Fin n)) (p : Id Type V (Fin n)) (x : V)
  (r : BookFiber (Fin n) (Fin n) (fsg_map U V f n eU p) (id_to_equiv V (Fin n) p .map x)) : BookFiber U V f x
  ≔ (equiv_inverse_map U (Fin n) eU (r .fst),
     equiv_path_reflecting V (Fin n) (id_to_equiv V (Fin n) p) x (f (equiv_inverse_map U (Fin n) eU (r .fst))) (r .snd))

{` An injection between n-element sets is surjective (via Blass counting, module 1720). `}
def equal_card_injection_fiber (U V : Type) (f : U → V) (finj : PathReflecting U V f) (n : Nat)
  (eU : Equiv U (Fin n)) (p : Id Type V (Fin n)) (x : V) : BookFiber U V f x
  ≔ fsg_fiber_from U V f n eU p x
      (bsix_injection_full n (fsg_map U V f n eU p) (fsg_injective U V f finj n eU p) (id_to_equiv V (Fin n) p .map x))

def full_subgraph_surjective (V : Type) (E : V → V → Type) (m : Nat) (hn : Mere (Id Type V (Fin (suc. m))))
  (H : Subgraph V E) (eU : Equiv (H .vertices) (Fin (suc. m))) (x : V)
  : BookFiber (H .vertices) V (H .incl) x
  ≔ mere_rec (Id Type V (Fin (suc. m))) (BookFiber (H .vertices) V (H .incl) x) (H .incl_embedding x)
      (p ↦ equal_card_injection_fiber (H .vertices) V (H .incl)
        (embedding_injection (H .vertices) V (H .incl) (H .incl_embedding)) (suc. m) eU p x) hn

{` lem:spanning-tree. `}
def SpanningTreeWithEdges (V : Type) (E : V → V → Type) (n : Nat) : Type
  ≔ Σ (SpanningTree V E) (T ↦
      Product (DecidableSubgraphEdges V E (T .fst))
        (Σ Nat (k ↦ Product (Id Nat (suc. k) n) (Equiv (SubgraphEdgeTotal V E (T .fst)) (Fin k)))))

def finite_of_card (V : Type) (n : Nat) (hn : Mere (Id Type V (Fin n))) : IsFinite V
  ≔ mere_rec (Id Type V (Fin n)) (IsFinite V) (mere_isprop (Σ Nat (m ↦ Id Type V (Fin m))))
      (p ↦ mere (Σ Nat (m ↦ Id Type V (Fin m))) (n, p)) hn

def spanning_tree (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (n : Nat) (hn : Mere (Id Type V (Fin n))) (decE : (x y : V) → DecidableEquality (E x y))
  : Mere (SpanningTreeWithEdges V E n)
  ≔ let decV ≔ finite_decidable_equality V (finite_of_card V n hn) in
    match n [
    | zero. ↦ mere_rec V (Mere (SpanningTreeWithEdges V E zero.)) (mere_isprop (SpanningTreeWithEdges V E zero.))
        (v ↦ match mere_rec (Id Type V (Fin zero.)) Empty empty_prop (p ↦ transport Type (X ↦ X) V (Fin zero.) p v) hn [])
        (graph_vertex_merely V E Q hc)
    | suc. m ↦ mere_rec (TreeGrowth V E m) (Mere (SpanningTreeWithEdges V E (suc. m)))
        (mere_isprop (SpanningTreeWithEdges V E (suc. m)))
        (g ↦
          let H ≔ g .fst in
          mere (SpanningTreeWithEdges V E (suc. m))
            ((H, (g .snd .snd .snd .fst,
                  native_embedding_surjection_equiv (H .vertices) V (H .incl) (H .incl_embedding)
                    (x ↦ mere (BookFiber (H .vertices) V (H .incl) x)
                      (full_subgraph_surjective V E m hn H (g .snd .snd .snd .snd .fst) x)) .equiv)),
             (g .snd .snd .fst, (m, (refl (suc. m : Nat), g .snd .snd .snd .snd .snd)))))
        (tree_growth V E Q hc decV (x y ↦ decE x y) (suc. m) hn m (le_refl (suc. m))) ]
