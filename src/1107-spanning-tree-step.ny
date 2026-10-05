export "1106-crossing-edge"

{` lem:spanning-tree-step (fggroups.tex:712).

   Setting: a connected graph (V, E) with V of decidable equality and E a family of
   sets; a subgraph H = (U, D) whose vertex embedding is decidable; u ∈ U and
   v ∈ V \ U.  The lemma: there merely exists a larger subgraph with exactly one
   more vertex and one more edge, (U ⊔ 1, D ⊔ 1), such that the induced map
   U/D → (U ⊔ 1)/(D ⊔ 1) is an equivalence.

   Formalization.  StepData H records the new vertex w ∉ U, the old vertex u0
   and the crossing edge (from u0 to w or from w to u0).  step_subgraph H d is
   the larger subgraph: its vertex type is literally U ⊔ 1 (inl u ↦ h u,
   inr _ ↦ w), the old edges are kept on inl × inl, and the only new edge is the
   crossing edge (predicate "e is the transport of the crossing edge").
   spanning_tree_step proves mere existence of StepData (via
   lem:crossing-edge, with V ≃ U ⊔ (V \ U) by decidability) and, for every
   StepData:
   - step_edge_total: the edges of the new subgraph are D ⊔ 1;
   - step_quotient: for EVERY graph quotient R of (U, D), the carrier R itself,
     with the vertex map extended by [inr _] ↦ [u0], is a graph quotient of
     (U ⊔ 1, D ⊔ 1).  This is "the induced map U/D → (U⊔1)/(D⊔1) is an
     equivalence" (the induced map is the identity of R, compatible with the
     inclusion of vertices); it is proved, as in the book, by
     xca:graph-quotient-in-steps and xca:graph-quotient-whisker (module 1103);
   - step_vertices_decidable: the new vertex embedding is again decidable. `}

{` ---------- Generic helpers ---------- `}

def embedding_domain_set (A B : Type) (f : A → B) (h : IsEmbedding A B f) (hB : isSet B) : isSet A
  ≔ x y p q ↦
    let e ≔ native_equivalence (Id A x y) (Id B (f x) (f y)) (embedding_on_paths A B f h x y) in
    concat (Id A x y) p (equiv_inverse_map (Id A x y) (Id B (f x) (f y)) e (e .map p)) q
      (inverse (Id A x y) (equiv_inverse_map (Id A x y) (Id B (f x) (f y)) e (e .map p)) p
        (equiv_retraction (Id A x y) (Id B (f x) (f y)) e p))
      (concat (Id A x y) (equiv_inverse_map (Id A x y) (Id B (f x) (f y)) e (e .map p))
        (equiv_inverse_map (Id A x y) (Id B (f x) (f y)) e (e .map q)) q
        (refl (equiv_inverse_map (Id A x y) (Id B (f x) (f y)) e) (hB (f x) (f y) (e .map p) (e .map q)))
        (equiv_retraction (Id A x y) (Id B (f x) (f y)) e q))

def path_inverse_equiv (A : Type) (x y : A) : Equiv (Id A x y) (Id A y x)
  ≔ quasi_inverse_equiv (Id A x y) (Id A y x) (inverse A x y) (inverse A y x)
      (inverse_inverse A x y) (inverse_inverse A y x)

def empty_sum_equiv (A : Type) : Equiv (Sum Empty A) A
  ≔ quasi_inverse_equiv (Sum Empty A) A (s ↦ match s [ inl. z ↦ match z [] | inr. a ↦ a ]) (a ↦ inr. a)
      (s ↦ match s [ inl. z ↦ match z [] | inr. a ↦ refl (inr. a : Sum Empty A) ]) (a ↦ refl a)

def sum_empty_equiv (A : Type) : Equiv (Sum A Empty) A
  ≔ quasi_inverse_equiv (Sum A Empty) A (s ↦ match s [ inl. a ↦ a | inr. z ↦ match z [] ]) (a ↦ inl. a)
      (s ↦ match s [ inl. a ↦ refl (inl. a : Sum A Empty) | inr. z ↦ match z [] ]) (a ↦ refl a)

def empty_equiv (A : Type) (h : A → Empty) : Equiv A Empty
  ≔ quasi_inverse_equiv A Empty h (z ↦ match z []) (a ↦ match h a []) (z ↦ match z [])

{` Σ_e Σ_{p : a0 = a} (tr_p e0 = e) ≃ (a0 = a). `}
def transported_edge_equiv (A : Type) (B : A → Type) (a0 a : A) (e0 : B a0)
  : Equiv (Σ (B a) (e ↦ Σ (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e))) (Id A a0 a)
  ≔ compose_equiv (Σ (B a) (e ↦ Σ (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e)))
      (Σ (Id A a0 a) (p ↦ Σ (B a) (e ↦ Id (B a) (transport A B a0 a p e0) e))) (Id A a0 a)
      (quasi_inverse_equiv (Σ (B a) (e ↦ Σ (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e)))
        (Σ (Id A a0 a) (p ↦ Σ (B a) (e ↦ Id (B a) (transport A B a0 a p e0) e)))
        (t ↦ (t .snd .fst, (t .fst, t .snd .snd))) (t ↦ (t .snd .fst, (t .fst, t .snd .snd)))
        (t ↦ refl t) (t ↦ refl t))
      (contractible_fiber_projection (Id A a0 a) (p ↦ Σ (B a) (e ↦ Id (B a) (transport A B a0 a p e0) e))
        (p ↦ iscontr_idfrom (B a) (transport A B a0 a p e0)))

def transported_edge_prop (A : Type) (hA : isSet A) (B : A → Type) (hB : (a : A) → isSet (B a)) (a0 a : A) (e0 : B a0)
  (e : B a) : isProp (Σ (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e))
  ≔ x y ↦ (hA a0 a (x .fst) (y .fst),
      pathover_of_eq (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e) (x .fst) (y .fst)
        (hA a0 a (x .fst) (y .fst)) (x .snd) (y .snd)
        (hB a (transport A B a0 a (y .fst) e0) e
          (transport (Id A a0 a) (p ↦ Id (B a) (transport A B a0 a p e0) e) (x .fst) (y .fst)
            (hA a0 a (x .fst) (y .fst)) (x .snd)) (y .snd)))

{` ---------- Step data and the extended subgraph ---------- `}

def StepData (V : Type) (E : V → V → Type) (H : Subgraph V E) : Type ≔ sig (
  new_vertex : V,
  new_vertex_outside : Not (BookFiber (H .vertices) V (H .incl) new_vertex),
  old_vertex : H .vertices,
  crossing : Sum (E (H .incl old_vertex) new_vertex) (E new_vertex (H .incl old_vertex)) )

def step_incl (V : Type) (E : V → V → Type) (H : Subgraph V E) (d : StepData V E H) (x : Sum (H .vertices) Unit) : V
  ≔ match x [ inl. u ↦ H .incl u | inr. _ ↦ d .new_vertex ]

def false_prop_type : PropTypes ≔ (Empty, empty_prop)

def StepNewEdgeFwd (V : Type) (E : V → V → Type) (H : Subgraph V E) (u0 : H .vertices) (w : V)
  (e0 : E (H .incl u0) w) (u : H .vertices) (e : E (H .incl u) w) : Type
  ≔ Σ (Id (H .vertices) u0 u) (p ↦ Id (E (H .incl u) w) (transport (H .vertices) (z ↦ E (H .incl z) w) u0 u p e0) e)

def StepNewEdgeBack (V : Type) (E : V → V → Type) (H : Subgraph V E) (u0 : H .vertices) (w : V)
  (e0 : E w (H .incl u0)) (u : H .vertices) (e : E w (H .incl u)) : Type
  ≔ Σ (Id (H .vertices) u0 u) (p ↦ Id (E w (H .incl u)) (transport (H .vertices) (z ↦ E w (H .incl z)) u0 u p e0) e)

def step_vertices_set (V : Type) (E : V → V → Type) (H : Subgraph V E) (hV : isSet V) : isSet (H .vertices)
  ≔ embedding_domain_set (H .vertices) V (H .incl) (H .incl_embedding) hV

def step_edges_fwd (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (u : H .vertices) (e : E (H .incl u) (d .new_vertex)) : PropTypes
  ≔ match d .crossing [
  | inl. e0 ↦ (StepNewEdgeFwd V E H (d .old_vertex) (d .new_vertex) e0 u e,
      transported_edge_prop (H .vertices) (step_vertices_set V E H hV) (z ↦ E (H .incl z) (d .new_vertex))
        (z ↦ hE (H .incl z) (d .new_vertex)) (d .old_vertex) u e0 e)
  | inr. _ ↦ false_prop_type ]

def step_edges_back (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (u : H .vertices) (e : E (d .new_vertex) (H .incl u)) : PropTypes
  ≔ match d .crossing [
  | inl. _ ↦ false_prop_type
  | inr. e0 ↦ (StepNewEdgeBack V E H (d .old_vertex) (d .new_vertex) e0 u e,
      transported_edge_prop (H .vertices) (step_vertices_set V E H hV) (z ↦ E (d .new_vertex) (H .incl z))
        (z ↦ hE (d .new_vertex) (H .incl z)) (d .old_vertex) u e0 e) ]

def step_edges (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (a b : Sum (H .vertices) Unit)
  (e : E (step_incl V E H d a) (step_incl V E H d b)) : PropTypes
  ≔ match a [
  | inl. u1 ↦ match b [
    | inl. u2 ↦ H .edges u1 u2 e
    | inr. _ ↦ step_edges_fwd V E hV hE H d u1 e ]
  | inr. _ ↦ match b [
    | inl. u2 ↦ step_edges_back V E hV hE H d u2 e
    | inr. _ ↦ false_prop_type ] ]

def step_incl_injective (V : Type) (E : V → V → Type) (H : Subgraph V E) (d : StepData V E H)
  (a b : Sum (H .vertices) Unit) (p : Id V (step_incl V E H d a) (step_incl V E H d b)) : Id (Sum (H .vertices) Unit) a b
  ≔ match a [
  | inl. u1 ↦ match b [
    | inl. u2 ↦ refl ((u : H .vertices) ↦ (inl. u : Sum (H .vertices) Unit))
        (embedding_injection (H .vertices) V (H .incl) (H .incl_embedding) u1 u2 p)
    | inr. _ ↦ match d .new_vertex_outside (u1, inverse V (H .incl u1) (d .new_vertex) p) [] ]
  | inr. s1 ↦ match b [
    | inl. u2 ↦ match d .new_vertex_outside (u2, p) []
    | inr. s2 ↦ match s1, s2 [ star., star. ↦ refl (inr. star. : Sum (H .vertices) Unit) ] ] ]

def step_subgraph (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) : Subgraph V E
  ≔ (Sum (H .vertices) Unit, step_incl V E H d,
     set_injection_embedding (Sum (H .vertices) Unit) V hV (step_incl V E H d) (step_incl_injective V E H d),
     step_edges V E hV hE H d)

{` ---------- Lifted old edges and their image under the whisker map ---------- `}

def lifted_edges (U : Type) (D : U → U → Type) (x y : Sum U Unit) : Type ≔ match x [
| inl. u1 ↦ match y [ inl. u2 ↦ D u1 u2 | inr. _ ↦ Empty ]
| inr. _ ↦ Empty ]

def lifted_image_to (U : Type) (D : U → U → Type) (u0 : U) (a b : U) (x y : Sum U Unit) (dd : lifted_edges U D x y)
  (p : Id U (whisker_vertex U u0 x) a) (q : Id U (whisker_vertex U u0 y) b) : D a b
  ≔ match x [
  | inl. u1 ↦ match y [
    | inl. u2 ↦ transport U (z ↦ D z b) u1 a p (transport U (z ↦ D u1 z) u2 b q dd)
    | inr. _ ↦ match dd [] ]
  | inr. _ ↦ match dd [] ]

def lifted_image_from (U : Type) (D : U → U → Type) (u0 : U) (a b : U) (dd : D a b)
  : ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) a b
  ≔ (inl. a, (inl. b, (dd, (refl a, refl b))))

def lifted_image_to_from (U : Type) (D : U → U → Type) (u0 : U) (a b : U) (dd : D a b)
  : Id (D a b) (lifted_image_to U D u0 a b (inl. a) (inl. b) dd (refl a) (refl b)) dd
  ≔ concat (D a b) (transport U (z ↦ D z b) a a (refl a) (transport U (z ↦ D a z) b b (refl b) dd))
      (transport U (z ↦ D a z) b b (refl b) dd) dd
      (transport_refl U (z ↦ D z b) a (transport U (z ↦ D a z) b b (refl b) dd))
      (transport_refl U (z ↦ D a z) b dd)

def lifted_image_from_to (U : Type) (D : U → U → Type) (u0 : U) (x y : Sum U Unit) (dd : lifted_edges U D x y)
  (a b : U) (p : Id U (whisker_vertex U u0 x) a) (q : Id U (whisker_vertex U u0 y) b)
  : Id (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) a b)
      (lifted_image_from U D u0 a b (lifted_image_to U D u0 a b x y dd p q)) (x, (y, (dd, (p, q))))
  ≔ match x [
  | inl. u1 ↦ match y [
    | inl. u2 ↦
      J U u1 (a p ↦ Id (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) a b)
          (lifted_image_from U D u0 a b (lifted_image_to U D u0 a b (inl. u1) (inl. u2) dd p q))
          (inl. u1, (inl. u2, (dd, (p, q)))))
        (J U u2 (b q ↦ Id (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) u1 b)
            (lifted_image_from U D u0 u1 b (lifted_image_to U D u0 u1 b (inl. u1) (inl. u2) dd (refl u1) q))
            (inl. u1, (inl. u2, (dd, (refl u1, q)))))
          (refl ((z : D u1 u2) ↦ (inl. u1, (inl. u2, (z, (refl u1, refl u2))))
              : D u1 u2 → ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) u1 u2)
            (lifted_image_to_from U D u0 u1 u2 dd))
          b q)
        a p
    | inr. _ ↦ match dd [] ]
  | inr. _ ↦ match dd [] ]

def lifted_image_equiv (U : Type) (D : U → U → Type) (u0 : U) (a b : U)
  : Equiv (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) a b) (D a b)
  ≔ quasi_inverse_equiv (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D) a b) (D a b)
      (t ↦ lifted_image_to U D u0 a b (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd))
      (lifted_image_from U D u0 a b)
      (t ↦ lifted_image_from_to U D u0 (t .fst) (t .snd .fst) (t .snd .snd .fst) a b (t .snd .snd .snd .fst) (t .snd .snd .snd .snd))
      (lifted_image_to_from U D u0 a b)

{` ---------- The new edge families ---------- `}

def step_crossing_data (V : Type) (E : V → V → Type) (H : Subgraph V E) (w : V)
  (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0))) : StepData V E H
  ≔ (w, hw, u0, c)

def step_whisker_family (U : Type) (u0 : U) (A B : Type) (c : Sum A B) (x y : Sum U Unit) : Type
  ≔ match c [ inl. _ ↦ WhiskerEdges U u0 x y | inr. _ ↦ WhiskerRevEdges U u0 x y ]

def step_new_edges_equiv (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (w : V) (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0))) (a b : Sum (H .vertices) Unit)
  : Equiv (subgraph_edges V E (step_subgraph V E hV hE H (step_crossing_data V E H w hw u0 c)) a b)
      (SumEdges (Sum (H .vertices) Unit) (step_whisker_family (H .vertices) u0 (E (H .incl u0) w) (E w (H .incl u0)) c)
        (lifted_edges (H .vertices) (subgraph_edges V E H)) a b)
  ≔ let U ≔ H .vertices in
    let D ≔ subgraph_edges V E H in
    match c [
    | inl. e0 ↦ match a [
      | inl. u1 ↦ match b [
        | inl. u2 ↦ canonical_inverse_equiv (Sum Empty (D u1 u2)) (D u1 u2) (empty_sum_equiv (D u1 u2))
        | inr. s ↦ compose_equiv (Σ (E (H .incl u1) w) (e ↦ StepNewEdgeFwd V E H u0 w e0 u1 e)) (Id U u1 u0)
            (Sum (Id U u1 u0) Empty)
            (compose_equiv (Σ (E (H .incl u1) w) (e ↦ StepNewEdgeFwd V E H u0 w e0 u1 e)) (Id U u0 u1) (Id U u1 u0)
              (transported_edge_equiv U (z ↦ E (H .incl z) w) u0 u1 e0) (path_inverse_equiv U u0 u1))
            (canonical_inverse_equiv (Sum (Id U u1 u0) Empty) (Id U u1 u0) (sum_empty_equiv (Id U u1 u0))) ]
      | inr. s ↦ match b [
        | inl. u2 ↦ compose_equiv (Σ (E w (H .incl u2)) (_ ↦ Empty)) Empty (Sum Empty Empty)
            (empty_equiv (Σ (E w (H .incl u2)) (_ ↦ Empty)) (t ↦ t .snd))
            (canonical_inverse_equiv (Sum Empty Empty) Empty (sum_empty_equiv Empty))
        | inr. _ ↦ compose_equiv (Σ (E w w) (_ ↦ Empty)) Empty (Sum Empty Empty)
            (empty_equiv (Σ (E w w) (_ ↦ Empty)) (t ↦ t .snd))
            (canonical_inverse_equiv (Sum Empty Empty) Empty (sum_empty_equiv Empty)) ] ]
    | inr. e0 ↦ match a [
      | inl. u1 ↦ match b [
        | inl. u2 ↦ canonical_inverse_equiv (Sum Empty (D u1 u2)) (D u1 u2) (empty_sum_equiv (D u1 u2))
        | inr. s ↦ compose_equiv (Σ (E (H .incl u1) w) (_ ↦ Empty)) Empty (Sum Empty Empty)
            (empty_equiv (Σ (E (H .incl u1) w) (_ ↦ Empty)) (t ↦ t .snd))
            (canonical_inverse_equiv (Sum Empty Empty) Empty (sum_empty_equiv Empty)) ]
      | inr. s ↦ match b [
        | inl. u2 ↦ compose_equiv (Σ (E w (H .incl u2)) (e ↦ StepNewEdgeBack V E H u0 w e0 u2 e)) (Id U u0 u2)
            (Sum (Id U u0 u2) Empty)
            (transported_edge_equiv U (z ↦ E w (H .incl z)) u0 u2 e0)
            (canonical_inverse_equiv (Sum (Id U u0 u2) Empty) (Id U u0 u2) (sum_empty_equiv (Id U u0 u2)))
        | inr. _ ↦ compose_equiv (Σ (E w w) (_ ↦ Empty)) Empty (Sum Empty Empty)
            (empty_equiv (Σ (E w w) (_ ↦ Empty)) (t ↦ t .snd))
            (canonical_inverse_equiv (Sum Empty Empty) Empty (sum_empty_equiv Empty)) ] ] ]

{` ---------- The quotient of the extended subgraph ---------- `}

def StepQuotientExtension (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (R : GraphQuotientSignature (H .vertices) (subgraph_edges V E H)) : Type
  ≔ Σ ((a b : Sum (H .vertices) Unit) → subgraph_edges V E (step_subgraph V E hV hE H d) a b
          → Id (R .carrier) (R .vertex (whisker_vertex (H .vertices) (d .old_vertex) a))
              (R .vertex (whisker_vertex (H .vertices) (d .old_vertex) b)))
      (ed ↦ GraphQuotientInduction (Sum (H .vertices) Unit) (subgraph_edges V E (step_subgraph V E hV hE H d))
        (R .carrier) (x ↦ R .vertex (whisker_vertex (H .vertices) (d .old_vertex) x)) ed)

def step_image_quotient (U : Type) (D : U → U → Type) (u0 : U) (R : GraphQuotientSignature U D)
  : GraphQuotientSignature U (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D))
  ≔ (R .carrier, R .vertex, a b t ↦ R .edge a b (lifted_image_equiv U D u0 a b .map t),
     gq_edge_transfer U (ImageEdges (Sum U Unit) U (whisker_vertex U u0) (lifted_edges U D)) D
       (lifted_image_equiv U D u0) (R .carrier) (R .vertex) (R .edge) (R .induction))

def step_quotient_at (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (w : V) (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0)))
  (R : GraphQuotientSignature (H .vertices) (subgraph_edges V E H))
  : StepQuotientExtension V E hV hE H (step_crossing_data V E H w hw u0 c) R
  ≔ let U ≔ H .vertices in
    let D ≔ subgraph_edges V E H in
    let Q1 ≔ step_image_quotient U D u0 R in
    let psi ≔ step_new_edges_equiv V E hV hE H w hw u0 c in
    match c [
    | inl. e0 ↦
      let S ≔ steps_signature (Sum U Unit) (WhiskerEdges U u0) (lifted_edges U D) (whisker_signature U u0) Q1 in
      (a b e ↦ S .edge a b (psi a b .map e),
       gq_edge_transfer (Sum U Unit) (subgraph_edges V E (step_subgraph V E hV hE H (step_crossing_data V E H w hw u0 (inl. e0))))
         (SumEdges (Sum U Unit) (WhiskerEdges U u0) (lifted_edges U D)) psi (S .carrier) (S .vertex) (S .edge) (S .induction))
    | inr. e0 ↦
      let S ≔ steps_signature (Sum U Unit) (WhiskerRevEdges U u0) (lifted_edges U D) (whisker_rev_signature U u0) Q1 in
      (a b e ↦ S .edge a b (psi a b .map e),
       gq_edge_transfer (Sum U Unit) (subgraph_edges V E (step_subgraph V E hV hE H (step_crossing_data V E H w hw u0 (inr. e0))))
         (SumEdges (Sum U Unit) (WhiskerRevEdges U u0) (lifted_edges U D)) psi (S .carrier) (S .vertex) (S .edge) (S .induction)) ]

def step_quotient (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (R : GraphQuotientSignature (H .vertices) (subgraph_edges V E H))
  : StepQuotientExtension V E hV hE H d R
  ≔ step_quotient_at V E hV hE H (d .new_vertex) (d .new_vertex_outside) (d .old_vertex) (d .crossing) R

{` Trees stay trees. `}
def step_tree (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H) (t : GraphTreeStructure (H .vertices) (subgraph_edges V E H))
  : GraphTreeStructure (Sum (H .vertices) Unit) (subgraph_edges V E (step_subgraph V E hV hE H d))
  ≔ let r ≔ step_quotient V E hV hE H d (graph_tree_signature (H .vertices) (subgraph_edges V E H) t) in
    unit_structure_tree (Sum (H .vertices) Unit) (subgraph_edges V E (step_subgraph V E hV hE H d))
      (_ ↦ star.) (r .fst) (r .snd)

{` ---------- Exactly one more edge ---------- `}

def whisker_total_to (U : Type) (u0 : U) (a b : Sum U Unit) (e : WhiskerEdges U u0 a b) : Σ U (y ↦ Id U y u0)
  ≔ match a [ inl. y ↦ match b [ inl. _ ↦ match e [] | inr. _ ↦ (y, e) ] | inr. _ ↦ match e [] ]

def whisker_total_roundtrip (U : Type) (u0 : U) (a b : Sum U Unit) (e : WhiskerEdges U u0 a b)
  : Id (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerEdges U u0 a b)))
      (inl. (whisker_total_to U u0 a b e .fst), (inr. star., whisker_total_to U u0 a b e .snd)) (a, (b, e))
  ≔ match a [
  | inl. y ↦ match b [ inl. _ ↦ match e [] | inr. s ↦ match s [ star. ↦ refl ((inl. y, (inr. star., e)) : Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerEdges U u0 a b))) ] ]
  | inr. _ ↦ match e [] ]

def whisker_total_equiv (U : Type) (u0 : U)
  : Equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerEdges U u0 a b))) (Σ U (y ↦ Id U y u0))
  ≔ quasi_inverse_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerEdges U u0 a b))) (Σ U (y ↦ Id U y u0))
      (t ↦ whisker_total_to U u0 (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ (inl. (t .fst), (inr. star., t .snd)))
      (t ↦ whisker_total_roundtrip U u0 (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ refl t)

def whisker_rev_total_to (U : Type) (u0 : U) (a b : Sum U Unit) (e : WhiskerRevEdges U u0 a b) : Σ U (y ↦ Id U u0 y)
  ≔ match a [ inl. _ ↦ match e [] | inr. _ ↦ match b [ inl. y ↦ (y, e) | inr. _ ↦ match e [] ] ]

def whisker_rev_total_roundtrip (U : Type) (u0 : U) (a b : Sum U Unit) (e : WhiskerRevEdges U u0 a b)
  : Id (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerRevEdges U u0 a b)))
      (inr. star., (inl. (whisker_rev_total_to U u0 a b e .fst), whisker_rev_total_to U u0 a b e .snd)) (a, (b, e))
  ≔ match a [
  | inl. _ ↦ match e []
  | inr. s ↦ match s [ star. ↦ match b [ inl. y ↦ refl ((inr. star., (inl. y, e)) : Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerRevEdges U u0 a b))) | inr. _ ↦ match e [] ] ] ]

def whisker_rev_total_equiv (U : Type) (u0 : U)
  : Equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerRevEdges U u0 a b))) (Σ U (y ↦ Id U u0 y))
  ≔ quasi_inverse_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerRevEdges U u0 a b))) (Σ U (y ↦ Id U u0 y))
      (t ↦ whisker_rev_total_to U u0 (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ (inr. star., (inl. (t .fst), t .snd)))
      (t ↦ whisker_rev_total_roundtrip U u0 (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ refl t)

def step_whisker_total_unit (U : Type) (u0 : U) (A B : Type) (c : Sum A B)
  : Equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ step_whisker_family U u0 A B c a b))) Unit
  ≔ match c [
  | inl. _ ↦ compose_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerEdges U u0 a b))) (Σ U (y ↦ Id U y u0)) Unit
      (whisker_total_equiv U u0) (contractible_unit_equiv (Σ U (y ↦ Id U y u0)) (path_to_contractible U u0))
  | inr. _ ↦ compose_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ WhiskerRevEdges U u0 a b))) (Σ U (y ↦ Id U u0 y)) Unit
      (whisker_rev_total_equiv U u0) (contractible_unit_equiv (Σ U (y ↦ Id U u0 y)) (iscontr_idfrom U u0)) ]

def lifted_total_to (U : Type) (D : U → U → Type) (a b : Sum U Unit) (e : lifted_edges U D a b)
  : Σ U (u1 ↦ Σ U (u2 ↦ D u1 u2))
  ≔ match a [ inl. u1 ↦ match b [ inl. u2 ↦ (u1, (u2, e)) | inr. _ ↦ match e [] ] | inr. _ ↦ match e [] ]

def lifted_total_roundtrip (U : Type) (D : U → U → Type) (a b : Sum U Unit) (e : lifted_edges U D a b)
  : Id (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ lifted_edges U D a b)))
      (inl. (lifted_total_to U D a b e .fst), (inl. (lifted_total_to U D a b e .snd .fst), lifted_total_to U D a b e .snd .snd))
      (a, (b, e))
  ≔ match a [
  | inl. u1 ↦ match b [ inl. u2 ↦ refl ((inl. u1, (inl. u2, e)) : Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ lifted_edges U D a b))) | inr. _ ↦ match e [] ]
  | inr. _ ↦ match e [] ]

def lifted_total_equiv (U : Type) (D : U → U → Type)
  : Equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ lifted_edges U D a b))) (Σ U (u1 ↦ Σ U (u2 ↦ D u1 u2)))
  ≔ quasi_inverse_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ lifted_edges U D a b))) (Σ U (u1 ↦ Σ U (u2 ↦ D u1 u2)))
      (t ↦ lifted_total_to U D (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ (inl. (t .fst), (inl. (t .snd .fst), t .snd .snd)))
      (t ↦ lifted_total_roundtrip U D (t .fst) (t .snd .fst) (t .snd .snd))
      (t ↦ refl t)

def sigma2_sum_to (A : Type) (F G : A → A → Type) (a b : A) (s : Sum (F a b) (G a b))
  : Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b)))
  ≔ match s [ inl. f ↦ inl. (a, (b, f)) | inr. g ↦ inr. (a, (b, g)) ]

def sigma2_sum_from (A : Type) (F G : A → A → Type)
  (s : Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b)))) : Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b)))
  ≔ match s [ inl. t ↦ (t .fst, (t .snd .fst, inl. (t .snd .snd))) | inr. t ↦ (t .fst, (t .snd .fst, inr. (t .snd .snd))) ]

def sigma2_sum_roundtrip (A : Type) (F G : A → A → Type) (a b : A) (s : Sum (F a b) (G a b))
  : Id (Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b))))
      (sigma2_sum_from A F G (sigma2_sum_to A F G a b s))
      (a, (b, s))
  ≔ match s [
  | inl. f ↦ refl ((a, (b, inl. f)) : Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b))))
  | inr. g ↦ refl ((a, (b, inr. g)) : Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b)))) ]

def sigma2_sum_distribute (A : Type) (F G : A → A → Type)
  : Equiv (Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b)))) (Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b))))
  ≔ quasi_inverse_equiv (Σ A (a ↦ Σ A (b ↦ Sum (F a b) (G a b)))) (Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b))))
      (t ↦ sigma2_sum_to A F G (t .fst) (t .snd .fst) (t .snd .snd))
      (sigma2_sum_from A F G)
      (t ↦ sigma2_sum_roundtrip A F G (t .fst) (t .snd .fst) (t .snd .snd))
      (s ↦ match s [ inl. t ↦ refl (inl. t : Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b))))
                   | inr. t ↦ refl (inr. t : Sum (Σ A (a ↦ Σ A (b ↦ F a b))) (Σ A (a ↦ Σ A (b ↦ G a b)))) ])


def sum_swap_equiv (A B : Type) : Equiv (Sum A B) (Sum B A)
  ≔ quasi_inverse_equiv (Sum A B) (Sum B A)
      (s ↦ match s [ inl. a ↦ inr. a | inr. b ↦ inl. b ]) (s ↦ match s [ inl. b ↦ inr. b | inr. a ↦ inl. a ])
      (s ↦ match s [ inl. a ↦ refl (inl. a : Sum A B) | inr. b ↦ refl (inr. b : Sum A B) ])
      (s ↦ match s [ inl. b ↦ refl (inl. b : Sum B A) | inr. a ↦ refl (inr. a : Sum B A) ])

def step_edge_total_at (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (w : V) (hw : Not (BookFiber (H .vertices) V (H .incl) w)) (u0 : H .vertices)
  (c : Sum (E (H .incl u0) w) (E w (H .incl u0)))
  : Equiv (SubgraphEdgeTotal V E (step_subgraph V E hV hE H (step_crossing_data V E H w hw u0 c)))
      (Sum (SubgraphEdgeTotal V E H) Unit)
  ≔ let U ≔ H .vertices in
    let D ≔ subgraph_edges V E H in
    let H' ≔ step_subgraph V E hV hE H (step_crossing_data V E H w hw u0 c) in
    let W ≔ step_whisker_family U u0 (E (H .incl u0) w) (E w (H .incl u0)) c in
    let L ≔ lifted_edges U D in
    let psi ≔ step_new_edges_equiv V E hV hE H w hw u0 c in
    compose_equiv (SubgraphEdgeTotal V E H')
      (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ SumEdges (Sum U Unit) W L a b)))
      (Sum (SubgraphEdgeTotal V E H) Unit)
      (family_equiv (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ subgraph_edges V E H' a b))
        (a ↦ Σ (Sum U Unit) (b ↦ SumEdges (Sum U Unit) W L a b))
        (a ↦ family_equiv (Sum U Unit) (b ↦ subgraph_edges V E H' a b) (b ↦ SumEdges (Sum U Unit) W L a b) (b ↦ psi a b)))
      (compose_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ SumEdges (Sum U Unit) W L a b)))
        (Sum (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ W a b))) (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ L a b))))
        (Sum (SubgraphEdgeTotal V E H) Unit)
        (sigma2_sum_distribute (Sum U Unit) W L)
        (compose_equiv (Sum (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ W a b))) (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ L a b))))
          (Sum Unit (SubgraphEdgeTotal V E H)) (Sum (SubgraphEdgeTotal V E H) Unit)
          (sum_equiv (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ W a b))) (Σ (Sum U Unit) (a ↦ Σ (Sum U Unit) (b ↦ L a b)))
            Unit (SubgraphEdgeTotal V E H)
            (step_whisker_total_unit U u0 (E (H .incl u0) w) (E w (H .incl u0)) c) (lifted_total_equiv U D))
          (sum_swap_equiv Unit (SubgraphEdgeTotal V E H))))

def step_edge_total (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (d : StepData V E H)
  : Equiv (SubgraphEdgeTotal V E (step_subgraph V E hV hE H d)) (Sum (SubgraphEdgeTotal V E H) Unit)
  ≔ step_edge_total_at V E hV hE H (d .new_vertex) (d .new_vertex_outside) (d .old_vertex) (d .crossing)

{` ---------- Decidability of the new vertex embedding ---------- `}

def step_not_in (V : Type) (E : V → V → Type) (H : Subgraph V E) (d : StepData V E H) (x : V)
  (n : Not (BookFiber (H .vertices) V (H .incl) x)) (m : Not (Id V x (d .new_vertex)))
  (a : Sum (H .vertices) Unit) (p : Id V x (step_incl V E H d a)) : Empty
  ≔ match a [ inl. u ↦ n (u, p) | inr. _ ↦ m p ]

def step_vertices_decidable (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (decV : DecidableEquality V) (H : Subgraph V E) (hdec : DecidableSubgraphVertices V E H) (d : StepData V E H)
  : DecidableSubgraphVertices V E (step_subgraph V E hV hE H d)
  ≔ x ↦ match hdec x [
  | inl. f ↦ inl. (inl. (f .fst), f .snd)
  | inr. n ↦ match decV x (d .new_vertex) [
    | inl. p ↦ inl. (inr. star., p)
    | inr. m ↦ inr. (t ↦ step_not_in V E H d x n m (t .fst) (t .snd)) ] ]

{` ---------- V ≃ U ⊔ (V \ U) for a decidable subgraph ---------- `}

def Outside (V : Type) (E : V → V → Type) (H : Subgraph V E) : Type
  ≔ Σ V (x ↦ Not (BookFiber (H .vertices) V (H .incl) x))

def side_map (V : Type) (E : V → V → Type) (H : Subgraph V E) (s : Sum (H .vertices) (Outside V E H)) : V
  ≔ match s [ inl. u ↦ H .incl u | inr. o ↦ o .fst ]

def decide_side (V : Type) (E : V → V → Type) (H : Subgraph V E) (x : V)
  (dd : Decidable (BookFiber (H .vertices) V (H .incl) x)) : Sum (H .vertices) (Outside V E H)
  ≔ match dd [ inl. f ↦ inl. (f .fst) | inr. n ↦ inr. (x, n) ]

def decide_side_spec (V : Type) (E : V → V → Type) (H : Subgraph V E) (x : V)
  (dd : Decidable (BookFiber (H .vertices) V (H .incl) x))
  : Id V (side_map V E H (decide_side V E H x dd)) x
  ≔ match dd [ inl. f ↦ inverse V x (H .incl (f .fst)) (f .snd) | inr. n ↦ refl x ]

def decide_side_inl (V : Type) (E : V → V → Type) (H : Subgraph V E) (u : H .vertices)
  (dd : Decidable (BookFiber (H .vertices) V (H .incl) (H .incl u)))
  : Id (Sum (H .vertices) (Outside V E H)) (decide_side V E H (H .incl u) dd) (inl. u)
  ≔ match dd [
  | inl. f ↦ refl ((z : H .vertices) ↦ (inl. z : Sum (H .vertices) (Outside V E H)))
      (embedding_injection (H .vertices) V (H .incl) (H .incl_embedding) (f .fst) u
        (inverse V (H .incl u) (H .incl (f .fst)) (f .snd)))
  | inr. n ↦ match n (u, refl (H .incl u)) [] ]

def decide_side_inr (V : Type) (E : V → V → Type) (H : Subgraph V E) (x : V)
  (n : Not (BookFiber (H .vertices) V (H .incl) x))
  (dd : Decidable (BookFiber (H .vertices) V (H .incl) x))
  : Id (Sum (H .vertices) (Outside V E H)) (decide_side V E H x dd) (inr. (x, n))
  ≔ match dd [
  | inl. f ↦ match n f []
  | inr. n' ↦ refl ((m : Not (BookFiber (H .vertices) V (H .incl) x)) ↦ (inr. (x, m) : Sum (H .vertices) (Outside V E H)))
      (negation_prop (BookFiber (H .vertices) V (H .incl) x) n' n) ]

def side_equiv (V : Type) (E : V → V → Type) (H : Subgraph V E) (hdec : DecidableSubgraphVertices V E H)
  : Equiv (Sum (H .vertices) (Outside V E H)) V
  ≔ quasi_inverse_equiv (Sum (H .vertices) (Outside V E H)) V (side_map V E H)
      (x ↦ decide_side V E H x (hdec x))
      (s ↦ match s [
        | inl. u ↦ decide_side_inl V E H u (hdec (H .incl u))
        | inr. o ↦ decide_side_inr V E H (o .fst) (o .snd) (hdec (o .fst)) ])
      (x ↦ decide_side_spec V E H x (hdec x))

{` ---------- lem:spanning-tree-step ---------- `}

def SpanningTreeStepConclusion (V : Type) (E : V → V → Type) (hV : isSet V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) : Type
  ≔ Σ (StepData V E H) (d ↦
      Product (Equiv (SubgraphEdgeTotal V E (step_subgraph V E hV hE H d)) (Sum (SubgraphEdgeTotal V E H) Unit))
        ((R : GraphQuotientSignature (H .vertices) (subgraph_edges V E H)) → StepQuotientExtension V E hV hE H d R))

def step_data_merely (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (H : Subgraph V E) (hdec : DecidableSubgraphVertices V E H) (u : H .vertices) (v : V)
  (hv : Not (BookFiber (H .vertices) V (H .incl) v))
  : Mere (StepData V E H)
  ≔ mere_rec
      (Σ (H .vertices) (u0 ↦ Σ (Outside V E H) (o ↦ Sum (E (H .incl u0) (o .fst)) (E (o .fst) (H .incl u0)))))
      (Mere (StepData V E H)) (mere_isprop (StepData V E H))
      (t ↦ mere (StepData V E H) (t .snd .fst .fst, t .snd .fst .snd, t .fst, t .snd .snd))
      (crossing_edge V E Q hc (H .vertices) (Outside V E H) (side_equiv V E H hdec) u (v, hv))

def spanning_tree_step (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (decV : DecidableEquality V) (hE : (x y : V) → isSet (E x y))
  (H : Subgraph V E) (hdec : DecidableSubgraphVertices V E H) (u : H .vertices) (v : V)
  (hv : Not (BookFiber (H .vertices) V (H .incl) v))
  : Mere (SpanningTreeStepConclusion V E (decidable_set_is_set V (hedberg V decV)) hE H)
  ≔ let hV ≔ decidable_set_is_set V (hedberg V decV) in
    mere_rec (StepData V E H) (Mere (SpanningTreeStepConclusion V E hV hE H))
      (mere_isprop (SpanningTreeStepConclusion V E hV hE H))
      (d ↦ mere (SpanningTreeStepConclusion V E hV hE H)
        (d, (step_edge_total V E hV hE H d, R ↦ step_quotient V E hV hE H d R)))
      (step_data_merely V E Q hc H hdec u v hv)

{` ---------- Helpers for module 1108 (full subtrees) ---------- `}

def equiv_path_reflecting (A B : Type) (e : Equiv A B) (x y : A) (q : Id B (e .map x) (e .map y)) : Id A x y
  ≔ concat A x (equiv_inverse_map A B e (e .map x)) y (equiv_unit A B e x)
      (concat A (equiv_inverse_map A B e (e .map x)) (equiv_inverse_map A B e (e .map y)) y
        (refl (equiv_inverse_map A B e) q) (equiv_retraction A B e y))

def fsc_inverse_map_injective (A B : Type) (e : Equiv A B) (x y : B)
  (q : Id A (equiv_inverse_map A B e x) (equiv_inverse_map A B e y)) : Id B x y
  ≔ concat B x (e .map (equiv_inverse_map A B e x)) y
      (inverse B (e .map (equiv_inverse_map A B e x)) x (equiv_counit A B e x))
      (concat B (e .map (equiv_inverse_map A B e x)) (e .map (equiv_inverse_map A B e y)) y
        (refl (e .map) q) (equiv_counit A B e y))
