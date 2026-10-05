export "1110-finite-index"
export "1104-one-vertex-graphs"
export "1108-spanning-tree"

{` thm:nielsen-schreier (fggroups.tex:800), first claim.

   S a set with decidable equality, F any free group signature on S (B F_S, the
   book's HIT; e.g. the constructed one), X : B F_S → Set transitive (a
   conjugacy class of a subgroup) of finite index m (def:finite-index).  Then
   Σ_{z : B F_S} X(z) is merely equivalent to B F_T for some set T; here T even
   has decidable equality, and B F_T is the constructed classifying type
   (constructed_free_group_signature T dT, module 877; by remark 279 / module
   1104 it is equivalent to every free group signature on T).

   Proof as in the book, without any HIT hypothesis:
   1. free_flattening_signature: Σ_z X(z) is a graph quotient of (V, E) with
      V ≔ X(base), E(x,y) ≔ Σ_{s:S} (x =_X^{loop_s} y) (flattening, module 1102,
      for the one-vertex graph (1, S) of remark 279).
   2. V is finite of cardinality m, E has decidable equality, and the graph is
      connected (transitivity, lem:conistrans); lem:spanning-tree gives a
      spanning tree with decidable edge predicate (module 1108).
   3. tree_complement_signature: with E0 the tree edges and E1 the complementary
      edges (E ≃ E0 ⊔ E1 by decidability) and T ≔ total type of E1, the carrier
      of B F_T is a graph quotient of (V, E): V/E ≃ (V/E0)/E1 ≃ 1/E1 ≃ B F_T
      (xca:graph-quotient-in-steps; V/E0 is the point; remark 279).
   4. uniqueness of graph quotients gives Σ_z X(z) ≃ B F_T.
   The counting part is module 1112. `}

{` ---------- Helpers ---------- `}

def ns_sigma_decide_step (X : Type) (B : X → Type) (hX : isSet X) (dB : (x : X) → DecidableEquality (B x))
  (u v : Σ X B) (d : Decidable (Id X (u .fst) (v .fst))) : Decidable (Id (Σ X B) u v)
  ≔ match d [
  | inr. n ↦ inr. (r ↦ n (r .fst))
  | inl. e ↦ match dB (v .fst) (transport X B (u .fst) (v .fst) e (u .snd)) (v .snd) [
    | inl. q ↦ inl. (e, pathover_of_eq X B (u .fst) (v .fst) e (u .snd) (v .snd) q)
    | inr. nq ↦ inr. (r ↦ nq (concat (B (v .fst)) (transport X B (u .fst) (v .fst) e (u .snd))
        (transport X B (u .fst) (v .fst) (r .fst) (u .snd)) (v .snd)
        (transport2 X B (u .fst) (v .fst) e (r .fst) (hX (u .fst) (v .fst) e (r .fst)) (u .snd))
        (pathover_transport_equiv X B (u .fst) (v .fst) (r .fst) (u .snd) (v .snd) .map (r .snd)))) ] ]

def ns_sigma_decidable_equality (X : Type) (B : X → Type) (hX : isSet X) (dX : DecidableEquality X)
  (dB : (x : X) → DecidableEquality (B x)) : DecidableEquality (Σ X B)
  ≔ u v ↦ ns_sigma_decide_step X B hX dB u v (dX (u .fst) (v .fst))

def prop_decidable_equality (P : Type) (hP : isProp P) : DecidableEquality P ≔ x y ↦ inl. (hP x y)

def decidable_split_to (A : Type) (P : A → Type) (a : A) (da : Decidable (P a)) : Sum (Σ A P) (Σ A (a ↦ Not (P a)))
  ≔ match da [ inl. p ↦ inl. (a, p) | inr. n ↦ inr. (a, n) ]

def decidable_split_from (A : Type) (P : A → Type) (s : Sum (Σ A P) (Σ A (a ↦ Not (P a)))) : A
  ≔ match s [ inl. t ↦ t .fst | inr. t ↦ t .fst ]

def decidable_split_eta (A : Type) (P : A → Type) (a : A) (da : Decidable (P a))
  : Id A (decidable_split_from A P (decidable_split_to A P a da)) a
  ≔ match da [ inl. p ↦ refl a | inr. n ↦ refl a ]

def decidable_split_beta_in (A : Type) (P : A → Type) (hP : (a : A) → isProp (P a)) (a : A) (p : P a)
  (da : Decidable (P a))
  : Id (Sum (Σ A P) (Σ A (a ↦ Not (P a)))) (decidable_split_to A P a da) (inl. (a, p))
  ≔ match da [
  | inl. p' ↦ refl ((q : P a) ↦ (inl. (a, q) : Sum (Σ A P) (Σ A (a ↦ Not (P a))))) (hP a p' p)
  | inr. n ↦ match n p [] ]

def decidable_split_beta_out (A : Type) (P : A → Type) (a : A) (n : Not (P a)) (da : Decidable (P a))
  : Id (Sum (Σ A P) (Σ A (a ↦ Not (P a)))) (decidable_split_to A P a da) (inr. (a, n))
  ≔ match da [
  | inl. p ↦ match n p []
  | inr. n' ↦ refl ((m : Not (P a)) ↦ (inr. (a, m) : Sum (Σ A P) (Σ A (a ↦ Not (P a))))) (negation_prop (P a) n' n) ]

def decidable_split_equiv (A : Type) (P : A → Type) (hP : (a : A) → isProp (P a)) (d : (a : A) → Decidable (P a))
  : Equiv A (Sum (Σ A P) (Σ A (a ↦ Not (P a))))
  ≔ quasi_inverse_equiv A (Sum (Σ A P) (Σ A (a ↦ Not (P a))))
      (a ↦ decidable_split_to A P a (d a)) (decidable_split_from A P)
      (a ↦ decidable_split_eta A P a (d a))
      (s ↦ match s [
        | inl. t ↦ decidable_split_beta_in A P hP (t .fst) (t .snd) (d (t .fst))
        | inr. t ↦ decidable_split_beta_out A P (t .fst) (t .snd) (d (t .fst)) ])

def prop_of_equiv (A B : Type) (e : Equiv A B) (h : isProp B) : isProp A
  ≔ a a' ↦ equiv_path_reflecting A B e a a' (h (e .map a) (e .map a'))

{` ---------- Step 1: flattening for B F_S ---------- `}

def FreeFlatEdges (S : Type) (F : FreeGroupSignature S) (X : F .carrier → Type) (x y : X (F .base)) : Type
  ≔ Σ S (s ↦ Id X (F .loop s) x y)

def free_flat_vertex_equiv (S : Type) (F : FreeGroupSignature S) (X : F .carrier → Type)
  : Equiv (X (F .base)) (FlatVertices OneVertex (OneVertexEdges S) (free_to_one_vertex S F) X)
  ≔ quasi_inverse_equiv (X (F .base)) (FlatVertices OneVertex (OneVertexEdges S) (free_to_one_vertex S F) X)
      (x ↦ ((), x)) (u ↦ u .snd) (x ↦ refl x) (u ↦ refl u)

def free_flattening_signature (S : Type) (F : FreeGroupSignature S) (X : F .carrier → Type)
  : GraphQuotientSignature (X (F .base)) (FreeFlatEdges S F X)
  ≔ let Q ≔ free_to_one_vertex S F in
    let R ≔ flattening_signature OneVertex (OneVertexEdges S) Q X in
    (R .carrier, x ↦ R .vertex ((), x), x y e ↦ R .edge ((), x) ((), y) e,
     gq_vertex_transfer (X (F .base)) (FlatVertices OneVertex (OneVertexEdges S) Q X) (free_flat_vertex_equiv S F X)
       (FlatEdges OneVertex (OneVertexEdges S) Q X) (R .carrier) (R .vertex) (R .edge) (R .induction))

def free_flat_edges_decidable (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (X : F .carrier → Type)
  (hX : (z : F .carrier) → isSet (X z)) (x y : X (F .base)) : DecidableEquality (FreeFlatEdges S F X x y)
  ≔ ns_sigma_decidable_equality S (s ↦ Id X (F .loop s) x y) (decidable_set_is_set S (hedberg S dec)) dec
      (s ↦ prop_decidable_equality (Id X (F .loop s) x y)
        (prop_of_equiv (Id X (F .loop s) x y) (Id (X (F .base)) (transport (F .carrier) X (F .base) (F .base) (F .loop s) x) y)
          (pathover_transport_equiv (F .carrier) X (F .base) (F .base) (F .loop s) x y)
          (hX (F .base) (transport (F .carrier) X (F .base) (F .base) (F .loop s) x) y)))

{` ---------- Step 3: the complement of a spanning tree ---------- `}

def tree_equiv (V : Type) (E : V → V → Type) (T : SpanningTree V E) : Equiv (T .fst .vertices) V
  ≔ native_equivalence (T .fst .vertices) V (T .fst .incl, T .snd .snd)

def tree_inv (V : Type) (E : V → V → Type) (T : SpanningTree V E) (x : V) : T .fst .vertices
  ≔ equiv_inverse_map (T .fst .vertices) V (tree_equiv V E T) x

def TreeCore (V : Type) (E : V → V → Type) (T : SpanningTree V E) (x y : V) : Type
  ≔ E (T .fst .incl (tree_inv V E T x)) (T .fst .incl (tree_inv V E T y))

def TreeEdges (V : Type) (E : V → V → Type) (T : SpanningTree V E) (x y : V) : Type
  ≔ subgraph_edges V E (T .fst) (tree_inv V E T x) (tree_inv V E T y)

def ComplementEdges (V : Type) (E : V → V → Type) (T : SpanningTree V E) (x y : V) : Type
  ≔ Σ (TreeCore V E T x y) (e ↦ Not (T .fst .edges (tree_inv V E T x) (tree_inv V E T y) e .fst))

def ComplementTotal (V : Type) (E : V → V → Type) (T : SpanningTree V E) : Type
  ≔ Σ V (x ↦ Σ V (y ↦ ComplementEdges V E T x y))

def complement_total_decidable (V : Type) (E : V → V → Type) (T : SpanningTree V E) (decV : DecidableEquality V)
  (decE : (x y : V) → DecidableEquality (E x y)) : DecidableEquality (ComplementTotal V E T)
  ≔ let hV ≔ decidable_set_is_set V (hedberg V decV) in
    ns_sigma_decidable_equality V (x ↦ Σ V (y ↦ ComplementEdges V E T x y)) hV decV
      (x ↦ ns_sigma_decidable_equality V (y ↦ ComplementEdges V E T x y) hV decV
        (y ↦ ns_sigma_decidable_equality (TreeCore V E T x y)
          (e ↦ Not (T .fst .edges (tree_inv V E T x) (tree_inv V E T y) e .fst))
          (decidable_set_is_set (TreeCore V E T x y) (hedberg (TreeCore V E T x y)
            (decE (T .fst .incl (tree_inv V E T x)) (T .fst .incl (tree_inv V E T y)))))
          (decE (T .fst .incl (tree_inv V E T x)) (T .fst .incl (tree_inv V E T y)))
          (e ↦ prop_decidable_equality (Not (T .fst .edges (tree_inv V E T x) (tree_inv V E T y) e .fst))
            (negation_prop (T .fst .edges (tree_inv V E T x) (tree_inv V E T y) e .fst)))))

def tree_edge_split (V : Type) (E : V → V → Type) (T : SpanningTree V E) (hdecE : DecidableSubgraphEdges V E (T .fst))
  (x y : V) : Equiv (E x y) (SumEdges V (TreeEdges V E T) (ComplementEdges V E T) x y)
  ≔ let H ≔ T .fst in
    let u ≔ tree_inv V E T x in
    let w ≔ tree_inv V E T y in
    compose_equiv (E x y) (TreeCore V E T x y) (SumEdges V (TreeEdges V E T) (ComplementEdges V E T) x y)
      (id_to_equiv (E x y) (TreeCore V E T x y)
        (refl E (inverse V (H .incl u) x (equiv_counit (H .vertices) V (tree_equiv V E T) x))
                (inverse V (H .incl w) y (equiv_counit (H .vertices) V (tree_equiv V E T) y))))
      (decidable_split_equiv (TreeCore V E T x y) (e ↦ H .edges u w e .fst) (e ↦ H .edges u w e .snd)
        (e ↦ hdecE u w e))

def unit_one_vertex_equiv : Equiv Unit OneVertex
  ≔ quasi_inverse_equiv Unit OneVertex (_ ↦ ()) (_ ↦ star.) (u ↦ match u [ star. ↦ refl (star. : Unit) ]) (o ↦ refl o)

def image_unit_total_equiv (V : Type) (E1 : V → V → Type) (a b : Unit)
  : Equiv (ImageEdges V Unit (_ ↦ star.) E1 a b) (Σ V (x ↦ Σ V (y ↦ E1 x y)))
  ≔ quasi_inverse_equiv (ImageEdges V Unit (_ ↦ star.) E1 a b) (Σ V (x ↦ Σ V (y ↦ E1 x y)))
      (t ↦ (t .fst, (t .snd .fst, t .snd .snd .fst)))
      (c ↦ (c .fst, (c .snd .fst, (c .snd .snd, (unit_prop star. a, unit_prop star. b)))))
      (t ↦ (refl (t .fst), (refl (t .snd .fst), (refl (t .snd .snd .fst),
          (unit_set star. a (unit_prop star. a) (t .snd .snd .snd .fst),
           unit_set star. b (unit_prop star. b) (t .snd .snd .snd .snd))))))
      (c ↦ refl c)

def tree_complement_signature (V : Type) (E : V → V → Type) (decV : DecidableEquality V)
  (decE : (x y : V) → DecidableEquality (E x y)) (T : SpanningTree V E) (hdecE : DecidableSubgraphEdges V E (T .fst))
  : GraphQuotientSignature V E
  ≔ let H ≔ T .fst in
    let U ≔ H .vertices in
    let D ≔ subgraph_edges V E H in
    let E0 ≔ TreeEdges V E T in
    let E1 ≔ ComplementEdges V E T in
    let Tc ≔ ComplementTotal V E T in
    let dTc ≔ complement_total_decidable V E T decV decE in
    let Q0 : GraphQuotientSignature V E0
      ≔ (Unit, _ ↦ star., _ _ _ ↦ refl (star. : Unit),
         gq_vertex_transfer V U (canonical_inverse_equiv U V (tree_equiv V E T)) D Unit (_ ↦ star.)
           (_ _ _ ↦ refl (star. : Unit)) (T .snd .fst)) in
    let B ≔ constructed_one_vertex_quotient Tc dTc in
    let Q1 : GraphQuotientSignature Unit (ImageEdges V Unit (_ ↦ star.) E1)
      ≔ (B .carrier, _ ↦ B .vertex (), a b t ↦ B .edge () () (image_unit_total_equiv V E1 a b .map t),
         gq_edge_transfer Unit (ImageEdges V Unit (_ ↦ star.) E1) (_ _ ↦ Tc) (image_unit_total_equiv V E1)
           (B .carrier) (_ ↦ B .vertex ()) (_ _ e ↦ B .edge () () e)
           (gq_vertex_transfer Unit OneVertex unit_one_vertex_equiv (OneVertexEdges Tc) (B .carrier) (B .vertex)
             (B .edge) (B .induction))) in
    let St ≔ steps_signature V E0 E1 Q0 Q1 in
    let psi ≔ tree_edge_split V E T hdecE in
    (St .carrier, St .vertex, x y e ↦ St .edge x y (psi x y .map e),
     gq_edge_transfer V E (SumEdges V E0 E1) psi (St .carrier) (St .vertex) (St .edge) (St .induction))

{` ---------- The theorem ---------- `}

def NielsenSchreierBasis (S : Type) (F : FreeGroupSignature S) (X : F .carrier → SetTypes) : Type
  ≔ Σ Type (T ↦ Σ (DecidableEquality T) (dT ↦
      Equiv (Σ (F .carrier) (z ↦ X z .fst)) (constructed_free_group_signature T dT .carrier)))

def nielsen_schreier_connected (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (X : F .carrier → SetTypes) (hc : Connected (Σ (F .carrier) (z ↦ X z .fst)))
  (m : Nat) (hm : Mere (Id Type (X (F .base) .fst) (Fin m)))
  : Mere (NielsenSchreierBasis S F X)
  ≔ let X' ≔ (z : F .carrier) ↦ X z .fst in
    let V ≔ X' (F .base) in
    let E ≔ FreeFlatEdges S F X' in
    let R ≔ free_flattening_signature S F X' in
    let decV ≔ finite_decidable_equality V (finite_of_card V m hm) in
    let decE ≔ free_flat_edges_decidable S dec F X' (z ↦ X z .snd) in
    mere_rec (SpanningTreeWithEdges V E m) (Mere (NielsenSchreierBasis S F X)) (mere_isprop (NielsenSchreierBasis S F X))
      (r ↦ mere (NielsenSchreierBasis S F X)
        (ComplementTotal V E (r .fst),
         (complement_total_decidable V E (r .fst) decV decE,
          graph_quotient_equiv V E R (tree_complement_signature V E decV decE (r .fst) (r .snd .fst)))))
      (spanning_tree V E R hc m hm decE)

{` thm:nielsen-schreier, first claim, with the book's hypotheses: X : B F_S → Set
   a transitive F_S-set (lem:conistrans turns transitivity into connectedness of
   Σ_z X(z)) of finite index m. `}
def nielsen_schreier (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (X : GSet (free_group S dec F)) (ht : IsTransitive (free_group S dec F) X)
  (m : Nat) (hm : GSetHasIndex (free_group S dec F) X m)
  : Mere (NielsenSchreierBasis S F X)
  ≔ nielsen_schreier_connected S dec F X
      (transitive_connected_equiv (free_group S dec F) X .map ht) m (hm (F .base))
