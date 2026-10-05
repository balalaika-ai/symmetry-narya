export "1101-graph-quotients"

{` def:graph-quotient-flattening (fggroups.tex:295) and the exercise at line 333.

   Given a graph quotient Q of (V, E) and X : V/E → U, put
   V' ≔ Σ_{v:V} X([v]) and E'((v,x),(w,y)) ≔ Σ_{e : E(v,w)} (x =_X^{edge_e} y).
   flattening_signature shows that Σ_{z : V/E} X(z) itself, with
   (v,x) ↦ ([v],x) and (e,q) ↦ pair⁼(edge_e, q), is a graph quotient of
   (V', E').  Hence for every graph quotient R of (V', E') we get the book's
   equivalence flt : Σ_{z:V/E} X(z) ≃ V'/E' (graph_quotient_flattening), whose
   inverse is the map φ of the implementation (both are the maps induced by the
   constructors, graph_quotient_map); the two round trips asked for in the
   exercise at line 333 are graph_quotient_roundtrip.

   In Narya an identification over edge_e in the family z ↦ (X(z) → P) is
   literally a function of identifications over edge_e in X, so the boundary data
   for Σ and for z ↦ Π_{x:X z} P(z,x) correspond judgmentally (flattening_boundary_map). `}

def FlatVertices (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type) : Type
  ≔ Σ V (v ↦ X (Q .vertex v))

def FlatEdges (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (u u' : FlatVertices V E Q X) : Type
  ≔ Σ (E (u .fst) (u' .fst)) (e ↦ Id X (Q .edge (u .fst) (u' .fst) e) (u .snd) (u' .snd))

def flat_vertex (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (u : FlatVertices V E Q X) : Σ (Q .carrier) X
  ≔ (Q .vertex (u .fst), u .snd)

def flat_edge (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (u u' : FlatVertices V E Q X) (e : FlatEdges V E Q X u u')
  : Id (Σ (Q .carrier) X) (flat_vertex V E Q X u) (flat_vertex V E Q X u')
  ≔ (Q .edge (u .fst) (u' .fst) (e .fst), e .snd)

def flat_family (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (P : Σ (Q .carrier) X → Type) : Q .carrier → Type
  ≔ z ↦ (x : X z) → P (z, x)

def flattening_boundary_map (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (P : Σ (Q .carrier) X → Type) (d : gq_boundary V E Q (flat_family V E Q X P))
  : GraphQuotientBoundary (FlatVertices V E Q X) (FlatEdges V E Q X) (Σ (Q .carrier) X)
      (flat_vertex V E Q X) (flat_edge V E Q X) P
  ≔ (u ↦ d .fst (u .fst) (u .snd),
     u u' e ↦ d .snd (u .fst) (u' .fst) (e .fst) (e .snd))

def flattening_boundary_unmap (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (P : Σ (Q .carrier) X → Type)
  (d : GraphQuotientBoundary (FlatVertices V E Q X) (FlatEdges V E Q X) (Σ (Q .carrier) X)
      (flat_vertex V E Q X) (flat_edge V E Q X) P)
  : gq_boundary V E Q (flat_family V E Q X P)
  ≔ (v x ↦ d .fst (v, x), v w e ↦ x ⤇ d .snd (v, x.0) (w, x.1) (e, x.2))

def flattening_induction (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  : GraphQuotientInduction (FlatVertices V E Q X) (FlatEdges V E Q X) (Σ (Q .carrier) X)
      (flat_vertex V E Q X) (flat_edge V E Q X)
  ≔ P d ↦
    let P' ≔ flat_family V E Q X P in
    let d' ≔ flattening_boundary_unmap V E Q X P d in
    (u ↦ gq_ind V E Q P' d' (u .fst) (u .snd),
     refl (flattening_boundary_map V E Q X P) (gq_ind_beta V E Q P' d'))

def flattening_signature (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  : GraphQuotientSignature (FlatVertices V E Q X) (FlatEdges V E Q X)
  ≔ (Σ (Q .carrier) X, flat_vertex V E Q X, flat_edge V E Q X, flattening_induction V E Q X)

{` The book's flt : Σ_{z:V/E} X(z) ≃ V'/E', for every graph quotient R of (V', E'). `}
def graph_quotient_flattening (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (X : Q .carrier → Type)
  (R : GraphQuotientSignature (FlatVertices V E Q X) (FlatEdges V E Q X))
  : Equiv (Σ (Q .carrier) X) (R .carrier)
  ≔ graph_quotient_equiv (FlatVertices V E Q X) (FlatEdges V E Q X) (flattening_signature V E Q X) R

{` flt([v], x) = [(v, x)], i.e. flt ∘ φ is the identity on vertices. `}
def graph_quotient_flattening_vertex (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E)
  (X : Q .carrier → Type) (R : GraphQuotientSignature (FlatVertices V E Q X) (FlatEdges V E Q X))
  (v : V) (x : X (Q .vertex v))
  : Id (R .carrier) (graph_quotient_flattening V E Q X R .map (Q .vertex v, x)) (R .vertex (v, x))
  ≔ graph_quotient_map_vertex (FlatVertices V E Q X) (FlatEdges V E Q X) (flattening_signature V E Q X) R (v, x)
