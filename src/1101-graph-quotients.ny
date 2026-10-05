export "404-group-examples"
export "190-universes"

{` Chapter 11 (fggroups.tex), definition at line 259: the graph quotient V/E of a
   graph (V, E), E : V → V → U, is the higher inductive type with points [x] for
   x : V and identifications edge_e : [x] = [y] for e : E(x,y).

   The pinned Narya has no higher inductive types.  As for pushouts (module 840)
   and free groups (module 860), a graph quotient is therefore a STRUCTURE on a
   type X with maps vertex : V → X and edge, namely the dependent eliminator
   (GraphQuotientInduction).  The book's computation rules (f([x]) ≡ a_x
   judgmental, apd_f(edge_e) = q_e) become ONE identification of boundary data
   (gq_ind_beta); the vertex rule is the proved identification gq_ind_vertex.

   A statement of the book about "the graph quotient V/E" is formalized for
   EVERY GraphQuotientSignature of (V, E); graph_quotient_equiv shows any two are
   equivalent (by maps commuting with the constructors), so the choice does not
   matter.  Trees (def. at line 626) need no parameter: GraphTreeStructure says
   that the trivial cocone into Unit satisfies the induction principle, and
   graph_tree_iff_contractible shows this is "V/E is contractible" for every
   signature.  Transfer lemmas move the structure along equivalences of
   vertices, of edge families and of the carrier. `}

def GraphQuotientBoundary (V : Type) (E : V → V → Type) (X : Type) (vertex : V → X)
  (edge : (x y : V) → E x y → Id X (vertex x) (vertex y)) (P : X → Type) : Type
  ≔ Σ ((x : V) → P (vertex x)) (a ↦ (x y : V) (e : E x y) → Id P (edge x y e) (a x) (a y))

def graph_quotient_evaluate (V : Type) (E : V → V → Type) (X : Type) (vertex : V → X)
  (edge : (x y : V) → E x y → Id X (vertex x) (vertex y)) (P : X → Type) (h : (z : X) → P z)
  : GraphQuotientBoundary V E X vertex edge P
  ≔ (x ↦ h (vertex x), x y e ↦ refl h (edge x y e))

def GraphQuotientInduction (V : Type) (E : V → V → Type) (X : Type) (vertex : V → X)
  (edge : (x y : V) → E x y → Id X (vertex x) (vertex y)) : Type
  ≔ (P : X → Type) (d : GraphQuotientBoundary V E X vertex edge P)
    → Σ ((z : X) → P z) (h ↦
        Id (GraphQuotientBoundary V E X vertex edge P) (graph_quotient_evaluate V E X vertex edge P h) d)

def GraphQuotientSignature (V : Type) (E : V → V → Type) : Type ≔ sig (
  carrier : Type,
  vertex : V → carrier,
  edge : (x y : V) → E x y → Id carrier (vertex x) (vertex y),
  induction : GraphQuotientInduction V E carrier vertex edge)

def gq_boundary (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type) : Type
  ≔ GraphQuotientBoundary V E (Q .carrier) (Q .vertex) (Q .edge) P

def gq_eval (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (h : (z : Q .carrier) → P z) : gq_boundary V E Q P
  ≔ graph_quotient_evaluate V E (Q .carrier) (Q .vertex) (Q .edge) P h

def gq_ind (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (d : gq_boundary V E Q P) : (z : Q .carrier) → P z
  ≔ Q .induction P d .fst

def gq_ind_beta (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (d : gq_boundary V E Q P)
  : Id (gq_boundary V E Q P) (gq_eval V E Q P (gq_ind V E Q P d)) d
  ≔ Q .induction P d .snd

{` The book's judgmental rule f([x]) ≡ a_x, here a proved identification. `}
def gq_ind_vertex (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (d : gq_boundary V E Q P) (x : V)
  : Id (P (Q .vertex x)) (gq_ind V E Q P d (Q .vertex x)) (d .fst x)
  ≔ gq_ind_beta V E Q P d .fst (refl x)

{` Cocones (nondependent boundary data) and recursion. `}
def GraphCocone (V : Type) (E : V → V → Type) (T : Type) : Type
  ≔ Σ (V → T) (a ↦ (x y : V) → E x y → Id T (a x) (a y))

def gq_cocone (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type) (h : Q .carrier → T)
  : GraphCocone V E T
  ≔ (x ↦ h (Q .vertex x), x y e ↦ refl h (Q .edge x y e))

def gq_rec (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type) (d : GraphCocone V E T)
  : Q .carrier → T
  ≔ Q .induction (_ ↦ T) d .fst

def gq_rec_beta (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type) (d : GraphCocone V E T)
  : Id (GraphCocone V E T) (gq_cocone V E Q T (gq_rec V E Q T d)) d
  ≔ Q .induction (_ ↦ T) d .snd

def gq_rec_vertex (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type) (d : GraphCocone V E T)
  (x : V) : Id T (gq_rec V E Q T d (Q .vertex x)) (d .fst x)
  ≔ gq_rec_beta V E Q T d .fst (refl x)

{` Uniqueness: sections (and maps) with identified boundary data are identified. `}
def gq_sections_equal (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (h k : (z : Q .carrier) → P z)
  (e : Id (gq_boundary V E Q P) (gq_eval V E Q P h) (gq_eval V E Q P k))
  : Id ((z : Q .carrier) → P z) h k
  ≔ funext (Q .carrier) P h k
      (Q .induction (z ↦ Id (P z) (h z) (k z))
        (x ↦ e .fst (refl x), x y d ↦ sym (e .snd (refl x) (refl y) (refl d))) .fst)

def gq_maps_equal (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type)
  (h k : Q .carrier → T)
  (e : Id (GraphCocone V E T) (gq_cocone V E Q T h) (gq_cocone V E Q T k))
  : Id (Q .carrier → T) h k
  ≔ gq_sections_equal V E Q (_ ↦ T) h k e

def gq_ind_eta (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (h : (z : Q .carrier) → P z)
  : Id ((z : Q .carrier) → P z) (gq_ind V E Q P (gq_eval V E Q P h)) h
  ≔ gq_sections_equal V E Q P (gq_ind V E Q P (gq_eval V E Q P h)) h (gq_ind_beta V E Q P (gq_eval V E Q P h))

def gq_rec_eta (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type) (h : Q .carrier → T)
  : Id (Q .carrier → T) (gq_rec V E Q T (gq_cocone V E Q T h)) h
  ≔ gq_ind_eta V E Q (_ ↦ T) h

{` The dependent and nondependent universal properties of V/E. `}
def gq_dependent_universal_property (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E)
  (P : Q .carrier → Type)
  : Equiv ((z : Q .carrier) → P z) (gq_boundary V E Q P)
  ≔ quasi_inverse_equiv ((z : Q .carrier) → P z) (gq_boundary V E Q P)
      (gq_eval V E Q P) (gq_ind V E Q P) (gq_ind_eta V E Q P) (gq_ind_beta V E Q P)

def gq_universal_property (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (T : Type)
  : Equiv (Q .carrier → T) (GraphCocone V E T)
  ≔ gq_dependent_universal_property V E Q (_ ↦ T)

{` Induction into a family of propositions needs only the vertex data. `}
def gq_ind_prop (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (P : Q .carrier → Type)
  (hP : (z : Q .carrier) → isProp (P z)) (a : (x : V) → P (Q .vertex x)) : (z : Q .carrier) → P z
  ≔ Q .induction P
      (a, x y e ↦ pathover_of_eq (Q .carrier) P (Q .vertex x) (Q .vertex y) (Q .edge x y e) (a x) (a y)
        (hP (Q .vertex y) (transport (Q .carrier) P (Q .vertex x) (Q .vertex y) (Q .edge x y e) (a x)) (a y))) .fst

{` Postcomposition of cocones with a map. `}
def graph_cocone_post (V : Type) (E : V → V → Type) (T T' : Type) (f : T → T') (c : GraphCocone V E T)
  : GraphCocone V E T'
  ≔ (x ↦ f (c .fst x), x y e ↦ refl f (c .snd x y e))

{` Any two graph quotients of (V, E) are equivalent, by the maps induced by the
   constructors.  This justifies speaking of "the" graph quotient. `}
def graph_quotient_map (V : Type) (E : V → V → Type) (Q R : GraphQuotientSignature V E) : Q .carrier → R .carrier
  ≔ gq_rec V E Q (R .carrier) (R .vertex, R .edge)

def graph_quotient_map_vertex (V : Type) (E : V → V → Type) (Q R : GraphQuotientSignature V E) (x : V)
  : Id (R .carrier) (graph_quotient_map V E Q R (Q .vertex x)) (R .vertex x)
  ≔ gq_rec_vertex V E Q (R .carrier) (R .vertex, R .edge) x

def graph_quotient_roundtrip (V : Type) (E : V → V → Type) (Q R : GraphQuotientSignature V E) (z : Q .carrier)
  : Id (Q .carrier) (graph_quotient_map V E R Q (graph_quotient_map V E Q R z)) z
  ≔ let f ≔ graph_quotient_map V E R Q in
    let g ≔ graph_quotient_map V E Q R in
    let C ≔ GraphCocone V E (Q .carrier) in
    let c1 ≔ graph_cocone_post V E (R .carrier) (Q .carrier) f (gq_cocone V E Q (R .carrier) g) in
    let c2 ≔ graph_cocone_post V E (R .carrier) (Q .carrier) f (R .vertex, R .edge) in
    let c3 : C ≔ (Q .vertex, Q .edge) in
    happly (Q .carrier) (_ ↦ Q .carrier) (z ↦ f (g z)) (z ↦ z)
      (gq_maps_equal V E Q (Q .carrier) (z ↦ f (g z)) (z ↦ z)
        (concat C c1 c2 c3
          (refl (graph_cocone_post V E (R .carrier) (Q .carrier) f) (gq_rec_beta V E Q (R .carrier) (R .vertex, R .edge)))
          (gq_rec_beta V E R (Q .carrier) (Q .vertex, Q .edge)))) z

def graph_quotient_equiv (V : Type) (E : V → V → Type) (Q R : GraphQuotientSignature V E)
  : Equiv (Q .carrier) (R .carrier)
  ≔ quasi_inverse_equiv (Q .carrier) (R .carrier) (graph_quotient_map V E Q R) (graph_quotient_map V E R Q)
      (graph_quotient_roundtrip V E Q R) (graph_quotient_roundtrip V E R Q)

{` Transfer along an equivalence of the carrier: if (X, vertex, edge) is a graph
   quotient and χ : X ≃ Y, then (Y, χ ∘ vertex, ap_χ ∘ edge) is one. `}
def gq_carrier_transfer (V : Type) (E : V → V → Type) (X Y : Type) (chi : Equiv X Y)
  : (vertex : V → X) (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
    → GraphQuotientInduction V E X vertex edge
    → GraphQuotientInduction V E Y (x ↦ chi .map (vertex x)) (x y e ↦ refl (chi .map) (edge x y e))
  ≔ equivalence_induction X
      (Y chi ↦ (vertex : V → X) (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
        → GraphQuotientInduction V E X vertex edge
        → GraphQuotientInduction V E Y (x ↦ chi .map (vertex x)) (x y e ↦ refl (chi .map) (edge x y e)))
      (vertex edge ind ↦ ind) Y chi

{` Transfer along an equivalence of vertex types φ : V' ≃ V (edges pulled back). `}
def gq_vertex_transfer (V' V : Type) (phi : Equiv V' V)
  : (E : V → V → Type) (X : Type) (vertex : V → X) (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
    → GraphQuotientInduction V E X vertex edge
    → GraphQuotientInduction V' (x y ↦ E (phi .map x) (phi .map y)) X (x ↦ vertex (phi .map x))
        (x y e ↦ edge (phi .map x) (phi .map y) e)
  ≔ equivalence_induction V'
      (V phi ↦ (E : V → V → Type) (X : Type) (vertex : V → X) (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
        → GraphQuotientInduction V E X vertex edge
        → GraphQuotientInduction V' (x y ↦ E (phi .map x) (phi .map y)) X (x ↦ vertex (phi .map x))
            (x y e ↦ edge (phi .map x) (phi .map y) e))
      (E X vertex edge ind ↦ ind) V phi

{` Induction over families of equivalences (helper): the type of families B with
   fiberwise equivalences A i ≃ B i is contractible. `}
def family_equiv_singleton_contractible (I : Type) (A : I → Type)
  : isContr (Σ (I → Type) (B ↦ (i : I) → Equiv (A i) (B i)))
  ≔ hlevel_equiv zero. ((i : I) → Σ Type (B ↦ Equiv (A i) B)) (Σ (I → Type) (B ↦ (i : I) → Equiv (A i) (B i)))
      (choice_equiv I (_ ↦ Type) (i B ↦ Equiv (A i) B))
      (pi_contractible I (i ↦ Σ Type (B ↦ Equiv (A i) B)) (i ↦ equiv_singleton_contractible (A i)))

def family_equivalence_induction (I : Type) (A : I → Type)
  (P : (B : I → Type) → ((i : I) → Equiv (A i) (B i)) → Type)
  (base : P A (i ↦ identity_equiv (A i))) (B : I → Type) (psi : (i : I) → Equiv (A i) (B i)) : P B psi
  ≔ let T ≔ Σ (I → Type) (B ↦ (i : I) → Equiv (A i) (B i)) in
    transport T (u ↦ P (u .fst) (u .snd)) (A, i ↦ identity_equiv (A i)) (B, psi)
      (contractible_prop T (family_equiv_singleton_contractible I A) (A, i ↦ identity_equiv (A i)) (B, psi)) base

{` Transfer along fiberwise equivalences of edge families ψ : E' x y ≃ E x y. `}
def gq_edge_transfer (V : Type) (E' E : V → V → Type) (psi : (x y : V) → Equiv (E' x y) (E x y))
  (X : Type) (vertex : V → X) (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
  (ind : GraphQuotientInduction V E X vertex edge)
  : GraphQuotientInduction V E' X vertex (x y e ↦ edge x y (psi x y .map e))
  ≔ family_equivalence_induction (Σ V (_ ↦ V)) (i ↦ E' (i .fst) (i .snd))
      (B psi2 ↦ (edge2 : (x y : V) → B (x, y) → Id X (vertex x) (vertex y))
        → GraphQuotientInduction V (x y ↦ B (x, y)) X vertex edge2
        → GraphQuotientInduction V E' X vertex (x y e ↦ edge2 x y (psi2 (x, y) .map e)))
      (edge2 ind2 ↦ ind2) (i ↦ E (i .fst) (i .snd)) (i ↦ psi (i .fst) (i .snd)) edge ind

{` Changing the edge identifications by a homotopy. `}
def gq_edge_homotopy (V : Type) (E : V → V → Type) (X : Type) (vertex : V → X)
  (edge edge' : (x y : V) → E x y → Id X (vertex x) (vertex y))
  (h : (x y : V) (e : E x y) → Id (Id X (vertex x) (vertex y)) (edge x y e) (edge' x y e))
  (ind : GraphQuotientInduction V E X vertex edge) : GraphQuotientInduction V E X vertex edge'
  ≔ transport ((x y : V) → E x y → Id X (vertex x) (vertex y)) (GraphQuotientInduction V E X vertex) edge edge'
      (funext3 V (_ ↦ V) (x y ↦ E x y) (x y _ ↦ Id X (vertex x) (vertex y)) edge edge' h) ind

{` def. at line 626: trees and connected graphs.  A tree: the graph quotient is
   contractible; here: Unit with the trivial cocone is a graph quotient. `}
def GraphTreeStructure (V : Type) (E : V → V → Type) : Type
  ≔ GraphQuotientInduction V E Unit (_ ↦ star.) (x y _ ↦ refl (star. : Unit))

def graph_tree_signature (V : Type) (E : V → V → Type) (t : GraphTreeStructure V E) : GraphQuotientSignature V E
  ≔ (Unit, _ ↦ star., x y _ ↦ refl (star. : Unit), t)

def book_unit_contractible_gq : BookIsContr Unit ≔ book_contraction Unit unit_contractible

def graph_tree_iff_contractible_to (V : Type) (E : V → V → Type) (t : GraphTreeStructure V E)
  (Q : GraphQuotientSignature V E) : BookIsContr (Q .carrier)
  ≔ let e ≔ graph_quotient_equiv V E (graph_tree_signature V E t) Q in
    (e .map star., z ↦ concat (Q .carrier) (e .map star.)
        (e .map (equiv_inverse_map Unit (Q .carrier) e z)) z
        (refl (e .map) (book_unit_contractible_gq .contract (equiv_inverse_map Unit (Q .carrier) e z)))
        (equiv_counit Unit (Q .carrier) e z))

def graph_tree_iff_contractible_from (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E)
  (h : BookIsContr (Q .carrier)) : GraphTreeStructure V E
  ≔ let chi ≔ contractible_unit_equiv (Q .carrier) (native_contraction (Q .carrier) h) in
    gq_edge_homotopy V E Unit (_ ↦ star.) (x y e ↦ refl (chi .map) (Q .edge x y e)) (x y _ ↦ refl (star. : Unit))
      (x y e ↦ unit_set star. star. (refl (chi .map) (Q .edge x y e)) (refl (star. : Unit)))
      (gq_carrier_transfer V E (Q .carrier) Unit chi (Q .vertex) (Q .edge) (Q .induction))

{` For every graph quotient Q of (V, E): (V, E) is a tree iff Q is contractible. `}
def graph_tree_iff_contractible (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E)
  : Product (GraphTreeStructure V E → BookIsContr (Q .carrier)) (BookIsContr (Q .carrier) → GraphTreeStructure V E)
  ≔ (t ↦ graph_tree_iff_contractible_to V E t Q, h ↦ graph_tree_iff_contractible_from V E Q h)

{` Connected graphs: V/E is connected.  Stated for a given graph quotient Q; it
   does not depend on Q (graph_connected_invariant). `}
def IsConnectedGraph (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) : Type ≔ Connected (Q .carrier)

def graph_connected_invariant (V : Type) (E : V → V → Type) (Q R : GraphQuotientSignature V E)
  (h : IsConnectedGraph V E Q) : IsConnectedGraph V E R
  ≔ transport Type Connected (Q .carrier) (R .carrier)
      (ua (Q .carrier) (R .carrier) (graph_quotient_equiv V E Q R)) h
