export "1105-subgraphs-trees"

{` lem:crossing-edge (fggroups.tex:676).  A connected graph (V, E) (its graph
   quotient Q is connected) whose vertex type decomposes as V ≃ V0 ⊔ V1, with
   v0 : V0 and v1 : V1, merely has an edge from V0 to V1 or from V1 to V0.

   As in the book: by vertex transfer (module 1101, the book's "path induction")
   we may take V ≡ V0 ⊔ V1; then the family of propositions P on V/E with
   P([inl v]) ≔ True and P([inr v]) ≔ ∥crossing edge∥ is defined by recursion
   (edges between the summands are equivalences of propositions because they
   witness the crossing), and connectedness transports P([inl v0]) to
   P([inr v1]).  The equivalence ψ : V0 ⊔ V1 ≃ V is the decomposition. `}

def CrossingEdgeSum (V0 V1 : Type) (E : Sum V0 V1 → Sum V0 V1 → Type) : Type
  ≔ Σ V0 (u0 ↦ Σ V1 (u1 ↦ Sum (E (inl. u0) (inr. u1)) (E (inr. u1) (inl. u0))))

def crossing_prop (V0 V1 : Type) (E : Sum V0 V1 → Sum V0 V1 → Type) : PropTypes
  ≔ (Mere (CrossingEdgeSum V0 V1 E), mere_isprop (CrossingEdgeSum V0 V1 E))

def true_prop_type : PropTypes ≔ (Unit, unit_prop)

def crossing_vertex_prop (V0 V1 : Type) (E : Sum V0 V1 → Sum V0 V1 → Type) (x : Sum V0 V1) : PropTypes
  ≔ match x [ inl. _ ↦ true_prop_type | inr. _ ↦ crossing_prop V0 V1 E ]

def crossing_edge_prop (V0 V1 : Type) (E : Sum V0 V1 → Sum V0 V1 → Type) (x y : Sum V0 V1) (e : E x y)
  : Id PropTypes (crossing_vertex_prop V0 V1 E x) (crossing_vertex_prop V0 V1 E y)
  ≔ match x [
  | inl. u0 ↦ match y [
    | inl. _ ↦ refl true_prop_type
    | inr. u1 ↦ proposition_extensionality true_prop_type (crossing_prop V0 V1 E)
        (_ ↦ mere (CrossingEdgeSum V0 V1 E) (u0, (u1, inl. e))) (_ ↦ star.) ]
  | inr. u1 ↦ match y [
    | inl. u0 ↦ proposition_extensionality (crossing_prop V0 V1 E) true_prop_type
        (_ ↦ star.) (_ ↦ mere (CrossingEdgeSum V0 V1 E) (u0, (u1, inr. e)))
    | inr. _ ↦ refl (crossing_prop V0 V1 E) ] ]

def crossing_edge_sum (V0 V1 : Type) (E : Sum V0 V1 → Sum V0 V1 → Type)
  (Q : GraphQuotientSignature (Sum V0 V1) E) (hc : Connected (Q .carrier)) (v0 : V0) (v1 : V1)
  : Mere (CrossingEdgeSum V0 V1 E)
  ≔ let Pr ≔ gq_rec (Sum V0 V1) E Q PropTypes (crossing_vertex_prop V0 V1 E, crossing_edge_prop V0 V1 E) in
    let a ≔ Q .vertex (inl. v0) in
    let b ≔ Q .vertex (inr. v1) in
    let pa : Pr a .fst
      ≔ transport PropTypes (T ↦ T .fst) true_prop_type (Pr a)
          (inverse PropTypes (Pr a) true_prop_type
            (gq_rec_vertex (Sum V0 V1) E Q PropTypes (crossing_vertex_prop V0 V1 E, crossing_edge_prop V0 V1 E) (inl. v0)))
          star. in
    let pb : Pr b .fst
      ≔ mere_rec (Id (Q .carrier) a b) (Pr b .fst) (Pr b .snd)
          (p ↦ transport (Q .carrier) (z ↦ Pr z .fst) a b p pa) (hc .snd a b) in
    transport PropTypes (T ↦ T .fst) (Pr b) (crossing_prop V0 V1 E)
      (gq_rec_vertex (Sum V0 V1) E Q PropTypes (crossing_vertex_prop V0 V1 E, crossing_edge_prop V0 V1 E) (inr. v1))
      pb

{` lem:crossing-edge for a decomposition ψ : V0 ⊔ V1 ≃ V. `}
def CrossingEdge (V : Type) (E : V → V → Type) (V0 V1 : Type) (psi : Equiv (Sum V0 V1) V) : Type
  ≔ Mere (Σ V0 (u0 ↦ Σ V1 (u1 ↦
      Sum (E (psi .map (inl. u0)) (psi .map (inr. u1))) (E (psi .map (inr. u1)) (psi .map (inl. u0))))))

def crossing_edge (V : Type) (E : V → V → Type) (Q : GraphQuotientSignature V E) (hc : IsConnectedGraph V E Q)
  (V0 V1 : Type) (psi : Equiv (Sum V0 V1) V) (v0 : V0) (v1 : V1)
  : CrossingEdge V E V0 V1 psi
  ≔ crossing_edge_sum V0 V1 (x y ↦ E (psi .map x) (psi .map y))
      (Q .carrier, x ↦ Q .vertex (psi .map x), x y e ↦ Q .edge (psi .map x) (psi .map y) e,
       gq_vertex_transfer (Sum V0 V1) V psi E (Q .carrier) (Q .vertex) (Q .edge) (Q .induction))
      hc v0 v1
