export "1102-graph-quotient-flattening"

{` xca:graph-quotient-in-steps (fggroups.tex:340) and xca:graph-quotient-whisker
   (fggroups.tex:356), with the helpers they need.

   A structure (X, vertex, edge) is a graph quotient as soon as evaluation
   ((z : X) → P z) → boundary data is an equivalence for every family P
   (gq_induction_of_isequiv).  Both exercises are proved this way: evaluation is
   identified, up to a pointwise homotopy, with a composite of explicit
   equivalences.

   In steps: E = E0 ⊔ E1 (family form, edges Sum (E0 x y) (E1 x y)).  Gluing E0
   gives Q0; the edges of E1 are then glued to Q0 along the composite
   E1 ⇉ V → V/E0, i.e. the family ImageEdges (the total-edge description of the
   book: an E1-edge from a to b in V/E0 is an E1-edge from x to y with [x] = a and
   [y] = b).  steps_signature: (V/E0)/E1 is a graph quotient of (V, E0 ⊔ E1);
   graph_quotient_in_steps: V/(E0 ⊔ E1) ≃ (V/E0)/E1 for every quotient.

   Whisker: the vertex type is X ⊔ 1, and the single edge from inl x to inr 0 is
   the family WhiskerEdges with WhiskerEdges (inl y) (inr _) ≔ (y = x) and Empty
   otherwise (its total type Σ_y (y = x) is contractible: one edge, from inl x).
   whisker_signature: X with inl y ↦ y, inr _ ↦ x is a graph quotient, hence
   X ≃ (X ⊔ 1)/1.  whisker_rev_signature is the same with the edge reversed
   (from inr 0 to inl x), needed for spanning trees. `}

{` A structure whose evaluation maps are equivalences is a graph quotient. `}
def gq_induction_of_isequiv (V : Type) (E : V → V → Type) (X : Type) (vertex : V → X)
  (edge : (x y : V) → E x y → Id X (vertex x) (vertex y))
  (h : (P : X → Type) → isEquiv ((z : X) → P z) (GraphQuotientBoundary V E X vertex edge P)
         (graph_quotient_evaluate V E X vertex edge P))
  : GraphQuotientInduction V E X vertex edge
  ≔ P d ↦
    let e : Equiv ((z : X) → P z) (GraphQuotientBoundary V E X vertex edge P)
      ≔ (graph_quotient_evaluate V E X vertex edge P, h P) in
    (equiv_inverse_map ((z : X) → P z) (GraphQuotientBoundary V E X vertex edge P) e d,
     equiv_counit ((z : X) → P z) (GraphQuotientBoundary V E X vertex edge P) e d)

{` A map homotopic to an equivalence is an equivalence. `}
def isequiv_of_homotopic (A B : Type) (e : Equiv A B) (f : A → B) (h : (a : A) → Id B (e .map a) (f a))
  : isEquiv A B f
  ≔ equiv_change_map A B e f h .equiv

{` Total maps over an equivalence of bases with fiberwise equivalences. `}
def sigma_total_isequiv (A : Type) (F : A → Type) (B : Type) (f : Equiv A B)
  : (G : B → Type) (g : (a : A) → Equiv (F a) (G (f .map a)))
    → isEquiv (Σ A F) (Σ B G) (u ↦ (f .map (u .fst), g (u .fst) .map (u .snd)))
  ≔ equivalence_induction A
      (B f ↦ (G : B → Type) (g : (a : A) → Equiv (F a) (G (f .map a)))
        → isEquiv (Σ A F) (Σ B G) (u ↦ (f .map (u .fst), g (u .fst) .map (u .snd))))
      (G g ↦ family_equiv A F G g .equiv) B f

{` Dependent functions out of a contractible type are determined by their value
   at the center. `}
def pi_contractible_domain_equiv (T : Type) (hT : isContr T) (G : T → Type)
  : Equiv ((t : T) → G t) (G (hT .center))
  ≔ let c0 ≔ hT .center in
    let k ≔ contractible_prop T hT c0 in
    quasi_inverse_equiv ((t : T) → G t) (G c0) (g ↦ g c0)
      (c t ↦ transport T G c0 t (k t) c)
      (g ↦ funext T G (t ↦ transport T G c0 t (k t) (g c0)) g
        (t ↦ pathover_transport_equiv T G c0 t (k t) (g c0) (g t) .map (refl g (k t))))
      (c ↦ concat (G c0) (transport T G c0 c0 (k c0) c) (transport T G c0 c0 (refl c0) c) c
        (transport2 T G c0 c0 (k c0) (refl c0)
          (prop_is_set T (contractible_prop T hT) c0 c0 (k c0) (refl c0)) c)
        (transport_refl T G c0 c))

def pi_singleton_into_equiv (A : Type) (a : A) (G : (y : A) → Id A y a → Type)
  : Equiv ((y : A) (p : Id A y a) → G y p) (G a (refl a))
  ≔ let T ≔ Σ A (y ↦ Id A y a) in
    compose_equiv ((y : A) (p : Id A y a) → G y p) ((t : T) → G (t .fst) (t .snd)) (G a (refl a))
      (quasi_inverse_equiv ((y : A) (p : Id A y a) → G y p) ((t : T) → G (t .fst) (t .snd))
        (g t ↦ g (t .fst) (t .snd)) (g y p ↦ g (y, p)) (g ↦ refl g) (g ↦ refl g))
      (pi_contractible_domain_equiv T (path_to_contractible A a) (t ↦ G (t .fst) (t .snd)))

def pi_singleton_from_equiv (A : Type) (a : A) (G : (y : A) → Id A a y → Type)
  : Equiv ((y : A) (p : Id A a y) → G y p) (G a (refl a))
  ≔ let T ≔ Σ A (y ↦ Id A a y) in
    compose_equiv ((y : A) (p : Id A a y) → G y p) ((t : T) → G (t .fst) (t .snd)) (G a (refl a))
      (quasi_inverse_equiv ((y : A) (p : Id A a y) → G y p) ((t : T) → G (t .fst) (t .snd))
        (g t ↦ g (t .fst) (t .snd)) (g y p ↦ g (y, p)) (g ↦ refl g) (g ↦ refl g))
      (pi_contractible_domain_equiv T (iscontr_idfrom A a) (t ↦ G (t .fst) (t .snd)))

{` ---------- In steps ---------- `}

def ImageEdges (V C : Type) (f : V → C) (E1 : V → V → Type) (a b : C) : Type
  ≔ Σ V (x ↦ Σ V (y ↦ Σ (E1 x y) (_ ↦ Product (Id C (f x) a) (Id C (f y) b))))

def SumEdges (V : Type) (E0 E1 : V → V → Type) (x y : V) : Type ≔ Sum (E0 x y) (E1 x y)

def steps_vertex (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (x : V) : Q1 .carrier
  ≔ Q1 .vertex (Q0 .vertex x)

def image_edge_at (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0) (x y : V) (e : E1 x y)
  : ImageEdges V (Q0 .carrier) (Q0 .vertex) E1 (Q0 .vertex x) (Q0 .vertex y)
  ≔ (x, (y, (e, (refl (Q0 .vertex x), refl (Q0 .vertex y)))))

def steps_edge (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (x y : V) (s : SumEdges V E0 E1 x y)
  : Id (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1 x) (steps_vertex V E0 E1 Q0 Q1 y)
  ≔ match s [
  | inl. e ↦ refl (Q1 .vertex) (Q0 .edge x y e)
  | inr. e ↦ Q1 .edge (Q0 .vertex x) (Q0 .vertex y) (image_edge_at V E0 E1 Q0 x y e) ]

{` The intermediate boundary type: E0-data on V/E0 plus E1-data at the image edges. `}
def StepsMiddle (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type) : Type
  ≔ Σ (gq_boundary V E0 Q0 (c ↦ P (Q1 .vertex c))) (k ↦
      (x y : V) (e : E1 x y) → Id P (Q1 .edge (Q0 .vertex x) (Q0 .vertex y) (image_edge_at V E0 E1 Q0 x y e))
        (k .fst x) (k .fst y))

{` The image-edge data are determined by their values at the reflexivity edges. `}
def ImageEdgesUncurried (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type) (x y : V) (e : E1 x y) : Type
  ≔ (a : C) (p : Id C (f x) a) (b : C) (q : Id C (f y) b) → F a b (x, (y, (e, (p, q))))

def image_edges_reorder (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type)
  : Equiv ((a b : C) (t : ImageEdges V C f E1 a b) → F a b t)
      ((x y : V) (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
  ≔ quasi_inverse_equiv ((a b : C) (t : ImageEdges V C f E1 a b) → F a b t)
      ((x y : V) (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
      (k x y e a p b q ↦ k a b (x, (y, (e, (p, q)))))
      (c a b t ↦ c (t .fst) (t .snd .fst) (t .snd .snd .fst) a (t .snd .snd .snd .fst) b (t .snd .snd .snd .snd))
      (k ↦ refl k) (c ↦ refl c)

def image_edges_contract (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type) (x y : V) (e : E1 x y)
  : Equiv (ImageEdgesUncurried V C f E1 F x y e) (F (f x) (f y) (x, (y, (e, (refl (f x), refl (f y))))))
  ≔ compose_equiv (ImageEdgesUncurried V C f E1 F x y e)
      ((b : C) (q : Id C (f y) b) → F (f x) b (x, (y, (e, (refl (f x), q)))))
      (F (f x) (f y) (x, (y, (e, (refl (f x), refl (f y))))))
      (pi_singleton_from_equiv C (f x) (a p ↦ (b : C) (q : Id C (f y) b) → F a b (x, (y, (e, (p, q))))))
      (pi_singleton_from_equiv C (f y) (b q ↦ F (f x) b (x, (y, (e, (refl (f x), q))))))

def ImageEdgesRefl (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type) (x y : V) (e : E1 x y) : Type
  ≔ F (f x) (f y) (x, (y, (e, (refl (f x), refl (f y)))))

def image_edges_contract_y (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type) (x y : V)
  : Equiv ((e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e) ((e : E1 x y) → ImageEdgesRefl V C f E1 F x y e)
  ≔ pi_family_equiv (E1 x y) (e ↦ ImageEdgesUncurried V C f E1 F x y e) (e ↦ ImageEdgesRefl V C f E1 F x y e)
      (e ↦ image_edges_contract V C f E1 F x y e)

def image_edges_contract_x (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type) (x : V)
  : Equiv ((y : V) (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
      ((y : V) (e : E1 x y) → ImageEdgesRefl V C f E1 F x y e)
  ≔ pi_family_equiv V (y ↦ (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
      (y ↦ (e : E1 x y) → ImageEdgesRefl V C f E1 F x y e) (y ↦ image_edges_contract_y V C f E1 F x y)

def image_edges_pi_equiv (V C : Type) (f : V → C) (E1 : V → V → Type)
  (F : (a b : C) → ImageEdges V C f E1 a b → Type)
  : Equiv ((a b : C) (t : ImageEdges V C f E1 a b) → F a b t)
      ((x y : V) (e : E1 x y) → ImageEdgesRefl V C f E1 F x y e)
  ≔ compose_equiv ((a b : C) (t : ImageEdges V C f E1 a b) → F a b t)
      ((x y : V) (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
      ((x y : V) (e : E1 x y) → ImageEdgesRefl V C f E1 F x y e)
      (image_edges_reorder V C f E1 F)
      (pi_family_equiv V (x ↦ (y : V) (e : E1 x y) → ImageEdgesUncurried V C f E1 F x y e)
        (x ↦ (y : V) (e : E1 x y) → ImageEdgesRefl V C f E1 F x y e)
        (x ↦ image_edges_contract_x V C f E1 F x))

def SumBoundary (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type) : Type
  ≔ GraphQuotientBoundary V (SumEdges V E0 E1) (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1) (steps_edge V E0 E1 Q0 Q1) P

def steps_middle_to_sum (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type) (m : StepsMiddle V E0 E1 Q0 Q1 P) : SumBoundary V E0 E1 Q0 Q1 P
  ≔ (m .fst .fst, x y s ↦ match s [ inl. e ↦ m .fst .snd x y e | inr. e ↦ m .snd x y e ])

def steps_sum_to_middle (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type) (d : SumBoundary V E0 E1 Q0 Q1 P) : StepsMiddle V E0 E1 Q0 Q1 P
  ≔ ((d .fst, x y e ↦ d .snd x y (inl. e)), x y e ↦ d .snd x y (inr. e))

def steps_middle_sum_equiv (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type) : Equiv (StepsMiddle V E0 E1 Q0 Q1 P) (SumBoundary V E0 E1 Q0 Q1 P)
  ≔ quasi_inverse_equiv (StepsMiddle V E0 E1 Q0 Q1 P) (SumBoundary V E0 E1 Q0 Q1 P)
      (steps_middle_to_sum V E0 E1 Q0 Q1 P) (steps_sum_to_middle V E0 E1 Q0 Q1 P)
      (m ↦ refl m)
      (d ↦ (refl (d .fst),
        funext3 V (_ ↦ V) (x y ↦ SumEdges V E0 E1 x y)
          (x y s ↦ Id P (steps_edge V E0 E1 Q0 Q1 x y s) (d .fst x) (d .fst y))
          (steps_middle_to_sum V E0 E1 Q0 Q1 P (steps_sum_to_middle V E0 E1 Q0 Q1 P d) .snd) (d .snd)
          (x y s ↦ match s [ inl. e ↦ refl (d .snd x y (inl. e)) | inr. e ↦ refl (d .snd x y (inr. e)) ])))

def steps_q1_to_middle (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  (P : Q1 .carrier → Type)
  : Equiv (gq_boundary (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1) Q1 P) (StepsMiddle V E0 E1 Q0 Q1 P)
  ≔ let E1' ≔ ImageEdges V (Q0 .carrier) (Q0 .vertex) E1 in
    let f ≔ gq_dependent_universal_property V E0 Q0 (c ↦ P (Q1 .vertex c)) in
    let F ≔ (h0 : (c : Q0 .carrier) → P (Q1 .vertex c)) ↦ (a b : Q0 .carrier) (t : E1' a b) → Id P (Q1 .edge a b t) (h0 a) (h0 b) in
    let G ≔ (k : gq_boundary V E0 Q0 (c ↦ P (Q1 .vertex c))) ↦
      (x y : V) (e : E1 x y) → Id P (Q1 .edge (Q0 .vertex x) (Q0 .vertex y) (image_edge_at V E0 E1 Q0 x y e))
        (k .fst x) (k .fst y) in
    let g ≔ (h0 : (c : Q0 .carrier) → P (Q1 .vertex c)) ↦
      image_edges_pi_equiv V (Q0 .carrier) (Q0 .vertex) E1 (a b t ↦ Id P (Q1 .edge a b t) (h0 a) (h0 b)) in
    (u ↦ (f .map (u .fst), g (u .fst) .map (u .snd)),
     sigma_total_isequiv ((c : Q0 .carrier) → P (Q1 .vertex c)) F (gq_boundary V E0 Q0 (c ↦ P (Q1 .vertex c))) f G g)

def steps_induction (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  : GraphQuotientInduction V (SumEdges V E0 E1) (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1) (steps_edge V E0 E1 Q0 Q1)
  ≔ gq_induction_of_isequiv V (SumEdges V E0 E1) (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1) (steps_edge V E0 E1 Q0 Q1)
      (P ↦
        let E1' ≔ ImageEdges V (Q0 .carrier) (Q0 .vertex) E1 in
        let comp ≔ compose_equiv ((z : Q1 .carrier) → P z) (gq_boundary (Q0 .carrier) E1' Q1 P) (SumBoundary V E0 E1 Q0 Q1 P)
          (gq_dependent_universal_property (Q0 .carrier) E1' Q1 P)
          (compose_equiv (gq_boundary (Q0 .carrier) E1' Q1 P) (StepsMiddle V E0 E1 Q0 Q1 P) (SumBoundary V E0 E1 Q0 Q1 P)
            (steps_q1_to_middle V E0 E1 Q0 Q1 P) (steps_middle_sum_equiv V E0 E1 Q0 Q1 P)) in
        isequiv_of_homotopic ((z : Q1 .carrier) → P z) (SumBoundary V E0 E1 Q0 Q1 P) comp
          (graph_quotient_evaluate V (SumEdges V E0 E1) (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1) (steps_edge V E0 E1 Q0 Q1) P)
          (h ↦ (refl (x ↦ h (Q1 .vertex (Q0 .vertex x))),
            funext3 V (_ ↦ V) (x y ↦ SumEdges V E0 E1 x y)
              (x y s ↦ Id P (steps_edge V E0 E1 Q0 Q1 x y s) (h (Q1 .vertex (Q0 .vertex x))) (h (Q1 .vertex (Q0 .vertex y))))
              (comp .map h .snd)
              (graph_quotient_evaluate V (SumEdges V E0 E1) (Q1 .carrier) (steps_vertex V E0 E1 Q0 Q1) (steps_edge V E0 E1 Q0 Q1) P h .snd)
              (x y s ↦ match s [
                | inl. e ↦ refl (refl h (refl (Q1 .vertex) (Q0 .edge x y e)))
                | inr. e ↦ refl (refl h (Q1 .edge (Q0 .vertex x) (Q0 .vertex y) (image_edge_at V E0 E1 Q0 x y e))) ]))))

{` (V/E0)/E1 is a graph quotient of (V, E0 ⊔ E1). `}
def steps_signature (V : Type) (E0 E1 : V → V → Type) (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  : GraphQuotientSignature V (SumEdges V E0 E1)
  ≔ (Q1 .carrier, steps_vertex V E0 E1 Q0 Q1, steps_edge V E0 E1 Q0 Q1, steps_induction V E0 E1 Q0 Q1)

{` xca:graph-quotient-in-steps: V/(E0 ⊔ E1) ≃ (V/E0)/E1. `}
def graph_quotient_in_steps (V : Type) (E0 E1 : V → V → Type) (R : GraphQuotientSignature V (SumEdges V E0 E1))
  (Q0 : GraphQuotientSignature V E0)
  (Q1 : GraphQuotientSignature (Q0 .carrier) (ImageEdges V (Q0 .carrier) (Q0 .vertex) E1))
  : Equiv (R .carrier) (Q1 .carrier)
  ≔ graph_quotient_equiv V (SumEdges V E0 E1) R (steps_signature V E0 E1 Q0 Q1)

{` ---------- Whisker ---------- `}

def WhiskerEdges (X : Type) (x : X) (v w : Sum X Unit) : Type ≔ match v [
| inl. y ↦ match w [ inl. _ ↦ Empty | inr. _ ↦ Id X y x ]
| inr. _ ↦ Empty ]

def whisker_vertex (X : Type) (x : X) (v : Sum X Unit) : X ≔ match v [ inl. y ↦ y | inr. _ ↦ x ]

def whisker_edge (X : Type) (x : X) (v w : Sum X Unit) (e : WhiskerEdges X x v w)
  : Id X (whisker_vertex X x v) (whisker_vertex X x w)
  ≔ match v [
  | inl. y ↦ match w [ inl. _ ↦ match e [] | inr. _ ↦ e ]
  | inr. _ ↦ match e [] ]

def WhiskerBoundary (X : Type) (x : X) (P : X → Type) : Type
  ≔ GraphQuotientBoundary (Sum X Unit) (WhiskerEdges X x) X (whisker_vertex X x) (whisker_edge X x) P

def WhiskerEdgeData (X : Type) (x : X) (P : X → Type) (al : (y : X) → P y) (ar : P x) : Type
  ≔ (y : X) (p : Id X y x) → Id P p (al y) ar

def whisker_edges_from (X : Type) (x : X) (P : X → Type) (a : (v : Sum X Unit) → P (whisker_vertex X x v))
  (c : WhiskerEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
  : (v w : Sum X Unit) (e : WhiskerEdges X x v w) → Id P (whisker_edge X x v w e) (a v) (a w)
  ≔ v w e ↦ match v [
        | inl. y ↦ match w [ inl. _ ↦ match e [] | inr. u ↦ match u [ star. ↦ c y e ] ]
        | inr. _ ↦ match e [] ]

def whisker_edges_equiv (X : Type) (x : X) (P : X → Type) (a : (v : Sum X Unit) → P (whisker_vertex X x v))
  : Equiv ((v w : Sum X Unit) (e : WhiskerEdges X x v w) → Id P (whisker_edge X x v w e) (a v) (a w))
      (WhiskerEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
  ≔ quasi_inverse_equiv ((v w : Sum X Unit) (e : WhiskerEdges X x v w) → Id P (whisker_edge X x v w e) (a v) (a w))
      (WhiskerEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
      (b y p ↦ b (inl. y) (inr. star.) p)
      (whisker_edges_from X x P a)
      (b ↦ funext3 (Sum X Unit) (_ ↦ Sum X Unit) (v w ↦ WhiskerEdges X x v w)
          (v w e ↦ Id P (whisker_edge X x v w e) (a v) (a w))
          (whisker_edges_from X x P a (y p ↦ b (inl. y) (inr. star.) p)) b
          (v w e ↦ match v [
            | inl. y ↦ match w [ inl. _ ↦ match e [] | inr. u ↦ match u [ star. ↦ refl (b (inl. y) (inr. star.) e) ] ]
            | inr. _ ↦ match e [] ]))
      (c ↦ refl c)

def sum_pi_join (X : Type) (P : Sum X Unit → Type) (c : Product ((y : X) → P (inl. y)) (P (inr. star.)))
  : (v : Sum X Unit) → P v
  ≔ v ↦ match v [ inl. y ↦ c .fst y | inr. u ↦ match u [ star. ↦ c .snd ] ]

def sum_pi_split_equiv (X : Type) (P : Sum X Unit → Type)
  : Equiv ((v : Sum X Unit) → P v) (Product ((y : X) → P (inl. y)) (P (inr. star.)))
  ≔ quasi_inverse_equiv ((v : Sum X Unit) → P v) (Product ((y : X) → P (inl. y)) (P (inr. star.)))
      (a ↦ (y ↦ a (inl. y), a (inr. star.)))
      (sum_pi_join X P)
      (a ↦ funext (Sum X Unit) P (sum_pi_join X P (y ↦ a (inl. y), a (inr. star.))) a
        (v ↦ match v [ inl. y ↦ refl (a (inl. y)) | inr. u ↦ match u [ star. ↦ refl (a (inr. star.)) ] ]))
      (c ↦ refl c)

def whisker_fiber_contractible (X : Type) (x : X) (P : X → Type) (al : (y : X) → P y)
  : isContr (Σ (P x) (ar ↦ WhiskerEdgeData X x P al ar))
  ≔ hlevel_equiv zero. (Σ (P x) (ar ↦ Id (P x) (al x) ar)) (Σ (P x) (ar ↦ WhiskerEdgeData X x P al ar))
      (family_equiv (P x) (ar ↦ Id (P x) (al x) ar) (ar ↦ WhiskerEdgeData X x P al ar)
        (ar ↦ canonical_inverse_equiv (WhiskerEdgeData X x P al ar) (Id (P x) (al x) ar)
          (pi_singleton_into_equiv X x (y p ↦ Id P p (al y) ar))))
      (iscontr_idfrom (P x) (al x))

def whisker_restrict_equiv (X : Type) (x : X) (P : X → Type)
  : Equiv (WhiskerBoundary X x P) ((y : X) → P y)
  ≔ let A ≔ (v : Sum X Unit) → P (whisker_vertex X x v) in
    let B ≔ Product ((y : X) → P y) (P x) in
    let C ≔ (a : A) ↦ WhiskerEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)) in
    let D ≔ (c : B) ↦ WhiskerEdgeData X x P (c .fst) (c .snd) in
    let F ≔ (al : (y : X) → P y) ↦ Σ (P x) (ar ↦ WhiskerEdgeData X x P al ar) in
    compose_equiv (WhiskerBoundary X x P) (Σ A C) ((y : X) → P y)
      (family_equiv A
        (a ↦ (v w : Sum X Unit) (e : WhiskerEdges X x v w) → Id P (whisker_edge X x v w e) (a v) (a w)) C
        (a ↦ whisker_edges_equiv X x P a))
      (compose_equiv (Σ A C) (Σ B D) ((y : X) → P y)
        ((u ↦ ((y ↦ u .fst (inl. y), u .fst (inr. star.)), u .snd)),
         sigma_total_isequiv A C B (sum_pi_split_equiv X (v ↦ P (whisker_vertex X x v))) D (a ↦ identity_equiv (C a)))
        (compose_equiv (Σ B D) (Σ ((y : X) → P y) F) ((y : X) → P y)
          (quasi_inverse_equiv (Σ B D) (Σ ((y : X) → P y) F)
            (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (u ↦ ((u .fst, u .snd .fst), u .snd .snd))
            (u ↦ refl u) (u ↦ refl u))
          (contractible_fiber_projection ((y : X) → P y) F (al ↦ whisker_fiber_contractible X x P al))))

def whisker_induction (X : Type) (x : X)
  : GraphQuotientInduction (Sum X Unit) (WhiskerEdges X x) X (whisker_vertex X x) (whisker_edge X x)
  ≔ gq_induction_of_isequiv (Sum X Unit) (WhiskerEdges X x) X (whisker_vertex X x) (whisker_edge X x)
      (P ↦ isequiv_of_homotopic ((z : X) → P z) (WhiskerBoundary X x P)
        (canonical_inverse_equiv (WhiskerBoundary X x P) ((y : X) → P y) (whisker_restrict_equiv X x P))
        (graph_quotient_evaluate (Sum X Unit) (WhiskerEdges X x) X (whisker_vertex X x) (whisker_edge X x) P)
        (h ↦ equiv_retraction (WhiskerBoundary X x P) ((y : X) → P y) (whisker_restrict_equiv X x P)
          (graph_quotient_evaluate (Sum X Unit) (WhiskerEdges X x) X (whisker_vertex X x) (whisker_edge X x) P h)))

def whisker_signature (X : Type) (x : X) : GraphQuotientSignature (Sum X Unit) (WhiskerEdges X x)
  ≔ (X, whisker_vertex X x, whisker_edge X x, whisker_induction X x)

{` xca:graph-quotient-whisker: X ≃ (X ⊔ 1)/1, for every graph quotient R. `}
def graph_quotient_whisker (X : Type) (x : X) (R : GraphQuotientSignature (Sum X Unit) (WhiskerEdges X x))
  : Equiv X (R .carrier)
  ≔ graph_quotient_equiv (Sum X Unit) (WhiskerEdges X x) (whisker_signature X x) R

{` The same with the single edge reversed, from inr 0 to inl x. `}
def WhiskerRevEdges (X : Type) (x : X) (v w : Sum X Unit) : Type ≔ match v [
| inl. _ ↦ Empty
| inr. _ ↦ match w [ inl. y ↦ Id X x y | inr. _ ↦ Empty ] ]

def whisker_rev_edge (X : Type) (x : X) (v w : Sum X Unit) (e : WhiskerRevEdges X x v w)
  : Id X (whisker_vertex X x v) (whisker_vertex X x w)
  ≔ match v [
  | inl. _ ↦ match e []
  | inr. _ ↦ match w [ inl. y ↦ e | inr. _ ↦ match e [] ] ]

def WhiskerRevBoundary (X : Type) (x : X) (P : X → Type) : Type
  ≔ GraphQuotientBoundary (Sum X Unit) (WhiskerRevEdges X x) X (whisker_vertex X x) (whisker_rev_edge X x) P

def WhiskerRevEdgeData (X : Type) (x : X) (P : X → Type) (al : (y : X) → P y) (ar : P x) : Type
  ≔ (y : X) (p : Id X x y) → Id P p ar (al y)

def whisker_rev_edges_from (X : Type) (x : X) (P : X → Type) (a : (v : Sum X Unit) → P (whisker_vertex X x v))
  (c : WhiskerRevEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
  : (v w : Sum X Unit) (e : WhiskerRevEdges X x v w) → Id P (whisker_rev_edge X x v w e) (a v) (a w)
  ≔ v w e ↦ match v [
        | inl. _ ↦ match e []
        | inr. u ↦ match u [ star. ↦ match w [ inl. y ↦ c y e | inr. _ ↦ match e [] ] ] ]

def whisker_rev_edges_equiv (X : Type) (x : X) (P : X → Type) (a : (v : Sum X Unit) → P (whisker_vertex X x v))
  : Equiv ((v w : Sum X Unit) (e : WhiskerRevEdges X x v w) → Id P (whisker_rev_edge X x v w e) (a v) (a w))
      (WhiskerRevEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
  ≔ quasi_inverse_equiv ((v w : Sum X Unit) (e : WhiskerRevEdges X x v w) → Id P (whisker_rev_edge X x v w e) (a v) (a w))
      (WhiskerRevEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)))
      (b y p ↦ b (inr. star.) (inl. y) p)
      (whisker_rev_edges_from X x P a)
      (b ↦ funext3 (Sum X Unit) (_ ↦ Sum X Unit) (v w ↦ WhiskerRevEdges X x v w)
          (v w e ↦ Id P (whisker_rev_edge X x v w e) (a v) (a w))
          (whisker_rev_edges_from X x P a (y p ↦ b (inr. star.) (inl. y) p)) b
          (v w e ↦ match v [
            | inl. _ ↦ match e []
            | inr. u ↦ match u [ star. ↦ match w [ inl. y ↦ refl (b (inr. star.) (inl. y) e) | inr. _ ↦ match e [] ] ] ]))
      (c ↦ refl c)

def whisker_rev_fiber_contractible (X : Type) (x : X) (P : X → Type) (al : (y : X) → P y)
  : isContr (Σ (P x) (ar ↦ WhiskerRevEdgeData X x P al ar))
  ≔ hlevel_equiv zero. (Σ (P x) (ar ↦ Id (P x) ar (al x))) (Σ (P x) (ar ↦ WhiskerRevEdgeData X x P al ar))
      (family_equiv (P x) (ar ↦ Id (P x) ar (al x)) (ar ↦ WhiskerRevEdgeData X x P al ar)
        (ar ↦ canonical_inverse_equiv (WhiskerRevEdgeData X x P al ar) (Id (P x) ar (al x))
          (pi_singleton_from_equiv X x (y p ↦ Id P p ar (al y)))))
      (path_to_contractible (P x) (al x))

def whisker_rev_restrict_equiv (X : Type) (x : X) (P : X → Type)
  : Equiv (WhiskerRevBoundary X x P) ((y : X) → P y)
  ≔ let A ≔ (v : Sum X Unit) → P (whisker_vertex X x v) in
    let B ≔ Product ((y : X) → P y) (P x) in
    let C ≔ (a : A) ↦ WhiskerRevEdgeData X x P (y ↦ a (inl. y)) (a (inr. star.)) in
    let D ≔ (c : B) ↦ WhiskerRevEdgeData X x P (c .fst) (c .snd) in
    let F ≔ (al : (y : X) → P y) ↦ Σ (P x) (ar ↦ WhiskerRevEdgeData X x P al ar) in
    compose_equiv (WhiskerRevBoundary X x P) (Σ A C) ((y : X) → P y)
      (family_equiv A
        (a ↦ (v w : Sum X Unit) (e : WhiskerRevEdges X x v w) → Id P (whisker_rev_edge X x v w e) (a v) (a w)) C
        (a ↦ whisker_rev_edges_equiv X x P a))
      (compose_equiv (Σ A C) (Σ B D) ((y : X) → P y)
        ((u ↦ ((y ↦ u .fst (inl. y), u .fst (inr. star.)), u .snd)),
         sigma_total_isequiv A C B (sum_pi_split_equiv X (v ↦ P (whisker_vertex X x v))) D (a ↦ identity_equiv (C a)))
        (compose_equiv (Σ B D) (Σ ((y : X) → P y) F) ((y : X) → P y)
          (quasi_inverse_equiv (Σ B D) (Σ ((y : X) → P y) F)
            (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (u ↦ ((u .fst, u .snd .fst), u .snd .snd))
            (u ↦ refl u) (u ↦ refl u))
          (contractible_fiber_projection ((y : X) → P y) F (al ↦ whisker_rev_fiber_contractible X x P al))))

def whisker_rev_induction (X : Type) (x : X)
  : GraphQuotientInduction (Sum X Unit) (WhiskerRevEdges X x) X (whisker_vertex X x) (whisker_rev_edge X x)
  ≔ gq_induction_of_isequiv (Sum X Unit) (WhiskerRevEdges X x) X (whisker_vertex X x) (whisker_rev_edge X x)
      (P ↦ isequiv_of_homotopic ((z : X) → P z) (WhiskerRevBoundary X x P)
        (canonical_inverse_equiv (WhiskerRevBoundary X x P) ((y : X) → P y) (whisker_rev_restrict_equiv X x P))
        (graph_quotient_evaluate (Sum X Unit) (WhiskerRevEdges X x) X (whisker_vertex X x) (whisker_rev_edge X x) P)
        (h ↦ equiv_retraction (WhiskerRevBoundary X x P) ((y : X) → P y) (whisker_rev_restrict_equiv X x P)
          (graph_quotient_evaluate (Sum X Unit) (WhiskerRevEdges X x) X (whisker_vertex X x) (whisker_rev_edge X x) P h)))

def whisker_rev_signature (X : Type) (x : X) : GraphQuotientSignature (Sum X Unit) (WhiskerRevEdges X x)
  ≔ (X, whisker_vertex X x, whisker_rev_edge X x, whisker_rev_induction X x)
