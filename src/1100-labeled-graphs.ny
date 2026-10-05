export "1103-graph-quotient-steps"

{` fggroups.tex, definition at line 219 (S-labeled graphs) and the claims around it
   (lines 227-255).

   LabeledGraph S ≔ Σ_{V:U} (S → V → V → U); E(s,x,y) is the type of s-coloured edges
   from x to y.  Claims formalized:
   - line 227: functional graphs (Σ_y E(s,x,y) contractible for all s, x) are the
     graphs of functions: function_graph_functional, and functional_graphs_equiv
     (S → V → V) ≃ Σ_E IsFunctionalGraph (the map is f ↦ (s x y ↦ f s x = y));
   - line 243: if S is contractible a labelled graph is just a graph V → V → U
     (contractible_labels_equiv);
   - line 245: summing over the colours gives an unlabelled graph (labeled_graph_forget);
   - lines 249-255: graphs as tuples (V, E, s, t, c) with a total type of edges
     (labeled_total_equiv, via lem:typefamiliesandfibrations, module 19); dropping c
     gives the unlabelled graph (total_graph_forget). `}

def LabeledGraph (S : Type) : Type ≔ Σ Type (V ↦ S → V → V → Type)

def UnlabeledGraph : Type ≔ Σ Type (V ↦ V → V → Type)

def IsFunctionalGraph (S V : Type) (E : S → V → V → Type) : Type
  ≔ (s : S) (x : V) → BookIsContr (Σ V (y ↦ E s x y))

def function_graph (S V : Type) (f : S → V → V) : S → V → V → Type ≔ s x y ↦ Id V (f s x) y

def function_graph_functional (S V : Type) (f : S → V → V) : IsFunctionalGraph S V (function_graph S V f)
  ≔ s x ↦ book_contraction (Σ V (y ↦ Id V (f s x) y)) (iscontr_idfrom V (f s x))

{` Families with contractible total space are the representable ones. `}
def ContractibleTotalFamilies (V : Type) : Type ≔ Σ (V → Type) (R ↦ BookIsContr (Σ V R))

def representable_family (V : Type) (y : V) : ContractibleTotalFamilies V
  ≔ (y' ↦ Id V y y', book_contraction (Σ V (y' ↦ Id V y y')) (iscontr_idfrom V y))

def representable_family_fiberwise (V : Type) (R : V → Type) (c : BookIsContr (Σ V R)) (y : V)
  : Equiv (Id V (c .center .fst) y) (R y)
  ≔ let f ≔ (z : V) (p : Id V (c .center .fst) z) ↦ transport V R (c .center .fst) z p (c .center .snd) in
    (f y, fiberwise_from_total V (z ↦ Id V (c .center .fst) z) R f
      (contractible_map_equiv (Σ V (z ↦ Id V (c .center .fst) z)) (Σ V R) (totalize V (z ↦ Id V (c .center .fst) z) R f)
        (book_contraction (Σ V (z ↦ Id V (c .center .fst) z)) (iscontr_idfrom V (c .center .fst))) c) y)

def contractible_total_equiv (V : Type) : Equiv V (ContractibleTotalFamilies V)
  ≔ quasi_inverse_equiv V (ContractibleTotalFamilies V) (representable_family V) (u ↦ u .snd .center .fst)
      (y ↦ refl y)
      (u ↦ let p ≔ funext V (_ ↦ Type) (representable_family V (u .snd .center .fst) .fst) (u .fst)
              (y ↦ ua (Id V (u .snd .center .fst) y) (u .fst y) (representable_family_fiberwise V (u .fst) (u .snd) y)) in
        (p, pathover_of_eq (V → Type) (R ↦ BookIsContr (Σ V R)) (representable_family V (u .snd .center .fst) .fst) (u .fst) p
              (representable_family V (u .snd .center .fst) .snd) (u .snd)
              (book_iscontr_isprop (Σ V (u .fst))
                (transport (V → Type) (R ↦ BookIsContr (Σ V R)) (representable_family V (u .snd .center .fst) .fst) (u .fst) p
                  (representable_family V (u .snd .center .fst) .snd)) (u .snd))))

{` Line 227: the functional S-graphs on V are exactly the graphs of maps S → V → V. `}
def functional_graphs_equiv (S V : Type)
  : Equiv (S → V → V) (Σ (S → V → V → Type) (IsFunctionalGraph S V))
  ≔ compose_equiv (S → V → V) ((s : S) → V → ContractibleTotalFamilies V) (Σ (S → V → V → Type) (IsFunctionalGraph S V))
      (pi_family_equiv S (_ ↦ V → V) (_ ↦ V → ContractibleTotalFamilies V)
        (_ ↦ pi_family_equiv V (_ ↦ V) (_ ↦ ContractibleTotalFamilies V) (_ ↦ contractible_total_equiv V)))
      (compose_equiv ((s : S) → V → ContractibleTotalFamilies V)
        ((s : S) → Σ (V → V → Type) (E ↦ (x : V) → BookIsContr (Σ V (E x))))
        (Σ (S → V → V → Type) (IsFunctionalGraph S V))
        (pi_family_equiv S (_ ↦ V → ContractibleTotalFamilies V) (_ ↦ Σ (V → V → Type) (E ↦ (x : V) → BookIsContr (Σ V (E x))))
          (_ ↦ choice_equiv V (_ ↦ V → Type) (x R ↦ BookIsContr (Σ V R))))
        (choice_equiv S (_ ↦ V → V → Type) (s E ↦ (x : V) → BookIsContr (Σ V (E x)))))

{` Line 245: forgetting the colours. `}
def labeled_graph_forget (S : Type) (G : LabeledGraph S) : UnlabeledGraph
  ≔ (G .fst, x y ↦ Σ S (s ↦ G .snd s x y))

{` Line 243: with a contractible set of colours, labelled graphs are graphs. `}
def contractible_labels_equiv (S : Type) (h : BookIsContr S) : Equiv (LabeledGraph S) UnlabeledGraph
  ≔ family_equiv Type (V ↦ S → V → V → Type) (V ↦ V → V → Type)
      (V ↦ pi_contractible_domain_equiv S (native_contraction S h) (_ ↦ V → V → Type))

{` Lines 249-255: graphs with a total type of edges and source, target, colour maps. `}
def TotalLabeledGraph (S : Type) : Type
  ≔ Σ Type (V ↦ Σ Type (E ↦ Product (E → V) (Product (E → V) (E → S))))

def total_graph_forget (S : Type) (G : TotalLabeledGraph S) : Σ Type (V ↦ Σ Type (E ↦ Product (E → V) (E → V)))
  ≔ (G .fst, (G .snd .fst, (G .snd .snd .fst, G .snd .snd .snd .fst)))

def labeled_total_fiber_equiv (S V : Type)
  : Equiv (S → V → V → Type) (Σ Type (E ↦ Product (E → V) (Product (E → V) (E → S))))
  ≔ let A ≔ Product S (Product V V) in
    compose_equiv (S → V → V → Type) (A → Type) (Σ Type (E ↦ Product (E → V) (Product (E → V) (E → S))))
      (quasi_inverse_equiv (S → V → V → Type) (A → Type)
        (E a ↦ E (a .fst) (a .snd .fst) (a .snd .snd)) (F s x y ↦ F (s, (x, y))) (E ↦ refl E) (F ↦ refl F))
      (compose_equiv (A → Type) (MapsInto A) (Σ Type (E ↦ Product (E → V) (Product (E → V) (E → S))))
        (canonical_inverse_equiv (MapsInto A) (A → Type) (native_equivalence (MapsInto A) (A → Type) (maps_families_equiv A)))
        (family_equiv Type (E ↦ E → A) (E ↦ Product (E → V) (Product (E → V) (E → S)))
          (E ↦ quasi_inverse_equiv (E → A) (Product (E → V) (Product (E → V) (E → S)))
            (f ↦ (e ↦ f e .snd .fst, (e ↦ f e .snd .snd, e ↦ f e .fst)))
            (g e ↦ (g .snd .snd e, (g .fst e, g .snd .fst e)))
            (f ↦ refl f) (g ↦ refl g))))

def labeled_total_equiv (S : Type) : Equiv (LabeledGraph S) (TotalLabeledGraph S)
  ≔ family_equiv Type (V ↦ S → V → V → Type) (V ↦ Σ Type (E ↦ Product (E → V) (Product (E → V) (E → S))))
      (V ↦ labeled_total_fiber_equiv S V)
