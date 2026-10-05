export "1121-generation-epi"

{` Running-text claims of fggroups.tex, section "Graphs and Cayley graphs".

   - lines 129-132: Σ_X (X ≃ X) is a subtype of Σ_X (X → X)
     (equiv_endo_structures_embedding);
   - lines 133-134: thinking of functions as their graphs, Σ_X (X → X) is a subtype of
     Σ_X (X → X → U) (function_graph_structures_embedding);
   - footnote at line 171: (t = sh_G) ≃ (sh_G = t) (path_flip_equiv, module 1121);
   - lines 174-175: if S generates G, G is the automorphism group of ρ_S(sh_G) in
     Σ_X (S → X → X) (gens_gp_automorphisms, module 1121) and even in the larger type
     Σ_X (S → X → X → U) (gens_gp_automorphisms_graphs). `}

def function_graph_unlabeled (X : Type) (f : X → X) : X → X → Type ≔ x y ↦ Id X (f x) y

def function_graph_unlabeled_embedding (X : Type) : IsEmbedding (X → X) (X → X → Type) (function_graph_unlabeled X)
  ≔ embedding_compose (X → X) (Σ (X → X → Type) (R ↦ (x : X) → BookIsContr (Σ X (R x)))) (X → X → Type)
      (compose_equiv (X → X) (X → ContractibleTotalFamilies X) (Σ (X → X → Type) (R ↦ (x : X) → BookIsContr (Σ X (R x))))
        (pi_family_equiv X (_ ↦ X) (_ ↦ ContractibleTotalFamilies X) (_ ↦ contractible_total_equiv X))
        (choice_equiv X (_ ↦ X → Type) (x R ↦ BookIsContr (Σ X R))) .map)
      (u ↦ u .fst)
      (embedding_of_equiv (X → X) (Σ (X → X → Type) (R ↦ (x : X) → BookIsContr (Σ X (R x))))
        (compose_equiv (X → X) (X → ContractibleTotalFamilies X) (Σ (X → X → Type) (R ↦ (x : X) → BookIsContr (Σ X (R x))))
          (pi_family_equiv X (_ ↦ X) (_ ↦ ContractibleTotalFamilies X) (_ ↦ contractible_total_equiv X))
          (choice_equiv X (_ ↦ X → Type) (x R ↦ BookIsContr (Σ X R)))))
      (subtype_projection_embedding (X → X → Type) (R ↦ (x : X) → BookIsContr (Σ X (R x)))
        (R ↦ pi_prop X (x ↦ BookIsContr (Σ X (R x))) (x ↦ book_iscontr_isprop (Σ X (R x)))))

{` Lines 129-132. `}
def equiv_endo_structures_embedding
  : IsEmbedding (Σ Type (X ↦ Equiv X X)) (Σ Type (X ↦ X → X)) (totalize Type (X ↦ Equiv X X) (X ↦ X → X) (X e ↦ e .map))
  ≔ sigma_fiberwise_embedding Type (X ↦ Equiv X X) (X ↦ X → X) (X e ↦ e .map) (X ↦ equiv_map_embedding X X)

{` Lines 133-134. `}
def function_graph_structures_embedding
  : IsEmbedding (Σ Type (X ↦ X → X)) (Σ Type (X ↦ X → X → Type))
      (totalize Type (X ↦ X → X) (X ↦ X → X → Type) (X f ↦ function_graph_unlabeled X f))
  ≔ sigma_fiberwise_embedding Type (X ↦ X → X) (X ↦ X → X → Type) (X f ↦ function_graph_unlabeled X f)
      (X ↦ function_graph_unlabeled_embedding X)

{` Lines 174-175: ρ_S followed by "graph of each function" is still an embedding. `}
def rho_graph_map (G : Group) (S : Type) (iota : S → USym G) (t : BG G .carrier) : Σ Type (X ↦ S → X → X → Type)
  ≔ (rho_map G S iota t .fst, s ↦ function_graph_unlabeled (rho_map G S iota t .fst) (rho_map G S iota t .snd s))

def gens_gp_graph_embedding (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  (h : GeneratesGroup S dec G iota)
  : IsEmbedding (BG G .carrier) (Σ Type (X ↦ S → X → X → Type)) (rho_graph_map G S iota)
  ≔ embedding_compose (BG G .carrier) (RhoTarget S) (Σ Type (X ↦ S → X → X → Type)) (rho_map G S iota)
      (totalize Type (X ↦ S → X → X) (X ↦ S → X → X → Type) (X f s ↦ function_graph_unlabeled X (f s)))
      (gens_gp_only_if S dec G iota h)
      (sigma_fiberwise_embedding Type (X ↦ S → X → X) (X ↦ S → X → X → Type) (X f s ↦ function_graph_unlabeled X (f s))
        (X ↦ postcomposition_embedding S (X → X) (X → X → Type) (function_graph_unlabeled X)
          (function_graph_unlabeled_embedding X)))

def gens_gp_automorphisms_graphs (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  (h : GeneratesGroup S dec G iota)
  : BookEquiv (USym G) (Id (Σ Type (X ↦ S → X → X → Type)) (rho_graph_map G S iota (shape G)) (rho_graph_map G S iota (shape G)))
  ≔ embedding_on_paths (BG G .carrier) (Σ Type (X ↦ S → X → X → Type)) (rho_graph_map G S iota)
      (gens_gp_graph_embedding S dec G iota h) (shape G) (shape G)
