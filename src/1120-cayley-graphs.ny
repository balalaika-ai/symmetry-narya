export "1104-one-vertex-graphs"
export "1100-labeled-graphs"
export "109-connected-map-sections"
export "96-yoneda-embedding"
export "406-symmetric-group-three"

{` fggroups.tex, section "Graphs and Cayley graphs": generation (def:gens-gp, in
   the surjective form of line 209; the literal epimorphism form is module 1121),
   the map ρ_S of lem:gens-gp-iff, the Cayley graph (def:cayley-graph) and the
   "only if" direction of lem:gens-gp-iff.

   The free group is the constructed F_S (module 877) for S with decidable
   equality (the book: "a (finite or just decidable) set of generators S", line
   138); free_induced_hom S dec G ι is the homomorphism F_S → G induced by
   ι : S → USym G (the book's ι need not be injective here).

   ρ_S(t) ≔ (t = sh_G, s ↦ (p ↦ ι(s) · p)) with ι(s) · p = concat p (ι s) (book order:
   first p, then ι(s)).

   rho_embedding_of_surjective (lem:gens-gp-iff, "only if"): if F_S → G is
   surjective on symmetries then ρ_S is an embedding.  Proof: ρ_S is identified
   with Ev ∘ Y, where Y(t) ≔ (z ↦ t = Bφ(z)) : BG → (B F_S → U) is the
   representable family restricted along Bφ (an embedding because Bφ has
   connected fibers, lem:epi-surj easy direction, and families of sets restrict
   faithfully along connected maps, module 109), and Ev(P) ≔ (P(base), s ↦ transport
   along loop_s) is an embedding (universal property of B F_S composed with the
   embedding (X = X) ↪ (X → X)).  The "if" direction is false as printed
   (module 1121). `}

{` ---------- Generic embedding lemmas ---------- `}

def embedding_of_equiv (A B : Type) (e : Equiv A B) : IsEmbedding A B (e .map)
  ≔ path_equivalences_embedding A B (e .map)
      (x y ↦ book_equivalence (Id A x y) (Id B (e .map x) (e .map y)) (equivalence_on_paths A B e x y) .equiv)

def embedding_compose (A B C : Type) (f : A → B) (g : B → C) (hf : IsEmbedding A B f) (hg : IsEmbedding B C g)
  : IsEmbedding A C (x ↦ g (f x))
  ≔ path_equivalences_embedding A C (x ↦ g (f x))
      (x y ↦ book_equivalence (Id A x y) (Id C (g (f x)) (g (f y)))
        (compose_equiv (Id A x y) (Id B (f x) (f y)) (Id C (g (f x)) (g (f y)))
          (native_equivalence (Id A x y) (Id B (f x) (f y)) (embedding_on_paths A B f hf x y))
          (native_equivalence (Id B (f x) (f y)) (Id C (g (f x)) (g (f y))) (embedding_on_paths B C g hg (f x) (f y)))) .equiv)

def embedding_homotopic (A B : Type) (f g : A → B) (h : (a : A) → Id B (f a) (g a)) (hf : IsEmbedding A B f)
  : IsEmbedding A B g
  ≔ transport (A → B) (IsEmbedding A B) f g (funext A (_ ↦ B) f g h) hf

def prop_of_equiv_book (A B : Type) (e : BookEquiv A B) (h : isProp B) : isProp A
  ≔ let n ≔ native_equivalence A B e in
    a a' ↦ concat A a (equiv_inverse_map A B n (n .map a)) a' (equiv_unit A B n a)
      (concat A (equiv_inverse_map A B n (n .map a)) (equiv_inverse_map A B n (n .map a')) a'
        (refl (equiv_inverse_map A B n) (h (n .map a) (n .map a'))) (equiv_retraction A B n a'))

def sigma_fiberwise_embedding (A : Type) (B C : A → Type) (g : (a : A) → B a → C a)
  (hg : (a : A) → IsEmbedding (B a) (C a) (g a))
  : IsEmbedding (Σ A B) (Σ A C) (totalize A B C g)
  ≔ c ↦ prop_of_equiv_book (BookFiber (Σ A B) (Σ A C) (totalize A B C g) c) (BookFiber (B (c .fst)) (C (c .fst)) (g (c .fst)) (c .snd))
      (book_equivalence (BookFiber (Σ A B) (Σ A C) (totalize A B C g) c) (BookFiber (B (c .fst)) (C (c .fst)) (g (c .fst)) (c .snd))
        (total_fiber_equiv A B C g (c .fst) (c .snd)))
      (hg (c .fst) (c .snd))

def equiv_map_embedding (X Y : Type) : IsEmbedding (Equiv X Y) (X → Y) (e ↦ e .map)
  ≔ embedding_compose (Equiv X Y) (Σ (X → Y) (isEquiv X Y)) (X → Y) (e ↦ (e .map, e .equiv)) (u ↦ u .fst)
      (embedding_of_equiv (Equiv X Y) (Σ (X → Y) (isEquiv X Y)) (equiv_sigma_equiv X Y))
      (subtype_projection_embedding (X → Y) (isEquiv X Y) (isequiv_isprop X Y))

def coe_embedding (X : Type) : IsEmbedding (Id Type X X) (X → X) (p ↦ p .trr)
  ≔ embedding_compose (Id Type X X) (Equiv X X) (X → X) (transport_univalence_equiv X X .map) (e ↦ e .map)
      (embedding_of_equiv (Id Type X X) (Equiv X X) (transport_univalence_equiv X X))
      (equiv_map_embedding X X)

{` ---------- Generation, ρ_S and the Cayley graph ---------- `}

def free_induced_hom (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  : GroupHom (constructed_free_group S dec) G
  ≔ equiv_inverse_map (GroupHom (constructed_free_group S dec) G) (S → USym G) (constructed_free_group_hom_equiv S dec G) iota

def free_induced_hom_generator (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G) (s : S)
  : Id (USym G) (usym_hom (constructed_free_group S dec) G (free_induced_hom S dec G iota) (constructed_free_group_generator S dec s))
      (iota s)
  ≔ concat (USym G)
      (usym_hom (constructed_free_group S dec) G (free_induced_hom S dec G iota) (constructed_free_group_generator S dec s))
      (constructed_free_group_hom_equiv S dec G .map (free_induced_hom S dec G iota) s) (iota s)
      (inverse (USym G) (constructed_free_group_hom_equiv S dec G .map (free_induced_hom S dec G iota) s)
        (usym_hom (constructed_free_group S dec) G (free_induced_hom S dec G iota) (constructed_free_group_generator S dec s))
        (constructed_free_group_hom_equiv_evaluation S dec G (free_induced_hom S dec G iota) s))
      (happly S (_ ↦ USym G) (constructed_free_group_hom_equiv S dec G .map (free_induced_hom S dec G iota)) iota
        (equiv_counit (GroupHom (constructed_free_group S dec) G) (S → USym G) (constructed_free_group_hom_equiv S dec G) iota) s)

{` Line 209: "S generates G iff the map on elements U F_S → U G is surjective". `}
def GeneratesSurjectively (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G) : Type
  ≔ Surjective (USym (constructed_free_group S dec)) (USym G) (usym_hom (constructed_free_group S dec) G (free_induced_hom S dec G iota))

def RhoTarget (S : Type) : Type ≔ Σ Type (X ↦ S → X → X)

{` ρ_S(t) ≔ (t = sh_G, s ↦ ι(s) · _). `}
def rho_map (G : Group) (S : Type) (iota : S → USym G) (t : BG G .carrier) : RhoTarget S
  ≔ (Id (BG G .carrier) t (shape G), s p ↦ concat (BG G .carrier) t (shape G) (shape G) p (iota s))

def RhoEmbedding (G : Group) (S : Type) (iota : S → USym G) : Type
  ≔ IsEmbedding (BG G .carrier) (RhoTarget S) (rho_map G S iota)

{` def:cayley-graph, literally: vertices USym G, edges S × USym G, the edge (s, g)
   has source g, target ι(s)·g and colour s. `}
def cayley_graph (G : Group) (S : Type) (iota : S → USym G) : TotalLabeledGraph S
  ≔ (USym G, (Product S (USym G), (e ↦ e .snd, (e ↦ usym_mul G (iota (e .fst)) (e .snd), e ↦ e .fst))))

{` Line 240: the Cayley graph is ρ_S(sh_G) considered as an S-coloured graph
   (the graph of its functions, module 1100): the total edge types correspond,
   compatibly with source, target and colour. `}
def cayley_rho_graph (G : Group) (S : Type) (iota : S → USym G) : LabeledGraph S
  ≔ (rho_map G S iota (shape G) .fst, function_graph S (rho_map G S iota (shape G) .fst) (rho_map G S iota (shape G) .snd))

def cayley_edges_equiv (G : Group) (S : Type) (iota : S → USym G)
  : Equiv (Product S (USym G)) (Σ S (s ↦ Σ (USym G) (g ↦ Σ (USym G) (h ↦ Id (USym G) (usym_mul G (iota s) g) h))))
  ≔ quasi_inverse_equiv (Product S (USym G)) (Σ S (s ↦ Σ (USym G) (g ↦ Σ (USym G) (h ↦ Id (USym G) (usym_mul G (iota s) g) h))))
      (e ↦ (e .fst, (e .snd, (usym_mul G (iota (e .fst)) (e .snd), refl (usym_mul G (iota (e .fst)) (e .snd))))))
      (u ↦ (u .fst, u .snd .fst))
      (e ↦ refl e)
      (u ↦ (refl (u .fst), (refl (u .snd .fst),
        contractible_prop (Σ (USym G) (h ↦ Id (USym G) (usym_mul G (iota (u .fst)) (u .snd .fst)) h))
          (iscontr_idfrom (USym G) (usym_mul G (iota (u .fst)) (u .snd .fst)))
          (usym_mul G (iota (u .fst)) (u .snd .fst), refl (usym_mul G (iota (u .fst)) (u .snd .fst))) (u .snd .snd))))

def cayley_rho_edge_type (G : Group) (S : Type) (iota : S → USym G) (s : S) (g h : USym G)
  : Id Type (cayley_rho_graph G S iota .snd s g h) (Id (USym G) (usym_mul G (iota s) g) h)
  ≔ refl (Id (USym G) (usym_mul G (iota s) g) h)

{` Litmus: in the Cayley graph of Σ_3 for S = {τ, σ} (bool-indexed), the σ-edge out
   of τ ends at σ·τ, which sends 0 to 2. `}
def sigma3_generators (b : Bool) : USym (symmetric_group three) ≔ match b [ false. ↦ sigma3_tau | true. ↦ sigma3_sigma ]

def cayley_sigma3_litmus
  : Id (Fin three)
      (permutation_action (standard_set three)
        (cayley_graph (symmetric_group three) Bool sigma3_generators .snd .snd .snd .fst (true., sigma3_tau)) fin3_zero)
      fin3_two
  ≔ sigma3_sigma_tau_zero
