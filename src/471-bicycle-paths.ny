export "470-bicycle-meaning"

{` Identifications of bicycles (group.tex 1990–2017).

   First the displayed equivalence for arbitrary elements of
   Σ_{X:U} (X → X) × (X → X):
     ((X,a,b) = (X',a',b')) ≃ Σ_{e : X ≃ X'} (ea = a'e) × (eb = b'e),
   with ea = a'e an identification of functions X → X'. The equivalence
   sends p to the transport along its first component (univalence with the
   transport map, transport_univalence_equiv). `}

def SelfMapPairs : Type ≔ Σ Type (X ↦ Product (X → X) (X → X))

def SelfMapPairIsos (u v : SelfMapPairs) : Type
  ≔ Σ (Equiv (u .fst) (v .fst)) (e ↦ Product
      (Id (u .fst → v .fst) (x ↦ e .map (u .snd .fst x)) (x ↦ v .snd .fst (e .map x)))
      (Id (u .fst → v .fst) (x ↦ e .map (u .snd .snd x)) (x ↦ v .snd .snd (e .map x))))

{` Moving both endpoints of an identity type along identifications. `}
def bicycle_path_endpoints_equiv (A : Type) (x x' : A) (hx : Id A x x') (y y' : A) (hy : Id A y y')
  : Equiv (Id A x y) (Id A x' y')
  ≔ J A x (x' _ ↦ Equiv (Id A x y) (Id A x' y'))
      (J A y (y' _ ↦ Equiv (Id A x y) (Id A x y')) (identity_equiv (Id A x y)) y' hy) x' hx

def self_map_pair_family (X : Type) : Type ≔ Product (X → X) (X → X)

def SelfMapPathoverTarget (X X' : Type) (p : Id Type X X') (u : self_map_pair_family X)
  (v : self_map_pair_family X') : Type
  ≔ Product
      (Id (X → X') (x ↦ transport Type (Y ↦ Y) X X' p (u .fst x)) (x ↦ v .fst (transport Type (Y ↦ Y) X X' p x)))
      (Id (X → X') (x ↦ transport Type (Y ↦ Y) X X' p (u .snd x)) (x ↦ v .snd (transport Type (Y ↦ Y) X X' p x)))

def self_map_pair_paths_split (X : Type) (u v : self_map_pair_family X)
  : Equiv (Id (self_map_pair_family X) u v) (Product (Id (X → X) (u .fst) (v .fst)) (Id (X → X) (u .snd) (v .snd)))
  ≔ quasi_inverse_equiv (Id (self_map_pair_family X) u v)
      (Product (Id (X → X) (u .fst) (v .fst)) (Id (X → X) (u .snd) (v .snd)))
      (r ↦ (r .fst, r .snd)) (s ↦ (s .fst, s .snd)) (r ↦ refl r) (s ↦ refl s)

def self_map_transport_refl_left (X : Type) (f : X → X)
  : Id (X → X) f (x ↦ transport Type (Y ↦ Y) X X (refl X) (f x))
  ≔ funext X (_ ↦ X) f (x ↦ transport Type (Y ↦ Y) X X (refl X) (f x))
      (x ↦ inverse X (transport Type (Y ↦ Y) X X (refl X) (f x)) (f x) (transport_refl Type (Y ↦ Y) X (f x)))

def self_map_transport_refl_right (X : Type) (f : X → X)
  : Id (X → X) f (x ↦ f (transport Type (Y ↦ Y) X X (refl X) x))
  ≔ funext X (_ ↦ X) f (x ↦ f (transport Type (Y ↦ Y) X X (refl X) x))
      (x ↦ refl f (inverse X (transport Type (Y ↦ Y) X X (refl X) x) x (transport_refl Type (Y ↦ Y) X x)))

def self_map_pathover_refl_equiv (X : Type) (u v : self_map_pair_family X)
  : Equiv (Id (self_map_pair_family X) u v) (SelfMapPathoverTarget X X (refl X) u v)
  ≔ compose_equiv (Id (self_map_pair_family X) u v)
      (Product (Id (X → X) (u .fst) (v .fst)) (Id (X → X) (u .snd) (v .snd)))
      (SelfMapPathoverTarget X X (refl X) u v)
      (self_map_pair_paths_split X u v)
      (product_equiv (Id (X → X) (u .fst) (v .fst)) (Id (X → X) (u .snd) (v .snd))
        (Id (X → X) (x ↦ transport Type (Y ↦ Y) X X (refl X) (u .fst x)) (x ↦ v .fst (transport Type (Y ↦ Y) X X (refl X) x)))
        (Id (X → X) (x ↦ transport Type (Y ↦ Y) X X (refl X) (u .snd x)) (x ↦ v .snd (transport Type (Y ↦ Y) X X (refl X) x)))
        (bicycle_path_endpoints_equiv (X → X) (u .fst) (x ↦ transport Type (Y ↦ Y) X X (refl X) (u .fst x))
          (self_map_transport_refl_left X (u .fst))
          (v .fst) (x ↦ v .fst (transport Type (Y ↦ Y) X X (refl X) x)) (self_map_transport_refl_right X (v .fst)))
        (bicycle_path_endpoints_equiv (X → X) (u .snd) (x ↦ transport Type (Y ↦ Y) X X (refl X) (u .snd x))
          (self_map_transport_refl_left X (u .snd))
          (v .snd) (x ↦ v .snd (transport Type (Y ↦ Y) X X (refl X) x)) (self_map_transport_refl_right X (v .snd))))

{` lem:trp-in-function-type for this family, by path induction on p. `}
def self_map_pathover_equiv (X X' : Type) (p : Id Type X X') (u : self_map_pair_family X)
  (v : self_map_pair_family X')
  : Equiv (Id self_map_pair_family p u v) (SelfMapPathoverTarget X X' p u v)
  ≔ J Type X (X' p ↦ (v : self_map_pair_family X') →
        Equiv (Id self_map_pair_family p u v) (SelfMapPathoverTarget X X' p u v))
      (v ↦ self_map_pathover_refl_equiv X u v) X' p v

{` Reindexing a Σ-type along an equivalence of bases with the explicit map
   (a, c) ↦ (e a, c) (as sigma_reindex_equiv of module 284, which this
   module does not import). `}
def bicycle_sigma_base_change (A B : Type) (e : Equiv A B) (C : B → Type)
  : Equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
  ≔ equivalence_induction A (B e ↦ (C : B → Type) → Equiv (Σ A (a ↦ C (e .map a))) (Σ B C))
      (C ↦ identity_equiv (Σ A C)) B e C

def bicycle_sigma_base_change_map (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a)))
  : Id (Σ B C) (bicycle_sigma_base_change A B e C .map u) (e .map (u .fst), u .snd)
  ≔ equivalence_induction A
      (B e ↦ Σ ((C : B → Type) → Equiv (Σ A (a ↦ C (e .map a))) (Σ B C))
        (s ↦ (C : B → Type) (u : Σ A (a ↦ C (e .map a))) → Id (Σ B C) (s C .map u) (e .map (u .fst), u .snd)))
      ((C ↦ identity_equiv (Σ A C)), (C u ↦ refl u))
      B e .snd C u

def bicycle_sigma_reindex_map (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a))) : Σ B C
  ≔ (e .map (u .fst), u .snd)

def bicycle_sigma_reindex_inverse (A B : Type) (e : Equiv A B) (C : B → Type) (w : Σ B C) : Σ A (a ↦ C (e .map a))
  ≔ (equiv_inverse_map A B e (w .fst), refl C (equiv_counit A B e (w .fst)) .trl (w .snd))

def bicycle_sigma_reindex_counit (A B : Type) (e : Equiv A B) (C : B → Type) (w : Σ B C)
  : Id (Σ B C) (bicycle_sigma_reindex_map A B e C (bicycle_sigma_reindex_inverse A B e C w)) w
  ≔ (equiv_counit A B e (w .fst), refl C (equiv_counit A B e (w .fst)) .liftl (w .snd))

def bicycle_sigma_reindex_unit (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a)))
  : Id (Σ A (a ↦ C (e .map a))) (bicycle_sigma_reindex_inverse A B e C (bicycle_sigma_reindex_map A B e C u)) u
  ≔ let D ≔ Σ A (a ↦ C (e .map a)) in
    let f ≔ bicycle_sigma_reindex_map A B e C in
    let g ≔ bicycle_sigma_reindex_inverse A B e C in
    let E ≔ equiv_change_map D (Σ B C) (bicycle_sigma_base_change A B e C) f (bicycle_sigma_base_change_map A B e C) in
    let h ≔ equiv_inverse_map D (Σ B C) E in
    concat D (g (f u)) (h (f (g (f u)))) u
      (equiv_unit D (Σ B C) E (g (f u)))
      (concat D (h (f (g (f u)))) (h (f u)) u
        (refl h (bicycle_sigma_reindex_counit A B e C (f u)))
        (equiv_retraction D (Σ B C) E u))

def bicycle_sigma_reindex_equiv (A B : Type) (e : Equiv A B) (C : B → Type)
  : Equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
  ≔ quasi_inverse_equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
      (bicycle_sigma_reindex_map A B e C) (bicycle_sigma_reindex_inverse A B e C)
      (bicycle_sigma_reindex_unit A B e C) (bicycle_sigma_reindex_counit A B e C)

def self_map_iso_family (u v : SelfMapPairs) (e : Equiv (u .fst) (v .fst)) : Type
  ≔ Product
      (Id (u .fst → v .fst) (x ↦ e .map (u .snd .fst x)) (x ↦ v .snd .fst (e .map x)))
      (Id (u .fst → v .fst) (x ↦ e .map (u .snd .snd x)) (x ↦ v .snd .snd (e .map x)))

{` The displayed equivalence of group.tex 1996–2001. `}
def self_map_pairs_paths_equiv (u v : SelfMapPairs) : Equiv (Id SelfMapPairs u v) (SelfMapPairIsos u v)
  ≔ let T ≔ transport_univalence_equiv (u .fst) (v .fst) in
    compose_equiv (Id SelfMapPairs u v) (SigmaPath Type self_map_pair_family u v) (SelfMapPairIsos u v)
      (canonical_inverse_equiv (SigmaPath Type self_map_pair_family u v) (Id SelfMapPairs u v)
        (sigma_path_equiv Type self_map_pair_family u v))
      (compose_equiv (SigmaPath Type self_map_pair_family u v)
        (Σ (Id Type (u .fst) (v .fst)) (p ↦ self_map_iso_family u v (T .map p)))
        (SelfMapPairIsos u v)
        (family_equiv (Id Type (u .fst) (v .fst))
          (p ↦ Id self_map_pair_family p (u .snd) (v .snd))
          (p ↦ self_map_iso_family u v (T .map p))
          (p ↦ self_map_pathover_equiv (u .fst) (v .fst) p (u .snd) (v .snd)))
        (bicycle_sigma_reindex_equiv (Id Type (u .fst) (v .fst)) (Equiv (u .fst) (v .fst)) T
          (self_map_iso_family u v)))

{` Bicycles. "If X and X' are sets, then this is the subtype of X → X'
   consisting of equivalences e satisfying ea = a'e and eb = b'e"; we state
   the commutation pointwise (Commutes, module 63: e(a x) = a'(e x)). `}
def BicycleIsomorphisms (B B' : Bicycles) : Type
  ≔ Σ (Equiv (bicycle_carrier B) (bicycle_carrier B')) (e ↦ Product
      (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (e .map))
      (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (e .map)))

{` The structure on a set X in def:bicycle: Σ_{a} Σ_{b} (‖X‖ × Π ∃ ...);
   Bicycles is Σ SetTypes bicycle_structure by definition. `}
def bicycle_structure (X : SetTypes) : Type
  ≔ Σ (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦ BicycleConnected (X .fst) a b))

def bicycle_structure_set (X : SetTypes) : isSet (bicycle_structure X)
  ≔ sigma_set (SetAutomorphisms X) (a ↦ Σ (SetAutomorphisms X) (b ↦ BicycleConnected (X .fst) a b))
      (equivalences_set (X .fst) (X .fst) (X .snd))
      (a ↦ sigma_set (SetAutomorphisms X) (b ↦ BicycleConnected (X .fst) a b)
        (equivalences_set (X .fst) (X .fst) (X .snd))
        (b ↦ prop_is_set (BicycleConnected (X .fst) a b) (bicycle_connected_prop (X .fst) a b)))

def bicycle_structure_pathover_prop (S T : SetTypes) (s : Id SetTypes S T)
  (u : bicycle_structure S) (v : bicycle_structure T) : isProp (Id bicycle_structure s u v)
  ≔ hlevel_one_to_prop (Id bicycle_structure s u v)
      (pathover_hlevel (suc. zero.) SetTypes bicycle_structure
        (S ↦ set_to_hlevel_two (bicycle_structure S) (bicycle_structure_set S)) S T s u v)

{` The sets with two permutations, the base of the connectivity predicate. `}
def BicycleDataTriples : Type ≔ Σ SetTypes (X ↦ Σ (SetAutomorphisms X) (_ ↦ SetAutomorphisms X))

def bicycle_triple_connected (t : BicycleDataTriples) : Type
  ≔ BicycleConnected (t .fst .fst) (t .snd .fst) (t .snd .snd)

def BicycleCommutations (S T : SetTypes) (a b : SetAutomorphisms S) (a' b' : SetAutomorphisms T)
  (f : S .fst → T .fst) : Type
  ≔ Product (Commutes (S .fst) (T .fst) a a' f) (Commutes (S .fst) (T .fst) b b' f)

def bicycle_commutations_prop (S T : SetTypes) (a b : SetAutomorphisms S) (a' b' : SetAutomorphisms T)
  (f : S .fst → T .fst) : isProp (BicycleCommutations S T a b a' b' f)
  ≔ product_prop (Commutes (S .fst) (T .fst) a a' f) (Commutes (S .fst) (T .fst) b b' f)
      (commutes_prop (S .fst) (T .fst) (T .snd) a a' f) (commutes_prop (S .fst) (T .fst) (T .snd) b b' f)

{` The fiberwise step: a path of bicycle structures over s : X = X' is
   the same as the commutation of the transport along s with a, b. `}
def bicycle_structure_pathover_commutes (S T : SetTypes) (s : Id SetTypes S T)
  (u : bicycle_structure S) (v : bicycle_structure T)
  : Equiv (Id bicycle_structure s u v)
      (BicycleCommutations S T (u .fst) (u .snd .fst) (v .fst) (v .snd .fst) (set_paths_transport_equiv S T .map s .map))
  ≔ let ca ≔ automorphism_pathover_commutes S T s (u .fst) (v .fst) in
    let cb ≔ automorphism_pathover_commutes S T s (u .snd .fst) (v .snd .fst) in
    iff_equiv (Id bicycle_structure s u v)
      (BicycleCommutations S T (u .fst) (u .snd .fst) (v .fst) (v .snd .fst) (set_paths_transport_equiv S T .map s .map))
      (bicycle_structure_pathover_prop S T s u v)
      (bicycle_commutations_prop S T (u .fst) (u .snd .fst) (v .fst) (v .snd .fst) (set_paths_transport_equiv S T .map s .map))
      (q ↦ (ca .map (q .fst), cb .map (q .snd .fst)))
      (c ↦ let qa ≔ equiv_inverse_map (Id SetAutomorphisms s (u .fst) (v .fst))
               (Commutes (S .fst) (T .fst) (u .fst) (v .fst) (set_paths_transport_equiv S T .map s .map)) ca (c .fst) in
           let qb ≔ equiv_inverse_map (Id SetAutomorphisms s (u .snd .fst) (v .snd .fst))
               (Commutes (S .fst) (T .fst) (u .snd .fst) (v .snd .fst) (set_paths_transport_equiv S T .map s .map)) cb (c .snd) in
           (qa, (qb,
             pathover_hlevel zero. BicycleDataTriples bicycle_triple_connected
               (t ↦ prop_to_hlevel_one (bicycle_triple_connected t) (bicycle_connected_prop (t .fst .fst) (t .snd .fst) (t .snd .snd)))
               (S, (u .fst, u .snd .fst)) (T, (v .fst, v .snd .fst)) (s, (qa, qb)) (u .snd .snd) (v .snd .snd) .center)))

{` The identification of bicycle paths, group.tex 1996–2017, for bicycles:
   (B = B') ≃ Σ_{e : X ≃ X'} (ea = a'e) × (eb = b'e). The equivalence of the
   first component is transport along the underlying path of sets. `}
def bicycle_paths_equiv (B B' : Bicycles) : Equiv (Id Bicycles B B') (BicycleIsomorphisms B B')
  ≔ compose_equiv (Id Bicycles B B') (SigmaPath SetTypes bicycle_structure B B') (BicycleIsomorphisms B B')
      (canonical_inverse_equiv (SigmaPath SetTypes bicycle_structure B B') (Id Bicycles B B')
        (sigma_path_equiv SetTypes bicycle_structure B B'))
      (propositional_subtype_equiv (Id SetTypes (bicycle_set B) (bicycle_set B'))
        (Equiv (bicycle_carrier B) (bicycle_carrier B'))
        (s ↦ Id bicycle_structure s (B .snd) (B' .snd))
        (e ↦ BicycleCommutations (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (e .map))
        (s ↦ bicycle_structure_pathover_prop (bicycle_set B) (bicycle_set B') s (B .snd) (B' .snd))
        (e ↦ bicycle_commutations_prop (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (e .map))
        (set_paths_transport_equiv (bicycle_set B) (bicycle_set B'))
        (s ↦ bicycle_structure_pathover_commutes (bicycle_set B) (bicycle_set B') s (B .snd) (B' .snd)))

{` ev: the underlying equivalence of a path of bicycles, applied to a point
   (the book's ev_x(e) = e(x)); it is transport along the path of sets. `}
def bicycle_path_evaluate (B B' : Bicycles) (p : Id Bicycles B B') (x : bicycle_carrier B) : bicycle_carrier B'
  ≔ bicycle_paths_equiv B B' .map p .fst .map x

def bicycle_path_evaluate_transport (B B' : Bicycles) (p : Id Bicycles B B') (x : bicycle_carrier B)
  : Id (bicycle_carrier B') (bicycle_path_evaluate B B' p x)
      (transport Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B') (p .fst .fst) x)
  ≔ refl (transport Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B') (p .fst .fst) x)

{` The inverse direction, with the path of sets set_types_path (ua e), so
   that the path acts by e (litmus: bicycle_path_from_iso_evaluate is refl). `}
def bicycle_path_from_iso (B B' : Bicycles) (e : BicycleIsomorphisms B B') : Id Bicycles B B'
  ≔ let s ≔ set_types_path (bicycle_set B) (bicycle_set B') (e .fst) in
    (s, equiv_inverse_map (Id bicycle_structure s (B .snd) (B' .snd))
      (BicycleCommutations (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B')
        (set_paths_transport_equiv (bicycle_set B) (bicycle_set B') .map s .map))
      (bicycle_structure_pathover_commutes (bicycle_set B) (bicycle_set B') s (B .snd) (B' .snd)) (e .snd))

def bicycle_path_from_iso_evaluate (B B' : Bicycles) (e : BicycleIsomorphisms B B') (x : bicycle_carrier B)
  : Id (bicycle_carrier B') (bicycle_path_evaluate B B' (bicycle_path_from_iso B B' e) x) (e .fst .map x)
  ≔ refl (e .fst .map x)

{` The two directions are inverse on isomorphisms (the first components agree
   by definition). `}
def bicycle_path_from_iso_iso (B B' : Bicycles) (e : BicycleIsomorphisms B B')
  : Id (BicycleIsomorphisms B B') (bicycle_paths_equiv B B' .map (bicycle_path_from_iso B B' e)) e
  ≔ subtype_equal (Equiv (bicycle_carrier B) (bicycle_carrier B'))
      (f ↦ BicycleCommutations (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (f .map))
      (f ↦ bicycle_commutations_prop (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (f .map))
      (bicycle_paths_equiv B B' .map (bicycle_path_from_iso B B' e)) e
      (equiv_path (bicycle_carrier B) (bicycle_carrier B')
        (bicycle_paths_equiv B B' .map (bicycle_path_from_iso B B' e) .fst) (e .fst) (refl (e .fst .map)))

def bicycle_isomorphisms_set (B B' : Bicycles) : isSet (BicycleIsomorphisms B B')
  ≔ sigma_set (Equiv (bicycle_carrier B) (bicycle_carrier B'))
      (e ↦ Product
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (e .map))
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (e .map)))
      (equivalences_set (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B'))
      (e ↦ prop_is_set
        (Product
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (e .map))
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (e .map)))
        (product_prop
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (e .map))
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (e .map))
          (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_a B) (bicycle_a B') (e .map))
          (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_b B) (bicycle_b B') (e .map))))

{` Bicyc is a groupoid (needed for Aut_Bicyc in def:Dinfty-Q). `}
def bicycles_groupoid : isGroupoid Bicycles
  ≔ B B' ↦ hlevel_two_to_set (Id Bicycles B B')
      (hlevel_equiv (suc. (suc. zero.)) (BicycleIsomorphisms B B') (Id Bicycles B B')
        (canonical_inverse_equiv (Id Bicycles B B') (BicycleIsomorphisms B B') (bicycle_paths_equiv B B'))
        (set_to_hlevel_two (BicycleIsomorphisms B B') (bicycle_isomorphisms_set B B')))

{` "this is the subtype of X → X'": the underlying-map projection from the
   isomorphisms to X → X' is injective (an embedding, def:injection). `}
def bicycle_isomorphism_map (B B' : Bicycles) (e : BicycleIsomorphisms B B') : bicycle_carrier B → bicycle_carrier B'
  ≔ e .fst .map

def bicycle_isomorphism_map_embedding (B B' : Bicycles)
  : IsEmbedding (BicycleIsomorphisms B B') (bicycle_carrier B → bicycle_carrier B') (bicycle_isomorphism_map B B')
  ≔ path_reflecting_set_embedding (BicycleIsomorphisms B B') (bicycle_carrier B → bicycle_carrier B')
      (pi_set (bicycle_carrier B) (_ ↦ bicycle_carrier B') (_ ↦ bicycle_carrier_set B'))
      (bicycle_isomorphism_map B B')
      (e d p ↦ subtype_equal (Equiv (bicycle_carrier B) (bicycle_carrier B'))
        (f ↦ Product
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (f .map))
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (f .map)))
        (f ↦ product_prop
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (f .map))
          (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (f .map))
          (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_a B) (bicycle_a B') (f .map))
          (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_b B) (bicycle_b B') (f .map)))
        e d (equiv_path (bicycle_carrier B) (bicycle_carrier B') (e .fst) (d .fst) p))

{` group.tex 2014–2017: the symmetries of a bicycle (X,a,b) are the
   self-equivalences of X commuting with a and b. `}
def bicycle_symmetries_equiv (B : Bicycles) : Equiv (Id Bicycles B B) (BicycleIsomorphisms B B)
  ≔ bicycle_paths_equiv B B

{` The automorphism group Aut_Bicyc(B) and its symmetries. `}
def bicycle_automorphism_group (B : Bicycles) : Group ≔ automorphism_group Bicycles bicycles_groupoid B

def bicycle_automorphism_group_usym_equiv (B : Bicycles)
  : Equiv (USym (bicycle_automorphism_group B)) (BicycleIsomorphisms B B)
  ≔ compose_equiv (USym (bicycle_automorphism_group B)) (Id Bicycles B B) (BicycleIsomorphisms B B)
      (automorphism_group_usym_equiv Bicycles bicycles_groupoid B) (bicycle_paths_equiv B B)
