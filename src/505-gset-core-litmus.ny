export "504-torsors"
export "406-symmetric-group-three"

{` Litmus checks for the chapter-5 core: the standard Σ_n-set and the
   action of Σ_3 on Fin 3, the principal G-set is transitive and free, every
   element of a trivial G-set is fixed. `}

{` The standard Σ_n-set (example after std-action): the composite of the
   standard action of Σ_n with the projection BΣ_n → Set, X(A, !) ≔ A. Its
   underlying set is Fin n by definition. `}
def standard_symmetric_gset (n : Nat) : GSet (symmetric_group n) ≔ z ↦ z .fst

def standard_symmetric_gset_underlying (n : Nat)
  : Id Type (gset_underlying (symmetric_group n) (standard_symmetric_gset n)) (Fin n)
  ≔ refl (Fin n)

{` The action of a symmetry of Σ_S on the standard Σ_S-set is the
   permutation itself, definitionally. `}
def standard_symmetric_gset_act (n : Nat) (e : Equiv (Fin n) (Fin n)) (x : Fin n)
  : Id (Fin n) (gset_usym_act (symmetric_group n) (standard_symmetric_gset n)
        (permutation_symmetry (standard_set n) e) x) (e .map x)
  ≔ refl (e .map x)

{` Σ_3 acting on Fin 3: τ = (0 1) and σ = (1 2). `}
def sigma3_gset_tau_zero
  : Id (Fin three) (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) sigma3_tau fin3_zero) fin3_one
  ≔ refl fin3_one

def sigma3_gset_sigma_one
  : Id (Fin three) (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) sigma3_sigma fin3_one) fin3_two
  ≔ refl fin3_two

def sigma3_gset_sigma_zero
  : Id (Fin three) (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) sigma3_sigma fin3_zero) fin3_zero
  ≔ refl fin3_zero

{` (σ · τ) · 0 = σ · (τ · 0) = σ · 1 = 2: the action law in the book's
   orientation. `}
def sigma3_gset_mul_zero
  : Id (Fin three)
      (gset_usym_act (symmetric_group three) (standard_symmetric_gset three)
        (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau) fin3_zero) fin3_two
  ≔ gset_act_mul (symmetric_group three) (standard_symmetric_gset three) sigma3_sigma sigma3_tau fin3_zero

{` The principal G-set is transitive (its action type is contractible). `}
def principal_gset_transitive (G : Group) : IsTransitive G (principal_gset G)
  ≔ gset_paths_transitive G (shape G)

{` The principal G-set is free: the component of any point in its
   contractible action type is contractible. `}
def gset_contractible_component (A : Type) (h : BookIsContr A) (a : A)
  : BookIsContr (NativeComponent A a)
  ≔ let hn ≔ native_contraction A h in
    book_contraction (NativeComponent A a)
      (sigma_contractible A (x ↦ Mere (Id A a x)) hn
        (x ↦ (mere (Id A a x) (contractible_prop A hn a x),
              m ↦ mere_isprop (Id A a x) m (mere (Id A a x) (contractible_prop A hn a x)))))

def principal_gset_free (G : Group) : IsFreeGSet G (principal_gset G)
  ≔ g ↦ gset_contractible_component (ActionType G (principal_gset G))
      (gset_paths_action_type_contractible G (shape G)) (shape G, g)

{` Every element s of a trivial G-set triv_G S is fixed: i_s is an
   equivalence, with inverse z ↦ ((z, s), !). `}
def trivial_gset_component_point (G : Group) (S : SetTypes) (s : S .fst) (z : BG G .carrier)
  : NativeComponent (ActionType G (gset_trivial G S)) (shape G, s)
  ≔ ((z, s), mere_rec (Id (BG G .carrier) (shape G) z) (Mere (Id (ActionType G (gset_trivial G S)) (shape G, s) (z, s)))
        (mere_isprop (Id (ActionType G (gset_trivial G S)) (shape G, s) (z, s)))
        (p ↦ mere (Id (ActionType G (gset_trivial G S)) (shape G, s) (z, s))
          (action_type_path G (gset_trivial G S) (shape G) z s s p (gset_trivial_act G S (shape G) z p s)))
        (bg_connected G .snd (shape G) z))

def trivial_gset_component_same (G : Group) (S : SetTypes) (s : S .fst)
  (c : NativeComponent (ActionType G (gset_trivial G S)) (shape G, s)) : Id (S .fst) s (c .fst .snd)
  ≔ let T ≔ ActionType G (gset_trivial G S) in
    mere_rec (Id T (shape G, s) (c .fst)) (Id (S .fst) s (c .fst .snd)) (S .snd s (c .fst .snd))
      (r ↦ let ge ≔ action_type_path_equiv G (gset_trivial G S) (shape G, s) (c .fst) .map r in
        concat (S .fst) s (gset_act G (gset_trivial G S) (shape G) (c .fst .fst) (ge .fst) s) (c .fst .snd)
          (inverse (S .fst) (gset_act G (gset_trivial G S) (shape G) (c .fst .fst) (ge .fst) s) s
            (gset_trivial_act G S (shape G) (c .fst .fst) (ge .fst) s))
          (ge .snd))
      (c .snd)

def trivial_gset_fixed (G : Group) (S : SetTypes) (s : S .fst) : IsFixedElement G (gset_trivial G S) s
  ≔ let T ≔ ActionType G (gset_trivial G S) in
    let C ≔ NativeComponent T (shape G, s) in
    book_quasi_inverse_equiv C (BG G .carrier) (c ↦ c .fst .fst) (trivial_gset_component_point G S s)
      (c ↦ component_path T (shape G, s) (trivial_gset_component_point G S s (c .fst .fst)) c
        (action_type_path G (gset_trivial G S) (c .fst .fst) (c .fst .fst) s (c .fst .snd) (refl (c .fst .fst))
          (concat (S .fst) (gset_act G (gset_trivial G S) (c .fst .fst) (c .fst .fst) (refl (c .fst .fst)) s) s
            (c .fst .snd)
            (gset_act_refl G (gset_trivial G S) (c .fst .fst) s) (trivial_gset_component_same G S s c))))
      (z ↦ refl z)
    .equiv
