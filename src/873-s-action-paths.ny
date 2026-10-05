export "870-free-s-sets"

{` The type of types with an S-indexed family of endomaps, and its
   identity types: (X, f) = (Y, g) is equivalent to the type of
   equivalences e : X ≃ Y with e (f_a x) = g_a (e x) for all a and x
   (generalizing self_map_pairs_paths_equiv of module 471 to S-indexed
   families).  The underlying map sends p to transport along its first
   component, so evaluating the equivalence is p.1.trr. `}

def SActionTypes (S : Type) : Type ≔ Σ Type (X ↦ S → X → X)

def s_action_family (S : Type) (X : Type) : Type ≔ S → X → X

def SActionCommutes (S X Y : Type) (f : S → X → X) (g : S → Y → Y) (h : X → Y) : Type
  ≔ (a : S) (x : X) → Id Y (h (f a x)) (g a (h x))

def SActionIsos (S : Type) (u v : SActionTypes S) : Type
  ≔ Σ (Equiv (u .fst) (v .fst)) (e ↦ SActionCommutes S (u .fst) (v .fst) (u .snd) (v .snd) (e .map))

{` Moving both endpoints of an identity type along identifications. `}
def fsc_path_endpoints_equiv (A : Type) (x x' : A) (hx : Id A x x') (y y' : A) (hy : Id A y y')
  : Equiv (Id A x y) (Id A x' y')
  ≔ J A x (x' _ ↦ Equiv (Id A x y) (Id A x' y'))
      (J A y (y' _ ↦ Equiv (Id A x y) (Id A x y')) (identity_equiv (Id A x y)) y' hy) x' hx

def s_action_refl_point_equiv (X : Type) (f g : X → X) (x : X)
  : Equiv (Id X (f x) (g x)) (Id X (refl X .trr (f x)) (g (refl X .trr x)))
  ≔ fsc_path_endpoints_equiv X (f x) (refl X .trr (f x))
      (inverse X (refl X .trr (f x)) (f x) (transport_refl Type (Y ↦ Y) X (f x)))
      (g x) (g (refl X .trr x))
      (refl g (inverse X (refl X .trr x) x (transport_refl Type (Y ↦ Y) X x)))

def s_action_refl_letter_equiv (X : Type) (f g : X → X)
  : Equiv (Id (X → X) f g) ((x : X) → Id X (refl X .trr (f x)) (g (refl X .trr x)))
  ≔ compose_equiv (Id (X → X) f g) ((x : X) → Id X (f x) (g x))
      ((x : X) → Id X (refl X .trr (f x)) (g (refl X .trr x)))
      (canonical_inverse_equiv ((x : X) → Id X (f x) (g x)) (Id (X → X) f g) (funext_equiv X (_ ↦ X) f g))
      (pi_family_equiv X (x ↦ Id X (f x) (g x)) (x ↦ Id X (refl X .trr (f x)) (g (refl X .trr x)))
        (x ↦ s_action_refl_point_equiv X f g x))

def s_action_refl_equiv (S X : Type) (f g : S → X → X)
  : Equiv (Id (S → X → X) f g) (SActionCommutes S X X f g (refl X .trr))
  ≔ compose_equiv (Id (S → X → X) f g) ((a : S) → Id (X → X) (f a) (g a)) (SActionCommutes S X X f g (refl X .trr))
      (canonical_inverse_equiv ((a : S) → Id (X → X) (f a) (g a)) (Id (S → X → X) f g)
        (funext_equiv S (_ ↦ X → X) f g))
      (pi_family_equiv S (a ↦ Id (X → X) (f a) (g a)) (a ↦ (x : X) → Id X (refl X .trr (f a x)) (g a (refl X .trr x)))
        (a ↦ s_action_refl_letter_equiv X (f a) (g a)))

def s_action_pathover_equiv (S X X' : Type) (p : Id Type X X') (f : S → X → X) (g : S → X' → X')
  : Equiv (Id (s_action_family S) p f g) (SActionCommutes S X X' f g (p .trr))
  ≔ J Type X (X' p ↦ (g : S → X' → X') → Equiv (Id (s_action_family S) p f g) (SActionCommutes S X X' f g (p .trr)))
      (g ↦ s_action_refl_equiv S X f g) X' p g

{` Identifications of types with S-indexed endomaps are S-equivariant
   equivalences; the map is p ↦ (transport along p.1, ...). `}
def s_action_paths_equiv (S : Type) (u v : SActionTypes S) : Equiv (Id (SActionTypes S) u v) (SActionIsos S u v)
  ≔ let T ≔ transport_univalence_equiv (u .fst) (v .fst) in
    let C ≔ ((e ↦ SActionCommutes S (u .fst) (v .fst) (u .snd) (v .snd) (e .map)) : Equiv (u .fst) (v .fst) → Type) in
    compose_equiv (Id (SActionTypes S) u v) (SigmaPath Type (s_action_family S) u v) (SActionIsos S u v)
      (canonical_inverse_equiv (SigmaPath Type (s_action_family S) u v) (Id (SActionTypes S) u v)
        (sigma_path_equiv Type (s_action_family S) u v))
      (compose_equiv (SigmaPath Type (s_action_family S) u v) (Σ (Id Type (u .fst) (v .fst)) (p ↦ C (T .map p)))
        (SActionIsos S u v)
        (family_equiv (Id Type (u .fst) (v .fst))
          (p ↦ Id (s_action_family S) p (u .snd) (v .snd)) (p ↦ C (T .map p))
          (p ↦ s_action_pathover_equiv S (u .fst) (v .fst) p (u .snd) (v .snd)))
        (sigma_reindex_equiv (Id Type (u .fst) (v .fst)) (Equiv (u .fst) (v .fst)) T C))

def s_action_path_evaluate (S : Type) (u v : SActionTypes S) (p : Id (SActionTypes S) u v) (x : u .fst) : v .fst
  ≔ s_action_paths_equiv S u v .map p .fst .map x

{` Litmus: the evaluation is literally transport along the carrier path. `}
def s_action_path_evaluate_transport (S : Type) (u v : SActionTypes S) (p : Id (SActionTypes S) u v) (x : u .fst)
  : Id (v .fst) (s_action_path_evaluate S u v p x) (p .fst .trr x)
  ≔ refl (p .fst .trr x)

{` The underlying S-action type of an S-set. `}
def sset_actions (S : Type) (X : SSets S) : SActionTypes S ≔ (X .fst, a x ↦ X .snd a .map x)
