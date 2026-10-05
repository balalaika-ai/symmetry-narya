export "860-free-group-signatures"
export "284-chapter-two-completions"

{` Free S-sets: the generic algebraic part of the construction of free
   groups without higher inductive types (modules 870-874), generalizing
   the constructed circle (modules 220-223, the case S = 1, R = Z).

   An S-set is a type X with an S-indexed family of automorphisms
   f : S → (X ≃ X); an S-map (X, f) → (Y, g) is a map h with
   h (f_a x) = g_a (h x) for all a : S and x : X.  A FREE S-set on one
   generator (FreeSSet) is an S-set (R, s) with a point r0 such that for
   EVERY type Y (not only sets) and every F : S → (Y ≃ Y), evaluation at r0
   is an equivalence from S-maps (R, s) → (Y, F) to Y.

   Consequences proved here: S-maps out of R agreeing at r0 are equal; an
   induction principle (a family of propositions containing r0 and closed
   under every s_a and every s_a⁻¹ holds everywhere); the composition law
   φ_v ∘ φ_u = φ_{φ_v(u)} for the S-endomaps φ_u with φ_u(r0) = u; every
   S-endomap of (R, s) is an equivalence.  No sethood is assumed. `}

def SSetCommutes (S X Y : Type) (f : S → Equiv X X) (g : S → Equiv Y Y) (h : X → Y) : Type
  ≔ (a : S) (x : X) → Id Y (h (f a .map x)) (g a .map (h x))

def SSetMaps (S X Y : Type) (f : S → Equiv X X) (g : S → Equiv Y Y) : Type
  ≔ Σ (X → Y) (SSetCommutes S X Y f g)

def sset_map_evaluate (S X Y : Type) (f : S → Equiv X X) (g : S → Equiv Y Y) (x0 : X)
  (h : SSetMaps S X Y f g) : Y
  ≔ h .fst x0

def SSetIsFree (S R : Type) (s : S → Equiv R R) (r0 : R) : Type
  ≔ (Y : Type) (F : S → Equiv Y Y) → isEquiv (SSetMaps S R Y s F) Y (sset_map_evaluate S R Y s F r0)

def FreeSSet (S : Type) : Type ≔ sig (
  carrier : Type,
  act : S → Equiv carrier carrier,
  origin : carrier,
  free : SSetIsFree S carrier act origin)

def free_sset_evaluation (S : Type) (D : FreeSSet S) (Y : Type) (F : S → Equiv Y Y)
  : Equiv (SSetMaps S (D .carrier) Y (D .act) F) Y
  ≔ (sset_map_evaluate S (D .carrier) Y (D .act) F (D .origin), D .free Y F)

def free_sset_lift (S : Type) (D : FreeSSet S) (Y : Type) (F : S → Equiv Y Y) (y : Y)
  : SSetMaps S (D .carrier) Y (D .act) F
  ≔ equiv_inverse_map (SSetMaps S (D .carrier) Y (D .act) F) Y (free_sset_evaluation S D Y F) y

def free_sset_lift_origin (S : Type) (D : FreeSSet S) (Y : Type) (F : S → Equiv Y Y) (y : Y)
  : Id Y (free_sset_lift S D Y F y .fst (D .origin)) y
  ≔ equiv_counit (SSetMaps S (D .carrier) Y (D .act) F) Y (free_sset_evaluation S D Y F) y

{` S-maps out of a free S-set are determined by their value at r0. `}
def free_sset_maps_equal (S : Type) (D : FreeSSet S) (Y : Type) (F : S → Equiv Y Y)
  (h k : SSetMaps S (D .carrier) Y (D .act) F) (p : Id Y (h .fst (D .origin)) (k .fst (D .origin)))
  : Id (SSetMaps S (D .carrier) Y (D .act) F) h k
  ≔ equivalence_injective (SSetMaps S (D .carrier) Y (D .act) F) Y (free_sset_evaluation S D Y F) h k p

def free_sset_maps_agree (S : Type) (D : FreeSSet S) (Y : Type) (F : S → Equiv Y Y)
  (h k : SSetMaps S (D .carrier) Y (D .act) F) (p : Id Y (h .fst (D .origin)) (k .fst (D .origin)))
  (x : D .carrier) : Id Y (h .fst x) (k .fst x)
  ≔ free_sset_maps_equal S D Y F h k p .fst (refl x)

def sset_maps_identity (S X : Type) (f : S → Equiv X X) : SSetMaps S X X f f
  ≔ (x ↦ x, a x ↦ refl (f a .map x))

{` sset_maps_compose h h' is h' ∘ h (h first). `}
def sset_maps_compose (S X Y Z : Type) (f : S → Equiv X X) (g : S → Equiv Y Y) (k : S → Equiv Z Z)
  (h : SSetMaps S X Y f g) (h' : SSetMaps S Y Z g k) : SSetMaps S X Z f k
  ≔ (x ↦ h' .fst (h .fst x),
     a x ↦ concat Z (h' .fst (h .fst (f a .map x))) (h' .fst (g a .map (h .fst x))) (k a .map (h' .fst (h .fst x)))
       (refl (h' .fst) (h .snd a x)) (h' .snd a (h .fst x)))

{` Induction principle for free S-sets: apply freeness to the S-set Σ R P. `}
def fsc_total_step (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (step : (a : S) (x : D .carrier) → P x → P (D .act a .map x)) (a : S) (u : Σ (D .carrier) P)
  : Σ (D .carrier) P
  ≔ (D .act a .map (u .fst), step a (u .fst) (u .snd))

def fsc_total_back (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (back : (a : S) (x : D .carrier) → P (D .act a .map x) → P x) (a : S) (v : Σ (D .carrier) P)
  : Σ (D .carrier) P
  ≔ let R ≔ D .carrier in
    let x ≔ equiv_inverse_map R R (D .act a) (v .fst) in
    (x, back a x (transport R P (v .fst) (D .act a .map x)
      (inverse R (D .act a .map x) (v .fst) (equiv_counit R R (D .act a) (v .fst))) (v .snd)))

def fsc_total_action (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (hP : (x : D .carrier) → isProp (P x))
  (step : (a : S) (x : D .carrier) → P x → P (D .act a .map x))
  (back : (a : S) (x : D .carrier) → P (D .act a .map x) → P x) (a : S)
  : Equiv (Σ (D .carrier) P) (Σ (D .carrier) P)
  ≔ let R ≔ D .carrier in
    quasi_inverse_equiv (Σ R P) (Σ R P) (fsc_total_step S D P step a) (fsc_total_back S D P back a)
      (u ↦ subtype_equal R P hP (fsc_total_back S D P back a (fsc_total_step S D P step a u)) u
        (equiv_retraction R R (D .act a) (u .fst)))
      (v ↦ subtype_equal R P hP (fsc_total_step S D P step a (fsc_total_back S D P back a v)) v
        (equiv_counit R R (D .act a) (v .fst)))

def fsc_total_lift (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (hP : (x : D .carrier) → isProp (P x)) (p0 : P (D .origin))
  (step : (a : S) (x : D .carrier) → P x → P (D .act a .map x))
  (back : (a : S) (x : D .carrier) → P (D .act a .map x) → P x)
  : SSetMaps S (D .carrier) (Σ (D .carrier) P) (D .act) (fsc_total_action S D P hP step back)
  ≔ free_sset_lift S D (Σ (D .carrier) P) (fsc_total_action S D P hP step back) (D .origin, p0)

def fsc_total_lift_first (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (hP : (x : D .carrier) → isProp (P x)) (p0 : P (D .origin))
  (step : (a : S) (x : D .carrier) → P x → P (D .act a .map x))
  (back : (a : S) (x : D .carrier) → P (D .act a .map x) → P x)
  : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act)
  ≔ (y ↦ fsc_total_lift S D P hP p0 step back .fst y .fst,
     a y ↦ refl ((u ↦ u .fst) : Σ (D .carrier) P → D .carrier) (fsc_total_lift S D P hP p0 step back .snd a y))

def free_sset_induction (S : Type) (D : FreeSSet S) (P : D .carrier → Type)
  (hP : (x : D .carrier) → isProp (P x)) (p0 : P (D .origin))
  (step : (a : S) (x : D .carrier) → P x → P (D .act a .map x))
  (back : (a : S) (x : D .carrier) → P (D .act a .map x) → P x)
  (x : D .carrier) : P x
  ≔ let R ≔ D .carrier in
    transport R P (fsc_total_lift S D P hP p0 step back .fst x .fst) x
      (free_sset_maps_agree S D R (D .act) (fsc_total_lift_first S D P hP p0 step back) (sset_maps_identity S R (D .act))
        (refl ((u ↦ u .fst) : Σ R P → R)
          (free_sset_lift_origin S D (Σ R P) (fsc_total_action S D P hP step back) (D .origin, p0))) x)
      (fsc_total_lift S D P hP p0 step back .fst x .snd)

{` The S-endomaps φ_u of R with φ_u(r0) = u, and φ_v ∘ φ_u = φ_{φ_v(u)}. `}
def free_sset_endo (S : Type) (D : FreeSSet S) (u : D .carrier)
  : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act)
  ≔ free_sset_lift S D (D .carrier) (D .act) u

def free_sset_endo_origin (S : Type) (D : FreeSSet S) (u : D .carrier)
  : Id (D .carrier) (free_sset_endo S D u .fst (D .origin)) u
  ≔ free_sset_lift_origin S D (D .carrier) (D .act) u

def free_sset_endo_compose (S : Type) (D : FreeSSet S) (u v : D .carrier) (x : D .carrier)
  : Id (D .carrier) (free_sset_endo S D v .fst (free_sset_endo S D u .fst x))
      (free_sset_endo S D (free_sset_endo S D v .fst u) .fst x)
  ≔ let R ≔ D .carrier in
    let fu ≔ free_sset_endo S D u in let fv ≔ free_sset_endo S D v in
    let fw ≔ free_sset_endo S D (fv .fst u) in
    free_sset_maps_agree S D R (D .act) (sset_maps_compose S R R R (D .act) (D .act) (D .act) fu fv) fw
      (concat R (fv .fst (fu .fst (D .origin))) (fv .fst u) (fw .fst (D .origin))
        (refl (fv .fst) (free_sset_endo_origin S D u))
        (inverse R (fw .fst (D .origin)) (fv .fst u) (free_sset_endo_origin S D (fv .fst u)))) x

{` Every point u is merely sent back to r0 by some φ_v. `}
def FscLeftInverse (S : Type) (D : FreeSSet S) (u : D .carrier) : Type
  ≔ Σ (D .carrier) (v ↦ Id (D .carrier) (free_sset_endo S D v .fst u) (D .origin))

def fsc_left_inverse_step (S : Type) (D : FreeSSet S) (a : S) (x : D .carrier) (t : FscLeftInverse S D x)
  : FscLeftInverse S D (D .act a .map x)
  ≔ let R ≔ D .carrier in let s ≔ D .act a in let r0 ≔ D .origin in
    let w ≔ equiv_inverse_map R R s r0 in
    let fv ≔ free_sset_endo S D (t .fst) in let fw ≔ free_sset_endo S D w in
    (fw .fst (t .fst), calc
      free_sset_endo S D (fw .fst (t .fst)) .fst (s .map x)
      = fw .fst (fv .fst (s .map x))
        by inverse R (fw .fst (fv .fst (s .map x))) (free_sset_endo S D (fw .fst (t .fst)) .fst (s .map x))
          (free_sset_endo_compose S D (t .fst) w (s .map x))
      = fw .fst (s .map (fv .fst x)) by refl (fw .fst) (fv .snd a x)
      = fw .fst (s .map r0) by refl ((z ↦ fw .fst (s .map z)) : R → R) (t .snd)
      = s .map (fw .fst r0) by fw .snd a r0
      = s .map w by refl (s .map) (free_sset_endo_origin S D w)
      = r0 by equiv_counit R R s r0 ∎)

def fsc_left_inverse_back (S : Type) (D : FreeSSet S) (a : S) (x : D .carrier)
  (t : FscLeftInverse S D (D .act a .map x))
  : FscLeftInverse S D x
  ≔ let R ≔ D .carrier in let s ≔ D .act a in let r0 ≔ D .origin in
    let si ≔ equiv_inverse_map R R s in
    let w ≔ s .map r0 in
    let fv ≔ free_sset_endo S D (t .fst) in let fw ≔ free_sset_endo S D w in
    (fw .fst (t .fst), calc
      free_sset_endo S D (fw .fst (t .fst)) .fst x
      = fw .fst (fv .fst x)
        by inverse R (fw .fst (fv .fst x)) (free_sset_endo S D (fw .fst (t .fst)) .fst x)
          (free_sset_endo_compose S D (t .fst) w x)
      = si (s .map (fw .fst (fv .fst x))) by equiv_unit R R s (fw .fst (fv .fst x))
      = si (fw .fst (s .map (fv .fst x)))
        by refl si (inverse R (fw .fst (s .map (fv .fst x))) (s .map (fw .fst (fv .fst x))) (fw .snd a (fv .fst x)))
      = si (fw .fst (fv .fst (s .map x)))
        by refl ((z ↦ si (fw .fst z)) : R → R) (inverse R (fv .fst (s .map x)) (s .map (fv .fst x)) (fv .snd a x))
      = si (fw .fst r0) by refl ((z ↦ si (fw .fst z)) : R → R) (t .snd)
      = si w by refl si (free_sset_endo_origin S D w)
      = r0 by equiv_retraction R R s r0 ∎)

def free_sset_left_inverses (S : Type) (D : FreeSSet S) (u : D .carrier) : Mere (FscLeftInverse S D u)
  ≔ free_sset_induction S D (y ↦ Mere (FscLeftInverse S D y)) (y ↦ mere_isprop (FscLeftInverse S D y))
      (mere (FscLeftInverse S D (D .origin)) (D .origin, free_sset_endo_origin S D (D .origin)))
      (a x ↦ mere_rec (FscLeftInverse S D x) (Mere (FscLeftInverse S D (D .act a .map x)))
        (mere_isprop (FscLeftInverse S D (D .act a .map x)))
        (t ↦ mere (FscLeftInverse S D (D .act a .map x)) (fsc_left_inverse_step S D a x t)))
      (a x ↦ mere_rec (FscLeftInverse S D (D .act a .map x)) (Mere (FscLeftInverse S D x))
        (mere_isprop (FscLeftInverse S D x))
        (t ↦ mere (FscLeftInverse S D x) (fsc_left_inverse_back S D a x t)))
      u

{` A map with a left inverse g which itself has a left inverse k has g as
   two-sided inverse. `}
def fsc_left_inverse_is_right (R : Type) (h g k : R → R) (gh : (x : R) → Id R (g (h x)) x)
  (kg : (x : R) → Id R (k (g x)) x) (x : R) : Id R (h (g x)) x
  ≔ concat R (h (g x)) (k (g x)) x
      (concat R (h (g x)) (k (g (h (g x)))) (k (g x))
        (inverse R (k (g (h (g x)))) (h (g x)) (kg (h (g x)))) (refl k (gh (g x))))
      (kg x)

def fsc_endo_left_inverse (S : Type) (D : FreeSSet S) (h : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act))
  (t : FscLeftInverse S D (h .fst (D .origin))) (x : D .carrier)
  : Id (D .carrier) (free_sset_endo S D (t .fst) .fst (h .fst x)) x
  ≔ let R ≔ D .carrier in
    free_sset_maps_agree S D R (D .act)
      (sset_maps_compose S R R R (D .act) (D .act) (D .act) h (free_sset_endo S D (t .fst)))
      (sset_maps_identity S R (D .act)) (t .snd) x

{` Every S-endomap of a free S-set is an equivalence. `}
def free_sset_endo_isequiv (S : Type) (D : FreeSSet S) (h : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act))
  : isEquiv (D .carrier) (D .carrier) (h .fst)
  ≔ let R ≔ D .carrier in
    mere_rec (FscLeftInverse S D (h .fst (D .origin))) (isEquiv R R (h .fst)) (isequiv_isprop R R (h .fst))
      (t ↦ mere_rec (FscLeftInverse S D (free_sset_endo S D (t .fst) .fst (D .origin))) (isEquiv R R (h .fst))
        (isequiv_isprop R R (h .fst))
        (t' ↦ quasi_inverse_equiv R R (h .fst) (free_sset_endo S D (t .fst) .fst)
          (fsc_endo_left_inverse S D h t)
          (fsc_left_inverse_is_right R (h .fst) (free_sset_endo S D (t .fst) .fst) (free_sset_endo S D (t' .fst) .fst)
            (fsc_endo_left_inverse S D h t) (fsc_endo_left_inverse S D (free_sset_endo S D (t .fst)) t')) .equiv)
        (free_sset_left_inverses S D (free_sset_endo S D (t .fst) .fst (D .origin))))
      (free_sset_left_inverses S D (h .fst (D .origin)))

def free_sset_endo_equiv (S : Type) (D : FreeSSet S) (h : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act))
  : Equiv (D .carrier) (D .carrier)
  ≔ (h .fst, free_sset_endo_isequiv S D h)

{` The type of S-sets (with automorphisms as actions), and weak freeness:
   S-maps to every (Y, F) are equivalent to Y by SOME equivalence.  Weak
   freeness is invariant under identifications of S-sets. `}
def SSets (S : Type) : Type ≔ Σ Type (X ↦ S → Equiv X X)

def SSetIsWeaklyFree (S : Type) (X : SSets S) : Type
  ≔ (Y : Type) (F : S → Equiv Y Y) → Equiv (SSetMaps S (X .fst) Y (X .snd) F) Y

def free_sset_weakly_free (S : Type) (D : FreeSSet S) : SSetIsWeaklyFree S (D .carrier, D .act)
  ≔ Y F ↦ free_sset_evaluation S D Y F

def sset_weakly_free_transfer (S : Type) (X X' : SSets S) (w : Id (SSets S) X X') (h : SSetIsWeaklyFree S X)
  : SSetIsWeaklyFree S X'
  ≔ Y F ↦ compose_equiv (SSetMaps S (X' .fst) Y (X' .snd) F) (SSetMaps S (X .fst) Y (X .snd) F) Y
      (id_to_equiv (SSetMaps S (X' .fst) Y (X' .snd) F) (SSetMaps S (X .fst) Y (X .snd) F)
        (refl ((Z ↦ SSetMaps S (Z .fst) Y (Z .snd) F) : SSets S → Type) (inverse (SSets S) X X' w)))
      (h Y F)

{` An equivalence commuting with the actions identifies two S-sets. `}
def sset_path_from_equiv (S X : Type) (f : S → Equiv X X) (Y : Type) (e : Equiv X Y) (g : S → Equiv Y Y)
  (c : SSetCommutes S X Y f g (e .map))
  : Id (SSets S) (X, f) (Y, g)
  ≔ equivalence_induction X
      (Y e ↦ (g : S → Equiv Y Y) → SSetCommutes S X Y f g (e .map) → Id (SSets S) (X, f) (Y, g))
      (g c ↦ (refl X, funext S (_ ↦ Equiv X X) f g (a ↦ equiv_homotopy X X (f a) (g a) (c a))))
      Y e g c

{` Litmus: the free S-set structure is unique up to unique S-maps; the
   identity is the endomap φ_{r0}. `}
def free_sset_endo_origin_identity (S : Type) (D : FreeSSet S) (x : D .carrier)
  : Id (D .carrier) (free_sset_endo S D (D .origin) .fst x) x
  ≔ free_sset_maps_agree S D (D .carrier) (D .act) (free_sset_endo S D (D .origin))
      (sset_maps_identity S (D .carrier) (D .act)) (free_sset_endo_origin S D (D .origin)) x
