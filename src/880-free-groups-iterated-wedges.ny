export "879-free-sum-wedges"

{` xca at congp.tex:937: "Construct an equivalence F_{n⊔1} ≃ F_n ∨ Z for each
   n : N using the universal properties.  As a result, give identifications
   F_n = ((Z ∨ Z) ∨ ⋯) ∨ Z, with n copies of Z."

   Formalization (classifying types, for EVERY choice of the HIT signatures):
   - uniqueness by universal properties: free group signatures on
     equivalent index types have identified pointed classifying types
     (free_signatures_pointed_path), and two wedges of the same pointed types
     are identified (wedge_signatures_pointed_path);
   - F_{n⊔1} ≃ F_n ∨ Z: B F_{n⊔1} carries a wedge structure of (B F_n, base)
     and (S¹, base) (module 879, n⊔1 = Fin (n+1) = Fin n + 1), hence for
     EVERY wedge signature W of (B F_n, base) and (S¹, base),
     (B F_{n⊔1}, base) = (W, a12) as pointed types (free_succ_wedge_path),
     and as groups F_{n⊔1} = F_n ∨ Z (free_succ_sum_group_path), the sum
     group being Aut_W(a12), a group because W is identified with a
     groupoid;
   - the iterated wedges: a WedgeTower C n is a choice of the n-1 wedges in
     ((S¹ ∨ S¹) ∨ ⋯) ∨ S¹ (n = 0: the point, n = 1: S¹); for every tower and
     every free group signature on Fin n, (B F_n, base) = top of the tower
     (free_group_wedge_tower), and F_n = ((Z ∨ Z) ∨ ⋯) ∨ Z as groups
     (free_group_wedge_tower_group). `}

{` Free group signatures on equivalent index types are identified. `}
def bouquet_post (S A A' : Type) (k : A → A') (u : BouquetData S A) : BouquetData S A'
  ≔ (k (u .fst), s ↦ refl k (u .snd s))

def bouquet_reindex (S S' A : Type) (e : S → S') (u : BouquetData S' A) : BouquetData S A
  ≔ (u .fst, s ↦ u .snd (e s))

def free_signature_map (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : F .carrier → F' .carrier
  ≔ free_rec S F (F' .carrier) (F' .base, s ↦ F' .loop (e .map s))

def free_signature_map_back (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : F' .carrier → F .carrier
  ≔ free_rec S' F' (F .carrier) (F .base, s ↦ F .loop (equiv_inverse_map S S' e s))

def free_signature_map_retraction (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : Id (F .carrier → F .carrier)
      (x ↦ free_signature_map_back S S' e F F' (free_signature_map S S' e F F' x)) (x ↦ x)
  ≔ let B ≔ F .carrier in let B' ≔ F' .carrier in
    let phi ≔ free_signature_map S S' e F F' in let psi ≔ free_signature_map_back S S' e F F' in
    free_maps_equal S F B (x ↦ psi (phi x)) (x ↦ x)
      (calc
        bouquet_post S B' B psi (free_bouquet S F B' phi)
        = bouquet_post S B' B psi (F' .base, s ↦ F' .loop (e .map s))
          by refl (bouquet_post S B' B psi) (free_rec_beta S F B' (F' .base, s ↦ F' .loop (e .map s)))
        = bouquet_reindex S S' B (e .map) (F .base, s ↦ F .loop (equiv_inverse_map S S' e s))
          by refl (bouquet_reindex S S' B (e .map))
            (free_rec_beta S' F' B (F .base, s ↦ F .loop (equiv_inverse_map S S' e s)))
        = (F .base, s ↦ F .loop s)
          by (refl (F .base), funext S (_ ↦ Id B (F .base) (F .base))
            (s ↦ F .loop (equiv_inverse_map S S' e (e .map s))) (s ↦ F .loop s)
            (s ↦ refl (F .loop) (equiv_retraction S S' e s))) ∎)

def free_signature_map_section (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : Id (F' .carrier → F' .carrier)
      (x ↦ free_signature_map S S' e F F' (free_signature_map_back S S' e F F' x)) (x ↦ x)
  ≔ let B ≔ F .carrier in let B' ≔ F' .carrier in
    let phi ≔ free_signature_map S S' e F F' in let psi ≔ free_signature_map_back S S' e F F' in
    free_maps_equal S' F' B' (x ↦ phi (psi x)) (x ↦ x)
      (calc
        bouquet_post S' B B' phi (free_bouquet S' F' B psi)
        = bouquet_post S' B B' phi (F .base, s ↦ F .loop (equiv_inverse_map S S' e s))
          by refl (bouquet_post S' B B' phi) (free_rec_beta S' F' B (F .base, s ↦ F .loop (equiv_inverse_map S S' e s)))
        = bouquet_reindex S' S B' (equiv_inverse_map S S' e) (F' .base, s ↦ F' .loop (e .map s))
          by refl (bouquet_reindex S' S B' (equiv_inverse_map S S' e))
            (free_rec_beta S F B' (F' .base, s ↦ F' .loop (e .map s)))
        = (F' .base, s ↦ F' .loop s)
          by (refl (F' .base), funext S' (_ ↦ Id B' (F' .base) (F' .base))
            (s ↦ F' .loop (e .map (equiv_inverse_map S S' e s))) (s ↦ F' .loop s)
            (s ↦ refl (F' .loop) (equiv_counit S S' e s))) ∎)

def free_signatures_pointed_equiv (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : BookPointedEquiv (free_pointed S F) (free_pointed S' F')
  ≔ ((free_signature_map S S' e F F',
      inverse (F' .carrier) (free_signature_map S S' e F F' (F .base)) (F' .base)
        (free_rec_beta S F (F' .carrier) (F' .base, s ↦ F' .loop (e .map s)) .fst)),
     book_quasi_inverse_equiv (F .carrier) (F' .carrier) (free_signature_map S S' e F F') (free_signature_map_back S S' e F F')
       (x ↦ free_signature_map_retraction S S' e F F' (refl x))
       (x ↦ free_signature_map_section S S' e F F' (refl x)) .equiv)

def free_signatures_pointed_path (S S' : Type) (e : Equiv S S') (F : FreeGroupSignature S) (F' : FreeGroupSignature S')
  : Id Pointed (free_pointed S F) (free_pointed S' F')
  ≔ equiv_inverse_map (Id Pointed (free_pointed S F) (free_pointed S' F'))
      (BookPointedEquiv (free_pointed S F) (free_pointed S' F'))
      (pointed_path_equiv (free_pointed S F) (free_pointed S' F')) (free_signatures_pointed_equiv S S' e F F')

{` Two wedge signatures of the same pointed types are identified. `}
def wedge_cocone_post (A1 A2 : Pointed) (Z Z' : Type) (k : Z → Z') (c : WedgeCocone A1 A2 Z) : WedgeCocone A1 A2 Z'
  ≔ (a ↦ k (c .fst a), (a ↦ k (c .snd .fst a), refl k (c .snd .snd)))

def wedge_structure_cocone (A1 A2 : Pointed) (W : WedgeSignature A1 A2) : WedgeCocone A1 A2 (W .carrier)
  ≔ (a ↦ W .incl1 a, (a ↦ W .incl2 a, W .glue))

def wedge_comparison_map (A1 A2 : Pointed) (W W' : WedgeSignature A1 A2) : W .carrier → W' .carrier
  ≔ wedge_rec A1 A2 W (W' .carrier) (wedge_structure_cocone A1 A2 W')

def wedge_comparison_retraction (A1 A2 : Pointed) (W W' : WedgeSignature A1 A2)
  : Id (W .carrier → W .carrier)
      (x ↦ wedge_comparison_map A1 A2 W' W (wedge_comparison_map A1 A2 W W' x)) (x ↦ x)
  ≔ let phi ≔ wedge_comparison_map A1 A2 W W' in let psi ≔ wedge_comparison_map A1 A2 W' W in
    wedge_maps_equal A1 A2 W (W .carrier) (x ↦ psi (phi x)) (x ↦ x)
      (calc
        wedge_cocone_post A1 A2 (W' .carrier) (W .carrier) psi (wedge_cocone A1 A2 W (W' .carrier) phi)
        = wedge_cocone_post A1 A2 (W' .carrier) (W .carrier) psi (wedge_structure_cocone A1 A2 W')
          by refl (wedge_cocone_post A1 A2 (W' .carrier) (W .carrier) psi)
            (wedge_rec_beta A1 A2 W (W' .carrier) (wedge_structure_cocone A1 A2 W'))
        = wedge_structure_cocone A1 A2 W
          by wedge_rec_beta A1 A2 W' (W .carrier) (wedge_structure_cocone A1 A2 W) ∎)

def wedge_signatures_pointed_equiv (A1 A2 : Pointed) (W W' : WedgeSignature A1 A2)
  : BookPointedEquiv (wedge_pointed A1 A2 W) (wedge_pointed A1 A2 W')
  ≔ ((wedge_comparison_map A1 A2 W W',
      inverse (W' .carrier) (wedge_comparison_map A1 A2 W W' (W .incl1 (A1 .point))) (W' .incl1 (A1 .point))
        (wedge_rec_incl1 A1 A2 W (W' .carrier) (wedge_structure_cocone A1 A2 W') (A1 .point))),
     book_quasi_inverse_equiv (W .carrier) (W' .carrier) (wedge_comparison_map A1 A2 W W') (wedge_comparison_map A1 A2 W' W)
       (x ↦ wedge_comparison_retraction A1 A2 W W' (refl x))
       (x ↦ wedge_comparison_retraction A1 A2 W' W (refl x)) .equiv)

def wedge_signatures_pointed_path (A1 A2 : Pointed) (W W' : WedgeSignature A1 A2)
  : Id Pointed (wedge_pointed A1 A2 W) (wedge_pointed A1 A2 W')
  ≔ equiv_inverse_map (Id Pointed (wedge_pointed A1 A2 W) (wedge_pointed A1 A2 W'))
      (BookPointedEquiv (wedge_pointed A1 A2 W) (wedge_pointed A1 A2 W'))
      (pointed_path_equiv (wedge_pointed A1 A2 W) (wedge_pointed A1 A2 W')) (wedge_signatures_pointed_equiv A1 A2 W W')

{` Wedges of identified pointed types are identified. `}
def wedge_pointed_path_along (A1 A1' A2 : Pointed) (p : Id Pointed A1 A1') (W : WedgeSignature A1 A2)
  (W' : WedgeSignature A1' A2) : Id Pointed (wedge_pointed A1 A2 W) (wedge_pointed A1' A2 W')
  ≔ J Pointed A1 (A1' p ↦ (W' : WedgeSignature A1' A2) → Id Pointed (wedge_pointed A1 A2 W) (wedge_pointed A1' A2 W'))
      (W' ↦ wedge_signatures_pointed_path A1 A2 W W') A1' p W'

{` F_{n⊔1} ≃ F_n ∨ Z (n⊔1 = Fin (n+1) = Fin n + 1, the new letter generating Z). `}
def free_succ_wedge (n : Nat) (F' : FreeGroupSignature (Fin (suc. n))) (F : FreeGroupSignature (Fin n))
  (C : CircleSignature) : WedgeSignature (free_pointed (Fin n) F) (circle_pointed C)
  ≔ free_sum_wedge_signature (Fin n) Unit (Fin (suc. n)) (identity_equiv (Fin (suc. n))) F' F (circle_free_signature C)

def free_succ_wedge_own_path (n : Nat) (F' : FreeGroupSignature (Fin (suc. n))) (F : FreeGroupSignature (Fin n))
  (C : CircleSignature)
  : Id Pointed (free_pointed (Fin (suc. n)) F') (wedge_pointed (free_pointed (Fin n) F) (circle_pointed C) (free_succ_wedge n F' F C))
  ≔ (refl (F' .carrier),
     inverse (F' .carrier) (free_sum_incl1 (Fin n) Unit (Fin (suc. n)) (identity_equiv (Fin (suc. n))) F' F (F .base)) (F' .base)
       (free_sum_base1 (Fin n) Unit (Fin (suc. n)) (identity_equiv (Fin (suc. n))) F' F))

def free_succ_wedge_path (n : Nat) (F' : FreeGroupSignature (Fin (suc. n))) (F : FreeGroupSignature (Fin n))
  (C : CircleSignature) (W : WedgeSignature (free_pointed (Fin n) F) (circle_pointed C))
  : Id Pointed (free_pointed (Fin (suc. n)) F') (wedge_pointed (free_pointed (Fin n) F) (circle_pointed C) W)
  ≔ concat Pointed (free_pointed (Fin (suc. n)) F')
      (wedge_pointed (free_pointed (Fin n) F) (circle_pointed C) (free_succ_wedge n F' F C))
      (wedge_pointed (free_pointed (Fin n) F) (circle_pointed C) W)
      (free_succ_wedge_own_path n F' F C)
      (wedge_signatures_pointed_path (free_pointed (Fin n) F) (circle_pointed C) (free_succ_wedge n F' F C) W)

{` As groups: the sum F_n ∨ Z ≔ Aut_W(a12) for any wedge W of B F_n and S¹. `}
def fsc_pointed_path_groupoid (X Y : Pointed) (p : Id Pointed X Y) (h : isGroupoid (X .carrier)) : isGroupoid (Y .carrier)
  ≔ transport Type isGroupoid (X .carrier) (Y .carrier) (p .carrier) h

def fsc_pointed_path_connected (X Y : Pointed) (p : Id Pointed X Y) (h : Connected (X .carrier)) : Connected (Y .carrier)
  ≔ transport Type Connected (X .carrier) (Y .carrier) (p .carrier) h

def fsc_group_along (G : Group) (Y : Pointed) (p : Id Pointed (BG G) Y) : Group
  ≔ mkgroup (Y .carrier, Y .point, fsc_pointed_path_connected (BG G) Y p (bg_connected G),
      fsc_pointed_path_groupoid (BG G) Y p (bg_groupoid G))

def fsc_group_along_path (G : Group) (Y : Pointed) (p : Id Pointed (BG G) Y) : Id Group G (fsc_group_along G Y p)
  ≔ group_path_from_pointed_equiv G (fsc_group_along G Y p) (pointed_path_to_equiv (BG G) Y p)

def free_succ_sum_group (n : Nat) (C : CircleSignature)
  (W : WedgeSignature (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C)) : Group
  ≔ fsc_group_along (constructed_free_group (Fin (suc. n)) (fin_decidable_equality (suc. n)))
      (wedge_pointed (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C) W)
      (free_succ_wedge_path n (constructed_free_group_signature (Fin (suc. n)) (fin_decidable_equality (suc. n)))
        (constructed_free_group_signature (Fin n) (fin_decidable_equality n)) C W)

def free_succ_sum_group_classifying (n : Nat) (C : CircleSignature)
  (W : WedgeSignature (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C))
  : Id Pointed (BG (free_succ_sum_group n C W))
      (wedge_pointed (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C) W)
  ≔ refl (wedge_pointed (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C) W)

def free_succ_sum_group_path (n : Nat) (C : CircleSignature)
  (W : WedgeSignature (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C))
  : Id Group (constructed_free_group (Fin (suc. n)) (fin_decidable_equality (suc. n))) (free_succ_sum_group n C W)
  ≔ fsc_group_along_path (constructed_free_group (Fin (suc. n)) (fin_decidable_equality (suc. n)))
      (wedge_pointed (BG (constructed_free_group (Fin n) (fin_decidable_equality n))) (circle_pointed C) W)
      (free_succ_wedge_path n (constructed_free_group_signature (Fin (suc. n)) (fin_decidable_equality (suc. n)))
        (constructed_free_group_signature (Fin n) (fin_decidable_equality n)) C W)

{` Iterated wedges ((S¹ ∨ S¹) ∨ ⋯) ∨ S¹ with n copies of S¹: a tower is
   a choice of all intermediate wedge signatures; the pointed type at the
   top.  n = 0: the point (Unit, star); n = 1: S¹. `}
def WedgeTowerLevel : Type ≔ Σ Type (X ↦ X → Pointed)

def wedge_tower_succ (C : CircleSignature) (m : Nat) (prev : WedgeTowerLevel) : WedgeTowerLevel
  ≔ match m [
  | zero. ↦ (Unit, _ ↦ circle_pointed C)
  | suc. _ ↦ (Σ (prev .fst) (tau ↦ WedgeSignature (prev .snd tau) (circle_pointed C)),
      u ↦ wedge_pointed (prev .snd (u .fst)) (circle_pointed C) (u .snd)) ]

def wedge_tower (C : CircleSignature) (n : Nat) : WedgeTowerLevel
  ≔ match n [ zero. ↦ (Unit, _ ↦ (Unit, star.)) | suc. m ↦ wedge_tower_succ C m (wedge_tower C m) ]

def WedgeTower (C : CircleSignature) (n : Nat) : Type ≔ wedge_tower C n .fst

def wedge_tower_top (C : CircleSignature) (n : Nat) (tau : WedgeTower C n) : Pointed ≔ wedge_tower C n .snd tau

{` The point is a free group signature on Empty; S¹ is one on Fin 1. `}
def fsc_empty_loops (A : Type) (a : A) (e : Empty) : Id A a a ≔ match e []

def fsc_unit_section (P : Unit → Type) (p : P star.) (x : Unit) : P x ≔ match x [ star. ↦ p ]

def unit_free_signature_empty : FreeGroupSignature Empty
  ≔ (Unit, star., fsc_empty_loops Unit star.,
     P d ↦ (fsc_unit_section P (d .fst),
       (refl (d .fst), funext Empty (e ↦ Id P (fsc_empty_loops Unit star. e) (d .fst) (d .fst))
         (e ↦ refl (fsc_unit_section P (d .fst)) (fsc_empty_loops Unit star. e)) (d .snd)
         (e ↦ match e []))))

def fsc_fin_one_unit_equiv : Equiv (Fin (suc. zero.)) Unit
  ≔ quasi_inverse_equiv (Fin (suc. zero.)) Unit (_ ↦ star.) (u ↦ inr. u)
      (x ↦ match x [ inl. e ↦ match e [] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ])
      (u ↦ match u [ star. ↦ refl (star. : Unit) ])

{` (B F_n, base) is the top of every wedge tower, for every free group
   signature F on Fin n. `}
def free_group_wedge_tower_succ (C : CircleSignature) (m : Nat)
  (ih : (tau : WedgeTower C m) (F : FreeGroupSignature (Fin m))
    → Id Pointed (free_pointed (Fin m) F) (wedge_tower_top C m tau))
  (tau : WedgeTower C (suc. m)) (F : FreeGroupSignature (Fin (suc. m)))
  : Id Pointed (free_pointed (Fin (suc. m)) F) (wedge_tower_top C (suc. m) tau)
  ≔ match m [
  | zero. ↦ free_signatures_pointed_path (Fin (suc. zero.)) Unit fsc_fin_one_unit_equiv F (circle_free_signature C)
  | suc. k ↦
      let Fc ≔ constructed_free_group_signature (Fin (suc. k)) (fin_decidable_equality (suc. k)) in
      concat Pointed (free_pointed (Fin (suc. (suc. k))) F)
        (wedge_pointed (free_pointed (Fin (suc. k)) Fc) (circle_pointed C) (free_succ_wedge (suc. k) F Fc C))
        (wedge_tower_top C (suc. (suc. k)) tau)
        (free_succ_wedge_own_path (suc. k) F Fc C)
        (wedge_pointed_path_along (free_pointed (Fin (suc. k)) Fc) (wedge_tower_top C (suc. k) (tau .fst)) (circle_pointed C)
          (ih (tau .fst) Fc) (free_succ_wedge (suc. k) F Fc C) (tau .snd)) ]

def free_group_wedge_tower (C : CircleSignature) (n : Nat) (tau : WedgeTower C n) (F : FreeGroupSignature (Fin n))
  : Id Pointed (free_pointed (Fin n) F) (wedge_tower_top C n tau)
  ≔ match n [
  | zero. ↦ free_signatures_pointed_path Empty Empty (identity_equiv Empty) F unit_free_signature_empty
  | suc. m ↦ free_group_wedge_tower_succ C m (free_group_wedge_tower C m) tau F ]

{` As groups: F_n = ((Z ∨ Z) ∨ ⋯) ∨ Z (the iterated sum of groups). `}
def wedge_tower_group (C : CircleSignature) (n : Nat) (tau : WedgeTower C n) : Group
  ≔ fsc_group_along (constructed_free_group (Fin n) (fin_decidable_equality n)) (wedge_tower_top C n tau)
      (free_group_wedge_tower C n tau (constructed_free_group_signature (Fin n) (fin_decidable_equality n)))

def free_group_wedge_tower_group (C : CircleSignature) (n : Nat) (tau : WedgeTower C n)
  : Id Group (constructed_free_group (Fin n) (fin_decidable_equality n)) (wedge_tower_group C n tau)
  ≔ fsc_group_along_path (constructed_free_group (Fin n) (fin_decidable_equality n)) (wedge_tower_top C n tau)
      (free_group_wedge_tower C n tau (constructed_free_group_signature (Fin n) (fin_decidable_equality n)))

{` Litmus: the tower of height 2 is S¹ ∨ S¹, and the constructed wedge of
   two circles is one; F_2 = Z ∨ Z. `}
def wedge_tower_two_constructed : WedgeTower constructed_circle (suc. (suc. zero.))
  ≔ (star., constructed_circle_wedge)

def free_group_two_circle_wedge
  : Id Pointed (free_pointed (Fin (suc. (suc. zero.)))
        (constructed_free_group_signature (Fin (suc. (suc. zero.))) (fin_decidable_equality (suc. (suc. zero.)))))
      (wedge_pointed (circle_pointed constructed_circle) (circle_pointed constructed_circle) constructed_circle_wedge)
  ≔ free_group_wedge_tower constructed_circle (suc. (suc. zero.)) wedge_tower_two_constructed
      (constructed_free_group_signature (Fin (suc. (suc. zero.))) (fin_decidable_equality (suc. (suc. zero.))))
