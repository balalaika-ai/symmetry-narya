export "457-sign-permutations"

{` Chapter 4, prose after def:sgn-permutation (group.tex:1663): the concrete
   homomorphism sgn^A : Hom(Aut(A), Σ_2) of module 457, with
   Bsgn^A(B) ≔ (Bsgn(A) = Bsgn(B)), induces on symmetries the sign of
   permutations. Symmetries of Aut(A) are identified with permutations of A by
   transport (permutation_action; the inverse of permutation_symmetry), and
   USym Σ_2 with {±1} by sigma_two_sign. `}

def bool_eq_from_false_iff (a b : Bool) (f : Id Bool a false. → Id Bool b false.) (g : Id Bool b false. → Id Bool a false.)
  : Id Bool a b
  ≔ match a, b [
  | false., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool)
  | false., true. ↦ absurd (Id Bool false. true.) (bool_encode true. false. (f (refl (false. : Bool))))
  | true., false. ↦ absurd (Id Bool true. false.) (bool_encode true. false. (g (refl (false. : Bool)))) ]

{` A path x : a = b with x = x · r forces r = refl. `}
def path_postcompose_fixed (X : Type) (a b : X) (x : Id X a b) (r : Id X b b)
  (p : Id (Id X a b) x (concat X a b b x r)) : Id (Id X b b) (refl b) r
  ≔ calc refl b
      = concat X b a b (inverse X a b x) x by inverse (Id X b b) (concat X b a b (inverse X a b x) x) (refl b) (concat_inverse_left X a b x)
    = concat X b a b (inverse X a b x) (concat X a b b x r) by refl (concat X b a b (inverse X a b x)) p
    = concat X b b b (concat X b a b (inverse X a b x) x) r
      by inverse (Id X b b) (concat X b b b (concat X b a b (inverse X a b x) x) r) (concat X b a b (inverse X a b x) (concat X a b b x r))
        (concat_assoc X b a b b (inverse X a b x) x r)
    = concat X b b b (refl b) r by refl ((y ↦ concat X b b b y r) : Id X b b → Id X b b) (concat_inverse_left X a b x)
    = r by concat_1p X b b r ∎

{` A loop of a two-element set that does not move is refl. `}
def two_loop_refl_of_moves (T : BookFiniteSetsAt two) (r : Id (BookFiniteSetsAt two) T T) (e : Id Bool (two_loop_moves T r) false.)
  : Id (Id (BookFiniteSetsAt two) T T) (refl T) r
  ≔ two_loop_sign_section T r false. e

{` Bsgn^A transports along a loop r of Bsgn(B) by postcomposition with r, and
   this moves the two paths iff r moves the two points. `}
def sign_aut_paths_moves (T0 U : BookFiniteSetsAt two) (r : Id (BookFiniteSetsAt two) U U)
  : Id Bool (two_loop_moves (two_set_paths_point T0 U) (refl (two_set_paths_point T0) r)) (two_loop_moves U r)
  ≔ let B2 ≔ BookFiniteSetsAt two in
    let D ≔ two_set_paths_point T0 in
    let P ≔ Id B2 T0 U in let hP ≔ two_set_two_element (D U) in
    let tq ≔ bsigma_two_transport (D U) (D U) (refl D r) in
    let a ≔ two_loop_moves (D U) (refl D r) in let b ≔ two_loop_moves U r in
    two_element_point_elim P hP (Id Bool a b) (bool_set a b)
      (x ↦ let va : Id Bool a (two_differ P hP x (tq .map x)) ≔ two_moves_value P hP tq x in
        bool_eq_from_false_iff a b
          (ea ↦ concat Bool b (two_loop_moves U (refl U)) false.
            (refl (two_loop_moves U)
              (inverse (Id B2 U U) (refl U) r
                (path_postcompose_fixed B2 T0 U x r
                  (two_differ_false P hP x (tq .map x) (concat Bool (two_differ P hP x (tq .map x)) a false. (inverse Bool a (two_differ P hP x (tq .map x)) va) ea)))))
            (two_loop_moves_refl U))
          (eb ↦ concat Bool a (two_differ P hP x (tq .map x)) false. va
            (two_differ_eq P hP x (tq .map x)
              (inverse P (concat B2 T0 U U x r) x
                (concat P (concat B2 T0 U U x r) (concat B2 T0 U U x (refl U)) x
                  (refl (concat B2 T0 U U x) (inverse (Id B2 U U) (refl U) r (two_loop_refl_of_moves U r eb)))
                  (concat_p1 B2 T0 U x))))))

{` The sign of a permutation is whether ap Bsgn of its loop moves the two
   elements of Bsgn(A) (for n ≤ 1 it never does: Bsgn is constant). `}
def bsgn_small_loop_moves (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (A : BookFiniteSetsAt n)
  (s : Equiv (A .fst .fst) (A .fst .fst))
  : Id Bool (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A s))) false.
  ≔ let c : BookFiniteSetsAt n → BookFiniteSetsAt two ≔ _ ↦ shape sign_sigma_two in
    concat Bool (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A s)))
      (two_loop_moves (shape sign_sigma_two) (refl c (permutation_loop n A s))) false.
      (inverse Bool (two_loop_moves (shape sign_sigma_two) (refl c (permutation_loop n A s)))
        (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A s)))
        (two_loop_moves_homotopy (BookFiniteSetsAt n) (bsgn n) c (bsgn_small_constant n hn) A (permutation_loop n A s)))
      (two_loop_moves_refl (shape sign_sigma_two))

def permutation_sign_at_moves (n : Nat)
  : (A : BookFiniteSetsAt n) (s : Equiv (A .fst .fst) (A .fst .fst)) →
    Id Sign (bool_sign (two_loop_moves (bsgn n A) (refl (bsgn n) (permutation_loop n A s)))) (permutation_sign_at n A s)
  ≔ match n [
  | zero. ↦ A s ↦ refl bool_sign (bsgn_small_loop_moves zero. (inl. (refl (zero. : Nat))) A s)
  | suc. zero. ↦ A s ↦ refl bool_sign (bsgn_small_loop_moves (suc. zero.) (inr. (refl (suc. zero. : Nat))) A s)
  | suc. (suc. m) ↦ A s ↦ refl (permutation_sign_at (suc. (suc. m)) A s) ]

{` The permutation of A given by a symmetry g of Aut(A) (its action). `}
def aut_symmetry_permutation (n : Nat) (A0 : BookFiniteSetsAt n) (g : USym (permutation_group (A0 .fst)))
  : Equiv (A0 .fst .fst) (A0 .fst .fst)
  ≔ transport_equiv (A0 .fst .fst) (A0 .fst .fst) (g .fst .fst)

{` group.tex:1663: USym sgn^A (g) is the sign of the permutation of g. `}
def sign_aut_usym_sign (n : Nat) (A0 : BookFiniteSetsAt n) (g : USym (permutation_group (A0 .fst)))
  : Id Sign (sigma_two_sign (usym_hom (permutation_group (A0 .fst)) sign_sigma_two (sign_aut_hom n A0) g))
      (permutation_sign_at n A0 (aut_symmetry_permutation n A0 g))
  ≔ let S ≔ A0 .fst in
    let pt ≔ component_point SetTypes S in
    let ats ≔ aut_to_bsigma n A0 in
    let W : NativeComponent SetTypes S → BookFiniteSetsAt two ≔ B ↦ bsgn n (ats B) in
    let T ≔ W pt in
    let s ≔ aut_symmetry_permutation n A0 g in
    let M : Mere (Id SetTypes (Fin n, fin_set n) S) → Bool
      ≔ m ↦ two_loop_moves (bsgn n (S, m)) (refl (bsgn n) (permutation_loop n (S, m) s)) in
    calc sigma_two_sign (usym_hom (permutation_group S) sign_sigma_two (sign_aut_hom n A0) g)
      = two_loop_sign (bsgn_aut n A0 pt) (refl (bsgn_aut n A0) g)
        by two_loop_sign_conjugate (shape sign_sigma_two) (bsgn_aut n A0 pt) (bsgn_aut_point n A0) (refl (bsgn_aut n A0) g)
      = bool_sign (two_loop_moves T (refl W g)) by refl bool_sign (sign_aut_paths_moves T T (refl W g))
      = bool_sign (M (ats pt .snd))
        by refl ((q ↦ bool_sign (two_loop_moves T (refl (bsgn n) q))) : Id (BookFiniteSetsAt n) (ats pt) (ats pt) → Sign)
          (bsigma_path_ext n (ats pt) (ats pt) (refl ats g) (permutation_loop n (ats pt) s) (x ↦ refl (s .map x)))
      = bool_sign (M (A0 .snd))
        by refl ((m ↦ bool_sign (M m)) : Mere (Id SetTypes (Fin n, fin_set n) S) → Sign)
          (mere_isprop (Id SetTypes (Fin n, fin_set n) S) (ats pt .snd) (A0 .snd))
      = permutation_sign_at n A0 s by permutation_sign_at_moves n A0 s ∎

{` The same stated with a permutation σ of A and its symmetry. `}
def sign_aut_usym_permutation_sign (n : Nat) (A0 : BookFiniteSetsAt n) (σ : Equiv (A0 .fst .fst) (A0 .fst .fst))
  : Id Sign (sigma_two_sign (usym_hom (permutation_group (A0 .fst)) sign_sigma_two (sign_aut_hom n A0) (permutation_symmetry (A0 .fst) σ)))
      (permutation_sign_at n A0 σ)
  ≔ concat Sign (sigma_two_sign (usym_hom (permutation_group (A0 .fst)) sign_sigma_two (sign_aut_hom n A0) (permutation_symmetry (A0 .fst) σ)))
      (permutation_sign_at n A0 (aut_symmetry_permutation n A0 (permutation_symmetry (A0 .fst) σ)))
      (permutation_sign_at n A0 σ)
      (sign_aut_usym_sign n A0 (permutation_symmetry (A0 .fst) σ))
      (permutation_sign_at_homotopy n A0 (aut_symmetry_permutation n A0 (permutation_symmetry (A0 .fst) σ)) σ (x ↦ refl (σ .map x)))

{` For a finite set A (a point of BΣ_{Card A}): USym sgn^A (σ) = sgn(σ). `}
def sign_aut_usym_permutation_sign_finite (A : FiniteSets) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : Id Sign (sigma_two_sign (usym_hom (permutation_group (A .fst)) sign_sigma_two (sign_aut_hom (Card A) (finite_set_point A))
        (permutation_symmetry (A .fst) σ)))
      (permutation_sign A σ)
  ≔ sign_aut_usym_permutation_sign (Card A) (finite_set_point A) σ

{` Litmus: sgn^{Fin 2} sends the swap to −1. `}
def sign_aut_swap_litmus
  : Id Sign (sigma_two_sign (usym_hom (permutation_group (standard_set two)) sign_sigma_two (sign_aut_hom two (standard_shape two))
        (permutation_symmetry (standard_set two) (fin_swap01_equiv zero.))))
      minus.
  ≔ concat Sign (sigma_two_sign (usym_hom (permutation_group (standard_set two)) sign_sigma_two (sign_aut_hom two (standard_shape two))
        (permutation_symmetry (standard_set two) (fin_swap01_equiv zero.))))
      (permutation_sign_at two (standard_shape two) (fin_swap01_equiv zero.)) minus.
      (sign_aut_usym_permutation_sign two (standard_shape two) (fin_swap01_equiv zero.))
      (concat Sign (permutation_sign_at two (standard_shape two) (fin_swap01_equiv zero.))
        (sigma_two_sign (usgn two (permutation_symmetry (standard_set two) (fin_swap01_equiv zero.)))) minus.
        (permutation_sign_standard zero. (fin_swap01_equiv zero.)) (usgn_swap01 zero.))
