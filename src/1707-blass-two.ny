export "1706-blass-reduced-words"

{` thm:Blass-2. The book's group is G = Ω(C, c) for the pushout C of
   1 ← Y → X; its torsor f : X → C has fibers c = f(x), identified in the
   proof with reduced words. Here, without a pushout, the group is Aut(S)
   for the set S of reduced loop words (BAut(S) = component of S in Set),
   and the map X → BAut(S) sends x to the set T_x of reduced paths to x,
   which is merely S because p is surjective (bword_paths_loops_equiv). `}
def bword_loops_settype (W : bword_Setup) : SetTypes ≔ (bword_Loops W, bword_loops_set W)

def bword_paths_settype (W : bword_Setup) (x : W .cod) : SetTypes ≔ (bword_Paths W x, bword_paths_set W x)

def bword_paths_component (W : bword_Setup) (surj : Surjective (W .dom) (W .cod) (W .map)) (x : W .cod)
  : NativeComponent SetTypes (bword_loops_settype W)
  ≔ (bword_paths_settype W x,
      trunc_map native_truncation (BookFiber (W .dom) (W .cod) (W .map) x)
        (Id SetTypes (bword_loops_settype W) (bword_paths_settype W x))
        (w ↦ subtype_equal Type isSet isset_isprop (bword_loops_settype W) (bword_paths_settype W x)
          (ua (bword_Loops W) (bword_Paths W x)
            (canonical_inverse_equiv (bword_Paths W x) (bword_Loops W)
              (bword_paths_loops_equiv W x (w .fst) (inverse (W .cod) x (W .map (w .fst)) (w .snd))))))
        (surj x))

{` The core argument: if p : Y → X is surjective, Y has decidable equality
   and X is a set with trivial G-torsors for all groups G, then p merely has
   a section (as a split surjection Π_x p⁻¹(x)). Decidable equality of X is
   not needed for this step. `}
def blass_two_core (W : bword_Setup) (H : GroupTorsorsTrivial (W .cod))
  (surj : Surjective (W .dom) (W .cod) (W .map))
  : Mere (SplitSurjection (W .dom) (W .cod) (W .map))
  ≔ let S ≔ bword_loops_settype W in
    let BG ≔ NativeComponent SetTypes S in
    let sh ≔ component_point SetTypes S in
    let F : W .cod → BG ≔ bword_paths_component W surj in
    trunc_map native_truncation ((x : W .cod) → Id BG sh (F x)) (SplitSurjection (W .dom) (W .cod) (W .map))
      (e x ↦ bword_endpoint W x (set_component_transport S (F x) (e x) (bword_empty_loop W)))
      (contractible_set_trunc_constant (W .cod) BG sh
        (H (automorphism_group SetTypes sets_groupoid S)) F)

{` thm:Blass-2, surjection form of the proof: X and Y decidable sets
   (def:decidable-set: sets with decidable equality), p surjective. `}
def blass_two_surjection (X Y : Type) (hX : isSet X) (dX : DecidableEquality X)
  (hY : isSet Y) (dY : DecidableEquality Y) (H : GroupTorsorsTrivial X) (p : Y → X)
  (surj : Surjective Y X p) : Mere (MapSection Y X p)
  ≔ trunc_map native_truncation (SplitSurjection Y X p) (MapSection Y X p) (split_surjection_to_section Y X p)
      (blass_two_core (Y, X, hY, dY, hX, p) H surj)

{` Decidable equality of Σ_{x:X} B(x) over a set X with decidable equality
   and fibers with decidable equality. `}
def bword_sigma_decide_step (X : Type) (B : X → Type) (hX : isSet X) (dB : (x : X) → DecidableEquality (B x))
  (u v : Σ X B) (d : Decidable (Id X (u .fst) (v .fst))) : Decidable (Id (Σ X B) u v)
  ≔ match d [
  | inr. n ↦ inr. (r ↦ n (r .fst))
  | inl. e ↦ match dB (v .fst) (transport X B (u .fst) (v .fst) e (u .snd)) (v .snd) [
    | inl. q ↦ inl. (e, pathover_of_eq X B (u .fst) (v .fst) e (u .snd) (v .snd) q)
    | inr. nq ↦ inr. (r ↦ nq (concat (B (v .fst)) (transport X B (u .fst) (v .fst) e (u .snd))
        (transport X B (u .fst) (v .fst) (r .fst) (u .snd)) (v .snd)
        (transport2 X B (u .fst) (v .fst) e (r .fst) (hX (u .fst) (v .fst) e (r .fst)) (u .snd))
        (pathover_transport_equiv X B (u .fst) (v .fst) (r .fst) (u .snd) (v .snd) .map (r .snd)))) ] ]

def bword_sigma_decidable_equality (X : Type) (B : X → Type) (hX : isSet X) (dX : DecidableEquality X)
  (dB : (x : X) → DecidableEquality (B x)) : DecidableEquality (Σ X B)
  ≔ u v ↦ bword_sigma_decide_step X B hX dB u v (dX (u .fst) (v .fst))

{` thm:Blass-2 as printed: a decidable set X with ‖X → BG‖₀ contractible for
   all groups G; every family of non-empty decidable sets over X merely has
   a section. `}
def blass_two (X : Type) (hX : isSet X) (dX : DecidableEquality X) (H : GroupTorsorsTrivial X)
  (P : X → SetTypes) (dP : (x : X) → DecidableEquality (P x .fst)) (ne : (x : X) → Mere (P x .fst))
  : Mere ((x : X) → P x .fst)
  ≔ let T ≔ Σ X (x ↦ P x .fst) in
    trunc_map native_truncation (MapSection T X (t ↦ t .fst)) ((x : X) → P x .fst)
      (equiv_inverse_map ((x : X) → P x .fst) (MapSection T X (t ↦ t .fst)) (pi_section_equiv X (x ↦ P x .fst)))
      (blass_two_surjection X T hX dX (sigma_set X (x ↦ P x .fst) hX (x ↦ P x .snd))
        (bword_sigma_decidable_equality X (x ↦ P x .fst) hX dX dP) H (t ↦ t .fst)
        (projection_surjective X (x ↦ P x .fst) ne))

{` Litmus: Y = Bool over X = Unit. The path k(true) to the unique point is
   sent to the one-letter loop k(true)·k(false)⁻¹, the path k(false) to the
   empty loop, and back again. `}
def bword_bool_setup : bword_Setup
  ≔ (Bool, Unit, bool_set, choice_bool_decidable_equality, unit_set, (_ ↦ star.))

def bword_bool_path (b : Bool) : bword_Paths bword_bool_setup star.
  ≔ ((b, nil.), (refl star., (star., star.)))

def bword_bool_true_length
  : Id Nat (length (bword_Pair bword_bool_setup)
      (bword_to_loops bword_bool_setup star. false. (refl star.) (bword_bool_path true.) .fst)) (suc. zero.)
  ≔ refl (suc. zero.)

def bword_bool_true_letter
  : Id (List (Product Bool Bool))
      (match bword_to_loops bword_bool_setup star. false. (refl star.) (bword_bool_path true.) .fst [
       | nil. ↦ nil.
       | cons. d _ ↦ cons. (d .fst) nil. ])
      (cons. (true., false.) nil.)
  ≔ refl (cons. ((true., false.) : Product Bool Bool) nil.)

def bword_bool_false_length
  : Id Nat (length (bword_Pair bword_bool_setup)
      (bword_to_loops bword_bool_setup star. false. (refl star.) (bword_bool_path false.) .fst)) zero.
  ≔ refl zero.

def bword_bool_roundtrip_endpoint
  : Id Bool (bword_from_loops bword_bool_setup star. false. (refl star.)
      (bword_to_loops bword_bool_setup star. false. (refl star.) (bword_bool_path true.)) .fst .fst) true.
  ≔ refl (true. : Bool)
