export "1724-blass-cyclic"

{` Last theorem of choicefin.tex (Blass, Theorem 6): if ‖X → BC_n‖₀ is
   contractible for all sets X and positive n, then AC(n) holds for all n.
   The proof is the book's, by strong induction in the form ChoiceUpTo n
   (families of non-empty sets with at most n elements). For n+2-element
   sets, AC(n+1) applied to P(x)∖{y} gives fixed-point-free maps f_x; the
   index set splits into the decidable parts where f_x is not injective (choose
   in its image), injective but not transitive (choose an orbit, then a point
   of it) and injective and transitive (a cycle: use the hypothesis). `}

def bsix_path_reflecting_prop (A : Type) (hA : isSet A) (f : A → A) : isProp (PathReflecting A A f)
  ≔ pi_prop A (y ↦ (y' : A) → Id A (f y) (f y') → Id A y y')
      (y ↦ pi_prop A (y' ↦ Id A (f y) (f y') → Id A y y')
        (y' ↦ pi_prop (Id A (f y) (f y')) (_ ↦ Id A y y') (_ ↦ hA y y')))

def bsix_transitive_prop (A : Type) (f : A → A) : isProp (BsixTransitive A f)
  ≔ pi_prop A (y ↦ (z : A) → BsixReach A f y z)
      (y ↦ pi_prop A (z ↦ BsixReach A f y z) (z ↦ mere_isprop (Σ Nat (i ↦ Id A z (iterate A f i y)))))

def bsix_implication_decidable (U V : Type) (dU : Decidable U) (dV : Decidable V) : Decidable (U → V)
  ≔ match dV [
  | inl. v ↦ inl. (_ ↦ v)
  | inr. nv ↦ match dU [ inl. u ↦ inr. (h ↦ nv (h u)) | inr. nu ↦ inl. (u ↦ absurd V (nu u)) ] ]

def bsix_injective_decidable (A : Type) (hA : isSet A) (fin : IsFinite A) (f : A → A)
  : Decidable (PathReflecting A A f)
  ≔ let dA ≔ finite_decidable_equality A fin in
    finite_quantifiers A fin (y ↦ (y' : A) → Id A (f y) (f y') → Id A y y')
      (y ↦ pi_prop A (y' ↦ Id A (f y) (f y') → Id A y y')
        (y' ↦ pi_prop (Id A (f y) (f y')) (_ ↦ Id A y y') (_ ↦ hA y y')))
      (y ↦ finite_quantifiers A fin (y' ↦ Id A (f y) (f y') → Id A y y')
        (y' ↦ pi_prop (Id A (f y) (f y')) (_ ↦ Id A y y') (_ ↦ hA y y'))
        (y' ↦ bsix_implication_decidable (Id A (f y) (f y')) (Id A y y') (dA (f y) (f y')) (dA y y')) .fst) .fst

def bsix_transitive_decidable (A : Type) (fin : IsFinite A) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x))
  : Decidable (BsixTransitive A f)
  ≔ let dA ≔ finite_decidable_equality A fin in
    finite_quantifiers A fin (y ↦ (z : A) → BsixReach A f y z)
      (y ↦ pi_prop A (z ↦ BsixReach A f y z) (z ↦ mere_isprop (Σ Nat (i ↦ Id A z (iterate A f i y)))))
      (y ↦ finite_quantifiers A fin (z ↦ BsixReach A f y z)
        (z ↦ mere_isprop (Σ Nat (i ↦ Id A z (iterate A f i y))))
        (z ↦ bsix_reach_decidable A dA f y z (mper y)) .fst) .fst

{` The data of the split, for one family P of (n+2)-element sets with
   fixed-point-free maps f. `}
def bsix_carrier (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n))) (x : X .fst) : Type
  ≔ P x .fst .fst

def bsix_finite (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n))) (x : X .fst)
  : IsFinite (P x .fst .fst)
  ≔ trunc_map native_truncation (Id Type (Fin (suc. (suc. n))) (P x .fst .fst)) (Σ Nat (m ↦ Id Type (P x .fst .fst) (Fin m)))
      (q ↦ (suc. (suc. n), inverse Type (Fin (suc. (suc. n))) (P x .fst .fst) q)) (P x .snd)

def bsix_noninjective_part (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n)))
  (f : (x : X .fst) → P x .fst .fst → P x .fst .fst) : SetTypes
  ≔ (Σ (X .fst) (x ↦ PathReflecting (P x .fst .fst) (P x .fst .fst) (f x) → Empty),
      sigma_set (X .fst) (x ↦ PathReflecting (P x .fst .fst) (P x .fst .fst) (f x) → Empty) (X .snd)
        (x ↦ prop_is_set (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x) → Empty)
          (negation_prop (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)))))

def bsix_injective_part (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n)))
  (f : (x : X .fst) → P x .fst .fst → P x .fst .fst) (T : (x : X .fst) → Type) (hT : (x : X .fst) → isProp (T x))
  : SetTypes
  ≔ (Σ (X .fst) (x ↦ Σ (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)) (_ ↦ T x)),
      sigma_set (X .fst) (x ↦ Σ (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)) (_ ↦ T x)) (X .snd)
        (x ↦ prop_is_set (Σ (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)) (_ ↦ T x))
          (sigma_prop (PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)) (_ ↦ T x)
            (bsix_path_reflecting_prop (P x .fst .fst) (P x .fst .snd) (f x)) (_ ↦ hT x))))

def bsix_periods (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n)))
  (f : (x : X .fst) → P x .fst .fst → P x .fst .fst) (x : X .fst)
  (inj : PathReflecting (P x .fst .fst) (P x .fst .fst) (f x)) (y : P x .fst .fst)
  : Mere (BsixPeriod (P x .fst .fst) (f x) y)
  ≔ bsix_mere_periods (suc. (suc. n)) (P x .fst .fst) (P x .snd) (f x) inj y

def bsix_glue_three (n : Nat) (X : SetTypes) (P : X .fst → FiniteSetsAt (suc. (suc. n)))
  (f : (x : X .fst) → P x .fst .fst → P x .fst .fst)
  (tA : (z : bsix_noninjective_part n X P f .fst) → P (z .fst) .fst .fst)
  (tB : (z : bsix_injective_part n X P f (x ↦ BsixTransitive (P x .fst .fst) (f x) → Empty)
           (x ↦ negation_prop (BsixTransitive (P x .fst .fst) (f x))) .fst) → P (z .fst) .fst .fst)
  (tC : (z : bsix_injective_part n X P f (x ↦ BsixTransitive (P x .fst .fst) (f x))
           (x ↦ bsix_transitive_prop (P x .fst .fst) (f x)) .fst) → P (z .fst) .fst .fst)
  (x : X .fst) : P x .fst .fst
  ≔ let fin ≔ bsix_finite n X P x in
    match bsix_injective_decidable (P x .fst .fst) (P x .fst .snd) fin (f x) [
    | inr. ninj ↦ tA (x, ninj)
    | inl. inj ↦ match bsix_transitive_decidable (P x .fst .fst) fin (f x) (bsix_periods n X P f x inj) [
      | inl. tr ↦ tC (x, (inj, tr))
      | inr. ntr ↦ tB (x, (inj, ntr)) ] ]

{` Main step: ChoiceUpTo (n+1) and the hypothesis give AC(n+2). `}
def bsix_after_choice (H : CyclicTorsorsTrivial) (n : Nat) (cws : ChoiceUpTo (suc. n)) (X : SetTypes)
  (P : X .fst → FiniteSetsAt (suc. (suc. n))) (inh : (x : X .fst) → Mere (P x .fst .fst))
  (f : (x : X .fst) → P x .fst .fst → P x .fst .fst)
  (fpf : (x : X .fst) (y : P x .fst .fst) → Id (P x .fst .fst) (f x y) y → Empty)
  : Mere ((x : X .fst) → P x .fst .fst)
  ≔ let A : X .fst → Type ≔ x ↦ P x .fst .fst in
    let dA : (x : X .fst) → DecidableEquality (A x) ≔ x ↦ finite_decidable_equality (A x) (bsix_finite n X P x) in
    let XA ≔ bsix_noninjective_part n X P f in
    let XB ≔ bsix_injective_part n X P f (x ↦ BsixTransitive (A x) (f x) → Empty)
      (x ↦ negation_prop (BsixTransitive (A x) (f x))) in
    let XC ≔ bsix_injective_part n X P f (x ↦ BsixTransitive (A x) (f x)) (x ↦ bsix_transitive_prop (A x) (f x)) in
    let O : XB .fst → Type
      ≔ z ↦ BsixOrbits (A (z .fst)) (f (z .fst)) (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)) in
    let Goal ≔ Mere ((x : X .fst) → A x) in
    let goal_prop ≔ mere_isprop ((x : X .fst) → A x) in
    mere_rec ((z : XA .fst) → BsixImage (A (z .fst)) (f (z .fst))) Goal goal_prop
      (tA ↦ mere_rec ((z : XB .fst) → O z) Goal goal_prop
        (o ↦ mere_rec ((z : XB .fst) → BsixOrbitElements (A (z .fst)) (f (z .fst))
                (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)) (o z)) Goal goal_prop
          (tB ↦ mere_rec ((z : XC .fst) → A (z .fst)) Goal goal_prop
            (tC ↦ mere ((x : X .fst) → A x)
              (bsix_glue_three n X P f (z ↦ tA z .fst) (z ↦ tB z .fst) tC))
            (bsix_cyclic_sections H n XC (z ↦ A (z .fst)) (z ↦ P (z .fst) .fst .snd) (z ↦ P (z .fst) .snd)
              (z ↦ f (z .fst)) (z ↦ z .snd .fst) (z ↦ z .snd .snd)))
          (cws XB (z ↦ BsixOrbitElements (A (z .fst)) (f (z .fst))
                (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)) (o z))
            (z ↦ bsix_orbit_elements_bound (suc. n) (A (z .fst)) (P (z .fst) .snd) (f (z .fst))
              (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)) (z .snd .snd) (o z))
            (z ↦ quotient_surjective (A (z .fst))
              (bsix_reach_relation (A (z .fst)) (f (z .fst)) (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)))
              (o z))))
        (cws XB O
          (z ↦ bsix_orbits_bound (suc. n) (A (z .fst)) (P (z .fst) .snd) (f (z .fst)) (fpf (z .fst))
            (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)))
          (z ↦ trunc_map native_truncation (A (z .fst)) (O z)
            (bsix_orbit_class (A (z .fst)) (f (z .fst)) (bsix_periods n X P f (z .fst) (z .snd .fst)) (dA (z .fst)))
            (inh (z .fst)))))
      (cws XA (z ↦ BsixImage (A (z .fst)) (f (z .fst)))
        (z ↦ bsix_image_bound (suc. n) (A (z .fst)) (P (z .fst) .snd) (f (z .fst)) (z .snd))
        (z ↦ trunc_map native_truncation (A (z .fst)) (BsixImage (A (z .fst)) (f (z .fst)))
          (y ↦ (f (z .fst) y, mere (BookFiber (A (z .fst)) (A (z .fst)) (f (z .fst)) (f (z .fst) y)) (y, refl (f (z .fst) y))))
          (inh (z .fst))))

def blass_main_step (H : CyclicTorsorsTrivial) (n : Nat) (cws : ChoiceUpTo (suc. n)) : ChoiceOfSize (suc. (suc. n))
  ≔ X P inh ↦
    let Y : SetTypes ≔ (Σ (X .fst) (x ↦ P x .fst .fst),
      sigma_set (X .fst) (x ↦ P x .fst .fst) (X .snd) (x ↦ P x .fst .snd)) in
    mere_rec ((w : Y .fst) → Without (P (w .fst) .fst .fst) (w .snd)) (Mere ((x : X .fst) → P x .fst .fst))
      (mere_isprop ((x : X .fst) → P x .fst .fst))
      (g ↦ bsix_after_choice H n cws X P inh (x y ↦ g (x, y) .fst) (x y ↦ g (x, y) .snd))
      (cws Y (w ↦ Without (P (w .fst) .fst .fst) (w .snd))
        (w ↦ bsix_without_bound (suc. n) (P (w .fst) .fst .fst) (P (w .fst) .snd) (w .snd))
        (w ↦ bsix_without_inhabited n (P (w .fst) .fst .fst) (P (w .fst) .snd) (w .snd)))

{` Strong induction: ChoiceUpTo n for every n (the case n = 1 is AC(1), the
   book's trivial base case). `}
def bsix_choice_step (H : CyclicTorsorsTrivial) (m : Nat) (cws : ChoiceUpTo m) : ChoiceOfSize (suc. m)
  ≔ match m [ zero. ↦ choice_of_size_one | suc. k ↦ blass_main_step H k cws ]

def bsix_choice_up_to (H : CyclicTorsorsTrivial) (n : Nat) : ChoiceUpTo n
  ≔ match n [
  | zero. ↦ choice_up_to_zero
  | suc. m ↦ choice_up_to_succ m (bsix_choice_up_to H m) (bsix_choice_step H m (bsix_choice_up_to H m)) ]

{` The theorem: AC(n) for all n, including n = 0. `}
def blass_cyclic_choice (H : CyclicTorsorsTrivial) (n : Nat) : ChoiceOfSize n
  ≔ choice_up_to_size n (bsix_choice_up_to H n)

{` Non-vacuity of the hypothesis: it follows from AC (lem:ac-impl-triv-coh-sets,
   since Cyc_n is a pointed connected groupoid). `}
def choice_cyclic_torsors_trivial (ac : AxiomOfChoice) : CyclicTorsorsTrivial
  ≔ X n ↦ local_choice_torsors_trivial (X .fst) (X .snd) (ac X)
      (mkgroup (CycleComponent (suc. n), principal_component_point (suc. n),
        native_component_connected Cycles (principal_cycle (suc. n)),
        component_groupoid Cycles cycles_groupoid (principal_cycle (suc. n))))
