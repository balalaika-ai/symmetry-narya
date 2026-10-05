export "61-connected-coverings"

def permutation_powers_commute (A : Type) (e : Equiv A A) (n k : Int) (x : A)
  : Id A (permutation_power A e n (permutation_power A e k x)) (permutation_power A e k (permutation_power A e n x))
  ≔ calc
      permutation_power A e n (permutation_power A e k x) = permutation_power A e (int_add k n) x
        by permutation_power_add A e k n x
      = permutation_power A e (int_add n k) x
        by refl ((z ↦ permutation_power A e z x) : Int → A) (int_add_comm k n)
      = permutation_power A e k (permutation_power A e n x) by permutation_power_add A e n k x ∎

def PowerPeriod (A : Type) (e : Equiv A A) (n : Int) : Type
  ≔ Id (A → A) (permutation_power A e n) (identity A)
def power_period_prop (A : Type) (hs : isSet A) (e : Equiv A A) (n : Int) : isProp (PowerPeriod A e n)
  ≔ pi_set A (_ ↦ A) (_ ↦ hs) (permutation_power A e n) (identity A)

def cycle_periods (A : Type) (hs : isSet A) (e : Equiv A A) : Int → PropTypes
  ≔ n ↦ (PowerPeriod A e n, power_period_prop A hs e n)

def cycle_fix_from_point (A : Type) (hs : isSet A) (e : Equiv A A) (c : Cyclic A e)
  (x : A) (n : Int) (h : Id A (permutation_power A e n x) x) (y : A)
  : Id A (permutation_power A e n y) y
  ≔ mere_rec (OrbitWitness A e x y) (Id A (permutation_power A e n y) y) (hs (permutation_power A e n y) y)
      (w ↦ calc
        permutation_power A e n y = permutation_power A e n (permutation_power A e (w .fst) x)
          by refl (permutation_power A e n) (w .snd)
        = permutation_power A e (w .fst) (permutation_power A e n x) by permutation_powers_commute A e n (w .fst) x
        = permutation_power A e (w .fst) x by refl (permutation_power A e (w .fst)) h
        = y by w .snd ∎) (c .snd x y)

def cycle_period_from_point (A : Type) (hs : isSet A) (e : Equiv A A) (c : Cyclic A e)
  (x : A) (n : Int) (h : Id A (permutation_power A e n x) x) : PowerPeriod A e n
  ≔ funext A (_ ↦ A) (permutation_power A e n) (identity A) (cycle_fix_from_point A hs e c x n h)

def cycle_period_evaluation (A : Type) (hs : isSet A) (e : Equiv A A) (c : Cyclic A e) (x : A) (n : Int)
  : Equiv (PowerPeriod A e n) (Id A (permutation_power A e n x) x)
  ≔ iff_equiv (PowerPeriod A e n) (Id A (permutation_power A e n x) x)
      (power_period_prop A hs e n) (hs (permutation_power A e n x) x)
      (p ↦ p (refl x)) (cycle_period_from_point A hs e c x n)

def cycle_periods_at_point (A : Type) (hs : isSet A) (e : Equiv A A) (c : Cyclic A e) (x : A)
  : Id (Int → PropTypes) (cycle_periods A hs e)
      (n ↦ (Id A (permutation_power A e n x) x, hs (permutation_power A e n x) x))
  ≔ funext Int (_ ↦ PropTypes) (cycle_periods A hs e)
      (n ↦ (Id A (permutation_power A e n x) x, hs (permutation_power A e n x) x))
      (n ↦ proposition_extensionality (cycle_periods A hs e n)
        (Id A (permutation_power A e n x) x, hs (permutation_power A e n x) x)
        (p ↦ p (refl x)) (cycle_period_from_point A hs e c x n))

def power_period_zero (A : Type) (e : Equiv A A) : PowerPeriod A e int_zero ≔ refl (identity A)
def power_period_add (A : Type) (e : Equiv A A) (n k : Int) (p : PowerPeriod A e n) (q : PowerPeriod A e k)
  : PowerPeriod A e (int_add n k)
  ≔ funext A (_ ↦ A) (permutation_power A e (int_add n k)) (identity A) (x ↦ calc
      permutation_power A e (int_add n k) x = permutation_power A e k (permutation_power A e n x)
        by permutation_power_add A e n k x
      = permutation_power A e k x by refl (permutation_power A e k) (p (refl x))
      = x by q (refl x) ∎)

def power_period_neg (A : Type) (e : Equiv A A) (n : Int) (p : PowerPeriod A e n)
  : PowerPeriod A e (int_neg n)
  ≔ funext A (_ ↦ A) (permutation_power A e (int_neg n)) (identity A) (x ↦ calc
      permutation_power A e (int_neg n) x = permutation_power A e (int_neg n) (permutation_power A e n x)
        by refl (permutation_power A e (int_neg n)) (p (refl x))
      = x by permutation_power_inverse A e n x ∎)

def PeriodInclusion (A B : Type) (e : Equiv A A) (f : Equiv B B) : Type
  ≔ (n : Int) → PowerPeriod A e n → PowerPeriod B f n
