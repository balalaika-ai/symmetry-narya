export "43-set-truncation"

{` A decision carries a witness in its positive branch. This does not eliminate
   arbitrary mere existence into a non-proposition without additional data. `}
def decidable_pick (A : Type) (d : Decidable A) (t : Mere A) : A
  ≔ match d [ inl. a ↦ a | inr. no ↦ absurd A (mere_rec A Empty empty_prop no t) ]

def fin_surjection_section (n : Nat) (B : Type) (f : Fin n → B) (db : DecidableEquality B)
  (hf : Surjective (Fin n) B f) (b : B) : BookFiber (Fin n) B f b
  ≔ decidable_pick (BookFiber (Fin n) B f b)
      (fin_sigma_decidable n (i ↦ Id B b (f i)) (i ↦ db b (f i))) (hf b)

def RetractFixed (A B : Type) (f : A → B) (s : B → A) : Type
  ≔ Σ A (a ↦ Id A (s (f a)) a)

def retract_fixed_equiv (A B : Type) (ha : isSet A) (f : A → B) (s : B → A)
  (hs : (b : B) → Id B b (f (s b))) : Equiv B (RetractFixed A B f s)
  ≔ quasi_inverse_equiv B (RetractFixed A B f s)
      (b ↦ (s b, map_path B A s (f (s b)) b (inverse B b (f (s b)) (hs b))))
      (t ↦ f (t .fst))
      (b ↦ inverse B b (f (s b)) (hs b))
      (t ↦ subtype_equal A (a ↦ Id A (s (f a)) a) (a ↦ ha (s (f a)) a)
        (s (f (t .fst)), map_path B A s (f (s (f (t .fst)))) (f (t .fst))
          (inverse B (f (t .fst)) (f (s (f (t .fst)))) (hs (f (t .fst))))) t (t .snd))

def fin_surjection_target_finite (n : Nat) (B : Type) (db : DecidableEquality B)
  (f : Fin n → B) (hf : Surjective (Fin n) B f) : IsFinite B
  ≔ let s : B → Fin n ≔ (b ↦ fin_surjection_section n B f db hf b .fst) in
    let hs : (b : B) → Id B b (f (s b)) ≔ (b ↦ fin_surjection_section n B f db hf b .snd) in
    finite_of_equiv B (RetractFixed (Fin n) B f s) (retract_fixed_equiv (Fin n) B (fin_set n) f s hs)
      (finite_decidable_subset (Fin n) (fin_is_finite n) (a ↦ Id (Fin n) (s (f a)) a)
        (a ↦ fin_set n (s (f a)) a) (a ↦ fin_decidable_equality n (s (f a)) a))

def FiniteSurjectionTargets (B : Type) (A : Type) : Type
  ≔ (f : A → B) → Surjective A B f → IsFinite B

def finite_surjection_targets_prop (B A : Type) : isProp (FiniteSurjectionTargets B A)
  ≔ pi_prop (A → B) (f ↦ Surjective A B f → IsFinite B)
      (f ↦ pi_prop (Surjective A B f) (_ ↦ IsFinite B) (_ ↦ isfinite_prop B))

{` No global section of a merely finite surjection is selected: its target's
   finiteness is proved by proposition-valued induction on the domain. `}
def finite_surjection_target (A B : Type) (ha : IsFinite A) (db : DecidableEquality B)
  : FiniteSurjectionTargets B A
  ≔ finite_ind_prop (FiniteSurjectionTargets B) (finite_surjection_targets_prop B)
      (n ↦ fin_surjection_target_finite n B db) A ha

def DecidableRelation (A : Type) (R : EquivalenceRelation A) : Type
  ≔ (x y : A) → Decidable (Rel A R x y)

def quotient_decide_witnesses (A : Type) (R : EquivalenceRelation A) (d : DecidableRelation A R)
  (z w : Quotient A R) (u : BookFiber A (Quotient A R) (quotient_class A R) z)
  (v : BookFiber A (Quotient A R) (quotient_class A R) w) : Decidable (Id (Quotient A R) z w)
  ≔ match d (u .fst) (v .fst) [
  | inl. r ↦ inl. (concat (Quotient A R) z (quotient_class A R (u .fst)) w (u .snd)
      (concat (Quotient A R) (quotient_class A R (u .fst)) (quotient_class A R (v .fst)) w
        (quotient_encode A R (u .fst) (v .fst) r)
        (inverse (Quotient A R) w (quotient_class A R (v .fst)) (v .snd))))
  | inr. no ↦ inr. (p ↦ no (quotient_effective A R (u .fst) (v .fst) .map
      (concat (Quotient A R) (quotient_class A R (u .fst)) z (quotient_class A R (v .fst))
        (inverse (Quotient A R) z (quotient_class A R (u .fst)) (u .snd))
        (concat (Quotient A R) z w (quotient_class A R (v .fst)) p (v .snd))))) ]

def quotient_decidable_equality (A : Type) (R : EquivalenceRelation A) (d : DecidableRelation A R)
  : DecidableEquality (Quotient A R)
  ≔ z w ↦ mere_rec (BookFiber A (Quotient A R) (quotient_class A R) z)
      (Decidable (Id (Quotient A R) z w)) (decidability_prop (Id (Quotient A R) z w) (quotient_set A R z w))
      (u ↦ mere_rec (BookFiber A (Quotient A R) (quotient_class A R) w)
        (Decidable (Id (Quotient A R) z w)) (decidability_prop (Id (Quotient A R) z w) (quotient_set A R z w))
        (quotient_decide_witnesses A R d z w u) (quotient_surjective A R w)) (quotient_surjective A R z)

{` xca:dec-quot-finite-set, for the constructed predicate-image quotient. `}
def finite_quotient (A : Type) (ha : IsFinite A) (R : EquivalenceRelation A) (d : DecidableRelation A R)
  : IsFinite (Quotient A R)
  ≔ finite_surjection_target A (Quotient A R) ha (quotient_decidable_equality A R d)
      (quotient_class A R) (quotient_surjective A R)
