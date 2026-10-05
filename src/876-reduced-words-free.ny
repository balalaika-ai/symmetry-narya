export "875-reduced-word-orbits"
export "874-free-sset-classifying"

{` The reduced words R_S over a set S with decidable equality form a free
   S-set on ε (for EVERY target type), and hence give an actual free group
   signature and free group (no HITs, no axioms).

   The S-action is s_a = reduced_letter_action (inl a) of module 861
   (s_a(w) = ρ(a w)).  For each a, a reduced word either does not start
   with ā (then a·w is an edge) or is ā·w' (an edge at ā): this is the
   equivalence fsc_letter_split_equiv (decidable equality is used here).
   Reindexing the equivariance data φ(s_a w) = F_a(φ w) along it, using
   s_a(w) = a·w in the first case and s_a(ā·w') = w' together with
   φ(w') = F_a(φ(ā w')) ⟺ φ(ā w') = F_a⁻¹(φ w') in the second, turns it
   into the edge steps of module 875, whose maps are equivalent to Y by
   evaluation at ε. `}

def reduced_word_act (S : Type) (dec : DecidableEquality S) (a : S) : Equiv (ReducedWord S) (ReducedWord S)
  ≔ reduced_letter_action_equiv S dec (inl. a)

{` Reduced words = edges at a + edges at ā. `}
def fsc_letter_split (S : Type) (a : S) (t : Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
  : ReducedWord S
  ≔ match t [ inl. p ↦ (p .fst, p .snd .snd) | inr. p ↦ (cons. (inr. a) (p .fst), p .snd) ]

def fsc_letter_unsplit_cons (S : Type) (a : S) (y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. y v)) (d : Decidable (Id (SignedLetter S) y (letter_complement S (inl. a))))
  : Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a))
  ≔ match d [
  | inl. q ↦ inr. (v, transport (SignedLetter S) (z ↦ IsReducedWord S (cons. z v)) y (inr. a) q h)
  | inr. n ↦ inl. (cons. y v, (n, h)) ]

def fsc_letter_unsplit (S : Type) (dec : DecidableEquality S) (a : S) (w : SignedWord S) (h : IsReducedWord S w)
  : Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a))
  ≔ match w [
  | nil. ↦ inl. (nil., (star., star.))
  | cons. y v ↦ fsc_letter_unsplit_cons S a y v h
      (signed_letter_decidable_equality S dec y (letter_complement S (inl. a))) ]

def fsc_split_unsplit_cons (S : Type) (a : S) (y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. y v)) (d : Decidable (Id (SignedLetter S) y (letter_complement S (inl. a))))
  : Id (ReducedWord S) (fsc_letter_split S a (fsc_letter_unsplit_cons S a y v h d)) (cons. y v, h)
  ≔ match d [
  | inl. q ↦ reduced_word_path S
      (cons. (inr. a) v, transport (SignedLetter S) (z ↦ IsReducedWord S (cons. z v)) y (inr. a) q h) (cons. y v, h)
      (cons. (inverse (SignedLetter S) y (inr. a) q) (refl v))
  | inr. n ↦ refl ((cons. y v, h) : ReducedWord S) ]

def fsc_split_unsplit (S : Type) (dec : DecidableEquality S) (a : S) (w : SignedWord S) (h : IsReducedWord S w)
  : Id (ReducedWord S) (fsc_letter_split S a (fsc_letter_unsplit S dec a w h)) (w, h)
  ≔ match w [
  | nil. ↦ reduced_word_path S (nil., star.) (nil., h) (refl (nil. : SignedWord S))
  | cons. y v ↦ fsc_split_unsplit_cons S a y v h
      (signed_letter_decidable_equality S dec y (letter_complement S (inl. a))) ]

def fsc_edge_at_path (S : Type) (x : SignedLetter S) (p q : ReducedEdgeAt S x)
  (e : Id (SignedWord S) (p .fst) (q .fst)) : Id (ReducedEdgeAt S x) p q
  ≔ subtype_equal (SignedWord S) (w ↦ IsReducedWord S (cons. x w)) (w ↦ is_reduced_word_prop S (cons. x w)) p q e

def fsc_unsplit_split_left_cons (S : Type) (a : S) (y : SignedLetter S) (v : SignedWord S)
  (h : IsReducedWord S (cons. (inl. a) (cons. y v)))
  (d : Decidable (Id (SignedLetter S) y (letter_complement S (inl. a))))
  : Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit_cons S a y v (h .snd) d) (inl. (cons. y v, h))
  ≔ match d [
  | inl. q ↦ absurd (Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit_cons S a y v (h .snd) (inl. q)) (inl. (cons. y v, h))) (h .fst q)
  | inr. n ↦ inl. (fsc_edge_at_path S (inl. a) (cons. y v, (n, h .snd)) (cons. y v, h) (refl (cons. y v : SignedWord S))) ]

def fsc_unsplit_split_left (S : Type) (dec : DecidableEquality S) (a : S) (w : SignedWord S)
  (h : IsReducedWord S (cons. (inl. a) w))
  : Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit S dec a w (h .snd)) (inl. (w, h))
  ≔ match w [
  | nil. ↦ inl. (fsc_edge_at_path S (inl. a) (nil., (star., star.)) (nil., h) (refl (nil. : SignedWord S)))
  | cons. y v ↦ fsc_unsplit_split_left_cons S a y v h
      (signed_letter_decidable_equality S dec y (letter_complement S (inl. a))) ]

def fsc_unsplit_split_right (S : Type) (a : S) (v : SignedWord S) (h : IsReducedWord S (cons. (inr. a) v))
  (d : Decidable (Id (SignedLetter S) (inr. a) (letter_complement S (inl. a))))
  : Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit_cons S a (inr. a) v h d) (inr. (v, h))
  ≔ match d [
  | inl. q ↦ inr. (fsc_edge_at_path S (inr. a)
      (v, transport (SignedLetter S) (z ↦ IsReducedWord S (cons. z v)) (inr. a) (inr. a) q h) (v, h) (refl v))
  | inr. n ↦ absurd (Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit_cons S a (inr. a) v h (inr. n)) (inr. (v, h))) (n (refl (inr. a : SignedLetter S))) ]

def fsc_unsplit_split (S : Type) (dec : DecidableEquality S) (a : S)
  (t : Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
  : Id (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)))
      (fsc_letter_unsplit S dec a (fsc_letter_split S a t .fst) (fsc_letter_split S a t .snd)) t
  ≔ match t [
  | inl. p ↦ fsc_unsplit_split_left S dec a (p .fst) (p .snd)
  | inr. p ↦ fsc_unsplit_split_right S a (p .fst) (p .snd)
      (signed_letter_decidable_equality S dec (inr. a) (letter_complement S (inl. a))) ]

def fsc_letter_split_equiv (S : Type) (dec : DecidableEquality S) (a : S)
  : Equiv (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a))) (ReducedWord S)
  ≔ quasi_inverse_equiv (Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a))) (ReducedWord S)
      (fsc_letter_split S a) (r ↦ fsc_letter_unsplit S dec a (r .fst) (r .snd))
      (fsc_unsplit_split S dec a) (r ↦ fsc_split_unsplit S dec a (r .fst) (r .snd))

{` Generic reindexing of dependent functions. `}
def fsc_pi_base_change (A B : Type) (e : Equiv A B) (C : B → Type)
  : Equiv ((b : B) → C b) ((a : A) → C (e .map a))
  ≔ equivalence_induction A (B e ↦ (C : B → Type) → Equiv ((b : B) → C b) ((a : A) → C (e .map a)))
      (C ↦ identity_equiv ((a : A) → C a)) B e C

def fsc_sum_pi_cases (A B : Type) (C : Sum A B → Type) (f : (a : A) → C (inl. a)) (g : (b : B) → C (inr. b))
  (t : Sum A B) : C t
  ≔ match t [ inl. a ↦ f a | inr. b ↦ g b ]

def fsc_sum_pi_equiv (A B : Type) (C : Sum A B → Type)
  : Equiv ((t : Sum A B) → C t) (Product ((a : A) → C (inl. a)) ((b : B) → C (inr. b)))
  ≔ quasi_inverse_equiv ((t : Sum A B) → C t) (Product ((a : A) → C (inl. a)) ((b : B) → C (inr. b)))
      (k ↦ (a ↦ k (inl. a), b ↦ k (inr. b))) (u ↦ fsc_sum_pi_cases A B C (u .fst) (u .snd))
      (k ↦ funext (Sum A B) C (fsc_sum_pi_cases A B C (a ↦ k (inl. a)) (b ↦ k (inr. b))) k
        (t ↦ match t [ inl. a ↦ refl (k (inl. a)) | inr. b ↦ refl (k (inr. b)) ]))
      (u ↦ refl u)

def fsc_signed_pi_equiv (S : Type) (P : SignedLetter S → Type)
  : Equiv ((a : S) → Product (P (inl. a)) (P (inr. a))) ((x : SignedLetter S) → P x)
  ≔ quasi_inverse_equiv ((a : S) → Product (P (inl. a)) (P (inr. a))) ((x : SignedLetter S) → P x)
      (u ↦ fsc_sum_pi_cases S S P (a ↦ u a .fst) (a ↦ u a .snd)) (k a ↦ (k (inl. a), k (inr. a)))
      (u ↦ refl u)
      (k ↦ funext (SignedLetter S) P (fsc_sum_pi_cases S S P (a ↦ k (inl. a)) (a ↦ k (inr. a))) k
        (x ↦ match x [ inl. a ↦ refl (k (inl. a)) | inr. a ↦ refl (k (inr. a)) ]))

def fsc_edge_curry_equiv (S : Type) (D : ReducedEdge S → Type)
  : Equiv ((x : SignedLetter S) (p : ReducedEdgeAt S x) → D (x, p)) ((e : ReducedEdge S) → D e)
  ≔ quasi_inverse_equiv ((x : SignedLetter S) (p : ReducedEdgeAt S x) → D (x, p)) ((e : ReducedEdge S) → D e)
      (k e ↦ k (e .fst) (e .snd)) (k x p ↦ k (x, p)) (k ↦ refl k) (k ↦ refl k)

{` Equivariance data at a and the edge steps at a and at ā. `}
def FscLetterCommutes (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  (phi : ReducedWord S → Y) (a : S) (r : ReducedWord S) : Type
  ≔ Id Y (phi (reduced_letter_action S dec (inl. a) r)) (F a .map (phi r))

def FscEdgeStep (S Y : Type) (F : S → Equiv Y Y) (phi : ReducedWord S → Y) (e : ReducedEdge S) : Type
  ≔ Id Y (phi (reduced_edge_word S e)) (fsc_signed_map S Y F (e .fst) (phi (reduced_edge_tail S e)))

def fsc_commutes_left_equiv (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  (phi : ReducedWord S → Y) (a : S) (p : ReducedEdgeAt S (inl. a))
  : Equiv (FscLetterCommutes S dec Y F phi a (p .fst, p .snd .snd)) (FscEdgeStep S Y F phi (inl. a, p))
  ≔ fsc_path_endpoints_equiv Y (phi (reduced_letter_action S dec (inl. a) (p .fst, p .snd .snd)))
      (phi (cons. (inl. a) (p .fst), p .snd))
      (refl phi (reduced_letter_action_cons S dec (inl. a) (p .fst) (p .snd)))
      (F a .map (phi (p .fst, p .snd .snd))) (F a .map (phi (p .fst, p .snd .snd)))
      (refl (F a .map (phi (p .fst, p .snd .snd))))

def fsc_commutes_right_equiv (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  (phi : ReducedWord S → Y) (a : S) (p : ReducedEdgeAt S (inr. a))
  : Equiv (FscLetterCommutes S dec Y F phi a (cons. (inr. a) (p .fst), p .snd)) (FscEdgeStep S Y F phi (inr. a, p))
  ≔ compose_equiv (FscLetterCommutes S dec Y F phi a (cons. (inr. a) (p .fst), p .snd))
      (Id Y (phi (p .fst, p .snd .snd)) (F a .map (phi (cons. (inr. a) (p .fst), p .snd))))
      (FscEdgeStep S Y F phi (inr. a, p))
      (fsc_path_endpoints_equiv Y (phi (reduced_letter_action S dec (inl. a) (cons. (inr. a) (p .fst), p .snd)))
        (phi (p .fst, p .snd .snd))
        (refl phi (reduced_letter_action_cancel_head S dec (inl. a) (p .fst) (p .snd)))
        (F a .map (phi (cons. (inr. a) (p .fst), p .snd))) (F a .map (phi (cons. (inr. a) (p .fst), p .snd)))
        (refl (F a .map (phi (cons. (inr. a) (p .fst), p .snd)))))
      (preimage_path_equiv Y (F a) (phi (p .fst, p .snd .snd)) (phi (cons. (inr. a) (p .fst), p .snd)))

def fsc_commutes_letter_equiv (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  (phi : ReducedWord S → Y) (a : S)
  : Equiv ((r : ReducedWord S) → FscLetterCommutes S dec Y F phi a r)
      (Product ((p : ReducedEdgeAt S (inl. a)) → FscEdgeStep S Y F phi (inl. a, p))
        ((p : ReducedEdgeAt S (inr. a)) → FscEdgeStep S Y F phi (inr. a, p)))
  ≔ let E ≔ Sum (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)) in
    let C ≔ FscLetterCommutes S dec Y F phi a in
    let sp ≔ fsc_letter_split_equiv S dec a in
    compose_equiv ((r : ReducedWord S) → C r) ((t : E) → C (sp .map t))
      (Product ((p : ReducedEdgeAt S (inl. a)) → FscEdgeStep S Y F phi (inl. a, p))
        ((p : ReducedEdgeAt S (inr. a)) → FscEdgeStep S Y F phi (inr. a, p)))
      (fsc_pi_base_change E (ReducedWord S) sp C)
      (compose_equiv ((t : E) → C (sp .map t))
        (Product ((p : ReducedEdgeAt S (inl. a)) → C (p .fst, p .snd .snd))
          ((p : ReducedEdgeAt S (inr. a)) → C (cons. (inr. a) (p .fst), p .snd)))
        (Product ((p : ReducedEdgeAt S (inl. a)) → FscEdgeStep S Y F phi (inl. a, p))
          ((p : ReducedEdgeAt S (inr. a)) → FscEdgeStep S Y F phi (inr. a, p)))
        (fsc_sum_pi_equiv (ReducedEdgeAt S (inl. a)) (ReducedEdgeAt S (inr. a)) (t ↦ C (sp .map t)))
        (product_equiv ((p : ReducedEdgeAt S (inl. a)) → C (p .fst, p .snd .snd))
          ((p : ReducedEdgeAt S (inr. a)) → C (cons. (inr. a) (p .fst), p .snd))
          ((p : ReducedEdgeAt S (inl. a)) → FscEdgeStep S Y F phi (inl. a, p))
          ((p : ReducedEdgeAt S (inr. a)) → FscEdgeStep S Y F phi (inr. a, p))
          (pi_family_equiv (ReducedEdgeAt S (inl. a)) (p ↦ C (p .fst, p .snd .snd)) (p ↦ FscEdgeStep S Y F phi (inl. a, p))
            (fsc_commutes_left_equiv S dec Y F phi a))
          (pi_family_equiv (ReducedEdgeAt S (inr. a)) (p ↦ C (cons. (inr. a) (p .fst), p .snd))
            (p ↦ FscEdgeStep S Y F phi (inr. a, p))
            (fsc_commutes_right_equiv S dec Y F phi a))))

{` The equivariance data of φ is equivalent to its edge steps. `}
def fsc_commutes_steps_equiv (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  (phi : ReducedWord S → Y)
  : Equiv (SSetCommutes S (ReducedWord S) Y (reduced_word_act S dec) F phi) (ReducedEdgeSteps S Y F phi)
  ≔ let P ≔ ((x ↦ (p : ReducedEdgeAt S x) → FscEdgeStep S Y F phi (x, p)) : SignedLetter S → Type) in
    compose_equiv (SSetCommutes S (ReducedWord S) Y (reduced_word_act S dec) F phi)
      ((a : S) → Product (P (inl. a)) (P (inr. a))) (ReducedEdgeSteps S Y F phi)
      (pi_family_equiv S (a ↦ (r : ReducedWord S) → FscLetterCommutes S dec Y F phi a r)
        (a ↦ Product (P (inl. a)) (P (inr. a))) (fsc_commutes_letter_equiv S dec Y F phi))
      (compose_equiv ((a : S) → Product (P (inl. a)) (P (inr. a))) ((x : SignedLetter S) → P x)
        (ReducedEdgeSteps S Y F phi)
        (fsc_signed_pi_equiv S P)
        (fsc_edge_curry_equiv S (FscEdgeStep S Y F phi)))

{` Freeness of reduced words, for every target type, by evaluation at ε. `}
def reduced_word_sset_maps_equiv (S : Type) (dec : DecidableEquality S) (Y : Type) (F : S → Equiv Y Y)
  : Equiv (SSetMaps S (ReducedWord S) Y (reduced_word_act S dec) F) Y
  ≔ compose_equiv (SSetMaps S (ReducedWord S) Y (reduced_word_act S dec) F) (ReducedStepMaps S Y F) Y
      (family_equiv (ReducedWord S → Y) (SSetCommutes S (ReducedWord S) Y (reduced_word_act S dec) F)
        (ReducedEdgeSteps S Y F) (fsc_commutes_steps_equiv S dec Y F))
      (fsc_step_maps_equiv S Y F)

def reduced_words_free (S : Type) (dec : DecidableEquality S)
  : SSetIsFree S (ReducedWord S) (reduced_word_act S dec) (reduced_word_empty S)
  ≔ Y F ↦ reduced_word_sset_maps_equiv S dec Y F .equiv

def reduced_word_free_sset (S : Type) (dec : DecidableEquality S) : FreeSSet S
  ≔ (ReducedWord S, reduced_word_act S dec, reduced_word_empty S, reduced_words_free S dec)
