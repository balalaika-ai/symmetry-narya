export "69-orders-and-subgroups"

{` These are types of additional principles, not assumed inhabitants. `}
def ExcludedMiddle : Type ≔ (P : Type) → isProp P → Decidable P
def DoubleNegationElimination : Type ≔ (P : Type) → isProp P → Not (Not P) → P

def excluded_middle_prop : isProp ExcludedMiddle
  ≔ pi_prop Type (P ↦ isProp P → Decidable P)
      (P ↦ pi_prop (isProp P) (_ ↦ Decidable P) (hp ↦ decidability_prop P hp))
def double_negation_elimination_prop : isProp DoubleNegationElimination
  ≔ pi_prop Type (P ↦ isProp P → Not (Not P) → P)
      (P ↦ pi_prop (isProp P) (_ ↦ Not (Not P) → P) (hp ↦ pi_prop (Not (Not P)) (_ ↦ P) (_ ↦ hp)))

def double_negated_decidability (P : Type) : Not (Not (Decidable P))
  ≔ no ↦ no (inr. (p ↦ no (inl. p)))

def excluded_middle_implies_dne (lem : ExcludedMiddle) : DoubleNegationElimination
  ≔ P hp nn ↦ match lem P hp [ inl. p ↦ p | inr. no ↦ absurd P (nn no) ]
def dne_implies_excluded_middle (dne : DoubleNegationElimination) : ExcludedMiddle
  ≔ P hp ↦ dne (Decidable P) (decidability_prop P hp) (double_negated_decidability P)

def excluded_middle_dne_equiv : Equiv ExcludedMiddle DoubleNegationElimination
  ≔ iff_equiv ExcludedMiddle DoubleNegationElimination excluded_middle_prop double_negation_elimination_prop
      excluded_middle_implies_dne dne_implies_excluded_middle

{` xca:lem-prop uses exactly the map b ↦ (true = b). `}
def truth_proposition (b : Bool) : PropTypes ≔ (Id Bool true. b, bool_set true. b)

def truth_proposition_injective : PathReflecting Bool PropTypes truth_proposition
  ≔ x y p ↦ match x, y [
  | false., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool)
  | false., true. ↦ absurd (Id Bool false. true.) (bool_encode true. false. (p .fst .trl (refl (true. : Bool))))
  | true., false. ↦ absurd (Id Bool true. false.) (bool_encode true. false. (p .fst .trr (refl (true. : Bool)))) ]

def truth_proposition_decidable (b : Bool) : Decidable (truth_proposition b .fst)
  ≔ match b [ true. ↦ inl. (refl (true. : Bool)) | false. ↦ inr. (bool_encode true. false.) ]

def excluded_middle_truth_surjective (lem : ExcludedMiddle) : Surjective Bool PropTypes truth_proposition
  ≔ P ↦ match lem (P .fst) (P .snd) [
  | inl. p ↦ mere (BookFiber Bool PropTypes truth_proposition P)
      (true., proposition_extensionality P (truth_proposition true.) (_ ↦ refl (true. : Bool)) (_ ↦ p))
  | inr. no ↦ mere (BookFiber Bool PropTypes truth_proposition P)
      (false., proposition_extensionality P (truth_proposition false.)
        (p ↦ absurd (Id Bool true. false.) (no p)) (r ↦ absurd (P .fst) (bool_encode true. false. r))) ]

def excluded_middle_truth_equiv (lem : ExcludedMiddle) : Equiv Bool PropTypes
  ≔ set_bijection_equiv Bool PropTypes propositions_set truth_proposition truth_proposition_injective
      (excluded_middle_truth_surjective lem)

def truth_equiv_implies_excluded_middle (h : isEquiv Bool PropTypes truth_proposition) : ExcludedMiddle
  ≔ P hp ↦ let w ≔ h (P, hp) .center in
      transport Type Decidable (truth_proposition (w .fst) .fst) P (w .snd .fst) (truth_proposition_decidable (w .fst))

def excluded_middle_truth_criterion : Equiv ExcludedMiddle (isEquiv Bool PropTypes truth_proposition)
  ≔ iff_equiv ExcludedMiddle (isEquiv Bool PropTypes truth_proposition)
      excluded_middle_prop (isequiv_isprop Bool PropTypes truth_proposition)
      (lem ↦ excluded_middle_truth_equiv lem .equiv) truth_equiv_implies_excluded_middle
