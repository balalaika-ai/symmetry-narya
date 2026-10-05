export "486-universe-not-groupoid"
export "700-monoids-and-group-laws"
export "223-constructed-circle"

{` Chapter 7 (absgroup.tex), rem:ee=e_coherence, the claim that without
   the set condition the two identifications e · e = e provided by the unit
   laws are "potentially different". (The set case, where they agree, is
   monoid_unit_coherence in module 720.)

   Counterexample: for a circle C (any CircleSignature, as in module 486;
   instantiated below at the constructed circle) let A ≔ C → C with
   e ≔ id and μ(f, g) ≔ f ∘ g. Both unit laws and associativity hold
   judgmentally; choose the witnesses ρ(g) ≔ refl_g for g ∘ id = g and
   λ(g) ≔ funext(x ↦ c(g x)) for id ∘ g = g, where c : Π(x : C) x = x is
   the central loop with c(base) = loop (circle_central_loop, module 486).
   At g ≔ e the two witnesses of e · e = e are refl_id and funext(c);
   evaluating at base gives refl_base and loop, and loop ≠ refl. So the
   unit laws, as data on a type that is not a set, do not determine a
   single identification e · e = e. `}

def circle_endo_unit_laws (C : CircleSignature)
  : UnitLaws (C .carrier → C .carrier) (identity (C .carrier)) (compose (C .carrier) (C .carrier) (C .carrier))
  ≔ g ↦ (refl g, funext (C .carrier) (_ ↦ C .carrier) g g (x ↦ circle_central_loop C (g x)))

def circle_endo_assoc (C : CircleSignature) : AssocLaw (C .carrier → C .carrier) (compose (C .carrier) (C .carrier) (C .carrier))
  ≔ g1 g2 g3 ↦ refl (compose (C .carrier) (C .carrier) (C .carrier) g1 (compose (C .carrier) (C .carrier) (C .carrier) g2 g3))

def circle_endo_unit_witnesses_differ (C : CircleSignature)
  (r : Id (Id (C .carrier → C .carrier) (identity (C .carrier)) (identity (C .carrier)))
    (circle_endo_unit_laws C (identity (C .carrier)) .fst) (circle_endo_unit_laws C (identity (C .carrier)) .snd))
  : Empty
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let c ≔ circle_central_loop C in
    let ev : Id (X → X) (identity X) (identity X) → Id X b b ≔ q ↦ happly X (_ ↦ X) (identity X) (identity X) q b in
    circle_loop_not_refl C
      (calc
        C .loop = c b by inverse (Id X b b) (c b) (C .loop) (circle_central_loop_base C)
        = ev (funext X (_ ↦ X) (identity X) (identity X) c) by funext_beta X (_ ↦ X) (identity X) (identity X) c b
        = ev (refl (identity X))
          by refl ev (inverse (Id (X → X) (identity X) (identity X)) (refl (identity X))
            (funext X (_ ↦ X) (identity X) (identity X) c) r)
        = refl b by refl (refl b) ∎)

{` The remark as an existence statement: a type A with e, μ, witnesses
   of the unit laws and the associativity law, whose two identifications
   e · e = e differ. `}
def NonCoherentUnitalStructure : Type
  ≔ Σ Type (A ↦ Σ A (e ↦ Σ (A → A → A) (mul ↦ Σ (UnitLaws A e mul) (u ↦
      Product (AssocLaw A mul) (Id (Id A (mul e e) e) (u e .fst) (u e .snd) → Empty)))))

def circle_endo_non_coherent (C : CircleSignature) : NonCoherentUnitalStructure
  ≔ (C .carrier → C .carrier,
     (identity (C .carrier),
      (compose (C .carrier) (C .carrier) (C .carrier),
       (circle_endo_unit_laws C, (circle_endo_assoc C, circle_endo_unit_witnesses_differ C)))))

def unit_coherence_counterexample : NonCoherentUnitalStructure ≔ circle_endo_non_coherent constructed_circle
