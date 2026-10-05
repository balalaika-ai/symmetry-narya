export "741-induction-restriction-adjunction"
export "721-mere-inverses"

{` Chapter 7 (absgroup.tex), sec:phi-functors: coinduction φ_* (def:phi_*)
   along an abstract homomorphism φ : G → H (underlying sets S and T) and
   the adjunction φ^* ⊣ φ_* (xca:phi^*-|phi_*).

   φ_*(X) is the subset {b : T → X | Π_{s:S} b ∘ (- φ(s⁻¹)) = (s ·_X -) ∘ b}
   of T → X (equations of functions, as printed). The action is
   h · b ≔ b(h⁻¹ -), i.e. t ↦ b(h⁻¹ t) with h⁻¹ t multiplied in T. The
   printed formula "b(h⁻¹ ·_X -)" is ill-typed (h⁻¹ : T does not act on X);
   the text just before def:phi_* says "a(h⁻¹ -)", which is what is used. `}

def CoinduceCondition (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (b : H .carrier → agset_carrier G X) : Type
  ≔ (s : G .carrier) → Id (H .carrier → agset_carrier G X)
      (t ↦ b (H .mul t (φ .fst (G .inv s)))) (t ↦ agset_act G X s (b t))

def coinduce_condition_prop (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (b : H .carrier → agset_carrier G X) : isProp (CoinduceCondition G H φ X b)
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    pi_prop (G .carrier)
      (s ↦ Id (T → A) (t ↦ b (H .mul t (φ .fst (G .inv s)))) (t ↦ agset_act G X s (b t)))
      (s ↦ pi_set T (_ ↦ A) (_ ↦ agset_carrier_set G X) (t ↦ b (H .mul t (φ .fst (G .inv s)))) (t ↦ agset_act G X s (b t)))

def AgsetCoinduceCarrier (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) : Type
  ≔ Σ (H .carrier → agset_carrier G X) (CoinduceCondition G H φ X)

def agset_coinduce_carrier_set (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  : isSet (AgsetCoinduceCarrier G H φ X)
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    sigma_set (T → A) (CoinduceCondition G H φ X) (pi_set T (_ ↦ A) (_ ↦ agset_carrier_set G X))
      (b ↦ prop_is_set (CoinduceCondition G H φ X b) (coinduce_condition_prop G H φ X b))

def agset_coinduce_path (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (b c : AgsetCoinduceCarrier G H φ X)
  (h : (t : H .carrier) → Id (agset_carrier G X) (b .fst t) (c .fst t))
  : Id (AgsetCoinduceCarrier G H φ X) b c
  ≔ subtype_equal (H .carrier → agset_carrier G X) (CoinduceCondition G H φ X) (coinduce_condition_prop G H φ X) b c
      (funext (H .carrier) (_ ↦ agset_carrier G X) (b .fst) (c .fst) h)

{` h · b ≔ b(h⁻¹ -) satisfies the condition again. `}
def agset_coinduce_act (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h : H .carrier)
  (b : AgsetCoinduceCarrier G H φ X) : AgsetCoinduceCarrier G H φ X
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in let ih ≔ H .inv h in
    (t ↦ b .fst (H .mul ih t),
     s ↦ let q ≔ φ .fst (G .inv s) in
       funext T (_ ↦ A) (t ↦ b .fst (H .mul ih (H .mul t q))) (t ↦ agset_act G X s (b .fst (H .mul ih t)))
         (t ↦ concat A (b .fst (H .mul ih (H .mul t q))) (b .fst (H .mul (H .mul ih t) q))
            (agset_act G X s (b .fst (H .mul ih t)))
            (refl (b .fst) (H .laws .assoc ih t q))
            (happly T (_ ↦ A) (t' ↦ b .fst (H .mul t' q)) (t' ↦ agset_act G X s (b .fst t')) (b .snd s) (H .mul ih t))))

def agset_coinduce_act_mul (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h h' : H .carrier)
  (b : AgsetCoinduceCarrier G H φ X)
  : Id (AgsetCoinduceCarrier G H φ X) (agset_coinduce_act G H φ X (H .mul h h') b)
      (agset_coinduce_act G H φ X h (agset_coinduce_act G H φ X h' b))
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    agset_coinduce_path G H φ X (agset_coinduce_act G H φ X (H .mul h h') b)
      (agset_coinduce_act G H φ X h (agset_coinduce_act G H φ X h' b))
      (t ↦ calc
         b .fst (H .mul (H .inv (H .mul h h')) t) = b .fst (H .mul (H .mul (H .inv h') (H .inv h)) t)
           by refl ((k ↦ b .fst (H .mul k t)) : T → A) (ag_inv_mul H h h')
         = b .fst (H .mul (H .inv h') (H .mul (H .inv h) t))
           by refl (b .fst) (inverse T (H .mul (H .inv h') (H .mul (H .inv h) t)) (H .mul (H .mul (H .inv h') (H .inv h)) t)
             (H .laws .assoc (H .inv h') (H .inv h) t)) ∎)

def agset_coinduce_act_unit (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (b : AgsetCoinduceCarrier G H φ X)
  : Id (AgsetCoinduceCarrier G H φ X) (agset_coinduce_act G H φ X (H .unit) b) b
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    agset_coinduce_path G H φ X (agset_coinduce_act G H φ X (H .unit) b) b
      (t ↦ concat A (b .fst (H .mul (H .inv (H .unit)) t)) (b .fst (H .mul (H .unit) t)) (b .fst t)
         (refl ((k ↦ b .fst (H .mul k t)) : T → A) (ag_inv_unit H))
         (refl (b .fst) (H .laws .unit_left t)))

{` def:phi_*: φ_*(X), an H-set. `}
def agset_coinduce (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) : AbstractGSet H
  ≔ agset_from_action H (AgsetCoinduceCarrier G H φ X, agset_coinduce_carrier_set G H φ X) (agset_coinduce_act G H φ X)
      (agset_coinduce_act_mul G H φ X) (agset_coinduce_act_unit G H φ X)

def agset_coinduce_act_value (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h t : H .carrier)
  (b : AgsetCoinduceCarrier G H φ X)
  : Id (agset_carrier G X) (agset_act H (agset_coinduce G H φ X) h b .fst t) (b .fst (H .mul (H .inv h) t))
  ≔ refl (b .fst (H .mul (H .inv h) t))

{` φ(s⁻¹)⁻¹ = φ(s). `}
def coinduce_inv_phi_inv (G H : AbstractGroup) (φ : AbstractHom G H) (s : G .carrier)
  : Id (H .carrier) (H .inv (φ .fst (G .inv s))) (φ .fst s)
  ≔ concat (H .carrier) (H .inv (φ .fst (G .inv s))) (H .inv (H .inv (φ .fst s))) (φ .fst s)
      (refl (H .inv) (abstract_hom_preserves_inv G H (φ .fst) (φ .snd) s))
      (ag_inv_inv H (φ .fst s))

{` Forward: f ↦ (y ↦ (t ↦ f(t⁻¹ · y))). `}
def restrict_coinduce_fwd_point (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (f : AbstractGSetHom G (agset_restrict G H φ Y) X) (y : agset_carrier H Y) : AgsetCoinduceCarrier G H φ X
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in let B ≔ agset_carrier H Y in
    let fe ≔ agset_hom_equivariant G (agset_restrict G H φ Y) X f in
    (t ↦ f .fst (agset_act H Y (H .inv t) y),
     s ↦ let q ≔ φ .fst (G .inv s) in
       funext T (_ ↦ A) (t ↦ f .fst (agset_act H Y (H .inv (H .mul t q)) y))
         (t ↦ agset_act G X s (f .fst (agset_act H Y (H .inv t) y)))
         (t ↦ calc
            f .fst (agset_act H Y (H .inv (H .mul t q)) y) = f .fst (agset_act H Y (H .mul (H .inv q) (H .inv t)) y)
              by refl ((k ↦ f .fst (agset_act H Y k y)) : T → A) (ag_inv_mul H t q)
            = f .fst (agset_act H Y (H .mul (φ .fst s) (H .inv t)) y)
              by refl ((k ↦ f .fst (agset_act H Y (H .mul k (H .inv t)) y)) : T → A) (coinduce_inv_phi_inv G H φ s)
            = f .fst (agset_act H Y (φ .fst s) (agset_act H Y (H .inv t) y))
              by refl (f .fst) (agset_act_mul H Y (φ .fst s) (H .inv t) y)
            = agset_act G X s (f .fst (agset_act H Y (H .inv t) y)) by fe s (agset_act H Y (H .inv t) y) ∎))

def restrict_coinduce_fwd (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (f : AbstractGSetHom G (agset_restrict G H φ Y) X) : AbstractGSetHom H Y (agset_coinduce G H φ X)
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    let F ≔ restrict_coinduce_fwd_point G H φ X Y f in
    agset_hom_mk H Y (agset_coinduce G H φ X) F
      (h y ↦ agset_coinduce_path G H φ X (F (agset_act H Y h y)) (agset_act H (agset_coinduce G H φ X) h (F y))
        (t ↦ calc
           f .fst (agset_act H Y (H .inv t) (agset_act H Y h y)) = f .fst (agset_act H Y (H .mul (H .inv t) h) y)
             by refl (f .fst) (inverse (agset_carrier H Y) (agset_act H Y (H .mul (H .inv t) h) y)
               (agset_act H Y (H .inv t) (agset_act H Y h y)) (agset_act_mul H Y (H .inv t) h y))
           = f .fst (agset_act H Y (H .mul (H .inv t) (H .inv (H .inv h))) y)
             by refl ((k ↦ f .fst (agset_act H Y (H .mul (H .inv t) k) y)) : T → A) (ag_inv_involution H h)
           = f .fst (agset_act H Y (H .inv (H .mul (H .inv h) t)) y)
             by refl ((k ↦ f .fst (agset_act H Y k y)) : T → A)
               (inverse T (H .inv (H .mul (H .inv h) t)) (H .mul (H .inv t) (H .inv (H .inv h))) (ag_inv_mul H (H .inv h) t)) ∎))

{` Backward: F ↦ (y ↦ F(y)(e)). `}
def restrict_coinduce_bwd (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (F : AbstractGSetHom H Y (agset_coinduce G H φ X)) : AbstractGSetHom G (agset_restrict G H φ Y) X
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in let C ≔ agset_coinduce G H φ X in
    let Fe ≔ agset_hom_equivariant H Y C F in
    agset_hom_mk G (agset_restrict G H φ Y) X (y ↦ F .fst y .fst (H .unit))
      (s y ↦ let q ≔ φ .fst (G .inv s) in
        calc
          F .fst (agset_act H Y (φ .fst s) y) .fst (H .unit) = agset_act H C (φ .fst s) (F .fst y) .fst (H .unit)
            by refl ((c ↦ c .fst (H .unit)) : AgsetCoinduceCarrier G H φ X → A) (Fe (φ .fst s) y)
          = F .fst y .fst (H .mul (H .unit) q)
            by refl (F .fst y .fst)
              (calc
                 H .mul (H .inv (φ .fst s)) (H .unit) = H .inv (φ .fst s) by H .laws .unit_right (H .inv (φ .fst s))
                 = q by inverse T q (H .inv (φ .fst s)) (abstract_hom_preserves_inv G H (φ .fst) (φ .snd) s)
                 = H .mul (H .unit) q by inverse T (H .mul (H .unit) q) q (H .laws .unit_left q) ∎)
          = agset_act G X s (F .fst y .fst (H .unit))
            by happly T (_ ↦ A) (t ↦ F .fst y .fst (H .mul t q)) (t ↦ agset_act G X s (F .fst y .fst t))
              (F .fst y .snd s) (H .unit) ∎)

{` xca:phi^*-|phi_*: Hom_G(φ^*Y, X) ≃ Hom_H(Y, φ_*X). `}
def restrict_coinduce_abstract_adjunction (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  : Equiv (AbstractGSetHom G (agset_restrict G H φ Y) X) (AbstractGSetHom H Y (agset_coinduce G H φ X))
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in let B ≔ agset_carrier H Y in
    let R ≔ agset_restrict G H φ Y in let C ≔ agset_coinduce G H φ X in
    let fwd ≔ restrict_coinduce_fwd G H φ X Y in let bwd ≔ restrict_coinduce_bwd G H φ X Y in
    quasi_inverse_equiv (AbstractGSetHom G R X) (AbstractGSetHom H Y C) fwd bwd
      (f ↦ agset_hom_path G R X (bwd (fwd f)) f
        (y ↦ concat A (f .fst (agset_act H Y (H .inv (H .unit)) y)) (f .fst (agset_act H Y (H .unit) y)) (f .fst y)
           (refl ((k ↦ f .fst (agset_act H Y k y)) : T → A) (ag_inv_unit H))
           (refl (f .fst) (agset_act_unit H Y y))))
      (F ↦ agset_hom_path H Y C (fwd (bwd F)) F
        (y ↦ agset_coinduce_path G H φ X (fwd (bwd F) .fst y) (F .fst y)
          (t ↦ calc
             F .fst (agset_act H Y (H .inv t) y) .fst (H .unit) = agset_act H C (H .inv t) (F .fst y) .fst (H .unit)
               by refl ((c ↦ c .fst (H .unit)) : AgsetCoinduceCarrier G H φ X → A)
                 (agset_hom_equivariant H Y C F (H .inv t) y)
             = F .fst y .fst (H .inv (H .inv t))
               by refl (F .fst y .fst) (H .laws .unit_right (H .inv (H .inv t)))
             = F .fst y .fst t by refl (F .fst y .fst) (ag_inv_inv H t) ∎)))

def restrict_coinduce_abstract_adjunction_map (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (Y : AbstractGSet H) (f : AbstractGSetHom G (agset_restrict G H φ Y) X) (y : agset_carrier H Y) (t : H .carrier)
  : Id (agset_carrier G X) (restrict_coinduce_abstract_adjunction G H φ X Y .map f .fst y .fst t)
      (f .fst (agset_act H Y (H .inv t) y))
  ≔ refl (f .fst (agset_act H Y (H .inv t) y))

{` Litmus on the integers (int_add_abstract_group, module 721) with
   φ = id and X the principal torsor: b = negation lies in φ_*(X)
   (b(t - s) = s + b(t)), and the action of 2 sends it to t ↦ -(t - 2),
   whose value at 5 is -3, by computation. `}
def int_coinduce_negation : AgsetCoinduceCarrier int_add_abstract_group int_add_abstract_group
    (abstract_hom_id int_add_abstract_group) (agset_principal int_add_abstract_group)
  ≔ let Z ≔ int_add_abstract_group in
    (t ↦ Z .inv t,
     s ↦ funext Int (_ ↦ Int) (t ↦ Z .inv (Z .mul t (Z .inv s))) (t ↦ Z .mul s (Z .inv t))
       (t ↦ concat Int (Z .inv (Z .mul t (Z .inv s))) (Z .mul (Z .inv (Z .inv s)) (Z .inv t)) (Z .mul s (Z .inv t))
          (ag_inv_mul Z t (Z .inv s))
          (refl ((k ↦ Z .mul k (Z .inv t)) : Int → Int) (ag_inv_inv Z s))))

def int_coinduce_action_litmus
  : Id Int (agset_act int_add_abstract_group
      (agset_coinduce int_add_abstract_group int_add_abstract_group (abstract_hom_id int_add_abstract_group)
        (agset_principal int_add_abstract_group))
      (pos. (suc. (suc. zero.))) int_coinduce_negation .fst (pos. (suc. (suc. (suc. (suc. (suc. zero.)))))))
      (neg. (suc. (suc. zero.)))
  ≔ refl (neg. (suc. (suc. zero.)))
