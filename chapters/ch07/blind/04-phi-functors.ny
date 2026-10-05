export "03-torsors"

{` Blind statements, chapter 7, subsection "The left and right adjoint of restriction, abstractly". `}

{` def:phi^*: φ^*(S, ψ) ≔ (S, ψ ∘ φ). `}
def blind_phi_star (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (Y : BlindAbsGSet H) : BlindAbsGSet G
  ≔ (Y .fst, blind_abshom_compose G H (blind_perm_group (Y .fst)) phi (Y .snd))

{` def:phi_!. The relation (t,x) ~ (u,y) ≔ ∃ (g : S) (t φ(g) = u) × (x = g ·_X y) on T × X. `}
def BlindTX (H : BlindAbsGroup) (G : BlindAbsGroup) (X : BlindAbsGSet G) : Type ≔ Product (H .carrier) (X .fst .fst)

def blind_phi_rel_witness (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) (a b : BlindTX H G X) : Type
  ≔ Σ (G .carrier) (g ↦
      Product (Id (H .carrier) (H .mul (a .fst) (phi .fst g)) (b .fst))
        (Id (X .fst .fst) (a .snd) (blind_gset_act G X g (b .snd))))

def blind_phi_rel (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) (a b : BlindTX H G X) : Type
  ≔ Mere (blind_phi_rel_witness G H phi X a b)

def blind_phi_eqrel (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (r : (a : BlindTX H G X) → blind_phi_rel G H phi X a a)
  (s : (a b : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b a)
  (t : (a b c : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b c → blind_phi_rel G H phi X a c)
  : EquivalenceRelation (BlindTX H G X)
  ≔ ((a b ↦ (blind_phi_rel G H phi X a b, mere_isprop (blind_phi_rel_witness G H phi X a b))), r, s, t)

{` The permutation of T × X/~ induced by (t,x) ↦ (ht, x), given that it respects ~. `}
def blind_phi_induced (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (E : EquivalenceRelation (BlindTX H G X))
  (resp : (h : H .carrier) (a b : BlindTX H G X) → Rel (BlindTX H G X) E a b
    → Rel (BlindTX H G X) E (H .mul h (a .fst), a .snd) (H .mul h (b .fst), b .snd))
  (h : H .carrier) : Quotient (BlindTX H G X) E → Quotient (BlindTX H G X) E
  ≔ quotient_rec (BlindTX H G X) (Quotient (BlindTX H G X) E) E (quotient_set (BlindTX H G X) E)
      (a ↦ quotient_class (BlindTX H G X) E (H .mul h (a .fst), a .snd))
      (a b r ↦ quotient_encode (BlindTX H G X) E (H .mul h (a .fst), a .snd) (H .mul h (b .fst), b .snd) (resp h a b r))

{` xca:phi_!-OK: (1) ~ is an equivalence relation; (2) (t,x) ↦ (ht,x)
   respects ~; (3) these maps induce an abstract homomorphism
   H → abstr(Σ_{T×X/~}) (whose permutation of h acts as the induced map). `}
def BlindPhiShriekOK (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) : Type ≔ sig (
  rel_refl : (a : BlindTX H G X) → blind_phi_rel G H phi X a a,
  rel_sym : (a b : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b a,
  rel_trans : (a b c : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b c
    → blind_phi_rel G H phi X a c,
  respects : (h : H .carrier) (a b : BlindTX H G X) → blind_phi_rel G H phi X a b
    → blind_phi_rel G H phi X (H .mul h (a .fst), a .snd) (H .mul h (b .fst), b .snd),
  action : BlindAbsHom H (blind_perm_group
    (Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans),
     quotient_set (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans))),
  action_induced : (h : H .carrier) (q : Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans))
    → Id (Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans))
        (permutation_action
          (Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans),
           quotient_set (BlindTX H G X) (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans))
          (action .fst h) q)
        (blind_phi_induced G H phi X (blind_phi_eqrel G H phi X rel_refl rel_sym rel_trans) respects h q))

def blind_xca_phi_shriek_ok : Type
  ≔ (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X

def blind_phi_quotient (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (ok : BlindPhiShriekOK G H phi X) : SetTypes
  ≔ (Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X (ok .rel_refl) (ok .rel_sym) (ok .rel_trans)),
     quotient_set (BlindTX H G X) (blind_phi_eqrel G H phi X (ok .rel_refl) (ok .rel_sym) (ok .rel_trans)))

def blind_phi_class (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (ok : BlindPhiShriekOK G H phi X) (t : H .carrier) (x : X .fst .fst) : blind_phi_quotient G H phi X ok .fst
  ≔ quotient_class (BlindTX H G X) (blind_phi_eqrel G H phi X (ok .rel_refl) (ok .rel_sym) (ok .rel_trans)) (t, x)

{` φ_!(X) ≔ P_H ×_G X, defined using the data of xca:phi_!-OK. `}
def blind_phi_shriek (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (ok : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X)
  (X : BlindAbsGSet G) : BlindAbsGSet H
  ≔ (blind_phi_quotient G H phi X (ok X), ok X .action)

{` def:Hom-absG. `}
def BlindAbsGSetHom (G : BlindAbsGroup) (X Y : BlindAbsGSet G) : Type
  ≔ Σ (X .fst .fst → Y .fst .fst) (f ↦
      (s : G .carrier) → Id (X .fst .fst → Y .fst .fst) (x ↦ f (blind_gset_act G X s x)) (x ↦ blind_gset_act G Y s (f x)))

{` xca:phi_!-|phi^*. `}
def blind_xca_phi_shriek_adj : Type
  ≔ (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (ok : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X)
    (X : BlindAbsGSet G) (Y : BlindAbsGSet H)
    → BookEquiv (BlindAbsGSetHom H (blind_phi_shriek G H phi ok X) Y) (BlindAbsGSetHom G X (blind_phi_star G H phi Y))

{` def:phi_*: φ_*(X) ≔ {b : T → X | ∀ s, b ∘ (- φ(s⁻¹)) = (s ·_X -) ∘ b}.
   The action is printed as h · b ≔ b(h⁻¹ ·_X -), which is ill-typed (h : T
   and b : T → X); it is read as b(h⁻¹ · -) with the multiplication of H.
   The closure of the subset under this action and the action laws are
   claimed implicitly by the definition; they are the parameter `ok`. `}
def BlindPhiLowerSet (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) : Type
  ≔ Σ (H .carrier → X .fst .fst) (b ↦
      (s : G .carrier) → Id (H .carrier → X .fst .fst) (t ↦ b (H .mul t (phi .fst (G .inv s))))
        (t ↦ blind_gset_act G X s (b t)))

def blind_phi_lower_set_set (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  : isSet (BlindPhiLowerSet G H phi X)
  ≔ sigma_set (H .carrier → X .fst .fst)
      (b ↦ (s : G .carrier) → Id (H .carrier → X .fst .fst) (t ↦ b (H .mul t (phi .fst (G .inv s))))
        (t ↦ blind_gset_act G X s (b t)))
      (pi_set (H .carrier) (_ ↦ X .fst .fst) (_ ↦ X .fst .snd))
      (b ↦ prop_is_set ((s : G .carrier) → Id (H .carrier → X .fst .fst) (t ↦ b (H .mul t (phi .fst (G .inv s))))
        (t ↦ blind_gset_act G X s (b t)))
        (pi_prop (G .carrier)
          (s ↦ Id (H .carrier → X .fst .fst) (t ↦ b (H .mul t (phi .fst (G .inv s)))) (t ↦ blind_gset_act G X s (b t)))
          (s ↦ pi_set (H .carrier) (_ ↦ X .fst .fst) (_ ↦ X .fst .snd)
            (t ↦ b (H .mul t (phi .fst (G .inv s)))) (t ↦ blind_gset_act G X s (b t)))))

def blind_phi_lower_raw_act (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (h : H .carrier) (b : H .carrier → X .fst .fst) : H .carrier → X .fst .fst
  ≔ t ↦ b (H .mul (H .inv h) t)

def BlindPhiLowerOK (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) : Type ≔ sig (
  closed : (h : H .carrier) (b : BlindPhiLowerSet G H phi X) (s : G .carrier)
    → Id (H .carrier → X .fst .fst)
        (t ↦ blind_phi_lower_raw_act G H phi X h (b .fst) (H .mul t (phi .fst (G .inv s))))
        (t ↦ blind_gset_act G X s (blind_phi_lower_raw_act G H phi X h (b .fst) t)),
  act_mul : (h h' : H .carrier) (b : BlindPhiLowerSet G H phi X)
    → Id (BlindPhiLowerSet G H phi X)
        (blind_phi_lower_raw_act G H phi X (H .mul h h') (b .fst), closed (H .mul h h') b)
        (blind_phi_lower_raw_act G H phi X h (blind_phi_lower_raw_act G H phi X h' (b .fst)),
         closed h (blind_phi_lower_raw_act G H phi X h' (b .fst), closed h' b)),
  act_unit : (b : BlindPhiLowerSet G H phi X)
    → Id (BlindPhiLowerSet G H phi X) (blind_phi_lower_raw_act G H phi X (H .unit) (b .fst), closed (H .unit) b) b)

def blind_def_phi_lower_ok : Type
  ≔ (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) → BlindPhiLowerOK G H phi X

def blind_phi_lower (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (ok : (X : BlindAbsGSet G) → BlindPhiLowerOK G H phi X)
  (X : BlindAbsGSet G) : BlindAbsGSet H
  ≔ blind_gset_of_action H (BlindPhiLowerSet G H phi X, blind_phi_lower_set_set G H phi X)
      (h b ↦ (blind_phi_lower_raw_act G H phi X h (b .fst), ok X .closed h b))
      (ok X .act_mul) (ok X .act_unit)

{` xca:phi^*-|phi_*. `}
def blind_xca_phi_lower_adj : Type
  ≔ (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (ok : (X : BlindAbsGSet G) → BlindPhiLowerOK G H phi X)
    (X : BlindAbsGSet G) (Y : BlindAbsGSet H)
    → BookEquiv (BlindAbsGSetHom G (blind_phi_star G H phi Y) X) (BlindAbsGSetHom H Y (blind_phi_lower G H phi ok X))
