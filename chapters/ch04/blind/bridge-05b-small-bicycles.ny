export "bridge-05-bicycles"

{` Bridges for def:Dinfty-Q (Q₈) and the exercise at line 2303
   (hexagon and prism bicycles), blind file 05-bicycles.ny. The blind
   bicycles on Fin n are given by values (blind_fin_val, which numbers
   Fin n in the reverse order); the bicycle isomorphisms below were found
   by exhaustive search and are checked pointwise by refl:
   Q₈: ψ = (0 5 2 7 4 1 6 3) on depths (an involution); hexagon: the
   identity; prism: depth d ↦ inl d (d < 3), inr (d − 3). `}

def bridge_q8_psi : Fin blind_eight → Fin blind_eight ≔ [
  | inr. u ↦ match u [ star. ↦ (inr. star. : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_q8_psi_inv : Fin blind_eight → Fin blind_eight ≔ [
  | inr. u ↦ match u [ star. ↦ (inr. star. : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_q8_psi_rt (x : Fin blind_eight) : Id (Fin blind_eight) (bridge_q8_psi_inv (bridge_q8_psi x)) x ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_q8_psi_rt2 (x : Fin blind_eight) : Id (Fin blind_eight) (bridge_q8_psi (bridge_q8_psi_inv x)) x ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_q8_ca (x : Fin blind_eight) : Id (Fin blind_eight) (bridge_q8_psi (blind_quaternion_a x)) (quaternion_a_map (bridge_q8_psi x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inr. star. : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_q8_cb (x : Fin blind_eight) : Id (Fin blind_eight) (bridge_q8_psi (blind_quaternion_b x)) (quaternion_b_map (bridge_q8_psi x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin blind_eight) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_eight) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_eight) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ match u [ star. ↦ refl (inr. star. : Fin blind_eight) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))) ↦ match e [ ] ]

def bridge_hex_ca (x : Fin blind_six) : Id (Fin blind_six) (identity (Fin blind_six) (blind_hexagon_a x)) (hexagon_a_map (identity (Fin blind_six) x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_six) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inr. star. : Fin blind_six) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_six) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]

def bridge_hex_cb (x : Fin blind_six) : Id (Fin blind_six) (identity (Fin blind_six) (blind_hexagon_b x)) (hexagon_b_map (identity (Fin blind_six) x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_six) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_six) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_six) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inr. star. : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]

def bridge_prism_psi : Fin blind_six → Sum (Fin three) (Fin three) ≔ [
  | inr. u ↦ match u [ star. ↦ (inl. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inr. u) ↦ match u [ star. ↦ (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ (inr. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]

def bridge_prism_psi_inv : Sum (Fin three) (Fin three) → Fin blind_six ≔ [
  | inl. (inr. u) ↦ match u [ star. ↦ (inr. star. : Fin blind_six) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ (inl. (inr. star.) : Fin blind_six) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ (inl. (inl. (inr. star.)) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (e)))) ↦ match e [ ]
  | inr. (inr. u) ↦ match u [ star. ↦ (inl. (inl. (inl. (inr. star.))) : Fin blind_six) ]
  | inr. (inl. (inr. u)) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_six) ]
  | inr. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_six) ]
  | inr. (inl. (inl. (inl. (e)))) ↦ match e [ ] ]

def bridge_prism_psi_rt (x : Fin blind_six) : Id (Fin blind_six) (bridge_prism_psi_inv (bridge_prism_psi x)) x ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin blind_six) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin blind_six) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Fin blind_six) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin blind_six) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]

def bridge_prism_psi_rt2 (x : Sum (Fin three) (Fin three)) : Id (Sum (Fin three) (Fin three)) (bridge_prism_psi (bridge_prism_psi_inv x)) x ≔ match x [
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (e)))) ↦ match e [ ]
  | inr. (inr. u) ↦ match u [ star. ↦ refl (inr. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inr. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inr. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inr. (inl. (inl. (inl. (e)))) ↦ match e [ ] ]

def bridge_prism_ca (x : Fin blind_six) : Id (Sum (Fin three) (Fin three)) (bridge_prism_psi (blind_prism_a x)) (prism_a_map (bridge_prism_psi x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inr. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]

def bridge_prism_cb (x : Fin blind_six) : Id (Sum (Fin three) (Fin three)) (bridge_prism_psi (blind_prism_b x)) (prism_b_map (bridge_prism_psi x)) ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inr. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inr. u)) ↦ match u [ star. ↦ refl (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inr. u))) ↦ match u [ star. ↦ refl (inl. (inr. star.) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ match u [ star. ↦ refl (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ match u [ star. ↦ refl (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)) ]
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [ ] ]


def bridge_q8_psi_equiv : Equiv (Fin blind_eight) (Fin blind_eight)
  ≔ quasi_inverse_equiv (Fin blind_eight) (Fin blind_eight) bridge_q8_psi bridge_q8_psi_inv bridge_q8_psi_rt bridge_q8_psi_rt2

def bridge_q8_path (w : blind_quaternion_is_bicycle)
  : Id Bicycles (bridge_bic (blind_quaternion_bicycle w)) quaternion_bicycle
  ≔ bicycle_path_from_iso (bridge_bic (blind_quaternion_bicycle w)) quaternion_bicycle
      (bridge_q8_psi_equiv, (bridge_q8_ca, bridge_q8_cb))

def bridge_def_q8 (w : blind_quaternion_is_bicycle) : Id Group (bridge_g (blind_Q8 w)) quaternion_group
  ≔ bridge_bicycle_aut_path (blind_quaternion_bicycle w) quaternion_bicycle (bridge_q8_path w)

def bridge_hexagon_path (w : BlindBicycleOn (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b)
  : Id Bicycles (bridge_bic (blind_bicycle_of (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b w)) hexagon_bicycle
  ≔ bicycle_path_from_iso (bridge_bic (blind_bicycle_of (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b w)) hexagon_bicycle
      (identity_equiv (Fin blind_six), (bridge_hex_ca, bridge_hex_cb))

def bridge_prism_psi_equiv : Equiv (Fin blind_six) (Sum (Fin three) (Fin three))
  ≔ quasi_inverse_equiv (Fin blind_six) (Sum (Fin three) (Fin three)) bridge_prism_psi bridge_prism_psi_inv
      bridge_prism_psi_rt bridge_prism_psi_rt2

def bridge_prism_path (w : BlindBicycleOn (blind_bn_set blind_six) blind_prism_a blind_prism_b)
  : Id Bicycles (bridge_bic (blind_bicycle_of (blind_bn_set blind_six) blind_prism_a blind_prism_b w)) prism_bicycle
  ≔ bicycle_path_from_iso (bridge_bic (blind_bicycle_of (blind_bn_set blind_six) blind_prism_a blind_prism_b w)) prism_bicycle
      (bridge_prism_psi_equiv, (bridge_prism_ca, bridge_prism_cb))

def bridge_xca_hexagon_prism : blind_xca_hexagon_prism
  ≔ w1 w2 ↦
    let B1 ≔ blind_bicycle_of (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b w1 in
    let B2 ≔ blind_bicycle_of (blind_bn_set blind_six) blind_prism_a blind_prism_b w2 in
    let G1 ≔ blind_bicycle_aut B1 in let G2 ≔ blind_bicycle_aut B2 in
    let S3 ≔ blind_SG blind_three in
    let H ≔ bicycle_automorphism_group hexagon_bicycle in let P ≔ bicycle_automorphism_group prism_bicycle in
    let p1 ≔ bridge_bicycle_aut_path B1 hexagon_bicycle (bridge_hexagon_path w1) in
    let p2 ≔ bridge_bicycle_aut_path B2 prism_bicycle (bridge_prism_path w2) in
    let p3 : Id Group (bridge_g S3) (symmetric_group three) ≔ bridge_aut SetTypes sets_groupoid (standard_set three) in
    (equiv_inverse_map (BlindIso G1 G2) (GroupIso (bridge_g G1) (bridge_g G2)) (bridge_def_iso G1 G2)
       (group_path_iso_equiv (bridge_g G1) (bridge_g G2) .map
         (concat Group (bridge_g G1) P (bridge_g G2)
           (concat Group (bridge_g G1) H P p1 hexagon_prism_automorphism_path)
           (inverse Group (bridge_g G2) P p2))),
     equiv_inverse_map (BlindIso G1 S3) (GroupIso (bridge_g G1) (bridge_g S3)) (bridge_def_iso G1 S3)
       (group_path_iso_equiv (bridge_g G1) (bridge_g S3) .map
         (concat Group (bridge_g G1) (symmetric_group three) (bridge_g S3)
           (concat Group (bridge_g G1) H (symmetric_group three) p1 hexagon_automorphism_group_path)
           (inverse Group (bridge_g S3) (symmetric_group three) p3))))
