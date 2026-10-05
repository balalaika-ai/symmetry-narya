export "bridge-05a-free"
export "bridge-04a-wedge"
export "../../../src/880-free-groups-iterated-wedges"

{` Bridges for congp.tex:937 (FG_{n ⊔ 1} ≃ FG_n ∨ Z and the iterated
   wedge of circles). Blind wedges become ours by bridge_wedge_signature
   (bridge-04a-wedge) with the same pointed type; a blind circle tower of
   height m is converted to one of our wedge towers of height m+1 by
   induction on m, transporting each chosen wedge along the identification
   of the previous stage (b05_tower). Our identifications of pointed types
   become BookPointedEquivs by pointed_path_to_equiv. `}

def bridge_xca_free_wedge_step : blind_xca_free_wedge_step
  ≔ n C F' F W ↦
    pointed_path_to_equiv (blind_free_pointed (Sum (Fin n) Unit, fin_set (suc. n)) F')
      (blind_wedge_pointed (blind_free_pointed (Fin n, fin_set n) F) (circle_pointed C) W)
      (free_succ_wedge_path n (b05_sig (Sum (Fin n) Unit, fin_set (suc. n)) F') (b05_sig (Fin n, fin_set n) F) C
        (bridge_wedge_signature (blind_free_pointed (Fin n, fin_set n) F) (circle_pointed C) W))

def b05_tower (C : CircleSignature) (m : Nat) (t : BlindCircleTower C m .fst)
  : Σ (WedgeTower C (suc. m)) (tau ↦ Id Pointed (BlindCircleTower C m .snd t) (wedge_tower_top C (suc. m) tau))
  ≔ match m [
  | zero. ↦ (star., refl (circle_pointed C))
  | suc. k ↦
    let A ≔ BlindCircleTower C k .snd (t .fst) in
    let r ≔ b05_tower C k (t .fst) in
    let A' ≔ wedge_tower_top C (suc. k) (r .fst) in
    let W ≔ bridge_wedge_signature A (circle_pointed C) (t .snd) in
    let W' ≔ transport Pointed (X ↦ WedgeSignature X (circle_pointed C)) A A' (r .snd) W in
    ((r .fst, W'), wedge_pointed_path_along A A' (circle_pointed C) (r .snd) W W') ]

def bridge_xca_free_iterated_wedge : blind_xca_free_iterated_wedge
  ≔ C m F t ↦
    let r ≔ b05_tower C m t in
    let B ≔ BlindCircleTower C m .snd t in
    let top ≔ wedge_tower_top C (suc. m) (r .fst) in
    let F0 ≔ b05_sig (Fin (suc. m), fin_set (suc. m)) F in
    pointed_path_to_equiv (blind_free_pointed (Fin (suc. m), fin_set (suc. m)) F) B
      (concat Pointed (free_pointed (Fin (suc. m)) F0) top B
        (free_group_wedge_tower C (suc. m) (r .fst) F0)
        (inverse Pointed B top (r .snd)))
