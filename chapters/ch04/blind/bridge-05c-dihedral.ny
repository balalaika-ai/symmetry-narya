export "bridge-05-bicycles"

{` Bridges for rem:inf-dihedral-frieze (line 2262) and the exercise
   at line 2298 (blind file 05-bicycles.ny). Items (i)-(iv) of the frieze
   remark hold for every normal bicycle (ours: bicycle_frieze_T/R_alt,
   bicycle_frieze_T/R_word). Item (v) and the exercise at 2298 are ours for
   infinite_dihedral_bicycle at the origin; they are transported to the
   blind D∞ along the pointed path (bridge_dihedral_path, origin), which is
   the identity on the carrier. `}

def BridgePointedBicycles : Type ≔ Σ Bicycles bicycle_carrier

def bridge_dihedral_pointed_path (w : blind_dihedral_is_bicycle)
  : Id BridgePointedBicycles (bridge_bic (blind_dihedral_bicycle w), dihedral_origin) (infinite_dihedral_bicycle, dihedral_origin)
  ≔ (bridge_dihedral_path w, bridge_dihedral_path w .fst .fst .liftr dihedral_origin)

def BridgeFriezeRPower (u : BridgePointedBicycles) : Type
  ≔ (hn : IsNormalBicycle (u .fst)) (n : Int) →
    Id (bicycle_carrier (u .fst))
      (bicycle_path_evaluate (u .fst) (u .fst) (bicycle_frieze_R (u .fst) hn (u .snd))
        (permutation_power (bicycle_carrier (u .fst)) (bicycle_a (u .fst)) n (u .snd)))
      (permutation_power (bicycle_carrier (u .fst)) (bicycle_a (u .fst)) n (bicycle_b (u .fst) .map (u .snd)))

def bridge_frieze_R_power_ours : BridgeFriezeRPower (infinite_dihedral_bicycle, dihedral_origin)
  ≔ hn n ↦ transport (IsNormalBicycle infinite_dihedral_bicycle)
      (h ↦ Id (Sum Int Int)
        (bicycle_path_evaluate infinite_dihedral_bicycle infinite_dihedral_bicycle
          (bicycle_frieze_R infinite_dihedral_bicycle h dihedral_origin)
          (permutation_power (Sum Int Int) dihedral_a_equiv n dihedral_origin))
        (permutation_power (Sum Int Int) dihedral_a_equiv n (dihedral_b_map dihedral_origin)))
      infinite_dihedral_bicycle_normal hn
      (is_normal_bicycle_prop infinite_dihedral_bicycle infinite_dihedral_bicycle_normal hn)
      (dihedral_frieze_R_power dihedral_origin n)

def bridge_rem_dihedral_frieze : blind_rem_dihedral_frieze
  ≔ w hn ↦
    let B ≔ blind_dihedral_bicycle w in
    let B' ≔ bridge_bic B in let hn' ≔ bridge_normal_to B hn in
    let X ≔ Sum Int Int in let a ≔ B .snd .fst in let b ≔ B .snd .snd .fst in
    let x0 : X ≔ inl. (pos. zero.) in
    let c ≔ blind_cbid B hn in let c' ≔ bicycle_cbid B' hn' in
    let L ≔ Id Bicycles B' B' in let LB ≔ Id BlindBicycles B B in
    let E ≔ refl bridge_bic in
    let ainv ≔ equiv_inverse_map X X a in let binv ≔ equiv_inverse_map X X b in
    let ev' : L → X → X ≔ p y ↦ bicycle_path_evaluate B' B' p y in
    let s ≔ blind_bsem B in let wm ≔ bicycle_word_map B' in
    let la : BlindZZList ≔ cons. (inl. blind_int_minus_one) nil. in let lb : BlindZZList ≔ cons. (inr. blind_int_minus_one) nil. in
    (equivalence_injective LB L (bridge_bicycle_paths B B) (c (a .map x0) x0) (c x0 (ainv x0))
       (concat L (E (c (a .map x0) x0)) (c' (a .map x0) x0) (E (c x0 (ainv x0))) (bridge_def_cbid B hn (a .map x0) x0)
         (concat L (c' (a .map x0) x0) (c' x0 (ainv x0)) (E (c x0 (ainv x0))) (bicycle_frieze_T_alt B' hn' x0)
           (inverse L (E (c x0 (ainv x0))) (c' x0 (ainv x0)) (bridge_def_cbid B hn x0 (ainv x0))))),
     (equivalence_injective LB L (bridge_bicycle_paths B B) (c (b .map x0) x0) (c x0 (binv x0))
        (concat L (E (c (b .map x0) x0)) (c' (b .map x0) x0) (E (c x0 (binv x0))) (bridge_def_cbid B hn (b .map x0) x0)
          (concat L (c' (b .map x0) x0) (c' x0 (binv x0)) (E (c x0 (binv x0))) (bicycle_frieze_R_alt B' hn' x0)
            (inverse L (E (c x0 (binv x0))) (c' x0 (binv x0)) (bridge_def_cbid B hn x0 (binv x0))))),
      (l ↦ concat X (ev' (E (c (a .map x0) x0)) (s l x0)) (ev' (c' (a .map x0) x0) (wm l x0))
          (s (append (Sum Int Int) l la) x0)
          (refl ev' (bridge_def_cbid B hn (a .map x0) x0) (bridge_sem X a b l x0))
          (concat X (ev' (c' (a .map x0) x0) (wm l x0)) (wm (append (Sum Int Int) l la) x0) (s (append (Sum Int Int) l la) x0)
            (bicycle_frieze_T_word B' hn' x0 l)
            (inverse X (s (append (Sum Int Int) l la) x0) (wm (append (Sum Int Int) l la) x0)
              (bridge_sem X a b (append (Sum Int Int) l la) x0))),
       (l ↦ concat X (ev' (E (c (b .map x0) x0)) (s l x0)) (ev' (c' (b .map x0) x0) (wm l x0))
           (s (append (Sum Int Int) l lb) x0)
           (refl ev' (bridge_def_cbid B hn (b .map x0) x0) (bridge_sem X a b l x0))
           (concat X (ev' (c' (b .map x0) x0) (wm l x0)) (wm (append (Sum Int Int) l lb) x0) (s (append (Sum Int Int) l lb) x0)
             (bicycle_frieze_R_word B' hn' x0 l)
             (inverse X (s (append (Sum Int Int) l lb) x0) (wm (append (Sum Int Int) l lb) x0)
               (bridge_sem X a b (append (Sum Int Int) l lb) x0))),
        n ↦ concat X (ev' (E (c (b .map x0) x0)) (permutation_power X a n x0))
              (ev' (c' (b .map x0) x0) (permutation_power X a n x0))
              (permutation_power X a n (b .map x0))
              (refl ((p ↦ ev' p (permutation_power X a n x0)) : L → X) (bridge_def_cbid B hn (b .map x0) x0))
              (transport BridgePointedBicycles BridgeFriezeRPower (infinite_dihedral_bicycle, dihedral_origin) (B', x0)
                (inverse BridgePointedBicycles (B', x0) (infinite_dihedral_bicycle, dihedral_origin) (bridge_dihedral_pointed_path w))
                bridge_frieze_R_power_ours hn' n)))))

{` Line 2298: (X, a, b) = (X, T, R). Ours is dihedral_frieze_identification
   for D∞ at the origin with its normality proof; it is transported to any
   normality proof (a proposition) and along the pointed path to the blind
   D∞, then the blind T, R (transport along the underlying path of the
   symmetry) are identified with ours via bridge_def_cbid. `}
def BridgeGeometric (u : BridgePointedBicycles) : Type
  ≔ (hn : IsNormalBicycle (u .fst)) →
    let T ≔ bicycle_paths_equiv (u .fst) (u .fst) .map (bicycle_frieze_T (u .fst) hn (u .snd)) .fst in
    let R ≔ bicycle_paths_equiv (u .fst) (u .fst) .map (bicycle_frieze_R (u .fst) hn (u .snd)) .fst in
    Σ (BicycleConnected (bicycle_carrier (u .fst)) T R) (h ↦ Id Bicycles (u .fst) (u .fst .fst, (T, (R, h))))

def bridge_geometric_ours : BridgeGeometric (infinite_dihedral_bicycle, dihedral_origin)
  ≔ hn ↦ transport (IsNormalBicycle infinite_dihedral_bicycle)
      (h ↦
        let T ≔ bicycle_paths_equiv infinite_dihedral_bicycle infinite_dihedral_bicycle
          .map (bicycle_frieze_T infinite_dihedral_bicycle h dihedral_origin) .fst in
        let R ≔ bicycle_paths_equiv infinite_dihedral_bicycle infinite_dihedral_bicycle
          .map (bicycle_frieze_R infinite_dihedral_bicycle h dihedral_origin) .fst in
        Σ (BicycleConnected (Sum Int Int) T R) (k ↦ Id Bicycles infinite_dihedral_bicycle ((Sum Int Int, dihedral_set), (T, (R, k)))))
      infinite_dihedral_bicycle_normal hn
      (is_normal_bicycle_prop infinite_dihedral_bicycle infinite_dihedral_bicycle_normal hn)
      (dihedral_frieze_bicycle .snd .snd .snd, dihedral_frieze_identification)

def bridge_xca_dihedral_geometric : blind_xca_dihedral_geometric
  ≔ w hn ↦
    let B ≔ blind_dihedral_bicycle w in
    let B' ≔ bridge_bic B in let hn' ≔ bridge_normal_to B hn in
    let X ≔ Sum Int Int in let a ≔ B .snd .fst in let b ≔ B .snd .snd .fst in
    let x0 : X ≔ inl. (pos. zero.) in
    let c ≔ blind_cbid B hn in let c' ≔ bicycle_cbid B' hn' in
    let L ≔ Id Bicycles B' B' in
    let EQ ≔ Equiv X X in
    let tr : Id BlindBicycles B B → EQ ≔ S ↦ transport_equiv X X (map_path BlindBicycles Type (u ↦ u .fst .fst) B B S) in
    let pe : L → EQ ≔ p ↦ bicycle_paths_equiv B' B' .map p .fst in
    let T ≔ tr (c (a .map x0) x0) in let R ≔ tr (c (b .map x0) x0) in
    let T' ≔ pe (c' (a .map x0) x0) in let R' ≔ pe (c' (b .map x0) x0) in
    let qT : Id EQ T' T
      ≔ concat EQ T' (pe (refl bridge_bic (c (a .map x0) x0))) T
          (refl pe (inverse L (refl bridge_bic (c (a .map x0) x0)) (c' (a .map x0) x0) (bridge_def_cbid B hn (a .map x0) x0)))
          (equiv_path X X (pe (refl bridge_bic (c (a .map x0) x0))) T (refl (T .map))) in
    let qR : Id EQ R' R
      ≔ concat EQ R' (pe (refl bridge_bic (c (b .map x0) x0))) R
          (refl pe (inverse L (refl bridge_bic (c (b .map x0) x0)) (c' (b .map x0) x0) (bridge_def_cbid B hn (b .map x0) x0)))
          (equiv_path X X (pe (refl bridge_bic (c (b .map x0) x0))) R (refl (R .map))) in
    let Fam : Product EQ EQ → Type
      ≔ tr' ↦ Σ (BicycleConnected X (tr' .fst) (tr' .snd)) (k ↦ Id Bicycles B' (B' .fst, (tr' .fst, (tr' .snd, k)))) in
    let g0 : Fam (T', R')
      ≔ transport BridgePointedBicycles BridgeGeometric (infinite_dihedral_bicycle, dihedral_origin) (B', x0)
          (inverse BridgePointedBicycles (B', x0) (infinite_dihedral_bicycle, dihedral_origin) (bridge_dihedral_pointed_path w))
          bridge_geometric_ours hn' in
    let g : Fam (T, R) ≔ transport (Product EQ EQ) Fam (T', R') (T, R) (qT, qR) g0 in
    let h ≔ bridge_str_from blind_zz_set T R (g .fst) in
    let target : BlindBicycles ≔ (blind_zz_set, (T, (R, h))) in
    (h, equivalence_injective BlindBicycles Bicycles bridge_def_bicycles B target
      (concat Bicycles B' (B' .fst, (T, (R, g .fst))) (bridge_bic target) (g .snd)
        (refl (B' .fst), (refl T, (refl R, bicycle_connected_prop X T R (g .fst) (bridge_bic target .snd .snd .snd))))))
