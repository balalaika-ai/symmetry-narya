export "03-cauchy"
export "bridge-01-finite-groups"
export "../../../src/1005-cauchy-theorem"
export "../../../src/1025-p-group-center"
export "../../../src/1038-order-p-squared-groups"

{` Bridges for fingp.tex, section "Cauchy's theorem": lem:fixedptsize,
   thm:cauchys, lem:nontrivcenter, cor:orderpsquaredgroups. The blind X^G is
   our InvariantMaps (refl); the blind center Π_z (z = z) receives our central
   symmetries through chapter 12's central_extension (whose value at sh_G is
   the given symmetry). `}

def bridge_def_fixed_points (G : Group) (X : GSet G) : Id Type (BlindFixedPoints G X) (InvariantMaps G X)
  ≔ refl (InvariantMaps G X)

def bridge_def_is_cyclic (G : Group) : Id Type (Not (BlindIsCyclic G)) (NotCyclicGroup G) ≔ refl (NotCyclicGroup G)

def bridge_order_power (p n : Nat) (G : Group) (hG : BlindHasOrder G (blind_pow p n))
  : Id Nat (group_card G (hG .fst)) (nat_power p n)
  ≔ concat Nat (group_card G (hG .fst)) (blind_pow p n) (nat_power p n) (hG .snd) (bridge_def_pow p n)

{` lem:fixedptsize. `}
def bridge_fixedptsize : blind_fixedptsize
  ≔ p hp n G hG X ne hX hd ↦
    fixed_point_size p hp (suc. n) star. G (hG .fst) (bridge_order_power p (suc. n) G hG) X ne hX hd

{` thm:cauchys. `}
def bridge_cauchys : blind_cauchys
  ≔ p hp G hG hd ↦ match p [
  | zero. ↦ match hp .fst []
  | suc. b ↦ cauchy_theorem b hp G hG hd ]

{` lem:nontrivcenter. A central symmetry g ≠ e extends to c : Π_z (z = z)
   with c(sh_G) = g, so c differs from z ↦ refl z. `}
def bridge_center_element (G : Group) (g : USym G) (hg : CentralSymmetry G g) (ne : Not (Id (USym G) g (usym_unit G)))
  : Σ (BlindCenter G) (c ↦ Not (Id (BlindCenter G) c (z ↦ refl z)))
  ≔ (central_extension G g hg, e ↦
      ne (concat (USym G) g (central_extension G g hg (shape G)) (usym_unit G)
            (inverse (USym G) (central_extension G g hg (shape G)) g (central_extension_base G g hg))
            (refl ((c ↦ c (shape G)) : BlindCenter G → USym G) e)))

def bridge_nontrivcenter_element : blind_nontrivcenter_element
  ≔ p hp n G hG ↦
    let T ≔ Σ (BlindCenter G) (c ↦ Not (Id (BlindCenter G) c (z ↦ refl z))) in
    mere_rec (Σ (USym G) (g ↦ Product (CentralSymmetry G g) (Not (Id (USym G) g (usym_unit G))))) (Mere T) (mere_isprop T)
      (u ↦ mere T (bridge_center_element G (u .fst) (u .snd .fst) (u .snd .snd)))
      (p_group_center_nontrivial_element p hp (suc. n) star. G (hG .fst) (bridge_order_power p (suc. n) G hG))

def bridge_nontrivcenter : blind_nontrivcenter
  ≔ p hp n G hG k ↦
    mere_rec (Σ (BlindCenter G) (c ↦ Not (Id (BlindCenter G) c (z ↦ refl z)))) Empty empty_prop
      (u ↦ u .snd (concat (BlindCenter G) (u .fst) (k .center) (z ↦ refl z)
                    (inverse (BlindCenter G) (k .center) (u .fst) (k .contract (u .fst))) (k .contract (z ↦ refl z))))
      (bridge_nontrivcenter_element p hp n G hG)

{` cor:orderpsquaredgroups. `}
def bridge_orderpsquaredgroups : blind_orderpsquaredgroups
  ≔ p hp G hG nc ↦ match p [
  | zero. ↦ match hp .fst []
  | suc. b ↦ order_p_squared_noncyclic b hp G (hG .fst) (bridge_order_power (suc. b) 2 G hG) nc ]
