{` Blind statements for chapter 10 (fingp.tex), section "Lagrange's theorem, counting version". `}
export "01-finite-groups"
export "../../../src/901-kernels-cokernels-images"

{` G/H for a subgroup i : Hom(H, G): the underlying set of the G-set coker i (subgroups.tex: G/H ≔ coker i_H,
   whose value at sh_G is ‖Σ_{x:BH} sh_G = Bi(x)‖_0; the proof of lem:Lagrangeascounting calls the same set
   the orbits of i^*G, Σ_{x:BH} (sh_G = Bi x), which is a set for a monomorphism). `}
def BlindCosets (G : Group) (m : GroupMonos G) : Type ≔ gset_underlying G (cokernel (m .fst) G (m .snd .fst))

{` "H is a subgroup of K" for subgroups (H, i), (K, j) of G: i factors through j. `}
def BlindMonoLe (G : Group) (m m' : GroupMonos G) : Type
  ≔ Σ (GroupHom (m .fst) (m' .fst))
      (k ↦ Id (GroupHom (m .fst) G) (group_hom_compose (m .fst) (m' .fst) G k (m' .snd .fst)) (m .snd .fst))

def BlindSubgroupLe (G : Group) (S T : Subgroups G) : Type ≔ BlindMonoLe G (subgroup_to_mono G S) (subgroup_to_mono G T)

{` The full subgroup G of G, as the image of the identity. `}
def blind_full_subgroup (G : Group) : Subgroups G ≔ image_subgroup G G (group_hom_id G)

{` lem:Lagrangeascounting (1). For a subgroup i : Hom(H, G) of a finite group G, G/H and H are finite and
   |G| = |G/H| · |H|. `}
def blind_lagrangeascounting : Type
  ≔ (G : Group) (hG : BlindIsFiniteGroup G) (m : GroupMonos G)
    → Σ (IsFinite (BlindCosets G m)) (hQ ↦ Σ (BlindIsFiniteGroup (m .fst)) (hH ↦
        Id Nat (blind_group_order G hG) (mul (cardinality (BlindCosets G m) hQ) (blind_group_order (m .fst) hH))))

{` lem:Lagrangeascounting (2). If |H| = |G|, then H = G as subgroups of G. `}
def blind_lagrangeascounting_full : Type
  ≔ (G : Group) (hG : BlindIsFiniteGroup G) (m : GroupMonos G) (hH : BlindIsFiniteGroup (m .fst))
    → Id Nat (blind_group_order (m .fst) hH) (blind_group_order G hG)
    → Id (Subgroups G) (mono_to_subgroup G m) (blind_full_subgroup G)

{` cor:cyclicgroupsaresimple. For p prime, C_p has no subgroup that is both non-trivial and proper
   (trivial / proper as in def:triv-proper-Mono). `}
def blind_cyclicgroupsaresimple : Type
  ≔ (p : Nat) → BlindIsPrime p
    → Not (Σ (Subgroups (cyclic_group p))
             (S ↦ Product (Not (IsTrivialSubgroup (cyclic_group p) S)) (IsProperSubgroup (cyclic_group p) S)))

{` cor:whatSylow2needs. f : Hom(G, G') surjective (on symmetries) with kernel N, H a subgroup of G; if H and G'
   are finite with coprime orders, then H is a subgroup of N. `}
def blind_whatsylow2needs : Type
  ≔ (G G' : Group) (f : GroupHom G G') (surj : Surjective (USym G) (USym G') (usym_hom G G' f))
    (m : GroupMonos G) (hH : BlindIsFiniteGroup (m .fst)) (hG' : BlindIsFiniteGroup G')
    → BlindCoprime (blind_group_order (m .fst) hH) (blind_group_order G' hG')
    → BlindMonoLe G m (kernel G G' f)
