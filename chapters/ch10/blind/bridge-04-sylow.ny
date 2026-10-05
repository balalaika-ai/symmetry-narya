export "04-sylow"
export "bridge-01-finite-groups"
export "../../../src/1034-sylow-three"
export "../../../src/1036-sylow-one"
export "../../../src/1014-sylow-sigma-three"
export "../../../src/520-orbit-relations"

{` Bridges for fingp.tex, section "Sylow's Theorems": thm:sylow1,
   def:sylowsubgroup, lem:numberofconjofSylow, thm:sylow2, thm:sylow3.

   The blind p-Sylow predicate is logically equivalent to ours (the same
   data with blind_pow for nat_power), so the blind and our Syl_G^p are the
   same G-subset of Sub(G) (proposition extensionality pointwise). Blind
   conjugation is the action of the G-set Sub(G), which is our
   subgroup_conjugate (subgroups_gset_act, module 902); the blind orbit of P
   is our set of conjugates. Blind containment of subgroups is a
   factorization of the inclusion homomorphisms; ours (stabilizer
   containment) gives it through the map of G-sets x ↦ y. `}

def bridge_divides_pow (p n m : Nat) (d : NatDivides (blind_pow p n) m) : NatDivides (nat_power p n) m
  ≔ transport Nat (x ↦ NatDivides x m) (blind_pow p n) (nat_power p n) (bridge_def_pow p n) d

def bridge_divides_pow_back (p n m : Nat) (d : NatDivides (nat_power p n) m) : NatDivides (blind_pow p n) m
  ≔ transport Nat (x ↦ NatDivides x m) (nat_power p n) (blind_pow p n)
      (inverse Nat (blind_pow p n) (nat_power p n) (bridge_def_pow p n)) d

{` def:sylowsubgroup: the blind predicate and ours imply each other. `}
def bridge_def_sylow_to (G : Group) (p : Nat) (S : Subgroups G) (b : BlindIsSylow G p S) : IsSylowSubgroup p G S
  ≔ let n ≔ b .fst in
    let hG ≔ b .snd .fst .fst in
    let hS ≔ b .snd .snd .fst in
    (hG, (hS, (n,
      (concat Nat (group_card (subgroup_group G S) hS) (blind_pow p n) (nat_power p n) (b .snd .snd .snd) (bridge_def_pow p n),
       (bridge_divides_pow p n (group_card G hG) (b .snd .fst .snd .fst),
        d ↦ b .snd .fst .snd .snd (bridge_divides_pow_back p (suc. n) (group_card G hG) d))))))

def bridge_def_sylow_from (G : Group) (p : Nat) (S : Subgroups G) (s : IsSylowSubgroup p G S) : BlindIsSylow G p S
  ≔ let hG ≔ s .fst in
    let hS ≔ s .snd .fst in
    let n ≔ s .snd .snd .fst in
    (n,
     ((hG, (bridge_divides_pow_back p n (group_card G hG) (s .snd .snd .snd .snd .fst),
            d ↦ s .snd .snd .snd .snd .snd (bridge_divides_pow p (suc. n) (group_card G hG) d))),
      (hS, concat Nat (group_card (subgroup_group G S) hS) (nat_power p n) (blind_pow p n) (s .snd .snd .snd .fst)
             (inverse Nat (blind_pow p n) (nat_power p n) (bridge_def_pow p n)))))

def bridge_def_sylow_gsubset (G : Group) (p : Nat)
  : Id (GSubsets G (subgroups_gset G)) (blind_sylow_gsubset G p) (sylow_gsubset p G)
  ≔ funext (BG G .carrier) (z ↦ Subgroups (group_at G z) → PropTypes) (blind_sylow_gsubset G p) (sylow_gsubset p G)
      (z ↦ funext (Subgroups (group_at G z)) (_ ↦ PropTypes) (blind_sylow_gsubset G p z) (sylow_gsubset p G z)
        (S ↦ proposition_extensionality (blind_sylow_gsubset G p z S) (sylow_gsubset p G z S)
          (mere_rec (BlindIsSylow (group_at G z) p S) (IsSylowSubgroup p (group_at G z) S)
             (is_sylow_subgroup_prop p (group_at G z) S) (bridge_def_sylow_to (group_at G z) p S))
          (s ↦ mere (BlindIsSylow (group_at G z) p S) (bridge_def_sylow_from (group_at G z) p S s))))

def bridge_def_sylow_gset (G : Group) (p : Nat) : Id (GSet G) (blind_sylow_gset G p) (sylow_gset p G)
  ≔ refl (gsubset_gset G (subgroups_gset G)) (bridge_def_sylow_gsubset G p)

def bridge_def_sylow_set (G : Group) (p : Nat) : Equiv (BlindSylowSet G p) (SylowSubgroups p G)
  ≔ family_equiv (Subgroups G) (S ↦ Mere (BlindIsSylow G p S)) (IsSylowSubgroup p G)
      (S ↦ iff_equiv (Mere (BlindIsSylow G p S)) (IsSylowSubgroup p G S) (mere_isprop (BlindIsSylow G p S))
        (is_sylow_subgroup_prop p G S)
        (mere_rec (BlindIsSylow G p S) (IsSylowSubgroup p G S) (is_sylow_subgroup_prop p G S) (bridge_def_sylow_to G p S))
        (s ↦ mere (BlindIsSylow G p S) (bridge_def_sylow_from G p S s)))

{` Conjugation: the blind action is ours. `}
def bridge_def_conj (G : Group) (g : USym G) (S : Subgroups G)
  : Id (Subgroups G) (blind_conj_subgroup G g S) (subgroup_conjugate G g S)
  ≔ subgroups_gset_act G (shape G) (shape G) g S

def bridge_conjugate_to (G : Group) (S T : Subgroups G) (c : BlindConjugate G S T)
  : Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T))
  ≔ let R ≔ Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T) in
    mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (blind_conj_subgroup G g S) T)) (Mere R) (mere_isprop R)
      (u ↦ mere R (u .fst, concat (Subgroups G) (subgroup_conjugate G (u .fst) S) (blind_conj_subgroup G (u .fst) S) T
                     (inverse (Subgroups G) (blind_conj_subgroup G (u .fst) S) (subgroup_conjugate G (u .fst) S)
                       (bridge_def_conj G (u .fst) S)) (u .snd))) c

def bridge_conjugate_from (G : Group) (S T : Subgroups G) (c : Mere (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T)))
  : BlindConjugate G S T
  ≔ let R ≔ Σ (USym G) (g ↦ Id (Subgroups G) (blind_conj_subgroup G g S) T) in
    mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g S) T)) (Mere R) (mere_isprop R)
      (u ↦ mere R (u .fst, concat (Subgroups G) (blind_conj_subgroup G (u .fst) S) (subgroup_conjugate G (u .fst) S) T
                     (bridge_def_conj G (u .fst) S) (u .snd))) c

{` The blind orbit of P in Sub(G) is our set of conjugates of P. `}
def bridge_def_orbit_conjugates (G : Group) (P : Subgroups G)
  : Equiv (OrbitUnderlying G (subgroups_gset G) P) (SubgroupConjugates G P)
  ≔ let X ≔ subgroups_gset G in
    family_equiv (Subgroups G) (T ↦ Id (Orbits G X) (orbit_of_point G X P) (orbit_of_point G X T))
      (T ↦ Mere (Σ (gset_underlying G (P .gset)) (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
      (T ↦ iff_equiv (Id (Orbits G X) (orbit_of_point G X P) (orbit_of_point G X T))
        (Mere (Σ (gset_underlying G (P .gset)) (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
        (orbits_set G X (orbit_of_point G X P) (orbit_of_point G X T))
        (mere_isprop (Σ (gset_underlying G (P .gset)) (y ↦ Id (Subgroups G) (subgroup_at G P y) T)))
        (q ↦ subgroup_conjugates_orbit_iff G P T .snd
               (bridge_conjugate_to G P T (orbit_point_path_exists_equiv G X P T .map q)))
        (r ↦ equiv_inverse_map (Id (Orbits G X) (orbit_of_point G X P) (orbit_of_point G X T)) (OrbitRelation G X P T)
               (orbit_point_path_exists_equiv G X P T)
               (bridge_conjugate_from G P T (subgroup_conjugates_orbit_iff G P T .fst r))))

{` Stabilizer containment gives the blind containment (a factorization of
   the inclusion homomorphisms). `}
def bridge_le_hom (G : Group) (S T : Subgroups G) (c : SubgroupLe G S T)
  : GroupHom (subgroup_group G S) (subgroup_group G T)
  ≔ let f ≔ subgroup_fixed_gset_hom G S (T .gset) (T .point) c in
    let fp ≔ subgroup_fixed_gset_hom_point G S (T .gset) (T .point) c in
    mkhom (subgroup_group G S) (subgroup_group G T)
      (u ↦ (u .fst, f (u .fst) (u .snd)),
       (refl (shape G), inverse (gset_underlying G (T .gset)) (f (shape G) (S .point)) (T .point) fp))

def bridge_subgroup_le (G : Group) (S T : Subgroups G) (c : SubgroupLe G S T) : BlindSubgroupLe G S T
  ≔ let H ≔ subgroup_group G S in
    let B ≔ BG G .carrier in
    let k ≔ bridge_le_hom G S T c in
    let comp ≔ group_hom_compose H (subgroup_group G T) G k (subgroup_inclusion G T) in
    (k,
     equiv_inverse_map (Id (GroupHom H G) comp (subgroup_inclusion G S))
       (PointedHomotopy (BG H) (BG G) (hom_B H G comp) (hom_B H G (subgroup_inclusion G S)))
       (group_hom_path_equiv H G comp (subgroup_inclusion G S))
       (u ↦ refl (u .fst),
        calc
          concat B (shape G) (shape G) (shape G) (hom_point H G comp) (refl (shape G))
          = hom_point H G comp by concat_p1 B (shape G) (shape G) (hom_point H G comp)
          = refl (shape G) by concat_p1 B (shape G) (shape G) (refl (shape G)) ∎))

{` H ⊆ g · T gives g⁻¹ · H ⊆ T. `}
def bridge_le_conj_inv (G : Group) (g : USym G) (S T : Subgroups G) (c : SubgroupLe G S (subgroup_conjugate G g T))
  : SubgroupLe G (subgroup_conjugate G (usym_inv G g) S) T
  ≔ h r ↦
    let X ≔ S .gset in let Y ≔ T .gset in
    let U ≔ gset_underlying G X in let V ≔ gset_underlying G Y in
    let s ≔ S .point in let t ≔ T .point in
    let gi ≔ usym_inv G g in
    let k ≔ usym_mul G g (usym_mul G h gi) in
    let actk : (W : GSet G) (a : gset_underlying G W)
        → Id (gset_underlying G W) (gset_usym_act G W k a)
             (gset_usym_act G W g (gset_usym_act G W h (gset_usym_act G W gi a)))
      ≔ W a ↦ concat (gset_underlying G W) (gset_usym_act G W k a)
            (gset_usym_act G W g (gset_usym_act G W (usym_mul G h gi) a))
            (gset_usym_act G W g (gset_usym_act G W h (gset_usym_act G W gi a)))
            (gset_act_mul G W g (usym_mul G h gi) a)
            (map_path (gset_underlying G W) (gset_underlying G W) (gset_usym_act G W g)
              (gset_usym_act G W (usym_mul G h gi) a) (gset_usym_act G W h (gset_usym_act G W gi a))
              (gset_act_mul G W h gi a)) in
    let ks : Id U (gset_usym_act G X k s) s
      ≔ calc
          gset_usym_act G X k s
          = gset_usym_act G X g (gset_usym_act G X h (gset_usym_act G X gi s)) by actk X s
          = gset_usym_act G X g (gset_usym_act G X gi s)
            by map_path U U (gset_usym_act G X g) (gset_usym_act G X h (gset_usym_act G X gi s)) (gset_usym_act G X gi s) r
          = s by gset_act_inv_right G X g s ∎ in
    let kt : Id V (gset_usym_act G Y k (gset_usym_act G Y g t)) (gset_usym_act G Y g t) ≔ c k ks in
    let ght : Id V (gset_usym_act G Y g (gset_usym_act G Y h t)) (gset_usym_act G Y g t)
      ≔ calc
          gset_usym_act G Y g (gset_usym_act G Y h t)
          = gset_usym_act G Y g (gset_usym_act G Y h (gset_usym_act G Y gi (gset_usym_act G Y g t)))
            by map_path V V (u ↦ gset_usym_act G Y g (gset_usym_act G Y h u)) t
                 (gset_usym_act G Y gi (gset_usym_act G Y g t))
                 (inverse V (gset_usym_act G Y gi (gset_usym_act G Y g t)) t (gset_act_inv_left G Y g t))
          = gset_usym_act G Y k (gset_usym_act G Y g t)
            by inverse V (gset_usym_act G Y k (gset_usym_act G Y g t))
                 (gset_usym_act G Y g (gset_usym_act G Y h (gset_usym_act G Y gi (gset_usym_act G Y g t))))
                 (actk Y (gset_usym_act G Y g t))
          = gset_usym_act G Y g t by kt ∎ in
    calc
      gset_usym_act G Y h t
      = gset_usym_act G Y gi (gset_usym_act G Y g (gset_usym_act G Y h t))
        by inverse V (gset_usym_act G Y gi (gset_usym_act G Y g (gset_usym_act G Y h t))) (gset_usym_act G Y h t)
             (gset_act_inv_left G Y g (gset_usym_act G Y h t))
      = gset_usym_act G Y gi (gset_usym_act G Y g t)
        by map_path V V (gset_usym_act G Y gi) (gset_usym_act G Y g (gset_usym_act G Y h t)) (gset_usym_act G Y g t) ght
      = t by gset_act_inv_left G Y g t ∎

{` thm:sylow1. `}
def bridge_sylow1 : blind_sylow1
  ≔ p hp n G hG d ↦
    let R ≔ Σ (Subgroups G) (S ↦ BlindHasOrder (subgroup_group G S) (blind_pow p n)) in
    mere_rec (SubgroupOfOrder G (nat_power p n)) (Mere R) (mere_isprop R)
      (u ↦ mere R (u .fst, (u .snd .fst,
             concat Nat (group_card (subgroup_group G (u .fst)) (u .snd .fst)) (nat_power p n) (blind_pow p n) (u .snd .snd)
               (inverse Nat (blind_pow p n) (nat_power p n) (bridge_def_pow p n)))))
      (sylow_one p hp G hG n (bridge_divides_pow p n (group_card G hG) d))

{` lem:numberofconjofSylow. `}
def bridge_numberofconjofsylow : blind_numberofconjofsylow
  ≔ p hp G hG P sP ↦
    let s ≔ bridge_def_sylow_to G p P sP in
    let O ≔ OrbitUnderlying G (subgroups_gset G) P in
    let C ≔ SubgroupConjugates G P in
    let e ≔ bridge_def_orbit_conjugates G P in
    let hC ≔ subgroup_conjugates_finite G (sylow_group_finite p G P s) P (sylow_subgroup_finite p G P s) in
    let hO ≔ finite_of_equiv O C e hC in
    (hO, d ↦ sylow_conjugates_not_divisible p G P s
       (transport Nat (NatDivides p) (cardinality O hO) (cardinality C hC) (cardinality_equiv O C e hO hC) d))

{` thm:sylow2 (1). `}
def bridge_sylow2_conjugate : blind_sylow2_conjugate
  ≔ p hp G hG P Q sP sQ ↦
    bridge_conjugate_from G P Q
      (sylow_subgroups_conjugate p hp G P Q (bridge_def_sylow_to G p P sP) (bridge_def_sylow_to G p Q sQ))

def bridge_sylow2_transitive : blind_sylow2_transitive
  ≔ p hp G hG ↦
    transport (GSet G) (IsTransitive G) (sylow_gset p G) (blind_sylow_gset G p)
      (inverse (GSet G) (blind_sylow_gset G p) (sylow_gset p G) (bridge_def_sylow_gset G p))
      (sylow_gset_transitive p hp G hG)

{` thm:sylow2 (2). `}
def bridge_sylow2_subconjugate : blind_sylow2_subconjugate
  ≔ p hp G hG H s hH P sP ↦
    let R ≔ Σ (USym G) (g ↦ BlindSubgroupLe G (blind_conj_subgroup G g H) P) in
    mere_rec (Σ (USym G) (g ↦ SubgroupLe G H (subgroup_conjugate G g P))) (Mere R) (mere_isprop R)
      (u ↦
        let gi ≔ usym_inv G (u .fst) in
        mere R (gi,
          transport (Subgroups G) (S ↦ BlindSubgroupLe G S P) (subgroup_conjugate G gi H) (blind_conj_subgroup G gi H)
            (inverse (Subgroups G) (blind_conj_subgroup G gi H) (subgroup_conjugate G gi H) (bridge_def_conj G gi H))
            (bridge_subgroup_le G (subgroup_conjugate G gi H) P (bridge_le_conj_inv G (u .fst) H P (u .snd)))))
      (sylow_contains_conjugate p hp G P (bridge_def_sylow_to G p P sP) H (hH .fst) s
        (concat Nat (group_card (subgroup_group G H) (hH .fst)) (blind_pow p s) (nat_power p s) (hH .snd) (bridge_def_pow p s)))

{` thm:sylow3. (1) from sylow_count_divides; (2) from the congruence
   |Syl| ≡ 1 (mod p): the witness t with |Syl| = t·p + 1 is unique (p > 0),
   so it can be extracted from the truncation. `}
def bridge_nat_cases (x : Nat) : Sum (Id Nat x zero.) (Σ Nat (k ↦ Id Nat x (suc. k)))
  ≔ match x [ zero. ↦ inl. (refl (zero. : Nat)) | suc. k ↦ inr. (k, refl (suc. k : Nat)) ]

def bridge_sylow_witness_prop (b c : Nat) : isProp (Σ Nat (t ↦ Id Nat c (suc. (mul t (suc. b)))))
  ≔ u v ↦ subtype_equal Nat (t ↦ Id Nat c (suc. (mul t (suc. b)))) (t ↦ nat_set c (suc. (mul t (suc. b)))) u v
      (nat_mul_cancel_right b (u .fst) (v .fst)
        (refl ((x ↦ match x [ zero. ↦ zero. | suc. y ↦ y ]) : Nat → Nat)
          (concat Nat (suc. (mul (u .fst) (suc. b))) c (suc. (mul (v .fst) (suc. b)))
            (inverse Nat c (suc. (mul (u .fst) (suc. b))) (u .snd)) (v .snd))))

def bridge_sylow_witness (b c : Nat) (pos : Lt zero. c) (h : NatCongruent (suc. b) c (suc. zero.))
  : Σ Nat (t ↦ Id Nat c (suc. (mul t (suc. b))))
  ≔ let T ≔ Σ Nat (t ↦ Id Nat c (suc. (mul t (suc. b)))) in
    mere_rec (Σ Nat (k ↦ Sum (Id Nat c (add (suc. zero.) (mul k (suc. b)))) (Id Nat (suc. zero.) (add c (mul k (suc. b))))))
      T (bridge_sylow_witness_prop b c)
      (u ↦ match u .snd [
       | inl. e ↦ (u .fst, concat Nat c (add (suc. zero.) (mul (u .fst) (suc. b))) (suc. (mul (u .fst) (suc. b))) e
                    (concat Nat (add (suc. zero.) (mul (u .fst) (suc. b))) (suc. (add zero. (mul (u .fst) (suc. b))))
                      (suc. (mul (u .fst) (suc. b)))
                      (add_suc_left zero. (mul (u .fst) (suc. b)))
                      (refl ((x ↦ suc. x) : Nat → Nat) (add_zero_left (mul (u .fst) (suc. b))))))
       | inr. e ↦ match c [
         | zero. ↦ match pos []
         | suc. c' ↦
           let kz : Id Nat (mul (u .fst) (suc. b)) zero.
             ≔ nat_add_zero_right c' (mul (u .fst) (suc. b))
                 (refl ((x ↦ match x [ zero. ↦ zero. | suc. y ↦ y ]) : Nat → Nat)
                   (concat Nat (suc. (add c' (mul (u .fst) (suc. b)))) (add (suc. c') (mul (u .fst) (suc. b))) (suc. zero.)
                     (inverse Nat (add (suc. c') (mul (u .fst) (suc. b))) (suc. (add c' (mul (u .fst) (suc. b))))
                       (add_suc_left c' (mul (u .fst) (suc. b))))
                     (inverse Nat (suc. zero.) (add (suc. c') (mul (u .fst) (suc. b))) e))) in
           let cz : Id Nat c' zero.
             ≔ nat_add_zero_right_part c' (mul (u .fst) (suc. b))
                 (refl ((x ↦ match x [ zero. ↦ zero. | suc. y ↦ y ]) : Nat → Nat)
                   (concat Nat (suc. (add c' (mul (u .fst) (suc. b)))) (add (suc. c') (mul (u .fst) (suc. b))) (suc. zero.)
                     (inverse Nat (add (suc. c') (mul (u .fst) (suc. b))) (suc. (add c' (mul (u .fst) (suc. b))))
                       (add_suc_left c' (mul (u .fst) (suc. b))))
                     (inverse Nat (suc. zero.) (add (suc. c') (mul (u .fst) (suc. b))) e))) in
           (zero., concat Nat (suc. c') (suc. zero.) (suc. (mul zero. (suc. b)))
                     (refl ((x ↦ suc. x) : Nat → Nat) cz)
                     (refl ((x ↦ suc. x) : Nat → Nat) (inverse Nat (mul zero. (suc. b)) zero. (mul_zero_left (suc. b))))) ] ])
      h

def bridge_sylow_witness_at (p : Nat) (hp : NatIsPrime p) (c : Nat) (pos : Lt zero. c) (h : NatCongruent p c (suc. zero.))
  : Σ Nat (t ↦ Id Nat c (suc. (mul t p)))
  ≔ match p [ zero. ↦ match hp .fst [] | suc. b ↦ bridge_sylow_witness b c pos h ]

def bridge_sylow3 : blind_sylow3
  ≔ p hp G hG P sP ↦
    let s ≔ bridge_def_sylow_to G p P sP in
    let Y ≔ BlindSylowSet G p in
    let Z ≔ SylowSubgroups p G in
    let e ≔ bridge_def_sylow_set G p in
    let hZ ≔ sylow_subgroups_finite p hp G P s in
    let hY ≔ finite_of_equiv Y Z e hZ in
    let cYZ : Id Nat (cardinality Y hY) (cardinality Z hZ) ≔ cardinality_equiv Y Z e hY hZ in
    (hY,
     ((q hP eq ↦ match bridge_nat_cases (group_card (subgroup_group G P) hP) [
        | inl. z ↦ match cauchy_card_nonzero (USym (subgroup_group G P)) hP (usym_unit (subgroup_group G P)) z []
        | inr. kk ↦
          transport Nat (x ↦ NatDivides x q) (cardinality Z hZ) (cardinality Y hY) (inverse Nat (cardinality Y hY) (cardinality Z hZ) cYZ)
            (sylow_count_divides p hp G P s hG hP q (kk .fst)
              (concat Nat (group_card G hG) (mul q (group_card (subgroup_group G P) hP)) (mul q (suc. (kk .fst))) eq
                (refl (mul q) (kk .snd)))
              (kk .snd)) ]),
      let w ≔ bridge_sylow_witness_at p hp (cardinality Z hZ) (finite_inhabited_card_positive Z hZ (P, s))
        (sylow_three_congruence p hp G P s) in
      (w .fst, concat Nat (cardinality Y hY) (cardinality Z hZ) (suc. (mul (w .fst) p)) cYZ (w .snd))))
