export "976-sigma3-subgroup-classification"

{` Chapter 9 (subgroups.tex), xca:Sub(Sigma3) (line 1311): why module 976
   classifies only decidable subgroups. For a group G, an involution t
   (t·t = e) and a proposition P, the subgroup S_{t,P} is the quotient
   G-set z ↦ (sh_G = z)/~ with u ~ u' iff u = u' or (P and u' = u ∘ t),
   pointed at the class of refl (set quotients of module 41, effective).
   Its symmetries are e and, if P holds, t: t is a symmetry when P holds,
   and any symmetry k ≠ e forces P. For G = Σ_3 and t = (1 2), knowing
   which of the six subgroups S_{t,P} is decides P: so "every subgroup of
   Σ_3 is one of 1, A_3, Σ_3, T_0, T_1, T_2" implies excluded middle
   (sigma3_classification_decides). `}

def InvolutionRelationType (G : Group) (t : USym G) (P : Type) (z : BG G .carrier)
  (u u' : Id (BG G .carrier) (shape G) z) : Type
  ≔ Mere (Sum (Id (Id (BG G .carrier) (shape G) z) u u')
      (Product P (Id (Id (BG G .carrier) (shape G) z) u' (concat (BG G .carrier) (shape G) (shape G) z t u))))

def involution_cancel (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (z : BG G .carrier)
  (u : Id (BG G .carrier) (shape G) z)
  : Id (Id (BG G .carrier) (shape G) z) (concat (BG G .carrier) (shape G) (shape G) z t (concat (BG G .carrier) (shape G) (shape G) z t u)) u
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let L ≔ Id A s z in
    calc
      concat A s s z t (concat A s s z t u) = concat A s s z (concat A s s s t t) u
        by inverse L (concat A s s z (concat A s s s t t) u) (concat A s s z t (concat A s s z t u)) (concat_assoc A s s s z t t u)
      = concat A s s z (refl s) u by refl ((q ↦ concat A s s z q u) : Id A s s → L) ht
      = u by concat_1p A s z u ∎

def involution_relation (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type)
  (z : BG G .carrier) : EquivalenceRelation (Id (BG G .carrier) (shape G) z)
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let L ≔ Id A s z in
    let R ≔ InvolutionRelationType G t P z in
    let tc ≔ concat A s s z t in
    (u u' ↦ (R u u', mere_isprop (Sum (Id L u u') (Product P (Id L u' (tc u))))),
     u ↦ mere (Sum (Id L u u) (Product P (Id L u (tc u)))) (inl. (refl u)),
     u u' r ↦ mere_rec (Sum (Id L u u') (Product P (Id L u' (tc u)))) (R u' u) (mere_isprop (Sum (Id L u' u) (Product P (Id L u (tc u')))))
       (c ↦ match c [
        | inl. e ↦ mere (Sum (Id L u' u) (Product P (Id L u (tc u')))) (inl. (inverse L u u' e))
        | inr. pe ↦ mere (Sum (Id L u' u) (Product P (Id L u (tc u'))))
            (inr. (pe .fst,
              concat L u (tc (tc u)) (tc u')
                (inverse L (tc (tc u)) u (involution_cancel G t ht z u))
                (refl tc (inverse L u' (tc u) (pe .snd))))) ])
       r,
     u u' u'' r r' ↦
       let W ≔ Sum (Id L u u'') (Product P (Id L u'' (tc u))) in
       mere_rec (Sum (Id L u u') (Product P (Id L u' (tc u)))) (Mere W) (mere_isprop W)
         (c ↦ mere_rec (Sum (Id L u' u'') (Product P (Id L u'' (tc u')))) (Mere W) (mere_isprop W)
           (c' ↦ match c [
            | inl. e ↦ match c' [
              | inl. e' ↦ mere W (inl. (concat L u u' u'' e e'))
              | inr. pe' ↦ mere W (inr. (pe' .fst, concat L u'' (tc u') (tc u) (pe' .snd) (refl tc (inverse L u u' e)))) ]
            | inr. pe ↦ match c' [
              | inl. e' ↦ mere W (inr. (pe .fst, concat L u'' u' (tc u) (inverse L u' u'' e') (pe .snd)))
              | inr. pe' ↦ mere W (inl. (inverse L u'' u
                  (calc
                    u'' = tc u' by pe' .snd
                    = tc (tc u) by refl tc (pe .snd)
                    = u by involution_cancel G t ht z u ∎))) ] ])
           r')
         r)

def involution_gset (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type) : GSet G
  ≔ z ↦ (Quotient (Id (BG G .carrier) (shape G) z) (involution_relation G t ht P z),
         quotient_set (Id (BG G .carrier) (shape G) z) (involution_relation G t ht P z))

def involution_class (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type)
  (z : BG G .carrier) (u : Id (BG G .carrier) (shape G) z) : involution_gset G t ht P z .fst
  ≔ quotient_class (Id (BG G .carrier) (shape G) z) (involution_relation G t ht P z) u

{` The action on classes is post-composition: p · [u] = [u p]. `}
def involution_gset_act (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type)
  (z w : BG G .carrier) (p : Id (BG G .carrier) z w) (u : Id (BG G .carrier) (shape G) z)
  : Id (involution_gset G t ht P w .fst) (gset_act G (involution_gset G t ht P) z w p (involution_class G t ht P z u))
      (involution_class G t ht P w (concat (BG G .carrier) (shape G) z w u p))
  ≔ let A ≔ BG G .carrier in
    let X ≔ involution_gset G t ht P in
    let cl ≔ involution_class G t ht P in
    J A z (w p ↦ Id (X w .fst) (gset_act G X z w p (cl z u)) (cl w (concat A (shape G) z w u p)))
      (concat (X z .fst) (gset_act G X z z (refl z) (cl z u)) (cl z u) (cl z (concat A (shape G) z z u (refl z)))
        (gset_act_refl G X z (cl z u))
        (refl (cl z) (inverse (Id A (shape G) z) (concat A (shape G) z z u (refl z)) u (concat_p1 A (shape G) z u))))
      w p

def involution_gset_transitive (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type)
  : IsTransitive G (involution_gset G t ht P)
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let X ≔ involution_gset G t ht P in
    let Y ≔ X s .fst in
    let cl ≔ involution_class G t ht P s in
    let x0 ≔ cl (refl s) in
    let T ≔ (y : Y) → Mere (Σ (USym G) (g ↦ Id Y x0 (gset_usym_act G X g y))) in
    mere (Σ Y (x ↦ (y : Y) → Mere (Σ (USym G) (g ↦ Id Y x (gset_usym_act G X g y)))))
      (x0, y ↦ mere_rec (BookFiber (Id A s s) Y cl y) (Mere (Σ (USym G) (g ↦ Id Y x0 (gset_usym_act G X g y))))
        (mere_isprop (Σ (USym G) (g ↦ Id Y x0 (gset_usym_act G X g y))))
        (w ↦ let u ≔ w .fst in
          let g ≔ usym_inv G u in
          mere (Σ (USym G) (g ↦ Id Y x0 (gset_usym_act G X g y)))
            (g,
             calc
               x0 = cl (concat A s s s u g)
                 by refl cl (inverse (Id A s s) (concat A s s s u g) (refl s) (concat_inverse_right A s s u))
               = gset_usym_act G X g (cl u)
                 by inverse Y (gset_usym_act G X g (cl u)) (cl (concat A s s s u g)) (involution_gset_act G t ht P s s g u)
               = gset_usym_act G X g y by refl (gset_usym_act G X g) (inverse Y y (cl u) (w .snd)) ∎))
        (quotient_surjective (Id A s s) (involution_relation G t ht P s) y))

def involution_subgroup (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type) : Subgroups G
  ≔ (involution_gset G t ht P, involution_class G t ht P (shape G) (refl (shape G)), involution_gset_transitive G t ht P)

{` If P holds, t is a symmetry of S_{t,P}. `}
def involution_subgroup_has_t (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type) (p : P)
  : SubgroupHasSymmetry G (involution_subgroup G t ht P) t
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let L ≔ Id A s s in
    let X ≔ involution_gset G t ht P in
    let cl ≔ involution_class G t ht P s in
    let x ≔ concat A s s s (refl s) t in
    concat (X s .fst) (gset_usym_act G X t (cl (refl s))) (cl x) (cl (refl s))
      (involution_gset_act G t ht P s s t (refl s))
      (quotient_encode L (involution_relation G t ht P s) x (refl s)
        (mere (Sum (Id L x (refl s)) (Product P (Id L (refl s) (concat A s s s t x))))
          (inr. (p,
            inverse L (concat A s s s t x) (refl s)
              (concat L (concat A s s s t x) (concat A s s s t t) (refl s)
                (refl (concat A s s s t) (concat_1p A s s t)) ht)))))

{` Any symmetry k ≠ e of S_{t,P} forces P. `}
def involution_subgroup_member_prop (G : Group) (t : USym G) (ht : Id (USym G) (usym_mul G t t) (usym_unit G)) (P : Type)
  (hP : isProp P) (k : USym G) (nk : Not (Id (USym G) k (usym_unit G)))
  (r : SubgroupHasSymmetry G (involution_subgroup G t ht P) k) : P
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let L ≔ Id A s s in
    let X ≔ involution_gset G t ht P in
    let R ≔ involution_relation G t ht P s in
    let cl ≔ involution_class G t ht P s in
    let x ≔ concat A s s s (refl s) k in
    let e : Id (X s .fst) (cl x) (cl (refl s))
      ≔ concat (X s .fst) (cl x) (gset_usym_act G X k (cl (refl s))) (cl (refl s))
          (inverse (X s .fst) (gset_usym_act G X k (cl (refl s))) (cl x) (involution_gset_act G t ht P s s k (refl s))) r in
    mere_rec (Sum (Id L x (refl s)) (Product P (Id L (refl s) (concat A s s s t x)))) P hP
      (c ↦ match c [
       | inl. q ↦ match nk (concat L k x (refl s) (inverse L x k (concat_1p A s s k)) q) []
       | inr. pq ↦ pq .fst ])
      (quotient_effective L R x (refl s) .map e)

{` For Σ_3: (1 2) is an involution, and the classification of all
   subgroups of Σ_3 decides every proposition. `}
def sigma3_t12_involution
  : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) (sigma3_sym t12.) (sigma3_sym t12.)) (usym_unit (symmetric_group three))
  ≔ let G ≔ symmetric_group three in
    concat (USym G) (usym_mul G (sigma3_sym t12.) (sigma3_sym t12.)) (sigma3_sym ide.) (usym_unit G)
      (sigma3_mul_ext (sigma3_sym t12.) (sigma3_sym t12.) (sigma3_sym ide.)
        (i ↦ match i [
         | inr. star. ↦ refl (inr. star. : Fin three)
         | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Fin three)
         | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Fin three)
         | inl. (inl. (inl. v)) ↦ match v [] ]))
      (inverse (USym G) (usym_unit G) (sigma3_sym ide.) sigma3_unit_named)

def sigma3_prop_subgroup (P : Type) : Subgroups (symmetric_group three)
  ≔ involution_subgroup (symmetric_group three) (sigma3_sym t12.) sigma3_t12_involution P

def sigma3_prop_member (P : Type) (hP : isProp P) (n : Sigma3Name) (i : Fin three)
  (d : Not (Id (Fin three) (sigma3_act (sigma3_sym n) i) i)) (r : Sigma3Mem (sigma3_prop_subgroup P) n) : P
  ≔ involution_subgroup_member_prop (symmetric_group three) (sigma3_sym t12.) sigma3_t12_involution P hP (sigma3_sym n)
      (sigma3_sym_ne_unit n i d) r

def sigma3_classification_decides (cl : (S : Subgroups (symmetric_group three)) → Sigma3SixSubgroups S)
  (P : Type) (hP : isProp P) : Decidable P
  ≔ let G ≔ symmetric_group three in
    let SG ≔ Subgroups G in
    let S ≔ sigma3_prop_subgroup P in
    let from : (T : SG) → Id SG S T → (n : Sigma3Name) → Sigma3Mem T n → (i : Fin three)
          → Not (Id (Fin three) (sigma3_act (sigma3_sym n) i) i) → P
      ≔ T e n r i d ↦ sigma3_prop_member P hP n i d
          (subgroup_symmetry_transport G T S (inverse SG S T e) (sigma3_sym n) r) in
    match cl S [
    | inl. e ↦ inr. (p ↦ sigma3_not_trivial_mem t12. fin3_one (fin3_differ fin3_two fin3_one (refl (false. : Bool)))
        (subgroup_symmetry_transport G S (principal_subgroup G) e (sigma3_sym t12.)
          (involution_subgroup_has_t G (sigma3_sym t12.) sigma3_t12_involution P p)))
    | inr. (inl. e) ↦ inl. (from (alternating_subgroup (suc. zero.)) e cyc.
        (sigma3_a3_mem_of_plus (sigma3_sym cyc.) sigma3_sign_cyc) fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool))))
    | inr. (inr. (inl. e)) ↦ inl. (from (group_full_subgroup G) e t01.
        (full_subgroup_has_symmetry G (sigma3_sym t01.)) fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool))))
    | inr. (inr. (inr. (inl. e))) ↦ inl. (from (sigma3_point_subgroup fin3_zero) e t12. (refl fin3_zero)
        fin3_one (fin3_differ fin3_two fin3_one (refl (false. : Bool))))
    | inr. (inr. (inr. (inr. (inl. e)))) ↦ inl. (from (sigma3_point_subgroup fin3_one) e t02. (refl fin3_one)
        fin3_zero (fin3_differ fin3_two fin3_zero (refl (false. : Bool))))
    | inr. (inr. (inr. (inr. (inr. e)))) ↦ inl. (from (sigma3_point_subgroup fin3_two) e t01. (refl fin3_two)
        fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool)))) ]
