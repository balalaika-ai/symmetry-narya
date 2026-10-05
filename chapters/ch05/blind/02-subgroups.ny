{` Blind statements for chapter 5 (actions.tex), section "Subgroups". `}
export "01-gsets"
export "../../../src/417-cyclic-groups"

{` def:set-of-subgroups. Sub(G) ≔ Σ_{X : BG → Set} X(sh_G) × istrans(X). `}
def BlindSubgroups (G : Group) : Type
  ≔ Σ (BlindGSet G) (X ↦ Product (X (shape G) .fst) (BlindIsTrans G X))

{` Helper proofs needed to define the underlying group (they also prove xca:group-Xx!). `}
def blind_tot_pair (G : Group) (X : BlindGSet G) (x x0 : X (shape G) .fst) (g : USym G)
  (e : Id (X (shape G) .fst) x0 (blind_usym_act G X g x))
  : Id (BlindTot G X) (shape G, x) (shape G, x0)
  ≔ (g, pathover_of_eq (BlindBG G) (u ↦ X u .fst) (shape G) (shape G) g x x0
          (inverse (X (shape G) .fst) x0 (blind_usym_act G X g x) e))

def blind_tot_base_paths (G : Group) (X : BlindGSet G) (t : BlindIsTrans G X) (x y : X (shape G) .fst)
  : Mere (Id (BlindTot G X) (shape G, x) (shape G, y))
  ≔ mere_rec (Σ (X (shape G) .fst)
        (x0 ↦ (y0 : X (shape G) .fst) → Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) x0 (blind_usym_act G X g y0)))))
      (Mere (Id (BlindTot G X) (shape G, x) (shape G, y))) (mere_isprop (Id (BlindTot G X) (shape G, x) (shape G, y)))
      (c ↦ mere_rec (Σ (USym G) (g ↦ Id (X (shape G) .fst) (c .fst) (blind_usym_act G X g x)))
        (Mere (Id (BlindTot G X) (shape G, x) (shape G, y))) (mere_isprop (Id (BlindTot G X) (shape G, x) (shape G, y)))
        (a ↦ mere_rec (Σ (USym G) (g ↦ Id (X (shape G) .fst) (c .fst) (blind_usym_act G X g y)))
          (Mere (Id (BlindTot G X) (shape G, x) (shape G, y))) (mere_isprop (Id (BlindTot G X) (shape G, x) (shape G, y)))
          (b ↦ mere (Id (BlindTot G X) (shape G, x) (shape G, y))
                 (concat (BlindTot G X) (shape G, x) (shape G, c .fst) (shape G, y)
                   (blind_tot_pair G X x (c .fst) (a .fst) (a .snd))
                   (inverse (BlindTot G X) (shape G, y) (shape G, c .fst) (blind_tot_pair G X y (c .fst) (b .fst) (b .snd)))))
          (c .snd y))
        (c .snd x))
      t

def blind_tot_connected (G : Group) (X : BlindGSet G) (t : BlindIsTrans G X) : Connected (BlindTot G X)
  ≔ (mere_rec (Σ (X (shape G) .fst)
        (x0 ↦ (y0 : X (shape G) .fst) → Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) x0 (blind_usym_act G X g y0)))))
      (Mere (BlindTot G X)) (mere_isprop (BlindTot G X)) (c ↦ mere (BlindTot G X) (shape G, c .fst)) t,
     u v ↦ connected_pair_elim native_truncation (BlindBG G) (bg_connected G) (shape G)
       (z w ↦ (x : X z .fst) (y : X w .fst) → Mere (Id (BlindTot G X) (z, x) (w, y)))
       (z w ↦ pi_prop (X z .fst) (x ↦ (y : X w .fst) → Mere (Id (BlindTot G X) (z, x) (w, y)))
          (x ↦ pi_prop (X w .fst) (y ↦ Mere (Id (BlindTot G X) (z, x) (w, y))) (y ↦ mere_isprop (Id (BlindTot G X) (z, x) (w, y)))))
       (blind_tot_base_paths G X t)
       (u .fst) (v .fst) (u .snd) (v .snd))

def blind_tot_groupoid (G : Group) (X : BlindGSet G) : isGroupoid (BlindTot G X)
  ≔ hlevel_to_groupoid (BlindTot G X)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (BlindBG G) (u ↦ X u .fst) (groupoid_to_hlevel (BlindBG G) (bg_groupoid G))
        (u ↦ hlevel_raise (suc. (suc. zero.)) (X u .fst) (set_to_hlevel_two (X u .fst) (X u .snd))))

{` xca:group-Xx!. `}
def blind_group_Xx : Type
  ≔ (G : Group) (X : BlindGSet G) (t : BlindIsTrans G X) → Product (Connected (BlindTot G X)) (isGroupoid (BlindTot G X))

{` def:underlying-group-of-subgroup. mkgroup(Tot(X), (sh_G, pt)). `}
def blind_subgroup_group (G : Group) (S : BlindSubgroups G) : Group
  ≔ mkgroup (BlindTot G (S .fst), (shape G, S .snd .fst), blind_tot_connected G (S .fst) (S .snd .snd), blind_tot_groupoid G (S .fst))

{` lem:SubG=MonoG: mkgroup(fst), pointed by reflexivity. `}
def blind_subgroup_incl (G : Group) (S : BlindSubgroups G) : GroupHom (blind_subgroup_group G S) G
  ≔ mkhom (blind_subgroup_group G S) G ((u ↦ u .fst), refl (shape G))

{` def:RmtoS1 (recalled in ex:Rm0-subgroup): the Z-set R_m for m = n+1, base ↦ m, loop ↦ s. `}
def blind_Rm_data (n : Nat) : FreeLoop SetTypes
  ≔ (standard_set (suc. n), set_types_path (standard_set (suc. n)) (standard_set (suc. n)) (finite_fin_successor n))

def blind_Rm (C : CircleSignature) (n : Nat) : BlindGSet (circle_group C) ≔ circle_rec C SetTypes (blind_Rm_data n)

{` R_m(base) ≡ m holds up to the computation identification of the circle signature; 0 is transported along it. `}
def blind_Rm_zero (C : CircleSignature) (n : Nat) : blind_Rm C n (C .base) .fst
  ≔ circle_rec_beta C SetTypes (blind_Rm_data n) .fst .fst .trl (inr. star.)

{` ex:Rm0-subgroup: R_m is transitive. `}
def blind_Rm_transitive : Type ≔ (C : CircleSignature) (n : Nat) → BlindIsTrans (circle_group C) (blind_Rm C n)

{` ex:Rm0-subgroup: R_m(p)(0) = 0 iff p = loop^{mk} for some integer k. `}
def blind_Rm_stabilizer : Type
  ≔ (C : CircleSignature) (n : Nat) (p : Id (C .carrier) (C .base) (C .base))
    → BlindIff (Id (blind_Rm C n (C .base) .fst) (blind_usym_act (circle_group C) (blind_Rm C n) p (blind_Rm_zero C n)) (blind_Rm_zero C n))
        (Mere (Σ Int (k ↦ Id (Id (C .carrier) (C .base) (C .base)) p
                  (loop_power (C .carrier) (C .base) (C .loop) (int_mul (pos. (suc. n)) k)))))

{` def:RtoS1 (recalled in ex:Rm0-subgroup): R(base) ≔ Z, loop ↦ succ. `}
def blind_R_data : FreeLoop SetTypes ≔ ((Int, int_set), set_types_path (Int, int_set) (Int, int_set) int_succ_equiv)

def blind_R (C : CircleSignature) : BlindGSet (circle_group C) ≔ circle_rec C SetTypes blind_R_data

def blind_R_to_int (C : CircleSignature) (x : blind_R C (C .base) .fst) : Int
  ≔ circle_rec_beta C SetTypes blind_R_data .fst .fst .trr x

def blind_R_zero (C : CircleSignature) : blind_R C (C .base) .fst
  ≔ circle_rec_beta C SetTypes blind_R_data .fst .fst .trl int_zero

{` ex:Rm0-subgroup: R is transitive. `}
def blind_R_transitive : Type ≔ (C : CircleSignature) → BlindIsTrans (circle_group C) (blind_R C)

{` ex:Rm0-subgroup: R(loop^k)(0) = k. `}
def blind_R_loop_power : Type
  ≔ (C : CircleSignature) (k : Int)
    → Id Int (blind_R_to_int C (blind_usym_act (circle_group C) (blind_R C) (loop_power (C .carrier) (C .base) (C .loop) k) (blind_R_zero C))) k

{` ex:Rm0-subgroup: only refl_base keeps 0 in place. `}
def blind_R_stabilizer : Type
  ≔ (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
    → BlindIff (Id (blind_R C (C .base) .fst) (blind_usym_act (circle_group C) (blind_R C) p (blind_R_zero C)) (blind_R_zero C))
        (Id (Id (C .carrier) (C .base) (C .base)) p (refl (C .base)))

{` lem:SubGisset. `}
def blind_SubGisset : Type ≔ (G : Group) → isSet (BlindSubgroups G)

{` exa:fix1subSGn. For n = m+1 and k : n, (X, k) : Sub(Σ_n) with X the standard Σ_n-set
   (its transitivity is the separate statement blind_standard_sn_set_transitive). `}
def blind_fix1_subgroup (m : Nat) (k : Fin (suc. m)) (t : BlindIsTrans (symmetric_group (suc. m)) (blind_standard_sn_set (suc. m)))
  : BlindSubgroups (symmetric_group (suc. m))
  ≔ (blind_standard_sn_set (suc. m), (k, t))

{` exa:fix1subSGn: π ·_X k is π applied to k. `}
def blind_fix1_action : Type
  ≔ (m : Nat) (π : USym (symmetric_group (suc. m))) (k : Fin (suc. m))
    → Id (Fin (suc. m)) (blind_usym_act (symmetric_group (suc. m)) (blind_standard_sn_set (suc. m)) π k)
        (permutation_action (standard_set (suc. m)) π k)

{` exa:fix1subSGn: the underlying group of (X, k) is isomorphic to Σ_{n-1}. `}
def blind_fix1subSGn : Type
  ≔ (m : Nat) (k : Fin (suc. m)) (t : BlindIsTrans (symmetric_group (suc. m)) (blind_standard_sn_set (suc. m)))
    → GroupIso (blind_subgroup_group (symmetric_group (suc. m)) (blind_fix1_subgroup m k t)) (symmetric_group m)

{` xca:n-is-ptd-n+1. `}
def blind_n_is_ptd_n1 : Type
  ≔ (n : Nat) → Equiv (BookFiniteSetsAt n) (Σ (BookFiniteSetsAt (suc. n)) (A ↦ A .fst .fst))

{` xca:A-is-A-1+1. `}
def blind_A_is_A_1_1 : Type
  ≔ (A : Type) (hA : isSet A) (d : DecidableEquality A)
    → Equiv A (Σ Type (B ↦ Id Type A (Sum B (Fin (suc. zero.)))))

def blind_five : Nat ≔ suc. (suc. (suc. (suc. (suc. zero.))))
def blind_six : Nat ≔ suc. blind_five

{` exa:C3subC6. C₆ = Aut_Cyc(6, s); F(X, t) ≔ X/2. `}
def blind_C6 : Group ≔ cyclic_group_fin blind_five

def blind_c3c6_F : BlindGSet blind_C6
  ≔ c ↦ (ModQuotient (suc. zero.) (c .fst .fst .fst .fst) (c .fst .fst .snd),
         quotient_set (c .fst .fst .fst .fst) (mod_relation (suc. zero.) (c .fst .fst .fst .fst) (c .fst .fst .snd)))

{` The standard C₆-set (X, t) ↦ X, giving π(k). `}
def blind_c6_standard : BlindGSet blind_C6 ≔ c ↦ c .fst .fst .fst

def blind_c3c6_class (k : Fin blind_six) : blind_c3c6_F (shape blind_C6) .fst
  ≔ quotient_class (Fin blind_six)
      (mod_relation (suc. zero.) (Fin blind_six)
         (finite_fin_successor blind_five)) k

{` exa:C3subC6: F is transitive. `}
def blind_c3c6_transitive : Type ≔ BlindIsTrans blind_C6 blind_c3c6_F

{` exa:C3subC6: F(π)([k]) = [π(k)]. `}
def blind_c3c6_action : Type
  ≔ (π : USym blind_C6) (k : Fin blind_six)
    → Id (blind_c3c6_F (shape blind_C6) .fst) (blind_usym_act blind_C6 blind_c3c6_F π (blind_c3c6_class k))
        (blind_c3c6_class (blind_usym_act blind_C6 blind_c6_standard π k))

{` exa:C3subC6: the symmetries picked out by (F, [0]) are the even powers of s. `}
def blind_c3c6_picked_out : Type
  ≔ (π : USym blind_C6)
    → BlindIff (Id (blind_c3c6_F (shape blind_C6) .fst) (blind_usym_act blind_C6 blind_c3c6_F π (blind_c3c6_class (inr. star.)))
                  (blind_c3c6_class (inr. star.)))
        (Mere (Σ Int (k ↦ Id (USym blind_C6) π
           (cycle_group_power (finite_fin_cycle blind_five) (int_mul (pos. (suc. (suc. zero.))) k)))))

{` exa:C3subC6: the underlying group of (F, [0]) is equivalent to C₃. `}
def blind_c3c6_underlying : Type
  ≔ (t : BlindIsTrans blind_C6 blind_c3c6_F)
    → GroupIso (blind_subgroup_group blind_C6 (blind_c3c6_F, (blind_c3c6_class (inr. star.), t))) (cyclic_group_fin (suc. (suc. zero.)))

{` def:decidable-subgroup. `}
def BlindSubgroupDecidable (G : Group) (S : BlindSubgroups G) : Type ≔ DecidableEquality (S .fst (shape G) .fst)

{` def:typeofmono. ismono(i): USym i is injective (all preimages are propositions). `}
def BlindIsMono (H G : Group) (i : GroupHom H G) : Type ≔ IsEmbedding (USym H) (USym G) (usym_hom H G i)

def blind_ismono_prop : Type ≔ (H G : Group) (i : GroupHom H G) → isProp (BlindIsMono H G i)

{` def:typeofmono. Mono(G) ≔ Σ_H Σ_{i : Hom(H,G)} ismono(i). `}
def BlindMono (G : Group) : Type ≔ Σ Group (H ↦ Σ (GroupHom H G) (i ↦ BlindIsMono H G i))

{` def:typeofmono (1): trivial if H is the trivial group. `}
def BlindMonoTrivial (G : Group) (M : BlindMono G) : Type ≔ Id Group (M .fst) trivial_group

{` def:typeofmono (2): proper if i is not an isomorphism. `}
def BlindMonoProper (G : Group) (M : BlindMono G) : Type ≔ Not (IsGroupIso (M .fst) G (M .snd .fst))

{` ex:SGninSGn+1. A ↦ A ⊔ true. `}
def blind_plus_one (S : SetTypes) : SetTypes ≔ (Sum (S .fst) Unit, sum_set (S .fst) Unit (S .snd) unit_set)

def blind_sigma_incl_fun (n : Nat) (A : BlindBG (symmetric_group n)) : BlindBG (symmetric_group (suc. n))
  ≔ (blind_plus_one (A .fst),
     mere_rec (Id SetTypes (standard_set n) (A .fst)) (Mere (Id SetTypes (standard_set (suc. n)) (blind_plus_one (A .fst))))
       (mere_isprop (Id SetTypes (standard_set (suc. n)) (blind_plus_one (A .fst))))
       (p ↦ mere (Id SetTypes (standard_set (suc. n)) (blind_plus_one (A .fst))) (refl blind_plus_one p))
       (A .snd))

{` i_n with an arbitrary pointing path p : n+1 = n ⊔ true. `}
def blind_sigma_incl_at (n : Nat) (p : Id SetTypes (standard_set (suc. n)) (blind_plus_one (standard_set n)))
  : GroupHom (symmetric_group n) (symmetric_group (suc. n))
  ≔ mkhom (symmetric_group n) (symmetric_group (suc. n))
      (blind_sigma_incl_fun n,
       component_path SetTypes (standard_set (suc. n)) (shape (symmetric_group (suc. n)))
         (blind_sigma_incl_fun n (shape (symmetric_group n))) p)

{` ex:SGninSGn+1: i_n, pointed by reflexivity. `}
def blind_sigma_incl (n : Nat) : GroupHom (symmetric_group n) (symmetric_group (suc. n))
  ≔ blind_sigma_incl_at n (refl (standard_set (suc. n)))

{` ex:SGninSGn+1: i_n is a monomorphism. `}
def blind_SGninSGn1_mono : Type ≔ (n : Nat) → BlindIsMono (symmetric_group n) (symmetric_group (suc. n)) (blind_sigma_incl n)

{` ex:SGninSGn+1: USym i_n extends π by the new last element as a fixed point. `}
def blind_SGninSGn1_extends : Type
  ≔ (n : Nat) (π : USym (symmetric_group n))
    → Product
        ((x : Fin n) → Id (Fin (suc. n))
           (permutation_action (standard_set (suc. n)) (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (blind_sigma_incl n) π) (inl. x))
           (inl. (permutation_action (standard_set n) π x)))
        (Id (Fin (suc. n))
           (permutation_action (standard_set (suc. n)) (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (blind_sigma_incl n) π) (inr. star.))
           (inr. star.))

{` xca:SG2subSG3 (the printed i_3 read as i_2 : Σ₂ → Σ₃): for the pointing path induced by π : 3 ≃ 3, the image of
   USym i consists of the permutations fixing the element that π sends to the added point. `}
def blind_SG2subSG3 : Type
  ≔ (π : Equiv (Fin three) (Fin three)) (σ : USym (symmetric_group three))
    → BlindIff
        (Mere (BookFiber (USym (symmetric_group two)) (USym (symmetric_group three))
           (usym_hom (symmetric_group two) (symmetric_group three)
              (blind_sigma_incl_at two (set_types_path (standard_set three) (standard_set three) π))) σ))
        ((x : Fin three) → Id (Fin three) (π .map x) (inr. star.) → Id (Fin three) (permutation_action (standard_set three) σ x) x)

{` xca:C3subSG3. `}
def blind_C3subSG3 : Type
  ≔ Σ (GroupHom (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three)) (j ↦
    Σ (BlindIsMono (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three) j) (mj ↦
    Σ (GroupHom (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three)) (j' ↦
    Σ (BlindIsMono (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three) j') (mj' ↦
      Product
        (Not (Id (USym (cyclic_group_fin (suc. (suc. zero.))) → USym (symmetric_group three))
           (usym_hom (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three) j)
           (usym_hom (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group three) j')))
        (Id (BlindMono (symmetric_group three)) (cyclic_group_fin (suc. (suc. zero.)), (j, mj)) (cyclic_group_fin (suc. (suc. zero.)), (j', mj')))))))

{` ex:prodinclismono. `}
def blind_prod_incl1 (G H : Group) : GroupHom G (product_group G H)
  ≔ mkhom G (product_group G H) ((z ↦ (z, shape H)), refl (shape (product_group G H)))

def blind_prod_incl2 (G H : Group) : GroupHom H (product_group G H)
  ≔ mkhom H (product_group G H) ((w ↦ (shape G, w)), refl (shape (product_group G H)))

def blind_prodinclismono : Type
  ≔ (G H : Group)
    → Product (BlindIsMono G (product_group G H) (blind_prod_incl1 G H)) (BlindIsMono H (product_group G H) (blind_prod_incl2 G H))

{` ex:prodinclismono: USym i_G maps g to (g, refl). `}
def blind_prod_incl1_usym : Type
  ≔ (G H : Group) (g : USym G)
    → Id (USym (product_group G H)) (usym_hom G (product_group G H) (blind_prod_incl1 G H) g) (g, refl (shape H))

{` ex:prodinclismono, footnote: Bi_G is a set bundle. `}
def blind_prod_incl1_covering : Type
  ≔ (G H : Group) → IsCovering (BlindBG G) (BlindBG (product_group G H)) (z ↦ (z, shape H))

{` lem:SubG=MonoG. Pairs (H, i) without the monomorphism witness. `}
def BlindHomInto (G : Group) : Type ≔ Σ Group (H ↦ GroupHom H G)

def blind_F0 (G : Group) (S : BlindSubgroups G) : BlindHomInto G ≔ (blind_subgroup_group G S, blind_subgroup_incl G S)

{` lem:SubG=MonoG, part of the statement: F lands in Mono(G). `}
def blind_SubG_incl_mono : Type
  ≔ (G : Group) (S : BlindSubgroups G) → BlindIsMono (blind_subgroup_group G S) G (blind_subgroup_incl G S)

{` F : Sub(G) → Mono(G), given the (propositional) monomorphism witnesses. `}
def blind_F (G : Group) (m : (S : BlindSubgroups G) → BlindIsMono (blind_subgroup_group G S) G (blind_subgroup_incl G S))
  (S : BlindSubgroups G) : BlindMono G
  ≔ (blind_subgroup_group G S, (blind_subgroup_incl G S, m S))

{` lem:SubG=MonoG: F is an equivalence (for the witnesses m, which exist by blind_SubG_incl_mono and are unique). `}
def blind_SubG_MonoG : Type
  ≔ (G : Group) (m : (S : BlindSubgroups G) → BlindIsMono (blind_subgroup_group G S) G (blind_subgroup_incl G S))
    → BookIsEquiv (BlindSubgroups G) (BlindMono G) (blind_F G m)

{` exa:EforSG3: (X, 3) and (Σ₂, i₂) define the same subgroup: F(X, 3) = (Σ₂, i₂) (monomorphism witnesses are propositional). `}
def blind_EforSG3 : Type
  ≔ (t : BlindIsTrans (symmetric_group three) (blind_standard_sn_set three))
    → Id (BlindHomInto (symmetric_group three))
        (blind_F0 (symmetric_group three) (blind_standard_sn_set three, (inr. star., t)))
        (symmetric_group two, blind_sigma_incl two)

{` lem:setofsubgroups. `}
def blind_setofsubgroups : Type ≔ (G : Group) → isSet (BlindMono G)

{` lem:E-preserves-symms. `}
def blind_E_preserves_symms : Type
  ≔ (G : Group) (g : USym G) (S : BlindSubgroups G) (M : BlindHomInto G) (e : Id (BlindHomInto G) M (blind_F0 G S))
    → BlindIff (Id (S .fst (shape G) .fst) (blind_usym_act G (S .fst) g (S .snd .fst)) (S .snd .fst))
        (Mere (Σ (USym (M .fst)) (h ↦ Id (USym G) g (usym_hom (M .fst) G (M .snd) h))))

{` def:triv-proper-Mono (1): trivial if Tot(X) is contractible. `}
def BlindSubgroupTrivial (G : Group) (S : BlindSubgroups G) : Type ≔ BookIsContr (BlindTot G (S .fst))

{` def:triv-proper-Mono (1): "the underlying group is trivial, i.e. Tot(X) contractible". `}
def blind_subgroup_trivial_iff : Type
  ≔ (G : Group) (S : BlindSubgroups G)
    → BlindIff (BlindSubgroupTrivial G S) (Id Group (blind_subgroup_group G S) trivial_group)

{` def:triv-proper-Mono (2): proper if X(sh_G) is not contractible. `}
def BlindSubgroupProper (G : Group) (S : BlindSubgroups G) : Type ≔ Not (BookIsContr (S .fst (shape G) .fst))

{` ex:prodinclisGset: the (G×G')-set princ G' ∘ proj₂. `}
def blind_princ_proj2 (G G' : Group) : BlindGSet (product_group G G') ≔ u ↦ blind_princ G' (u .snd)

{` ex:prodinclisGset: Tot(princ G' ∘ proj₂) ≃ BG. `}
def blind_prodinclisGset_tot : Type
  ≔ (G G' : Group) → Equiv (BlindTot (product_group G G') (blind_princ_proj2 G G')) (BlindBG G)

{` ex:prodinclisGset: (G, i₁) = F(princ G' ∘ proj₂, refl_{sh_G'}) in Mono(G × G'). `}
def blind_prodinclisGset : Type
  ≔ (G G' : Group) (t : BlindIsTrans (product_group G G') (blind_princ_proj2 G G'))
    → Id (BlindHomInto (product_group G G'))
        (G, blind_prod_incl1 G G')
        (blind_F0 (product_group G G') (blind_princ_proj2 G G', (refl (shape G'), t)))

{` con:lagrange: choice maps. `}
def BlindChoiceMap (G : Group) (S : BlindSubgroups G) : Type
  ≔ (x : S .fst (shape G) .fst) → Σ (USym G) (g ↦ Id (S .fst (shape G) .fst) (blind_usym_act G (S .fst) g x) (S .snd .fst))

{` con:lagrange. L_H : choice maps → (USym G ≃ X(sh_G) × USym H). `}
def blind_lagrange_construction : Type
  ≔ (G : Group) (S : BlindSubgroups G)
    → BlindChoiceMap G S → Equiv (USym G) (Product (S .fst (shape G) .fst) (USym (blind_subgroup_group G S)))

{` cor:lagrange-dep-sum. `}
def blind_lagrange_dep_sum : Type
  ≔ (G : Group) (S : BlindSubgroups G)
    → BlindChoiceMap G S
    → Equiv (USym G) (Σ (S .fst (shape G) .fst) (x ↦ Id (BlindTot G (S .fst)) (shape G, x) (shape G, x)))

{` xca:lagrange. `}
def blind_lagrange : Type
  ≔ (G : Group) (hG : IsFiniteGroup G) (S : BlindSubgroups G) (hX : BlindIsFiniteGSet G (S .fst))
    → Σ (IsFiniteGroup (blind_subgroup_group G S))
        (hH ↦ Id Nat (group_card G hG) (mul (blind_gset_card G (S .fst) hX) (group_card (blind_subgroup_group G S) hH)))

{` xca:lagrange-Z-action-Rm: USym Z ≃ m × USym H_m (transitivity of R_m is blind_Rm_transitive). `}
def blind_lagrange_Z_action_Rm : Type
  ≔ (C : CircleSignature) (n : Nat) (t : BlindIsTrans (circle_group C) (blind_Rm C n))
    → Equiv (USym (circle_group C))
        (Product (Fin (suc. n)) (USym (blind_subgroup_group (circle_group C) (blind_Rm C n, (blind_Rm_zero C n, t)))))

{` The element 0 of X(base) for the G-set of fig:not-normal. `}
def blind_not_normal_zero (W : FigureEightSignature) (hW : isGroupoid (W .carrier)) : blind_not_normal_gset W hW (W .base) .fst
  ≔ figure_eight_rec_beta W SetTypes
      (standard_set three,
       (set_types_path (standard_set three) (standard_set three) (finite_fin_successor (suc. (suc. zero.))),
        set_types_path (standard_set three) (standard_set three) fin3_swap01_equiv)) .fst .fst .trl fin3_zero

{` xca:lagrange-if-subgr-not-normal: a choice map for (X, 0). `}
def blind_lagrange_if_subgr_not_normal : Type
  ≔ (W : FigureEightSignature) (hW : isGroupoid (W .carrier))
    → (x : blind_not_normal_gset W hW (W .base) .fst)
    → Σ (USym (blind_figure_eight_group W hW))
        (g ↦ Id (blind_not_normal_gset W hW (W .base) .fst)
               (blind_usym_act (blind_figure_eight_group W hW) (blind_not_normal_gset W hW) g x) (blind_not_normal_zero W hW))
