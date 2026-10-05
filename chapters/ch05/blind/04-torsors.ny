{` Blind statements for chapter 5 (actions.tex), sections "The classifying type is the type of torsors",
   "Any symmetry is a symmetry in Set" and "The lemma that is not Burnside's". `}
export "03-orbits"

{` def:Gtorsor. Torsor_G ≔ Σ_{X : GSet} ‖princ G = X‖. `}
def BlindTorsors (G : Group) : Type ≔ Σ (BlindGSet G) (X ↦ Mere (Id (BlindGSet G) (blind_princ G) X))

def blind_torsors_base (G : Group) : BlindTorsors G
  ≔ (blind_princ G, mere (Id (BlindGSet G) (blind_princ G) (blind_princ G)) (refl (blind_princ G)))

{` xca:torsor=free+transitive. `}
def blind_torsor_free_transitive : Type
  ≔ (G : Group) (X : BlindGSet G)
    → BlindIff (Mere (Id (BlindGSet G) (blind_princ G) X)) (Product (BlindGSetFree G X) (BlindIsTrans G X))

{` Remark (actions.tex 2065): Torsor_G is the component of the coverings over BG containing the universal covering. `}
def blind_torsors_component : Type
  ≔ (G : Group)
    → Equiv (BlindTorsors G)
        (NativeComponent (Coverings (BlindBG G)) (path_cover (BlindBG G) (bg_groupoid G) (shape G)))

{` Remark (actions.tex 2065): Torsor_G is a connected groupoid. `}
def blind_torsors_connected_groupoid : Type
  ≔ (G : Group) → Product (Connected (BlindTorsors G)) (isGroupoid (BlindTorsors G))

{` Remark (actions.tex 2065): pointed at princ G it classifies G itself ("guess which one"). `}
def blind_torsors_classify_G : Type
  ≔ (G : Group) (c : Connected (BlindTorsors G)) (h : isGroupoid (BlindTorsors G))
    → Id Group (mkgroup (BlindTorsors G, blind_torsors_base G, c, h)) G

{` def:BG2TorsG. P_y is a G-torsor. `}
def blind_pathsp_witness (G : Group) (y : BlindBG G) : Mere (Id (BlindGSet G) (blind_princ G) (blind_pathsp G y))
  ≔ trunc_map native_truncation (Id (BlindBG G) (shape G) y) (Id (BlindGSet G) (blind_princ G) (blind_pathsp G y))
      (q ↦ refl (blind_pathsp G) q) (bg_connected G .snd (shape G) y)

def blind_pathsp_torsor (G : Group) (y : BlindBG G) : BlindTorsors G ≔ (blind_pathsp G y, blind_pathsp_witness G y)

{` def:BG2TorsG. P_- : BG →* (Torsor_G, princ G), pointed by reflexivity. `}
def blind_BG2TorsG (G : Group) : BookPointedMap (BG G) (BlindTorsors G, blind_torsors_base G)
  ≔ (blind_pathsp_torsor G,
     subtype_equal (BlindGSet G) (X ↦ Mere (Id (BlindGSet G) (blind_princ G) X)) (X ↦ mere_isprop (Id (BlindGSet G) (blind_princ G) X))
       (blind_torsors_base G) (blind_pathsp_torsor G (shape G)) (refl (blind_princ G)))

{` def:BG2TorsG: the action type of P_y is contractible. `}
def blind_pathsp_tot_contractible : Type ≔ (G : Group) (y : BlindBG G) → BookIsContr (BlindTot G (blind_pathsp G y))

{` rem:pathsptransport: for q : y = z, P_q(x) sends p : y = x to p q⁻¹ (book order), i.e. q⁻¹ then p. `}
def blind_pathsp_ap_transport : Type
  ≔ (G : Group) (y z : BlindBG G) (q : Id (BlindBG G) y z) (x : BlindBG G) (p : Id (BlindBG G) y x)
    → Id (Id (BlindBG G) z x)
        (transport (BlindGSet G) (X ↦ X x .fst) (blind_pathsp G y) (blind_pathsp G z) (refl (blind_pathsp G) q) p)
        (concat (BlindBG G) z y x (inverse (BlindBG G) y z q) p)

{` lem:pathsptransportiseq. `}
def blind_pathsptransportiseq : Type
  ≔ (G : Group) (y z : BlindBG G)
    → BookIsEquiv (Id (BlindBG G) y z) (Id (BlindGSet G) (blind_pathsp G y) (blind_pathsp G z)) (q ↦ refl (blind_pathsp G) q)

{` lem:BGbytorsor. `}
def blind_BGbytorsor : Type ≔ (G : Group) → BookIsEquiv (BlindBG G) (BlindTorsors G) (blind_pathsp_torsor G)

{` def:restrictandinduce. f^*Y ≔ Y ∘ Bf. `}
def blind_restrict (G H : Group) (f : GroupHom G H) (Y : BlindGSet H) : BlindGSet G ≔ z ↦ Y (hom_function G H f z)

{` def:restrictandinduce. f_!X(w) ≔ ‖Σ_{z:BG} (Bf(z) = w) × X(z)‖₀. `}
def BlindInduceSum (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (w : BlindBG H) : Type
  ≔ Σ (BlindBG G) (z ↦ Product (Id (BlindBG H) (hom_function G H f z) w) (X z .fst))

def blind_induce (G H : Group) (f : GroupHom G H) (X : BlindGSet G) : BlindGSet H
  ≔ w ↦ (SetTrunc (BlindInduceSum G H f X w), set_trunc_set (BlindInduceSum G H f X w))

{` def:restrictandinduce, footnote: G̃_x = i_x^* princ G. `}
def blind_tilde_is_restriction : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst)
    → Id (BlindGSet (blind_stabilizer G X x)) (blind_tilde G X x)
        (blind_restrict (blind_stabilizer G X x) G (blind_stabilizer_incl G X x) (blind_princ G))

{` ft:f_!X(w)-orbitset: the G-set z ↦ (Bf(z) = w) × X(z). `}
def blind_induce_gset (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (w : BlindBG H) : BlindGSet G
  ≔ z ↦ (Product (Id (BlindBG H) (hom_function G H f z) w) (X z .fst),
         product_set (Id (BlindBG H) (hom_function G H f z) w) (X z .fst) (bg_groupoid H (hom_function G H f z) w) (X z .snd))

{` ft:f_!X(w)-orbitset: f_!X(w) is the set of orbits of that G-set, whose underlying set is princ H(w) × X(sh_G). `}
def blind_induce_orbitset : Type
  ≔ (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (w : BlindBG H)
    → Product (Equiv (blind_induce G H f X w .fst) (BlindOrbits G (blind_induce_gset G H f X w)))
        (Equiv (blind_induce_gset G H f X w (shape G) .fst) (Product (Id (BlindBG H) (shape H) w) (X (shape G) .fst)))

{` xca:why-setTrunc_f_!. `}
def blind_why_setTrunc : Type
  ≔ Σ Group (G ↦ Σ Group (H ↦ Σ (GroupHom G H) (f ↦ Σ (BlindGSet G) (X ↦
      Not ((w : BlindBG H) → isSet (BlindInduceSum G H f X w))))))

{` xca:adjunction-_!-^* (1): for an isomorphism f, f_!X ≃ X ∘ Bf⁻¹ (fiberwise). `}
def blind_induce_iso : Type
  ≔ (G H : Group) (f : GroupHom G H) (hf : IsGroupIso G H f) (X : BlindGSet G) (w : BlindBG H)
    → Equiv (blind_induce G H f X w .fst)
        (X (equiv_inverse_map (BlindBG G) (BlindBG H) (native_equivalence (BlindBG G) (BlindBG H) (hom_function G H f, hf)) w) .fst)

{` xca:adjunction-_!-^* (2). `}
def blind_adjunction_induce_restrict : Type
  ≔ (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (Y : BlindGSet H)
    → Equiv (BlindHomG H (blind_induce G H f X) Y) (BlindHomG G X (blind_restrict G H f Y))

{` rem:^*-_!-as-(pre)image: ∃_f X (b) ≔ ‖Σ_a (f(a) = b) × X(a)‖ is the image of the subtype X under f. `}
def blind_subtype_image (A B : Type) (f : A → B) (X : Subtypes A) : Subtypes B
  ≔ b ↦ (Mere (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))), mere_isprop (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))))

{` rem:^*-_!-as-(pre)image: predicates on connected types are constant. `}
def blind_connected_predicates_constant : Type
  ≔ (A : Type) (hA : Connected A) (P : Subtypes A) (x y : A) → Id PropTypes (P x) (P y)

{` rem:coinduced-Hset. f_*X(w) ≔ Π_{z:BG} ((Bf(z) = w) → X(z)), always a set. `}
def blind_coinduce (G H : Group) (f : GroupHom G H) (X : BlindGSet G) : BlindGSet H
  ≔ w ↦ ((z : BlindBG G) → Id (BlindBG H) (hom_function G H f z) w → X z .fst,
         pi_set (BlindBG G) (z ↦ Id (BlindBG H) (hom_function G H f z) w → X z .fst)
           (z ↦ pi_set (Id (BlindBG H) (hom_function G H f z) w) (_ ↦ X z .fst) (_ ↦ X z .snd)))

{` rem:coinduced-Hset, footnote: f_*X(w) is the set of invariant maps of the G-set z ↦ ((Bf(z) = w) → X(z)). `}
def blind_coinduce_invariant : Type
  ≔ (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (w : BlindBG H)
    → Equiv (blind_coinduce G H f X w .fst)
        (BlindInvariantMaps G (z ↦ (Id (BlindBG H) (hom_function G H f z) w → X z .fst,
            pi_set (Id (BlindBG H) (hom_function G H f z) w) (_ ↦ X z .fst) (_ ↦ X z .snd))))

{` rem:coinduced-subset. ∀_f X ≔ f_* X on subtypes. `}
def blind_subtype_coimage (A B : Type) (f : A → B) (X : Subtypes A) : Subtypes B
  ≔ b ↦ ((a : A) → Id B (f a) b → X a .fst,
         pi_prop A (a ↦ Id B (f a) b → X a .fst) (a ↦ pi_prop (Id B (f a) b) (_ ↦ X a .fst) (_ ↦ X a .snd)))

{` rem:coinduced-subset: b is in ∀_f X iff the whole preimage of b is contained in X. `}
def blind_coinduced_subset : Type
  ≔ (A B : Type) (f : A → B) (X : Subtypes A) (b : B)
    → BlindIff (blind_subtype_coimage A B f X b .fst) ((u : BookFiber A B f b) → X (u .fst) .fst)

{` xca:adjunction-^*-_*. `}
def blind_adjunction_restrict_coinduce : Type
  ≔ (G H : Group) (f : GroupHom G H) (X : BlindGSet G) (Y : BlindGSet H)
    → Equiv (BlindHomG G (blind_restrict G H f Y) X) (BlindHomG H Y (blind_coinduce G H f X))

{` con:inducedtorsor: f_! : Torsor_G →* Torsor_H on underlying G-sets, with f_! ∘ P^G = P^H ∘ Bf. `}
def blind_inducedtorsor : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Σ (BookPointedMap (BlindTorsors G, blind_torsors_base G) (BlindTorsors H, blind_torsors_base H))
        (F ↦ Product ((T : BlindTorsors G) → Id (BlindGSet H) (F .fst T .fst) (blind_induce G H f (T .fst)))
               (Id (BlindBG G → BlindTorsors H) (z ↦ F .fst (blind_pathsp_torsor G z)) (z ↦ blind_pathsp_torsor H (hom_function G H f z))))

{` lem:epifullyfaithful. `}
def blind_epifullyfaithful : Type
  ≔ (G H : Group) (f : GroupHom G H) (hs : Surjective (USym G) (USym H) (usym_hom G H f))
    → IsEmbedding (BlindGSet H) (BlindGSet G) (blind_restrict G H f)

{` sec:groupssubperm. ρ_G : Hom(G, Σ_{USym G}), Bρ_G(z) ≔ P_z(sh_G) = (z = sh_G), pointed by reflexivity. `}
def blind_usym_set_type (G : Group) : SetTypes ≔ (USym G, usym_set G)

def blind_rho_fun (G : Group) (z : BlindBG G) : SetTypes ≔ (Id (BlindBG G) z (shape G), bg_groupoid G z (shape G))

def blind_rho_B (G : Group) (z : BlindBG G) : BlindBG (permutation_group (blind_usym_set_type G))
  ≔ (blind_rho_fun G z,
     trunc_map native_truncation (Id (BlindBG G) (shape G) z) (Id SetTypes (blind_usym_set_type G) (blind_rho_fun G z))
       (q ↦ refl (blind_rho_fun G) q) (bg_connected G .snd (shape G) z))

def blind_rho (G : Group) : GroupHom G (permutation_group (blind_usym_set_type G))
  ≔ mkhom G (permutation_group (blind_usym_set_type G))
      (blind_rho_B G,
       component_path SetTypes (blind_usym_set_type G) (shape (permutation_group (blind_usym_set_type G)))
         (blind_rho_B G (shape G)) (refl (blind_usym_set_type G)))

{` lem:allgpsarepermutationgps (Cayley). `}
def blind_cayley : Type ≔ (G : Group) → BlindIsMono G (permutation_group (blind_usym_set_type G)) (blind_rho G)

{` Remark (actions.tex 2596): Bρ_G is a covering. `}
def blind_cayley_covering : Type
  ≔ (G : Group) → IsCovering (BlindBG G) (BlindBG (permutation_group (blind_usym_set_type G))) (blind_rho_B G)

{` rem:CayleyOversize. PP(z) ≔ (princ G(z) = princ G(z)). `}
def blind_PP (G : Group) : BlindGSet G
  ≔ z ↦ (Id SetTypes (blind_princ G z) (blind_princ G z), sets_groupoid (blind_princ G z) (blind_princ G z))

{` rem:CayleyOversize: USym Σ₃ has 6 elements; Bρ_G = ev_{sh_G} ∘ P_-; (princ G = princ G) ≃ (PP)^{hG}. `}
def blind_CayleyOversize : Type
  ≔ Product (Σ (IsFiniteGroup (symmetric_group three))
                (h ↦ Id Nat (group_card (symmetric_group three) h) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
    (Product ((G : Group) (z : BlindBG G) → Id SetTypes (blind_rho_B G z .fst) (blind_pathsp G z (shape G)))
       ((G : Group) → Equiv (Id (BlindGSet G) (blind_princ G) (blind_princ G)) (BlindInvariantMaps G (blind_PP G))))

{` The permutation of USym G underlying π : PP(sh_G). `}
def blind_PP_apply (G : Group) (π : blind_PP G (shape G) .fst) (g : USym G) : USym G
  ≔ transport Type (A ↦ A) (USym G) (USym G) (π .fst) g

{` xca:PP-fixed-permutations: π is fixed iff π(g g') = g π(g'). `}
def blind_PP_fixed_char : Type
  ≔ (G : Group) (π : blind_PP G (shape G) .fst)
    → BlindIff (BlindFixed G (blind_PP G) π)
        ((g g' : USym G) → Id (USym G) (blind_PP_apply G π (usym_mul G g g')) (usym_mul G g (blind_PP_apply G π g')))

{` xca:PP-fixed-permutations, literal: evaluation at refl is a bijection from the fixed permutations to USym G
   and is multiplicative for composition (π₁ ∘ π₂ = concat π₂ π₁). `}
def blind_PP_fixed_group : Type
  ≔ (G : Group)
    → Product
        (BookIsEquiv (Σ (blind_PP G (shape G) .fst) (π ↦ BlindFixed G (blind_PP G) π)) (USym G)
           (u ↦ blind_PP_apply G (u .fst) (refl (shape G))))
        ((π₁ π₂ : blind_PP G (shape G) .fst) (h₁ : BlindFixed G (blind_PP G) π₁) (h₂ : BlindFixed G (blind_PP G) π₂)
         → Id (USym G)
             (blind_PP_apply G (concat SetTypes (blind_princ G (shape G)) (blind_princ G (shape G)) (blind_princ G (shape G)) π₂ π₁) (refl (shape G)))
             (usym_mul G (blind_PP_apply G π₁ (refl (shape G))) (blind_PP_apply G π₂ (refl (shape G)))))

{` xca:PP-fixed-permutations, corrected: fixed permutations are right multiplications, so evaluation at refl reverses
   the order of composition (an anti-isomorphism; g ↦ g⁻¹ after evaluation is an isomorphism). `}
def blind_PP_fixed_group_corrected : Type
  ≔ (G : Group)
    → Product
        (BookIsEquiv (Σ (blind_PP G (shape G) .fst) (π ↦ BlindFixed G (blind_PP G) π)) (USym G)
           (u ↦ blind_PP_apply G (u .fst) (refl (shape G))))
        ((π₁ π₂ : blind_PP G (shape G) .fst) (h₁ : BlindFixed G (blind_PP G) π₁) (h₂ : BlindFixed G (blind_PP G) π₂)
         → Id (USym G)
             (blind_PP_apply G (concat SetTypes (blind_princ G (shape G)) (blind_princ G (shape G)) (blind_princ G (shape G)) π₂ π₁) (refl (shape G)))
             (usym_mul G (blind_PP_apply G π₂ (refl (shape G))) (blind_PP_apply G π₁ (refl (shape G)))))

{` exa:prep-burnside. The underlying set of the C₄-set is 4 → 2. `}
def blind_c4_underlying : Type
  ≔ Id Type (blind_underlying_set blind_C4 blind_c4_set) (Fin blind_four → Fin two)

{` exa:prep-burnside: s^k acts by rotating sequences: (s^k · f)(a) = f(s^{-k}(a)). `}
def blind_c4_rotation : Type
  ≔ (k : Int) (f : Fin blind_four → Fin two) (a : Fin blind_four)
    → Id (Fin two) (blind_usym_act blind_C4 blind_c4_set (cycle_group_power (finite_fin_cycle three) k) f a)
        (f (permutation_power (Fin blind_four) (finite_fin_successor three) (int_neg k) a))

{` exa:prep-burnside: six orbits. `}
def blind_c4_six_orbits : Type
  ≔ Σ (IsFinite (BlindOrbits blind_C4 blind_c4_set))
      (h ↦ Id Nat (cardinality (BlindOrbits blind_C4 blind_c4_set) h) blind_six)

{` exa:prep-burnside: Card(C₄ · x) × Card((C₄)_x) = 4 for every x. `}
def blind_c4_orbit_times_stabilizer : Type
  ≔ (τ : BlindOrbitWitness blind_C4 blind_c4_set) (f : Fin blind_four → Fin two)
    (h₁ : IsFinite (BlindOrbitSet blind_C4 blind_c4_set τ f)) (h₂ : IsFiniteGroup (blind_stabilizer blind_C4 blind_c4_set f))
    → Id Nat (mul (cardinality (BlindOrbitSet blind_C4 blind_c4_set τ f) h₁) (group_card (blind_stabilizer blind_C4 blind_c4_set f) h₂))
        blind_four

{` lem:burnside: X^g ≔ {x : X(sh_G) | g · x = x}. `}
def BlindFixedBy (G : Group) (X : BlindGSet G) (g : USym G) : Type
  ≔ Σ (X (shape G) .fst) (x ↦ Id (X (shape G) .fst) (blind_usym_act G X g x) x)

{` exa:prep-burnside: there are 24 pairs (g, x) with g · x = x. `}
def blind_c4_24_pairs : Type
  ≔ Σ (IsFinite (Σ (USym blind_C4) (g ↦ BlindFixedBy blind_C4 blind_c4_set g)))
      (h ↦ Id Nat (cardinality (Σ (USym blind_C4) (g ↦ BlindFixedBy blind_C4 blind_c4_set g)) h)
             (mul blind_six blind_four))

{` lem:burnside. `}
def blind_burnside : Type
  ≔ (G : Group) (hG : IsFiniteGroup G) (X : BlindGSet G) (hX : BlindIsFiniteGSet G X)
    → Σ ((g : USym G) → IsFinite (BlindFixedBy G X g)) (_ ↦
      Σ (IsFinite (Σ (USym G) (g ↦ BlindFixedBy G X g))) (h₂ ↦
      Σ (IsFinite (BlindOrbits G X)) (h₃ ↦
        Id Nat (cardinality (Σ (USym G) (g ↦ BlindFixedBy G X g)) h₂) (mul (cardinality (BlindOrbits G X) h₃) (group_card G hG)))))

{` Fermat's little theorem. `}
def blind_pow (n k : Nat) : Nat ≔ match k [ zero. ↦ suc. zero. | suc. k ↦ mul (blind_pow n k) n ]

def blind_monus (m n : Nat) : Nat ≔ match m, n [
  | zero., _ ↦ zero.
  | suc. m, zero. ↦ suc. m
  | suc. m, suc. n ↦ blind_monus m n ]

def BlindIsPrime (p : Nat) : Type
  ≔ Product (Lt (suc. zero.) p) ((d : Nat) → NatDivides d p → Sum (Id Nat d (suc. zero.)) (Id Nat d p))

{` Litmus checks for the arithmetic helpers: 2³ = 8 and 8 ∸ 2 = 6. `}
def blind_pow_litmus : Id Nat (blind_pow two three) (suc. (suc. blind_six)) ≔ refl _
def blind_monus_litmus : Id Nat (blind_monus (blind_pow two three) two) blind_six ≔ refl _

def blind_fermat : Type ≔ (p : Nat) (hp : BlindIsPrime p) (n : Nat) → NatDivides p (blind_monus (blind_pow n p) n)
