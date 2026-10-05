export "02-abstract"
export "../../../src/174-cyclic-permutations"

{` Blind statements, chapter 4, section "Homomorphisms". `}

{` rem:homom-eqs (with the pointing path refl, i.e. H pointed at k(sh_G)):
   ap k preserves refl, inverses and composition. `}
def blind_rem_homom_eqs : Type
  ≔ (G : BlindGroup) (B : Type) (k : blind_B G .fst → B) →
    let A ≔ blind_B G .fst in
    let s ≔ blind_shape G in
    let f ≔ map_path A B k s s in
    Product (Id (Id B (k s) (k s)) (f (refl s)) (refl (k s)))
      (Product ((g : Id A s s) → Id (Id B (k s) (k s)) (f (inverse A s s g)) (inverse B (k s) (k s) (f g)))
        ((g g' : Id A s s) → Id (Id B (k s) (k s)) (f (concat A s s s g g'))
          (concat B (k s) (k s) (k s) (f g) (f g'))))

{` def:grouphomomorphism. `}
def BlindHom (G H : BlindGroup) : Type ≔ Copy (BookPointedMap (blind_BG G) (blind_BG H))
def blind_mkhom (G H : BlindGroup) (k : BookPointedMap (blind_BG G) (blind_BG H)) : BlindHom G H ≔ copy. k
def blind_Bhom (G H : BlindGroup) (f : BlindHom G H) : BookPointedMap (blind_BG G) (blind_BG H)
  ≔ copy_value (BookPointedMap (blind_BG G) (blind_BG H)) f

{` def:loops-map: loops k (p) = k_pt^{-1} · ap k (p) · k_pt, i.e. first
   k_pt, then ap k p, then k_pt^{-1}; pointed via the inverse law. `}
def blind_loops_map (X Y : Pointed) (k : BookPointedMap X Y) (p : Loop X) : Loop Y
  ≔ let B ≔ Y .carrier in
    let b ≔ Y .point in
    let ka ≔ k .fst (X .point) in
    concat B b ka b (concat B b ka ka (k .snd) (map_path (X .carrier) B (k .fst) (X .point) (X .point) p))
      (inverse B b ka (k .snd))

def blind_loops_map_pt (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (Loop Y) (refl (Y .point)) (blind_loops_map X Y k (refl (X .point)))
  ≔ let B ≔ Y .carrier in
    let b ≔ Y .point in
    let ka ≔ k .fst (X .point) in
    inverse (Loop Y) (blind_loops_map X Y k (refl (X .point))) (refl b)
      (concat (Loop Y) (blind_loops_map X Y k (refl (X .point))) (concat B b ka b (k .snd) (inverse B b ka (k .snd))) (refl b)
        (map_path (Id B b ka) (Loop Y) (q ↦ concat B b ka b q (inverse B b ka (k .snd)))
          (concat B b ka ka (k .snd) (refl ka)) (k .snd) (concat_p1 B b ka (k .snd)))
        (concat_inverse_right B b ka (k .snd)))

def blind_loops_map_pointed (X Y : Pointed) (k : BookPointedMap X Y)
  : BookPointedMap (blind_loops X) (blind_loops Y)
  ≔ (blind_loops_map X Y k, blind_loops_map_pt X Y k)

{` rem:loops-map. `}
def blind_rem_loops_map_refl : Type
  ≔ (A B : Type) (a : A) (f : A → B) →
    Id (Id A a a → Id B (f a) (f a)) (blind_loops_map (A, a) (B, f a) (f, refl (f a))) (map_path A B f a a)

{` def:USym-hom. `}
def blind_usym_hom (G H : BlindGroup) (f : BlindHom G H) : BlindUSym G → BlindUSym H
  ≔ blind_loops_map (blind_BG G) (blind_BG H) (blind_Bhom G H f)

{` lem:grouphomomaxioms (also rem:first-abs-hom). `}
def blind_lem_grouphomomaxioms : Type
  ≔ (G H : BlindGroup) (f : BlindHom G H) →
    let u ≔ blind_usym_hom G H f in
    Product (Id (BlindUSym H) (u (blind_usym_unit G)) (blind_usym_unit H))
      (Product ((g : BlindUSym G) → Id (BlindUSym H) (u (blind_usym_inv G g)) (blind_usym_inv H (u g)))
        ((g g' : BlindUSym G) → Id (BlindUSym H) (u (blind_usym_mul G g' g)) (blind_usym_mul H (u g') (u g))))

{` def:groupisomorphism. `}
def BlindIsIso (G H : BlindGroup) (f : BlindHom G H) : Type
  ≔ BookIsEquiv (blind_B G .fst) (blind_B H .fst) (blind_Bhom G H f .fst)
def BlindIso (G H : BlindGroup) : Type ≔ Σ (BlindHom G H) (BlindIsIso G H)
def blind_iso_is_set : Type ≔ (G H : BlindGroup) → isSet (BlindIso G H)

{` def:identity-group-homomorphism. `}
def blind_id_hom (G : BlindGroup) : BlindHom G G ≔ blind_mkhom G G (book_pointed_identity (blind_BG G))
def blind_id_hom_is_iso : Type ≔ (G : BlindGroup) → BlindIsIso G G (blind_id_hom G)

{` remark:groupsasunivalenttype. `}
def blind_rem_groups_univalent : Type ≔ (G H : BlindGroup) → BookEquiv (Id BlindGroup G H) (BlindIso G H)

{` def:group-homomorphism-composition. `}
def blind_hom_compose (G G' G'' : BlindGroup) (f : BlindHom G G') (f' : BlindHom G' G'') : BlindHom G G''
  ≔ blind_mkhom G G'' (book_pointed_compose (blind_BG G) (blind_BG G') (blind_BG G'')
      (blind_Bhom G G' f) (blind_Bhom G' G'' f'))

{` rem:Bf-convention. `}
def blind_rem_bf_convention : Type
  ≔ (G H : BlindGroup) (T : BlindHom G H → Type) →
    BookIsEquiv ((f : BlindHom G H) → T f) ((k : BookPointedMap (blind_BG G) (blind_BG H)) → T (blind_mkhom G H k))
      (φ ↦ k ↦ φ (blind_mkhom G H k))

{` lem:hom-is-set. `}
def blind_lem_hom_is_set : Type ≔ (G H : BlindGroup) → isSet (BlindHom G H)

{` ex:groups-morphisms (1): - ⊔ T and - × T on components of Set. `}
def blind_set_sum (X T : SetTypes) : SetTypes ≔ (Sum (X .fst) (T .fst), sum_set (X .fst) (T .fst) (X .snd) (T .snd))
def blind_set_prod (X T : SetTypes) : SetTypes ≔ (Product (X .fst) (T .fst), product_set (X .fst) (T .fst) (X .snd) (T .snd))

def blind_component_map (A B : Type) (a : A) (f : A → B) (x : NativeComponent A a) : NativeComponent B (f a)
  ≔ (f (x .fst), mere_rec (Id A a (x .fst)) (Mere (Id B (f a) (f (x .fst)))) (mere_isprop (Id B (f a) (f (x .fst))))
      (p ↦ mere (Id B (f a) (f (x .fst))) (map_path A B f a (x .fst) p)) (x .snd))

def blind_hom_coprod (S T : SetTypes) : BlindHom (blind_SG_set S) (blind_SG_set (blind_set_sum S T))
  ≔ blind_mkhom (blind_SG_set S) (blind_SG_set (blind_set_sum S T))
      (blind_component_map SetTypes SetTypes S (X ↦ blind_set_sum X T), refl (blind_component_point SetTypes (blind_set_sum S T)))

def blind_hom_prod (S T : SetTypes) : BlindHom (blind_SG_set S) (blind_SG_set (blind_set_prod S T))
  ≔ blind_mkhom (blind_SG_set S) (blind_SG_set (blind_set_prod S T))
      (blind_component_map SetTypes SetTypes S (X ↦ blind_set_prod X T), refl (blind_component_point SetTypes (blind_set_prod S T)))

def blind_ex_fin_sum_identification : Type ≔ (m n : Nat) → Id Type (Fin (add m n)) (Sum (Fin m) (Fin n))
def blind_ex_fin_prod_identification : Type ≔ (m n : Nat) → Id Type (Fin (mul m n)) (Product (Fin m) (Fin n))

{` ex:groups-morphisms (2): unique homomorphisms to and from the trivial group. `}
def blind_ex_hom_to_trivial : Type ≔ (G : BlindGroup) → BookIsContr (BlindHom G blind_TG)
def blind_ex_hom_from_trivial : Type ≔ (G : BlindGroup) → BookIsContr (BlindHom blind_TG G)

{` ex:groups-morphisms (3): projections and inclusions. `}
def blind_hom_proj1 (G H : BlindGroup) : BlindHom (blind_group_product G H) G
  ≔ blind_mkhom (blind_group_product G H) G (u ↦ u .fst, refl (blind_shape G))
def blind_hom_proj2 (G H : BlindGroup) : BlindHom (blind_group_product G H) H
  ≔ blind_mkhom (blind_group_product G H) H (u ↦ u .snd, refl (blind_shape H))
def blind_hom_incl1 (G H : BlindGroup) : BlindHom G (blind_group_product G H)
  ≔ blind_mkhom G (blind_group_product G H) (z ↦ (z, blind_shape H), refl (blind_shape G, blind_shape H))
def blind_hom_incl2 (G H : BlindGroup) : BlindHom H (blind_group_product G H)
  ≔ blind_mkhom H (blind_group_product G H) (z ↦ (blind_shape G, z), refl (blind_shape G, blind_shape H))

{` ex:groups-morphisms (4): R_m : BZ → BS_m pointed by (the beta path
   replacing) refl classifies Z → S_m; it factors as mod_m : Z → C_m
   (base ↦ (bn m, s), loop ↦ the generating symmetry s) followed by the
   homomorphism C_m → S_m forgetting the cycle structure. `}
def blind_component_loop (A : Type) (a : A) (l : Id A a a)
  : Id (NativeComponent A a) (blind_component_point A a) (blind_component_point A a)
  ≔ subtype_equal A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x))
      (blind_component_point A a) (blind_component_point A a) l

def blind_circle_rec_pointing (C : CircleSignature) (A : Type) (d : FreeLoop A)
  : Id A (d .fst) (circle_rec C A d (C .base))
  ≔ inverse A (circle_rec C A d (C .base)) (d .fst) (circle_rec_beta C A d .fst)

def blind_Rm_hom (C : CircleSignature) (n : Nat) : BlindHom (blind_ZZ C) (blind_SG (suc. n))
  ≔ let A ≔ NativeComponent SetTypes (blind_bn_set (suc. n)) in
    let d : FreeLoop A ≔ (blind_component_point SetTypes (blind_bn_set (suc. n)),
      blind_component_loop SetTypes (blind_bn_set (suc. n)) (blind_set_loop (blind_bn_set (suc. n)) (finite_fin_successor n))) in
    blind_mkhom (blind_ZZ C) (blind_SG (suc. n)) (circle_rec C A d, blind_circle_rec_pointing C A d)

def blind_mod_m (C : CircleSignature) (n : Nat) : BlindHom (blind_ZZ C) (blind_CG n)
  ≔ let A ≔ NativeComponent Cycles (finite_fin_cycle n) in
    let d : FreeLoop A ≔ (blind_component_point Cycles (finite_fin_cycle n),
      blind_component_loop Cycles (finite_fin_cycle n) (cycle_generating_loop (finite_fin_cycle n))) in
    blind_mkhom (blind_ZZ C) (blind_CG n) (circle_rec C A d, blind_circle_rec_pointing C A d)

def blind_hom_forget_cycle (n : Nat) : BlindHom (blind_CG n) (blind_SG (suc. n))
  ≔ blind_mkhom (blind_CG n) (blind_SG (suc. n))
      (blind_component_map Cycles SetTypes (finite_fin_cycle n) (c ↦ c .fst .fst),
        refl (blind_component_point SetTypes (blind_bn_set (suc. n))))

def blind_ex_mod_m_factorization : Type
  ≔ (C : CircleSignature) (n : Nat) →
    Id (BlindHom (blind_ZZ C) (blind_SG (suc. n))) (blind_Rm_hom C n)
      (blind_hom_compose (blind_ZZ C) (blind_CG n) (blind_SG (suc. n)) (blind_mod_m C n) (blind_hom_forget_cycle n))

{` Remark after ex:groups-morphisms: (id, refl) and (id, tau) are different
   endomorphisms of S_3, tau the transposition (0 1); loops of (id, tau)
   is conjugation sigma ↦ tau^{-1} sigma tau. `}
def blind_fin3_zero : Fin blind_three ≔ inl. (inl. (inr. star.))
def blind_fin3_one : Fin blind_three ≔ inl. (inr. star.)
def blind_tau3 : Equiv (Fin blind_three) (Fin blind_three)
  ≔ transposition_equiv (Fin blind_three) (fin_decidable_equality blind_three) blind_fin3_zero blind_fin3_one

def blind_tau3_path
  : Id (NativeComponent SetTypes (blind_bn_set blind_three))
      (blind_component_point SetTypes (blind_bn_set blind_three)) (blind_component_point SetTypes (blind_bn_set blind_three))
  ≔ blind_component_loop SetTypes (blind_bn_set blind_three) (blind_set_loop (blind_bn_set blind_three) blind_tau3)

def blind_tau_tilde : BlindHom (blind_SG blind_three) (blind_SG blind_three)
  ≔ blind_mkhom (blind_SG blind_three) (blind_SG blind_three)
      (identity (NativeComponent SetTypes (blind_bn_set blind_three)), blind_tau3_path)

def blind_rem_id_ne_tau : Type
  ≔ Not (Id (BlindHom (blind_SG blind_three) (blind_SG blind_three)) (blind_id_hom (blind_SG blind_three)) blind_tau_tilde)

def blind_rem_tau_conjugation : Type
  ≔ let A ≔ NativeComponent SetTypes (blind_bn_set blind_three) in
    let s ≔ blind_component_point SetTypes (blind_bn_set blind_three) in
    (σ : BlindUSym (blind_SG blind_three)) →
      Id (BlindUSym (blind_SG blind_three)) (blind_usym_hom (blind_SG blind_three) (blind_SG blind_three) blind_tau_tilde σ)
        (concat A s s s (concat A s s s blind_tau3_path σ) (inverse A s s blind_tau3_path))

{` def:loops-compose. `}
def blind_loops_compose : Type
  ≔ (X Y Z : Pointed) (f : BookPointedMap X Y) (g : BookPointedMap Y Z) →
    Id (Loop X → Loop Z) (blind_loops_map X Z (book_pointed_compose X Y Z f g))
      (p ↦ blind_loops_map Y Z g (blind_loops_map X Y f p))

{` cor:USym-compose. `}
def blind_cor_usym_compose : Type
  ≔ (G H K : BlindGroup) (φ : BlindHom G H) (ψ : BlindHom H K) →
    Id (BlindUSym G → BlindUSym K) (blind_usym_hom G K (blind_hom_compose G H K φ ψ))
      (g ↦ blind_usym_hom H K ψ (blind_usym_hom G H φ g))

{` ex:Zinitial: ev_BG(f) = loops f (loop) is an equivalence. `}
def blind_ev (C : CircleSignature) (G : BlindGroup) (f : BookPointedMap (circle_pointed C) (blind_BG G)) : BlindUSym G
  ≔ blind_loops_map (circle_pointed C) (blind_BG G) f (C .loop)
def blind_ex_Zinitial : Type
  ≔ (C : CircleSignature) (G : BlindGroup) →
    BookIsEquiv (BookPointedMap (circle_pointed C) (blind_BG G)) (BlindUSym G) (blind_ev C G)

{` lem:Znatural. `}
def blind_ev_hom (C : CircleSignature) (G : BlindGroup) (u : BlindHom (blind_ZZ C) G) : BlindUSym G
  ≔ blind_usym_hom (blind_ZZ C) G u (C .loop)
def blind_lem_Znatural : Type
  ≔ (C : CircleSignature) (G H : BlindGroup) (f : BlindHom G H) (u : BlindHom (blind_ZZ C) G) →
    Id (BlindUSym H) (blind_ev_hom C H (blind_hom_compose (blind_ZZ C) G H u f))
      (blind_usym_hom G H f (blind_ev_hom C G u))

{` xca:BGtotype. `}
def blind_xca_BGtotype : Type
  ≔ (G : BlindGroup) (A : Type) (hA : isGroupoid A) →
    let X ≔ blind_B G .fst in
    let T1 ≔ X → A in
    let T2 ≔ Σ A (a ↦ Σ (X → A) (f ↦ Id A a (f (blind_shape G)))) in
    let T3 ≔ Σ A (a ↦ BookPointedMap (blind_BG G) (A, a)) in
    let T4 ≔ Σ A (a ↦ BlindHom G (blind_Aut A hA a)) in
    Product (BookEquiv T1 T2) (Product (BookEquiv T2 T3) (BookEquiv T3 T4))

{` exa:conj-concrete. `}
def blind_regroup (G : BlindGroup) (y : blind_B G .fst) : BlindGroup
  ≔ blind_mkgroup (blind_B G .fst, (y, blind_B G .snd .snd))

def blind_conj_map (G : BlindGroup) (y : blind_B G .fst) (p : Id (blind_B G .fst) (blind_shape G) y)
  : BookPointedMap (blind_BG G) (blind_BG (blind_regroup G y))
  ≔ (identity (blind_B G .fst), inverse (blind_B G .fst) (blind_shape G) y p)

def blind_exa_conj_iso : Type
  ≔ (G : BlindGroup) (y : blind_B G .fst) (p : Id (blind_B G .fst) (blind_shape G) y) →
    BlindIsIso G (blind_regroup G y) (blind_mkhom G (blind_regroup G y) (blind_conj_map G y p))
def blind_exa_conj_identification : Type
  ≔ (G : BlindGroup) (y : blind_B G .fst) → Id (blind_B G .fst) (blind_shape G) y → Id BlindGroup G (blind_regroup G y)
def blind_exa_conj_formula : Type
  ≔ (G : BlindGroup) (y : blind_B G .fst) (p : Id (blind_B G .fst) (blind_shape G) y) →
    let A ≔ blind_B G .fst in
    let s ≔ blind_shape G in
    Id (BlindUSym G → Id A y y)
      (blind_usym_hom G (blind_regroup G y) (blind_mkhom G (blind_regroup G y) (blind_conj_map G y p)))
      (g ↦ concat A y s y (inverse A s y p) (concat A s s y g p))

{` def:inner-autos, parametrized by the groupoid property of Group
   (needed for Aut(G)). The proposition ||G = mkgroup(BG, y)|| is proved
   from connectedness of BG. `}
def blind_inn_merely (X : BlindPtConnGroupoid) (y : X .fst)
  : Mere (Id BlindGroup (blind_mkgroup X) (blind_mkgroup (X .fst, (y, X .snd .snd))))
  ≔ let A ≔ X .fst in
    let T ≔ Id BlindGroup (blind_mkgroup X) (blind_mkgroup (X .fst, (y, X .snd .snd))) in
    mere_rec (Id A (X .snd .fst) y) (Mere T) (mere_isprop T)
      (p ↦ mere T (map_path A BlindGroup (z ↦ blind_mkgroup (X .fst, (z, X .snd .snd))) (X .snd .fst) y p))
      (X .snd .snd .fst .snd (X .snd .fst) y)

def blind_inn (h : blind_xca_typegroup_groupoid) (G : BlindGroup) : BlindHom G (blind_AutGroup h G)
  ≔ match G [
  | copy. X ↦
    blind_mkhom (blind_mkgroup X) (blind_AutGroup h (blind_mkgroup X))
      (y ↦ (blind_mkgroup (X .fst, (y, X .snd .snd)), blind_inn_merely X y),
        subtype_equal BlindGroup (K ↦ Mere (Id BlindGroup (blind_mkgroup X) K))
          (K ↦ mere_isprop (Id BlindGroup (blind_mkgroup X) K))
          (blind_component_point BlindGroup (blind_mkgroup X))
          (blind_mkgroup X, blind_inn_merely X (X .snd .fst))
          (refl (blind_mkgroup X))) ]
