export "bridge-00-core"
export "../../../src/422-wedge-abelian-groups"

{` Bridges bridge for rem:whatAREabeliangroups (line 759), blind file
   01-groups.ny. The blind reads a factorization of the fold map through
   BG ∨ BG → BG × BG by the universal property of the wedge: m with
   m(x, sh) = x, m(sh, y) = y agreeing at (sh, sh). Ours (module 422) is
   parametrized by a wedge signature, of which no inhabitant exists, so
   the blind statement is proved directly from our tools:
   - ⇐: our abelian_endomap_section (x ↦ m(x, -) as pointed maps) with
     abelian_endomap_section_beta, through the translation fromT below;
   - ⇒: Eckmann–Hilton with our naturality lemma;
   - proposition: the factorizations are a retract (on all but a
     propositional component) of the type T of sections σ of the set family
     x ↦ (BG, sh) →* (BG, x) with σ(sh) = id, which is a proposition because
     BG is connected. `}

def bridge_interchange (A : Type) (f : A → A → A) (a a' : A) (g : Id A a a') (b b' : A) (h : Id A b b')
  : Id (Id A (f a b) (f a' b'))
      (concat A (f a b) (f a' b) (f a' b') (refl ((x ↦ f x b) : A → A) g) (refl (f a') h))
      (concat A (f a b) (f a b') (f a' b') (refl (f a) h) (refl ((x ↦ f x b') : A → A) g))
  ≔ J A a (a' g ↦ Id (Id A (f a b) (f a' b'))
        (concat A (f a b) (f a' b) (f a' b') (refl ((x ↦ f x b) : A → A) g) (refl (f a') h))
        (concat A (f a b) (f a b') (f a' b') (refl (f a) h) (refl ((x ↦ f x b') : A → A) g)))
      (concat (Id A (f a b) (f a b')) (concat A (f a b) (f a b) (f a b') (refl (f a b)) (refl (f a) h)) (refl (f a) h)
        (concat A (f a b) (f a b') (f a b') (refl (f a) h) (refl (f a b')))
        (concat_1p A (f a b) (f a b') (refl (f a) h))
        (inverse (Id A (f a b) (f a b')) (concat A (f a b) (f a b') (f a b') (refl (f a) h) (refl (f a b'))) (refl (f a) h)
          (concat_p1 A (f a b) (f a b') (refl (f a) h))))
      a' g

{` ⇒ (Eckmann–Hilton). `}
def bridge_fold_abelian (G : BlindGroup) (F : BlindAbFoldFactorization G) : BlindIsAb G
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let m ≔ F .fst in let l ≔ F .snd .fst in let r ≔ F .snd .snd .fst in let c ≔ F .snd .snd .snd in
    let w ≔ m s s in
    let k ≔ l s in
    let L ≔ Id A w s in
    g h ↦
    let P ≔ refl ((x ↦ m x s) : A → A) g in
    let Q ≔ refl (m s) h in
    let N1 : Id L (concat A w w s P k) (concat A w s s k g)
      ≔ naturality A A (x ↦ m x s) (identity A) l s s g in
    let N2r : Id L (concat A w w s Q (r s)) (concat A w s s (r s) h)
      ≔ naturality A A (m s) (identity A) r s s h in
    let N2 : Id L (concat A w w s Q k) (concat A w s s k h)
      ≔ transport L (t ↦ Id L (concat A w w s Q t) (concat A w s s t h)) (r s) k (inverse L k (r s) c) N2r in
    let I : Id (Id A w w) (concat A w w w P Q) (concat A w w w Q P)
      ≔ bridge_interchange A m s s g s s h in
    let chain : Id L (concat A w s s k (concat A s s s g h)) (concat A w s s k (concat A s s s h g))
      ≔ calc
        concat A w s s k (concat A s s s g h)
        = concat A w s s (concat A w s s k g) h by inverse L (concat A w s s (concat A w s s k g) h) (concat A w s s k (concat A s s s g h)) (concat_assoc A w s s s k g h)
        = concat A w s s (concat A w w s P k) h by refl ((t ↦ concat A w s s t h) : L → L) (inverse L (concat A w w s P k) (concat A w s s k g) N1)
        = concat A w w s P (concat A w s s k h) by concat_assoc A w w s s P k h
        = concat A w w s P (concat A w w s Q k) by refl (concat A w w s P) (inverse L (concat A w w s Q k) (concat A w s s k h) N2)
        = concat A w w s (concat A w w w P Q) k by inverse L (concat A w w s (concat A w w w P Q) k) (concat A w w s P (concat A w w s Q k)) (concat_assoc A w w w s P Q k)
        = concat A w w s (concat A w w w Q P) k by refl ((t ↦ concat A w w s t k) : Id A w w → L) I
        = concat A w w s Q (concat A w w s P k) by concat_assoc A w w w s Q P k
        = concat A w w s Q (concat A w s s k g) by refl (concat A w w s Q) N1
        = concat A w s s (concat A w w s Q k) g by inverse L (concat A w s s (concat A w w s Q k) g) (concat A w w s Q (concat A w s s k g)) (concat_assoc A w w s s Q k g)
        = concat A w s s (concat A w s s k h) g by refl ((t ↦ concat A w s s t g) : L → L) N2
        = concat A w s s k (concat A s s s h g) by concat_assoc A w s s s k h g ∎ in
    inverse (Id A s s) (concat A s s s g h) (concat A s s s h g)
      (concat_cancel_left A w s s k (concat A s s s g h) (concat A s s s h g) chain)

{` The type T and the translations. `}
def BridgePM (G : BlindGroup) (x : blind_B G .fst) : Type ≔ BookPointedMap (blind_BG G) (blind_B G .fst, x)

def BridgeFoldT (G : BlindGroup) : Type
  ≔ Σ ((x : blind_B G .fst) → BridgePM G x)
      (σ ↦ Id (BridgePM G (blind_shape G)) (σ (blind_shape G)) (identity (blind_B G .fst), refl (blind_shape G)))

def bridge_pm_set (G : BlindGroup) (x : blind_B G .fst) : isSet (BridgePM G x)
  ≔ pointed_maps_set (blind_BG G) (blind_B G .fst, x) (blind_B G .snd .snd .fst) (blind_B G .snd .snd .snd)

def bridge_fold_T_prop (G : BlindGroup) : isProp (BridgeFoldT G)
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let idpt : BridgePM G s ≔ (identity A, refl s) in
    u v ↦ subtype_equal ((x : A) → BridgePM G x) (σ ↦ Id (BridgePM G s) (σ s) idpt)
      (σ ↦ bridge_pm_set G s (σ s) idpt) u v
      (funext A (x ↦ BridgePM G x) (u .fst) (v .fst)
        (x ↦ mere_rec (Id A s x) (Id (BridgePM G x) (u .fst x) (v .fst x)) (bridge_pm_set G x (u .fst x) (v .fst x))
          (p ↦ transport A (z ↦ Id (BridgePM G z) (u .fst z) (v .fst z)) s x p
            (concat (BridgePM G s) (u .fst s) idpt (v .fst s) (u .snd) (inverse (BridgePM G s) (v .fst s) idpt (v .snd))))
          (blind_B G .snd .snd .fst .snd s x)))

def bridge_inverse_from_unit (A : Type) (s w : A) (p : Id A s w) (e : Id A w s)
  (E : Id (Id A s s) (concat A s w s p e) (refl s)) : Id (Id A w s) (inverse A s w p) e
  ≔ calc
      inverse A s w p = concat A w s s (inverse A s w p) (refl s) by inverse (Id A w s) (concat A w s s (inverse A s w p) (refl s)) (inverse A s w p) (concat_p1 A w s (inverse A s w p))
      = concat A w s s (inverse A s w p) (concat A s w s p e) by refl (concat A w s s (inverse A s w p)) (inverse (Id A s s) (concat A s w s p e) (refl s) E)
      = concat A w w s (concat A w s w (inverse A s w p) p) e by inverse (Id A w s) (concat A w w s (concat A w s w (inverse A s w p) p) e) (concat A w s s (inverse A s w p) (concat A s w s p e)) (concat_assoc A w s w s (inverse A s w p) p e)
      = concat A w w s (refl w) e by refl ((t ↦ concat A w w s t e) : Id A w w → Id A w s) (concat_inverse_left A s w p)
      = e by concat_1p A w s e ∎

def bridge_fold_from_T (G : BlindGroup) (t : BridgeFoldT G) : BlindAbFoldFactorization G
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let σ ≔ t .fst in
    let PH ≔ pointed_map_path_equiv (blind_BG G) (blind_BG G) (σ s) (identity A, refl s) .map (t .snd) in
    (x y ↦ σ x .fst y,
     (x ↦ inverse A x (σ x .fst s) (σ x .snd),
      (y ↦ PH .fst y,
       bridge_inverse_from_unit A s (σ s .fst s) (σ s .snd) (PH .fst s) (PH .snd))))

def bridge_fold_coh (G : BlindGroup) (F : BlindAbFoldFactorization G)
  : let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let m ≔ F .fst in let l ≔ F .snd .fst in let r ≔ F .snd .snd .fst in
    PointedHomotopy (blind_BG G) (blind_BG G) (m s, inverse A (m s s) s (l s)) (identity A, refl s)
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let m ≔ F .fst in let l ≔ F .snd .fst in let r ≔ F .snd .snd .fst in let c ≔ F .snd .snd .snd in
    (r, concat (Id A s s) (concat A s (m s s) s (inverse A (m s s) s (l s)) (r s))
          (concat A s (m s s) s (inverse A (m s s) s (l s)) (l s)) (refl s)
          (refl (concat A s (m s s) s (inverse A (m s s) s (l s))) (inverse (Id A (m s s) s) (l s) (r s) c))
          (concat_inverse_left A (m s s) s (l s)))

def bridge_fold_to_T (G : BlindGroup) (F : BlindAbFoldFactorization G) : BridgeFoldT G
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let m ≔ F .fst in let l ≔ F .snd .fst in
    let f0 : BridgePM G s ≔ (m s, inverse A (m s s) s (l s)) in
    (x ↦ (m x, inverse A (m x s) x (l x)),
     equiv_inverse_map (Id (BridgePM G s) f0 (identity A, refl s))
       (PointedHomotopy (blind_BG G) (blind_BG G) f0 (identity A, refl s))
       (pointed_map_path_equiv (blind_BG G) (blind_BG G) f0 (identity A, refl s))
       (bridge_fold_coh G F))

{` The factorization without its last (propositional) component. `}
def BridgeFoldQ (G : BlindGroup) : Type
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    Σ (A → A → A) (m ↦ Σ ((x : A) → Id A (m x s) x) (_ ↦ (y : A) → Id A (m s y) y))

def bridge_fold_q (G : BlindGroup) (F : BlindAbFoldFactorization G) : BridgeFoldQ G
  ≔ (F .fst, (F .snd .fst, F .snd .snd .fst))

def bridge_fold_q_retract (G : BlindGroup) (F : BlindAbFoldFactorization G)
  : Id (BridgeFoldQ G) (bridge_fold_q G (bridge_fold_from_T G (bridge_fold_to_T G F))) (bridge_fold_q G F)
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let m ≔ F .fst in let l ≔ F .snd .fst in let r ≔ F .snd .snd .fst in
    let f0 : BridgePM G s ≔ (m s, inverse A (m s s) s (l s)) in
    let E ≔ pointed_map_path_equiv (blind_BG G) (blind_BG G) f0 (identity A, refl s) in
    let PHt ≔ bridge_fold_to_T G F .snd in
    (refl m,
     (funext A (x ↦ Id A (m x s) x) (x ↦ inverse A x (m x s) (inverse A (m x s) x (l x))) l
        (x ↦ inverse_inverse A (m x s) x (l x)),
      refl ((u ↦ u .fst) : PointedHomotopy (blind_BG G) (blind_BG G) f0 (identity A, refl s) → (y : A) → Id A (m s y) y)
        (equiv_counit (Id (BridgePM G s) f0 (identity A, refl s))
          (PointedHomotopy (blind_BG G) (blind_BG G) f0 (identity A, refl s)) E
          (bridge_fold_coh G F))))

def BridgeFoldC (G : BlindGroup) (q : BridgeFoldQ G) : Type
  ≔ Id (Id (blind_B G .fst) (q .fst (blind_shape G) (blind_shape G)) (blind_shape G))
      (q .snd .fst (blind_shape G)) (q .snd .snd (blind_shape G))

def bridge_fold_prop (G : BlindGroup) : isProp (BlindAbFoldFactorization G)
  ≔ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    let QT ≔ BridgeFoldQ G in
    let fT : BridgeFoldT G → QT ≔ t ↦ bridge_fold_q G (bridge_fold_from_T G t) in
    F F' ↦
    let qq : Id QT (bridge_fold_q G F) (bridge_fold_q G F')
      ≔ concat QT (bridge_fold_q G F) (fT (bridge_fold_to_T G F)) (bridge_fold_q G F')
          (inverse QT (fT (bridge_fold_to_T G F)) (bridge_fold_q G F) (bridge_fold_q_retract G F))
          (concat QT (fT (bridge_fold_to_T G F)) (fT (bridge_fold_to_T G F')) (bridge_fold_q G F')
            (refl fT (bridge_fold_T_prop G (bridge_fold_to_T G F) (bridge_fold_to_T G F')))
            (bridge_fold_q_retract G F')) in
    refl ((u ↦ (u .fst .fst, (u .fst .snd .fst, (u .fst .snd .snd, u .snd)))) : Σ QT (BridgeFoldC G) → BlindAbFoldFactorization G)
      (subtype_equal QT (BridgeFoldC G)
        (q ↦ blind_B G .snd .snd .snd (q .fst s s) s (q .snd .fst s) (q .snd .snd s))
        (bridge_fold_q G F, F .snd .snd .snd) (bridge_fold_q G F', F' .snd .snd .snd) qq)

def bridge_rem_abelian_fold : blind_rem_abelian_fold
  ≔ G ↦ (bridge_fold_prop G,
      (bridge_fold_abelian G,
       hab ↦ bridge_fold_from_T G (abelian_endomap_section (bridge_g G) hab, abelian_endomap_section_beta (bridge_g G) hab)))
