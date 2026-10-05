export "bridge-00-core"
export "05-bicycles"
export "../../../src/484-bicycle-text-claims"

{` Bridges for group.tex, section "Bicycles" (blind file
   05-bicycles.ny). The blind meaning [ℓ] (blind_sem) is defined on
   underlying maps with the function after the match; ours
   (bicycle_meaning_map) takes the point as an argument. They agree
   pointwise by list induction (bridge_sem), so the bicycle conditions are
   logically equivalent propositions and BlindBicycles ≃ Bicycles with
   refl on carrier, a and b. The blind evaluation of a symmetry is ours
   on the nose after applying the equivalence to the path. `}

def bridge_sem (X : Type) (a b : Equiv X X) (l : BlindZZList) (x : X)
  : Id X (blind_sem X a b l x) (bicycle_meaning_map X a b l x)
  ≔ match l [
  | nil. ↦ refl x
  | cons. h t ↦ match h [
    | inl. n ↦ refl (permutation_power X a n) (bridge_sem X a b t x)
    | inr. n ↦ refl (permutation_power X b n) (bridge_sem X a b t x) ] ]

def bridge_str_to (X : SetTypes) (a b : Equiv (X .fst) (X .fst)) (s : BlindBicycleStr X a b)
  : BicycleConnected (X .fst) a b
  ≔ (s .fst, x x' ↦
      mere_rec (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x)))
        (Mere (BicycleWordFrom (X .fst) a b x x')) (mere_isprop (BicycleWordFrom (X .fst) a b x x'))
        (u ↦ mere (BicycleWordFrom (X .fst) a b x x')
          (u .fst, concat (X .fst) x' (blind_sem (X .fst) a b (u .fst) x) (bicycle_meaning_map (X .fst) a b (u .fst) x)
            (u .snd) (bridge_sem (X .fst) a b (u .fst) x)))
        (s .snd x x'))

def bridge_str_from (X : SetTypes) (a b : Equiv (X .fst) (X .fst)) (s : BicycleConnected (X .fst) a b)
  : BlindBicycleStr X a b
  ≔ (s .fst, x x' ↦
      mere_rec (BicycleWordFrom (X .fst) a b x x')
        (Mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))
        (mere_isprop (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))
        (u ↦ mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x)))
          (u .fst, concat (X .fst) x' (bicycle_meaning_map (X .fst) a b (u .fst) x) (blind_sem (X .fst) a b (u .fst) x)
            (u .snd) (inverse (X .fst) (blind_sem (X .fst) a b (u .fst) x) (bicycle_meaning_map (X .fst) a b (u .fst) x)
              (bridge_sem (X .fst) a b (u .fst) x))))
        (s .snd x x'))

{` def:bicycle (line 1881). `}
def bridge_bic (B : BlindBicycles) : Bicycles
  ≔ (B .fst, (B .snd .fst, (B .snd .snd .fst, bridge_str_to (B .fst) (B .snd .fst) (B .snd .snd .fst) (B .snd .snd .snd))))

def bridge_bic_inv (B : Bicycles) : BlindBicycles
  ≔ (B .fst, (B .snd .fst, (B .snd .snd .fst, bridge_str_from (B .fst) (B .snd .fst) (B .snd .snd .fst) (B .snd .snd .snd))))

def bridge_def_bicycles : Equiv BlindBicycles Bicycles
  ≔ quasi_inverse_equiv BlindBicycles Bicycles bridge_bic bridge_bic_inv
      (B ↦ (refl (B .fst), (refl (B .snd .fst), (refl (B .snd .snd .fst),
        blind_bicycle_str_prop (B .fst) (B .snd .fst) (B .snd .snd .fst) (bridge_bic_inv (bridge_bic B) .snd .snd .snd)
          (B .snd .snd .snd)))))
      (B ↦ (refl (B .fst), (refl (B .snd .fst), (refl (B .snd .snd .fst),
        bicycle_connected_prop (B .fst .fst) (B .snd .fst) (B .snd .snd .fst) (bridge_bic (bridge_bic_inv B) .snd .snd .snd)
          (B .snd .snd .snd)))))

def bridge_def_bicycle_str (X : SetTypes) (a b : Equiv (X .fst) (X .fst))
  : Product (BlindBicycleStr X a b → BicycleConnected (X .fst) a b) (BicycleConnected (X .fst) a b → BlindBicycleStr X a b)
  ≔ (bridge_str_to X a b, bridge_str_from X a b)

def bridge_bicycle_paths (B B' : BlindBicycles) : Equiv (Id BlindBicycles B B') (Id Bicycles (bridge_bic B) (bridge_bic B'))
  ≔ equivalence_on_paths BlindBicycles Bicycles bridge_def_bicycles B B'

def bridge_bicycle_ev (B B' : BlindBicycles) (x0 : B .fst .fst) (e : Id BlindBicycles B B')
  : Id (B' .fst .fst) (blind_bicycle_ev B B' x0 e)
      (bicycle_path_evaluate (bridge_bic B) (bridge_bic B') (refl bridge_bic e) x0)
  ≔ refl (blind_bicycle_ev B B' x0 e)

{` BookIsEquiv along precomposition with an equivalence. `}
def bridge_isequiv_precompose (A B C : Type) (P : Equiv A B) (g : B → C) (h : BookIsEquiv B C g)
  : BookIsEquiv A C (a ↦ g (P .map a))
  ≔ book_equivalence A C (compose_equiv A B C P (native_equivalence B C (g, h))) .equiv

def bridge_isequiv_cancel (A B C : Type) (P : Equiv A B) (g : B → C) (h : BookIsEquiv A C (a ↦ g (P .map a)))
  : BookIsEquiv B C g
  ≔ book_equivalence B C
      (equiv_change_map B C
        (compose_equiv B A C (canonical_inverse_equiv A B P) (native_equivalence A C (a ↦ g (P .map a), h))) g
        (b ↦ refl g (equiv_counit A B P b))) .equiv

{` def:normal-bicycle (line 2101). `}
def bridge_normal_to (B : BlindBicycles) (hn : BlindNormalBicycle B) : IsNormalBicycle (bridge_bic B)
  ≔ x ↦ bridge_isequiv_cancel (Id BlindBicycles B B) (Id Bicycles (bridge_bic B) (bridge_bic B)) (B .fst .fst)
      (bridge_bicycle_paths B B) (bicycle_evaluation (bridge_bic B) x) (hn x)

def bridge_normal_from (B : BlindBicycles) (hn : IsNormalBicycle (bridge_bic B)) : BlindNormalBicycle B
  ≔ x ↦ bridge_isequiv_precompose (Id BlindBicycles B B) (Id Bicycles (bridge_bic B) (bridge_bic B)) (B .fst .fst)
      (bridge_bicycle_paths B B) (bicycle_evaluation (bridge_bic B) x) (hn x)

def bridge_def_normal_bicycle (B : BlindBicycles)
  : Product (BlindNormalBicycle B → IsNormalBicycle (bridge_bic B)) (IsNormalBicycle (bridge_bic B) → BlindNormalBicycle B)
  ≔ (bridge_normal_to B, bridge_normal_from B)

{` lem:evisinj-bicycle (line 2073). `}
def bridge_lem_evisinj_bicycle : blind_lem_evisinj_bicycle
  ≔ B B' x0 e e' h ↦ equivalence_injective (Id BlindBicycles B B') (Id Bicycles (bridge_bic B) (bridge_bic B'))
      (bridge_bicycle_paths B B') e e'
      (bicycle_evaluation_path_reflecting (bridge_bic B) (bridge_bic B') x0 (refl bridge_bic e) (refl bridge_bic e') h)

{` xca:normal-bicycle-equiv (line 2112). `}
def bridge_xca_normal_bicycle_equiv : blind_xca_normal_bicycle_equiv
  ≔ B x h ↦ bridge_normal_from B (normal_bicycle_from_point (bridge_bic B) x
      (bridge_isequiv_cancel (Id BlindBicycles B B) (Id Bicycles (bridge_bic B) (bridge_bic B)) (B .fst .fst)
        (bridge_bicycle_paths B B) (bicycle_evaluation (bridge_bic B) x) h))

{` def:cbid-bicycle (line 2119): the blind symmetry sending x to x' is ours
   (bicycle_cbid_unique). `}
def bridge_def_cbid (B : BlindBicycles) (hn : BlindNormalBicycle B) (x x' : B .fst .fst)
  : Id (Id Bicycles (bridge_bic B) (bridge_bic B)) (refl bridge_bic (blind_cbid B hn x x'))
      (bicycle_cbid (bridge_bic B) (bridge_normal_to B hn) x x')
  ≔ bicycle_cbid_unique (bridge_bic B) (bridge_normal_to B hn) x x' (refl bridge_bic (blind_cbid B hn x x'))
      (inverse (B .fst .fst) x' (blind_bicycle_ev B B x (blind_cbid B hn x x')) (hn x x' .center .snd))

{` Line 2142: the blind H_x is our stabilizer. `}
def bridge_def_bicycle_H (B : BlindBicycles) (x : B .fst .fst)
  : Id (Subtypes BlindZZList) (blind_bicycle_H B x) (bicycle_stabilizer (bridge_bic B) x)
  ≔ funext BlindZZList (_ ↦ PropTypes) (blind_bicycle_H B x) (bicycle_stabilizer (bridge_bic B) x)
      (l ↦ proposition_extensionality (blind_bicycle_H B x l) (bicycle_stabilizer (bridge_bic B) x l)
        (p ↦ concat (B .fst .fst) (bicycle_word_map (bridge_bic B) l x) (blind_bsem B l x) x
          (inverse (B .fst .fst) (blind_bsem B l x) (bicycle_word_map (bridge_bic B) l x)
            (bridge_sem (B .fst .fst) (B .snd .fst) (B .snd .snd .fst) l x)) p)
        (p ↦ concat (B .fst .fst) (blind_bsem B l x) (bicycle_word_map (bridge_bic B) l x) x
          (bridge_sem (B .fst .fst) (B .snd .fst) (B .snd .snd .fst) l x) p))

def bridge_xca_normal_iff_H : blind_xca_normal_iff_H
  ≔ B ↦
    let S ≔ Subtypes BlindZZList in
    let E ≔ bicycle_normal_stabilizers_equiv (bridge_bic B) in
    let st ≔ bicycle_stabilizer (bridge_bic B) in
    (hn ↦ x y ↦ concat S (blind_bicycle_H B x) (st x) (blind_bicycle_H B y) (bridge_def_bicycle_H B x)
        (concat S (st x) (st y) (blind_bicycle_H B y) (E .map (bridge_normal_to B hn) x y)
          (inverse S (blind_bicycle_H B y) (st y) (bridge_def_bicycle_H B y))),
     hH ↦ bridge_normal_from B
       (equiv_inverse_map (IsNormalBicycle (bridge_bic B)) ((x y : B .fst .fst) → Id S (st x) (st y)) E
         (x y ↦ concat S (st x) (blind_bicycle_H B x) (st y)
           (inverse S (blind_bicycle_H B x) (st x) (bridge_def_bicycle_H B x))
           (concat S (blind_bicycle_H B x) (blind_bicycle_H B y) (st y) (hH x y) (bridge_def_bicycle_H B y)))))

{` Line 2146. Commuting bicycles are normal (ours); the claimed
   equivalence Cyc × Cyc ≃ commuting bicycles is refuted by ours
   (cycle_product_not_onto_commuting: (Bool, not, not) is not a product). `}
def bridge_commuting_to (B : BlindBicycles) (c : BlindCommutingBicycle B) : IsCommutingBicycle (bridge_bic B)
  ≔ happly (B .fst .fst) (_ ↦ B .fst .fst) (x ↦ B .snd .fst .map (B .snd .snd .fst .map x))
      (x ↦ B .snd .snd .fst .map (B .snd .fst .map x)) c

def bridge_commuting_from (B : Bicycles) (c : IsCommutingBicycle B) : BlindCommutingBicycle (bridge_bic_inv B)
  ≔ funext (B .fst .fst) (_ ↦ B .fst .fst) (x ↦ B .snd .fst .map (B .snd .snd .fst .map x))
      (x ↦ B .snd .snd .fst .map (B .snd .fst .map x)) c

def bridge_xca_commuting_normal : blind_xca_commuting_normal
  ≔ B c ↦ bridge_normal_from B (commuting_bicycle_normal (bridge_bic B) (bridge_commuting_to B c))

def bridge_xca_cycles_commuting_bicycles_refuted : Not blind_xca_cycles_commuting_bicycles
  ≔ w ↦ cycle_product_not_onto_commuting (B ↦
      let Bt : BlindCommutingBicycles ≔ (bridge_bic_inv (B .fst), bridge_commuting_from (B .fst) (B .snd)) in
      let ctr ≔ w .snd .snd Bt .center in
      let c ≔ ctr .fst .fst in let d ≔ ctr .fst .snd in
      let X ≔ c .fst .fst .fst in let Y ≔ d .fst .fst .fst in
      let S : SetTypes ≔ (Product X Y, product_set X Y (c .fst .fst .snd) (d .fst .fst .snd)) in
      let a ≔ product_equiv X Y X Y (c .fst .snd) (identity_equiv Y) in
      let b ≔ product_equiv X Y X Y (identity_equiv X) (d .fst .snd) in
      let cd ≔ w .snd .fst c d in
      let P : BlindBicycles ≔ (S, (a, (b, cd .fst))) in
      let T ≔ Σ Cycles (c' ↦ Σ Cycles (d' ↦ Id Bicycles (cycle_product_bicycle c' d') (B .fst))) in
      mere T (c, (d,
        concat Bicycles (cycle_product_bicycle c d) (bridge_bic P) (B .fst)
          (refl (product_bicycle_set c d), (refl (product_bicycle_a c d), (refl (product_bicycle_b c d),
            bicycle_connected_prop (Product X Y) a b (product_bicycle_connected c d) (bridge_bic P .snd .snd .snd))))
          (concat Bicycles (bridge_bic P) (bridge_bic (w .fst (c, d) .fst)) (B .fst)
            (refl bridge_bic (inverse BlindBicycles (w .fst (c, d) .fst) P (cd .snd)))
            (concat Bicycles (bridge_bic (w .fst (c, d) .fst)) (bridge_bic (Bt .fst)) (B .fst)
              (refl ((u ↦ bridge_bic (u .fst)) : BlindCommutingBicycles → Bicycles)
                (inverse BlindCommutingBicycles Bt (w .fst (c, d)) (ctr .snd)))
              (equiv_counit BlindBicycles Bicycles bridge_def_bicycles (B .fst)))))))

{` Line 2178. `}
def bridge_xca_list_equivalence : blind_xca_list_equivalence
  ≔ B hn x0 l l' ↦
    let X ≔ B .fst .fst in let a ≔ B .snd .fst in let b ≔ B .snd .snd .fst in
    let B' ≔ bridge_bic B in
    (p ↦ funext X (_ ↦ X) (blind_bsem B l) (blind_bsem B l')
       (z ↦ concat X (blind_bsem B l z) (bicycle_word_map B' l z) (blind_bsem B l' z) (bridge_sem X a b l z)
         (concat X (bicycle_word_map B' l z) (bicycle_word_map B' l' z) (blind_bsem B l' z)
           (normal_bicycle_words_same_meaning B' (bridge_normal_to B hn) x0 l l'
             (concat X (bicycle_word_map B' l x0) (blind_bsem B l x0) (bicycle_word_map B' l' x0)
               (inverse X (blind_bsem B l x0) (bicycle_word_map B' l x0) (bridge_sem X a b l x0))
               (concat X (blind_bsem B l x0) (blind_bsem B l' x0) (bicycle_word_map B' l' x0) p (bridge_sem X a b l' x0)))
             z)
           (inverse X (blind_bsem B l' z) (bicycle_word_map B' l' z) (bridge_sem X a b l' z)))),
     q ↦ happly X (_ ↦ X) (blind_bsem B l) (blind_bsem B l') q x0)

{` rem:bicycle-list-concat (line 2184), first formula. `}
def bridge_rem_sem_append : blind_rem_sem_append
  ≔ X a b l l' ↦ funext X (_ ↦ X) (x ↦ blind_sem X a b l' (blind_sem X a b l x)) (blind_sem X a b (append (Sum Int Int) l' l))
      (x ↦ concat X (blind_sem X a b l' (blind_sem X a b l x)) (bicycle_meaning_map X a b l' (bicycle_meaning_map X a b l x))
        (blind_sem X a b (append (Sum Int Int) l' l) x)
        (concat X (blind_sem X a b l' (blind_sem X a b l x)) (bicycle_meaning_map X a b l' (blind_sem X a b l x))
          (bicycle_meaning_map X a b l' (bicycle_meaning_map X a b l x))
          (bridge_sem X a b l' (blind_sem X a b l x)) (refl (bicycle_meaning_map X a b l') (bridge_sem X a b l x)))
        (concat X (bicycle_meaning_map X a b l' (bicycle_meaning_map X a b l x))
          (bicycle_meaning_map X a b (append (Sum Int Int) l' l) x) (blind_sem X a b (append (Sum Int Int) l' l) x)
          (inverse X (bicycle_meaning_map X a b (append (Sum Int Int) l' l) x)
            (bicycle_meaning_map X a b l' (bicycle_meaning_map X a b l x)) (bicycle_meaning_append X a b l' l x))
          (inverse X (blind_sem X a b (append (Sum Int Int) l' l) x) (bicycle_meaning_map X a b (append (Sum Int Int) l' l) x)
            (bridge_sem X a b (append (Sum Int Int) l' l) x))))

{` rem:bicycle-list-concat (line 2184), cbid formulas: transferred along
   the equivalence on paths (equivalence_injective), with bridge_def_cbid
   and bridge_sem. `}
def bridge_cbid_args (B : Bicycles) (h : IsNormalBicycle B) (x x' y y' : bicycle_carrier B)
  (p : Id (bicycle_carrier B) x y) (q : Id (bicycle_carrier B) x' y')
  : Id (Id Bicycles B B) (bicycle_cbid B h x x') (bicycle_cbid B h y y')
  ≔ refl (bicycle_cbid B h) p q

def bridge_rem_cbid_shift : blind_rem_cbid_shift
  ≔ B hn x x' l ↦
    let B' ≔ bridge_bic B in let hn' ≔ bridge_normal_to B hn in
    let X ≔ B .fst .fst in let a ≔ B .snd .fst in let b ≔ B .snd .snd .fst in
    let L ≔ Id Bicycles B' B' in
    let c ≔ blind_cbid B hn in let c' ≔ bicycle_cbid B' hn' in
    let s ≔ blind_bsem B l in let w ≔ bicycle_word_map B' l in
    equivalence_injective (Id BlindBicycles B B) L (bridge_bicycle_paths B B) (c x x') (c (s x) (s x'))
      (concat L (refl bridge_bic (c x x')) (c' x x') (refl bridge_bic (c (s x) (s x')))
        (bridge_def_cbid B hn x x')
        (concat L (c' x x') (c' (w x) (w x')) (refl bridge_bic (c (s x) (s x')))
          (bicycle_cbid_meaning B' hn' l x x')
          (concat L (c' (w x) (w x')) (c' (s x) (s x')) (refl bridge_bic (c (s x) (s x')))
            (bridge_cbid_args B' hn' (w x) (w x') (s x) (s x')
              (inverse X (s x) (w x) (bridge_sem X a b l x)) (inverse X (s x') (w x') (bridge_sem X a b l x')))
            (inverse L (refl bridge_bic (c (s x) (s x'))) (c' (s x) (s x')) (bridge_def_cbid B hn (s x) (s x'))))))

def bridge_rem_cbid_concat : blind_rem_cbid_concat
  ≔ B hn x0 l l' ↦
    let B' ≔ bridge_bic B in let hn' ≔ bridge_normal_to B hn in
    let X ≔ B .fst .fst in let a ≔ B .snd .fst in let b ≔ B .snd .snd .fst in
    let L ≔ Id Bicycles B' B' in let LB ≔ Id BlindBicycles B B in
    let c ≔ blind_cbid B hn in let c' ≔ bicycle_cbid B' hn' in
    let s ≔ blind_bsem B in let w ≔ bicycle_word_map B' in
    let E ≔ refl bridge_bic in
    let bs : (k : BlindZZList) → Id X (w k x0) (s k x0)
      ≔ k ↦ inverse X (s k x0) (w k x0) (bridge_sem X a b k x0) in
    let ll ≔ append (Sum Int Int) l' l in
    let lr ≔ append (Sum Int Int) l l' in
    (equivalence_injective LB L (bridge_bicycle_paths B B)
       (concat BlindBicycles B B B (c x0 (s l' x0)) (c x0 (s l x0))) (c x0 (s ll x0))
       (concat L (E (concat BlindBicycles B B B (c x0 (s l' x0)) (c x0 (s l x0))))
          (concat Bicycles B' B' B' (c' x0 (w l' x0)) (c' x0 (w l x0))) (E (c x0 (s ll x0)))
          (concat L (E (concat BlindBicycles B B B (c x0 (s l' x0)) (c x0 (s l x0))))
             (concat Bicycles B' B' B' (E (c x0 (s l' x0))) (E (c x0 (s l x0))))
             (concat Bicycles B' B' B' (c' x0 (w l' x0)) (c' x0 (w l x0)))
             (map_path_concat BlindBicycles Bicycles bridge_bic B B B (c x0 (s l' x0)) (c x0 (s l x0)))
             (refl (concat Bicycles B' B' B')
               (concat L (E (c x0 (s l' x0))) (c' x0 (s l' x0)) (c' x0 (w l' x0)) (bridge_def_cbid B hn x0 (s l' x0))
                 (bridge_cbid_args B' hn' x0 (s l' x0) x0 (w l' x0) (refl x0)
                   (bridge_sem X a b l' x0)))
               (concat L (E (c x0 (s l x0))) (c' x0 (s l x0)) (c' x0 (w l x0)) (bridge_def_cbid B hn x0 (s l x0))
                 (bridge_cbid_args B' hn' x0 (s l x0) x0 (w l x0) (refl x0)
                   (bridge_sem X a b l x0)))))
          (concat L (concat Bicycles B' B' B' (c' x0 (w l' x0)) (c' x0 (w l x0))) (c' x0 (w ll x0)) (E (c x0 (s ll x0)))
             (bicycle_list_concat_forward B' hn' x0 l l')
             (concat L (c' x0 (w ll x0)) (c' x0 (s ll x0)) (E (c x0 (s ll x0)))
               (bridge_cbid_args B' hn' x0 (w ll x0) x0 (s ll x0) (refl x0) (bs ll))
               (inverse L (E (c x0 (s ll x0))) (c' x0 (s ll x0)) (bridge_def_cbid B hn x0 (s ll x0)))))),
     equivalence_injective LB L (bridge_bicycle_paths B B)
       (concat BlindBicycles B B B (c (s l' x0) x0) (c (s l x0) x0)) (c (s lr x0) x0)
       (concat L (E (concat BlindBicycles B B B (c (s l' x0) x0) (c (s l x0) x0)))
          (concat Bicycles B' B' B' (c' (w l' x0) x0) (c' (w l x0) x0)) (E (c (s lr x0) x0))
          (concat L (E (concat BlindBicycles B B B (c (s l' x0) x0) (c (s l x0) x0)))
             (concat Bicycles B' B' B' (E (c (s l' x0) x0)) (E (c (s l x0) x0)))
             (concat Bicycles B' B' B' (c' (w l' x0) x0) (c' (w l x0) x0))
             (map_path_concat BlindBicycles Bicycles bridge_bic B B B (c (s l' x0) x0) (c (s l x0) x0))
             (refl (concat Bicycles B' B' B')
               (concat L (E (c (s l' x0) x0)) (c' (s l' x0) x0) (c' (w l' x0) x0) (bridge_def_cbid B hn (s l' x0) x0)
                 (bridge_cbid_args B' hn' (s l' x0) x0 (w l' x0) x0 (bridge_sem X a b l' x0) (refl x0)))
               (concat L (E (c (s l x0) x0)) (c' (s l x0) x0) (c' (w l x0) x0) (bridge_def_cbid B hn (s l x0) x0)
                 (bridge_cbid_args B' hn' (s l x0) x0 (w l x0) x0 (bridge_sem X a b l x0) (refl x0)))))
          (concat L (concat Bicycles B' B' B' (c' (w l' x0) x0) (c' (w l x0) x0)) (c' (w lr x0) x0) (E (c (s lr x0) x0))
             (bicycle_list_concat_backward B' hn' x0 l l')
             (concat L (c' (w lr x0) x0) (c' (s lr x0) x0) (E (c (s lr x0) x0))
               (bridge_cbid_args B' hn' (w lr x0) x0 (s lr x0) x0 (bs lr) (refl x0))
               (inverse L (E (c (s lr x0) x0)) (c' (s lr x0) x0) (bridge_def_cbid B hn (s lr x0) x0))))))

{` def:Dinfty-Q (line 1955). The blind standard bicycles map to ours by
   explicit bicycle isomorphisms: the identity for D∞ (the blind a, b are
   ours pointwise), and for Q₈ the relabelling ψ found by search (the blind
   numbering of Fin 8 is reversed and the blind data correspond to ours
   only up to an automorphism). Hence the automorphism groups agree. `}
def bridge_bicycle_aut_path (B : BlindBicycles) (B' : Bicycles) (p : Id Bicycles (bridge_bic B) B')
  : Id Group (bridge_g (blind_bicycle_aut B)) (bicycle_automorphism_group B')
  ≔ concat Group (bridge_g (blind_bicycle_aut B)) (automorphism_group BlindBicycles blind_bicycles_groupoid B)
      (bicycle_automorphism_group B')
      (bridge_aut BlindBicycles blind_bicycles_groupoid B)
      (automorphism_group_equiv_path_at BlindBicycles Bicycles blind_bicycles_groupoid bicycles_groupoid bridge_def_bicycles
        B B' p)

def bridge_dihedral_a_commutes (x : Sum Int Int) : Id (Sum Int Int) (blind_dihedral_a x) (dihedral_a_map x)
  ≔ match x [ inl. n ↦ refl (inl. (int_succ n) : Sum Int Int) | inr. n ↦ refl (inr. (int_pred n) : Sum Int Int) ]

def bridge_dihedral_b_commutes (x : Sum Int Int) : Id (Sum Int Int) (blind_dihedral_b x) (dihedral_b_map x)
  ≔ match x [ inl. n ↦ refl (inr. n : Sum Int Int) | inr. n ↦ refl (inl. n : Sum Int Int) ]

def bridge_dihedral_path (w : blind_dihedral_is_bicycle)
  : Id Bicycles (bridge_bic (blind_dihedral_bicycle w)) infinite_dihedral_bicycle
  ≔ bicycle_path_from_iso (bridge_bic (blind_dihedral_bicycle w)) infinite_dihedral_bicycle
      (identity_equiv (Sum Int Int), (bridge_dihedral_a_commutes, bridge_dihedral_b_commutes))

def bridge_def_dinfty (w : blind_dihedral_is_bicycle) : Id Group (bridge_g (blind_Dinfty w)) infinite_dihedral_group
  ≔ bridge_bicycle_aut_path (blind_dihedral_bicycle w) infinite_dihedral_bicycle (bridge_dihedral_path w)
