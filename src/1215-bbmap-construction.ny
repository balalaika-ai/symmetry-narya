export "1214-bbmap-loops-injective"

{` Chapter 12, helper for the lemma at abelian.tex 928: a pointed map
   BB K →* BB L built from a map f : BK → BL (L abelian; K arbitrary).

   For u = (Z, α) : BB K (α : ‖BK = Z‖₀) put
     Comp(Z, α) ≔ Σ(k : Z → BL) Pred(Z, α, k),
   where Pred(Z, |r|₀, k) ≔ ‖f and k are related over r‖ (the identity type
   of the family Y ↦ (Y → BL) over r : BK = Z), defined on ‖BK = Z‖₀ by
   recursion into the set of propositions. At u = pt, Comp is the component
   of f in BK → BL. Evaluation at r .trr sh_K is an equivalence
   Comp(Z, |r|₀) ≃ BL (Lemma E, module 1213, after path induction on r), and
   its inverse gives the class in ‖BL = Comp(Z, α)‖₀. The construction is
   contravariant in Z, so Ω of the resulting map is f composed with
   inversion (module 1216). `}

def bbmap_pred (K L : Group) (f : BG K .carrier → BG L .carrier) (Z : Type) (α : SetTrunc (Id Type (BG K .carrier) Z))
  (k : Z → BG L .carrier) : Type
  ≔ set_trunc_rec (Id Type (BG K .carrier) Z) PropTypes propositions_set
      (r ↦ (Mere (Id ((Y ↦ Y → BG L .carrier) : Type → Type) r f k),
            mere_isprop (Id ((Y ↦ Y → BG L .carrier) : Type → Type) r f k))) α .fst

def BBMapComp (K L : Group) (f : BG K .carrier → BG L .carrier) (Z : Type) (α : SetTrunc (Id Type (BG K .carrier) Z))
  : Type
  ≔ Σ (Z → BG L .carrier) (k ↦ bbmap_pred K L f Z α k)

{` At the base point Comp is the component of f. `}
def bbmap_comp_base (K L : Group) (f : BG K .carrier → BG L .carrier)
  : Id Type (BBMapComp K L f (BG K .carrier) (set_trunc (Id Type (BG K .carrier) (BG K .carrier)) (refl (BG K .carrier))))
      (NativeComponent (BG K .carrier → BG L .carrier) f)
  ≔ refl (NativeComponent (BG K .carrier → BG L .carrier) f)

def bbmap_eval (K L : Group) (f : BG K .carrier → BG L .carrier) (Z : Type) (r : Id Type (BG K .carrier) Z)
  (c : BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) : BG L .carrier
  ≔ c .fst (r .trr (shape K))

def bbmap_eval_is_equiv (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (Z : Type)
  (r : Id Type (BG K .carrier) Z)
  : isEquiv (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) (BG L .carrier) (bbmap_eval K L f Z r)
  ≔ J Type (BG K .carrier)
      (Z r ↦ isEquiv (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) (BG L .carrier) (bbmap_eval K L f Z r))
      (native_equivalence (NativeComponent (BG K .carrier → BG L .carrier) f) (BG L .carrier)
        ((c ↦ c .fst (refl (BG K .carrier) .trr (shape K))),
         bbmap_component_eval_equiv (BG K .carrier) (bg_connected K) (refl (BG K .carrier) .trr (shape K)) L hL f)
        .equiv)
      Z r

def bbmap_eval_equiv (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (Z : Type)
  (r : Id Type (BG K .carrier) Z)
  : Equiv (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) (BG L .carrier)
  ≔ (bbmap_eval K L f Z r, bbmap_eval_is_equiv K L hL f Z r)

def bbmap_class_path (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (Z : Type)
  (r : Id Type (BG K .carrier) Z)
  : Id Type (BG L .carrier) (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r))
  ≔ inverse Type (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) (BG L .carrier)
      (ua (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)) (BG L .carrier) (bbmap_eval_equiv K L hL f Z r))

def bbmap_class (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (Z : Type)
  (α : SetTrunc (Id Type (BG K .carrier) Z))
  : SetTrunc (Id Type (BG L .carrier) (BBMapComp K L f Z α))
  ≔ set_trunc_induction (Id Type (BG K .carrier) Z)
      (β ↦ SetTrunc (Id Type (BG L .carrier) (BBMapComp K L f Z β)))
      (β ↦ set_trunc_set (Id Type (BG L .carrier) (BBMapComp K L f Z β)))
      (r ↦ set_trunc (Id Type (BG L .carrier) (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)))
        (bbmap_class_path K L hL f Z r)) α

def bbmap_class_beta (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (Z : Type)
  (r : Id Type (BG K .carrier) Z)
  : Id (SetTrunc (Id Type (BG L .carrier) (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r))))
      (bbmap_class K L hL f Z (set_trunc (Id Type (BG K .carrier) Z) r))
      (set_trunc (Id Type (BG L .carrier) (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)))
        (bbmap_class_path K L hL f Z r))
  ≔ set_trunc_induction_beta (Id Type (BG K .carrier) Z)
      (β ↦ SetTrunc (Id Type (BG L .carrier) (BBMapComp K L f Z β)))
      (β ↦ set_trunc_set (Id Type (BG L .carrier) (BBMapComp K L f Z β)))
      (r ↦ set_trunc (Id Type (BG L .carrier) (BBMapComp K L f Z (set_trunc (Id Type (BG K .carrier) Z) r)))
        (bbmap_class_path K L hL f Z r)) r

{` The underlying map BB K → BB L, u ↦ (Comp(u), class). `}
def bbmap_function (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (u : BB K .carrier)
  : BB L .carrier
  ≔ (BBMapComp K L f (u .fst) (u .snd), bbmap_class K L hL f (u .fst) (u .snd))

{` The pointing path (BL, |refl|₀) = (Comp(pt), class): first component
   the inverse of ua of evaluation. `}
def bbmap_base_path (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier)
  : Id Type (BG L .carrier) (BBMapComp K L f (BG K .carrier) (set_trunc (Id Type (BG K .carrier) (BG K .carrier)) (refl (BG K .carrier))))
  ≔ bbmap_class_path K L hL f (BG K .carrier) (refl (BG K .carrier))

def bbmap_point (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier)
  : Id (BB L .carrier) (bb_point L) (bbmap_function K L hL f (bb_point K))
  ≔ let BK ≔ BG K .carrier in let BL ≔ BG L .carrier in
    let C0 ≔ BBMapComp K L f BK (set_trunc (Id Type BK BK) (refl BK)) in
    let P0 ≔ bbmap_base_path K L hL f in
    let one ≔ set_trunc (Id Type BL BL) (refl BL) in
    (P0, pathover_of_eq Type (Z ↦ SetTrunc (Id Type BL Z)) BL C0 P0 one
      (bbmap_class K L hL f BK (set_trunc (Id Type BK BK) (refl BK)))
      (calc
        transport Type (Z ↦ SetTrunc (Id Type BL Z)) BL C0 P0 one
          = trunc_path_compose Type BL BL C0 (set_trunc (Id Type BL C0) P0) one
          by univ_cover_transport Type BL BL C0 P0 one
        = set_trunc (Id Type BL C0) P0
          by refl (set_trunc (Id Type BL C0)) (concat_1p Type BL C0 P0)
        = bbmap_class K L hL f BK (set_trunc (Id Type BK BK) (refl BK))
          by inverse (SetTrunc (Id Type BL C0)) (bbmap_class K L hL f BK (set_trunc (Id Type BK BK) (refl BK)))
            (set_trunc (Id Type BL C0) P0) (bbmap_class_beta K L hL f BK (refl BK)) ∎))

{` BB on maps: the pointed map BB K →* BB L attached to f. `}
def bbmap_pointed (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) : BookPointedMap (BB K) (BB L)
  ≔ (bbmap_function K L hL f, bbmap_point K L hL f)
