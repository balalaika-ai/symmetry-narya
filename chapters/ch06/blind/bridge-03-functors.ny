import "bridge-00-core"
import "bridge-01-wild-cats"
import "../../../src/610-preorder-functors-and-adjoints"
import "../../../src/614-truncation-functor"
import "../../../src/615-basepoint-functors"
import "../../../src/616-loop-functor"
import "../../../src/617-path-groupoid-functors"
import "../../../src/626-path-functor-categories"
import "../../../src/627-faithful-functor-examples"
import "../../../src/647-univalent-category-of-precategories"
import "../../../src/661-arrow-categories"
import "../../../src/686-category-of-groups"
import "../../../src/694-wild-precategory-pentagon-filler"
import "../../../src/690-gset-categories"
import "../../../src/281-pathover-groupoid-laws"

{` Bridges for cats.tex, section "Functors and natural
   transformations" (blind file 03). `}

{` def:functor. `}
def bridge_def_functor_laws_prop : blind_def_functor_laws_prop
  ≔ C D fo fh ↦ functor_laws_prop (bridge_w C) (bridge_w (D .fst)) (D .snd) (fo, fh)

{` xca:wild-functor-isos. `}
def bridge_xca_wild_functor_isos : blind_xca_wild_functor_isos
  ≔ C D F a b f i ↦ functor_preserves_iso (bridge_w C) (bridge_w D) (bridge_f C D F) a b f i

{` ex:functor-preorders. `}
def bridge_ex_functor_preorders : blind_ex_functor_preorders
  ≔ P Q ↦ book_equivalence (BlindWildFunctor (P .fst .fst) (Q .fst .fst)) (MonotoneMap (bridge_pre P) (bridge_pre Q))
      (compose_equiv (BlindWildFunctor (P .fst .fst) (Q .fst .fst)) (WildFunctor (bridge_pre P .wild) (bridge_pre Q .wild))
        (MonotoneMap (bridge_pre P) (bridge_pre Q))
        (bridge_def_functor (P .fst .fst) (Q .fst .fst))
        (preorder_functor_monotone_equiv (bridge_pre P) (bridge_pre Q)))

{` ex:USym-functor. `}
def bridge_ex_usym_functor : blind_ex_usym_functor ≔ (usym_functor .map_id, usym_functor .map_comp)

{` ex:action-functors. The blind G-set precategory and the three actions on
   arrows are ours (module 690) on the nose. `}
def bridge_def_gset_precat (G : Group) : Id WildPrecat (bridge_w (blind_gset_precat G .fst)) (GSetWild G)
  ≔ refl (GSetWild G)

def bridge_ex_action_functors : blind_ex_action_functors
  ≔ G H f ↦ ((gset_restrict_functor G H f .map_id, gset_restrict_functor G H f .map_comp),
             ((gset_induce_functor G H f .map_id, gset_induce_functor G H f .map_comp),
              (gset_coinduce_functor G H f .map_id, gset_coinduce_functor G H f .map_comp)))

{` def:n-trunc-functor. `}
def bridge_def_truncated_universe (k : Nat) : Id WildPrecat (bridge_w (blind_truncated_universe k)) (TruncatedTypeWild k)
  ≔ refl (TruncatedTypeWild k)

def bridge_ex_trunc_functor : blind_ex_trunc_functor ≔ k ↦ (TruncFunctor k .map_id, TruncFunctor k .map_comp)

{` ex:add-remove-basepoint: the forgetful functor is ours on the nose. `}
def bridge_def_forget_functor
  : Id (WildFunctor PointedWild TypeWild) (bridge_f blind_pointed_wild_precat blind_universe_wild_precat blind_forget_functor)
      ForgetBasepointFunctor
  ≔ refl ForgetBasepointFunctor

{` ex:slice-projection: same action on objects and arrows as ours. `}
def bridge_def_slice_projection (C : BlindPrecat) (c : C .fst .ob)
  : Id (FunctorData (SlicePrecat (bridge_p C) c .wild) (bridge_w (C .fst)))
      (functor_data (bridge_w (blind_slice_precat C c .fst)) (bridge_w (C .fst))
        (bridge_f (blind_slice_precat C c .fst) (C .fst) (blind_slice_projection C c)))
      (functor_data (SlicePrecat (bridge_p C) c .wild) (bridge_w (C .fst)) (slice_precat_projection (bridge_p C) c))
  ≔ refl (functor_data (SlicePrecat (bridge_p C) c .wild) (bridge_w (C .fst)) (slice_precat_projection (bridge_p C) c))

{` def:full-faithful. `}
def bridge_def_fully_faithful_equiv : blind_def_fully_faithful_equiv
  ≔ C D F h a b ↦ fully_faithful_equiv (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_ff_inv C D F h) a b .equiv

{` Example (WIP) at line 728: full subcategory inclusions are fully faithful. `}
def bridge_def_full_subcat_inclusion (C : BlindWildPrecat) (P : C .ob → PropTypes)
  : Id (WildFunctor (FullSubcat (bridge_w C) P) (bridge_w C))
      (bridge_f (blind_full_subcat C P) C (blind_full_subcat_inclusion C P)) (full_subcat_inclusion (bridge_w C) P)
  ≔ refl (full_subcat_inclusion (bridge_w C) P)

def bridge_wip_full_subcat_inclusion_ff : blind_wip_full_subcat_inclusion_ff
  ≔ C P ↦ bridge_ff (blind_full_subcat C P) C (blind_full_subcat_inclusion C P)
      (full_subcat_inclusion_fully_faithful (bridge_w C) P)

{` def:nat-trans. Ours proves the Π-level statement nat_square_prop; the
   pointwise one is the hom-set property it is built from. `}
def bridge_def_nat_trans_squares_prop : blind_def_nat_trans_squares_prop
  ≔ C D F G al a b f ↦ D .snd (F .fob a) (G .fob b)
      (D .fst .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
      (D .fst .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f))

def bridge_nat_squares_prop_from_ours (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst))
  (al : (a : C .ob) → D .fst .hom (F .fob a) (G .fob a)) : isProp (BlindNatSquares C (D .fst) F G al)
  ≔ nat_square_prop (bridge_w C) (bridge_w (D .fst)) (D .snd) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G) al

{` ex:pt-unpt-unit: components inl and refl squares, as ours. `}
def bridge_ex_pt_unpt_unit_components
  (pl : BlindWildFunctorLaws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom)
  : Id ((A : Type) → A → Sum A Unit) (blind_ex_pt_unpt_unit pl .fst) (plus_forget_unit .component)
  ≔ refl (plus_forget_unit .component)

{` ex:path-gpd-nat. `}
def bridge_def_path_functor (A B : Type) (f : A → B)
  : Id (WildFunctor (PathWild A) (PathWild B))
      (bridge_f (blind_path_wild_precat A) (blind_path_wild_precat B) (blind_path_functor A B f)) (path_wild_functor A B f)
  ≔ refl (path_wild_functor A B f)

def bridge_ex_path_gpd_nat : blind_ex_path_gpd_nat ≔ A B f g h ↦ path_wild_nat_trans A B f g h .natural

{` xca:funext-nat-trans, via the translation functors of the core. `}
def bridge_xca_funext_nat_trans : blind_xca_funext_nat_trans
  ≔ C D F G al ↦
    (i ↦ functor_cat_iso_components (bridge_w C) (bridge_p D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G)
           (bridge_nt C (D .fst) F G al)
           (functor_preserves_iso (BridgeFP C D) (BridgeOurFP C D) (bridge_fp_functor C D) F G al i),
     h ↦ functor_preserves_iso (BridgeOurFP C D) (BridgeFP C D) (bridge_fp_functor_inv C D)
           (bridge_f C (D .fst) F) (bridge_f C (D .fst) G) (bridge_nt C (D .fst) F G al)
           (functor_cat_components_iso (bridge_w C) (bridge_p D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G)
              (bridge_nt C (D .fst) F G al) h))

{` xca:functor-cat-univalent. `}
def bridge_xca_functor_cat_univalent : blind_xca_functor_cat_univalent
  ≔ C D u ↦ bridge_fp_univalent C D (functor_wild_univalent (bridge_w C) (bridge_c (D, u)))

{` xca:path-core-adj. `}
def bridge_xca_path_core_adj : blind_xca_path_core_adj
  ≔ A C ↦ book_two_out_of_three_composite (BlindWildFunctor (blind_path_wild_precat A) (C .fst .fst))
      (WildFunctor (PathWild A) (bridge_w (C .fst .fst))) (A → C .fst .fst .ob)
      (bridge_f (blind_path_wild_precat A) (C .fst .fst)) (F ↦ F .fob) (F ↦ F .obj)
      (refl ((F ↦ F .fob) : BlindWildFunctor (blind_path_wild_precat A) (C .fst .fst) → A → C .fst .fst .ob))
      (book_equivalence (BlindWildFunctor (blind_path_wild_precat A) (C .fst .fst))
         (WildFunctor (PathWild A) (bridge_w (C .fst .fst))) (bridge_def_functor (blind_path_wild_precat A) (C .fst .fst))
         .equiv)
      (path_functor_restriction_is_equiv A (bridge_c C))

{` ex:repr-functors: the blind representables (valued in U-small types)
   have the same actions and laws as ours (valued in all types) after the
   inclusion of U-small types. `}
def bridge_def_repr_cov (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : Id (FunctorData (bridge_w C) TypeWild)
      (functor_data (bridge_w C) TypeWild
        (functor_compose (bridge_w C) (TypeWildIn U) TypeWild (full_subcat_inclusion TypeWild (SmallTypePredicate U))
          (bridge_f C (blind_universe_wild_precat_in U) (blind_repr_cov U C s c))))
      (functor_data (bridge_w C) TypeWild (covariant_representable (bridge_w C) c))
  ≔ refl (functor_data (bridge_w C) TypeWild (covariant_representable (bridge_w C) c))

def bridge_def_repr_cov_laws (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : Id (FunctorLaws (bridge_w C) TypeWild (functor_data (bridge_w C) TypeWild (covariant_representable (bridge_w C) c)))
      (blind_repr_cov U C s c .fid, blind_repr_cov U C s c .fcomp)
      (covariant_representable (bridge_w C) c .map_id, covariant_representable (bridge_w C) c .map_comp)
  ≔ refl (covariant_representable (bridge_w C) c .map_id, covariant_representable (bridge_w C) c .map_comp)

def bridge_def_repr_contra (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : Id (FunctorData (OppositeWild (bridge_w C)) TypeWild)
      (functor_data (OppositeWild (bridge_w C)) TypeWild
        (functor_compose (OppositeWild (bridge_w C)) (TypeWildIn U) TypeWild
          (full_subcat_inclusion TypeWild (SmallTypePredicate U))
          (bridge_f (blind_op C) (blind_universe_wild_precat_in U) (blind_repr_contra U C s c))))
      (functor_data (OppositeWild (bridge_w C)) TypeWild (contravariant_representable (bridge_w C) c))
  ≔ refl (functor_data (OppositeWild (bridge_w C)) TypeWild (contravariant_representable (bridge_w C) c))

def bridge_def_repr_contra_laws (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : Id (FunctorLaws (OppositeWild (bridge_w C)) TypeWild
        (functor_data (OppositeWild (bridge_w C)) TypeWild (contravariant_representable (bridge_w C) c)))
      (blind_repr_contra U C s c .fid, blind_repr_contra U C s c .fcomp)
      (contravariant_representable (bridge_w C) c .map_id, contravariant_representable (bridge_w C) c .map_comp)
  ≔ refl (contravariant_representable (bridge_w C) c .map_id, contravariant_representable (bridge_w C) c .map_comp)

{` xca:wildprecat-of-wildprecats: the unit and associativity laws of
   composition of wild functors are ours (module 644) transported along
   the record translation. `}
def bridge_xca_wildprecat_of_wildprecats : blind_xca_wildprecat_of_wildprecats
  ≔ ((C D F ↦ refl (bridge_f_inv C D) (functor_left_unit (bridge_w C) (bridge_w D) (bridge_f C D F))),
     ((C D F ↦ refl (bridge_f_inv C D) (functor_right_unit (bridge_w C) (bridge_w D) (bridge_f C D F))),
      (C0 C1 C2 C3 F G H ↦ refl (bridge_f_inv C0 C3)
         (functor_assoc (bridge_w C0) (bridge_w C1) (bridge_w C2) (bridge_w C3)
           (bridge_f C0 C1 F) (bridge_f C1 C2 G) (bridge_f C2 C3 H)))))

{` xca:wildprecat-of-wildprecats, the adventurous part (pentagon fillers).
   Ours (modules 692-694) proves the pentagon in the wild precategory of
   wild precategories with the associator functor_assoc_yoneda, for any
   C_4. The transfer to the blind records is generic in the associator:
   ap of the record translation preserves concatenation. `}
def bridge_assoc_of (alpha : YwfAssoc) : BlindFunctorAssoc
  ≔ C0 C1 C2 C3 F G H ↦ refl (bridge_f_inv C0 C3)
      (alpha (bridge_w C0) (bridge_w C1) (bridge_w C2) (bridge_w C3)
        (bridge_f C0 C1 F) (bridge_f C1 C2 G) (bridge_f C2 C3 H))

def bridge_pentagon_transfer (alpha : YwfAssoc) (pent : WildPentagon (WildPrecatWildWith alpha))
  (l : BlindFunctorLunit) (r : BlindFunctorRunit)
  : BlindPentagon (blind_wpc_of l r (bridge_assoc_of alpha))
  ≔ C0 C1 C2 C3 C4 F G H K ↦
    let W ≔ WildPrecatWildWith alpha in
    let a ≔ bridge_w C0 in let b ≔ bridge_w C1 in let c ≔ bridge_w C2 in
    let d ≔ bridge_w C3 in let e ≔ bridge_w C4 in
    let f ≔ bridge_f C0 C1 F in let g ≔ bridge_f C1 C2 G in
    let h ≔ bridge_f C2 C3 H in let k ≔ bridge_f C3 C4 K in
    let A ≔ WildFunctor a e in
    let B ≔ BlindWildFunctor C0 C4 in
    let fi ≔ bridge_f_inv C0 C4 in
    let Q0 ≔ W .comp a d e k (W .comp a c d h (W .comp a b c g f)) in
    let Q1 ≔ W .comp a d e k (W .comp a b d (W .comp b c d h g) f) in
    let Q2 ≔ W .comp a b e (W .comp b d e k (W .comp b c d h g)) f in
    let Q3 ≔ W .comp a b e (W .comp b c e (W .comp c d e k h) g) f in
    let Q4 ≔ W .comp a c e (W .comp c d e k h) (W .comp a b c g f) in
    let a1 ≔ cat_whisker_left W a d e k (W .comp a c d h (W .comp a b c g f)) (W .comp a b d (W .comp b c d h g) f)
      (W .assoc a b c d f g h) in
    let a2 ≔ W .assoc a b d e f (W .comp b c d h g) k in
    let a3 ≔ cat_whisker_right W a b e (W .comp b d e k (W .comp b c d h g)) (W .comp b c e (W .comp c d e k h) g) f
      (W .assoc b c d e g h k) in
    let a4 ≔ W .assoc a c d e (W .comp a b c g f) h k in
    let a5 ≔ W .assoc a b c e f g (W .comp c d e k h) in
    let p0 ≔ fi Q0 in let p1 ≔ fi Q1 in let p2 ≔ fi Q2 in let p3 ≔ fi Q3 in let p4 ≔ fi Q4 in
    let b1 ≔ refl fi a1 in let b2 ≔ refl fi a2 in let b3 ≔ refl fi a3 in
    let b4 ≔ refl fi a4 in let b5 ≔ refl fi a5 in
    let lhs ≔ concat A Q0 Q1 Q3 a1 (concat A Q1 Q2 Q3 a2 a3) in
    let rhs ≔ concat A Q0 Q4 Q3 a4 a5 in
    let u0 ≔ concat B p0 p2 p3 (concat B p0 p1 p2 b1 b2) b3 in
    let u1 ≔ concat B p0 p1 p3 b1 (concat B p1 p2 p3 b2 b3) in
    let u2 ≔ concat B p0 p1 p3 b1 (refl fi (concat A Q1 Q2 Q3 a2 a3)) in
    let u3 ≔ refl fi lhs in
    let u4 ≔ refl fi rhs in
    let u5 ≔ concat B p0 p4 p3 b4 b5 in
    concat (Id B p0 p3) u0 u1 u5 (concat_assoc B p0 p1 p2 p3 b1 b2 b3)
      (concat (Id B p0 p3) u1 u2 u5
        (refl ((z ↦ concat B p0 p1 p3 b1 z) : Id B p1 p3 → Id B p0 p3)
          (inverse (Id B p1 p3) (refl fi (concat A Q1 Q2 Q3 a2 a3)) (concat B p1 p2 p3 b2 b3)
            (map_path_concat A B fi Q1 Q2 Q3 a2 a3)))
        (concat (Id B p0 p3) u2 u3 u5
          (inverse (Id B p0 p3) u3 u2 (map_path_concat A B fi Q0 Q1 Q3 a1 (concat A Q1 Q2 Q3 a2 a3)))
          (concat (Id B p0 p3) u3 u4 u5
            (refl ((z ↦ refl fi z) : Id A Q0 Q3 → Id B p0 p3) (pent a b c d e f g h k))
            (map_path_concat A B fi Q0 Q4 Q3 a4 a5))))

def bridge_xca_wildprecat_pentagon : blind_xca_wildprecat_pentagon
  ≔ let l ≔ bridge_xca_wildprecat_of_wildprecats .fst in
    let r ≔ bridge_xca_wildprecat_of_wildprecats .snd .fst in
    (l, (r, (bridge_assoc_of functor_assoc_yoneda,
      bridge_pentagon_transfer functor_assoc_yoneda wild_precat_yoneda_pentagon l r)))

{` ex:add-remove-basepoint: the blind f_+ sends inr u to inr u, ours to
   inr ★; the two pointed maps are identified, and the functor laws are
   transported from ours (module 615). `}
def bridge_plus_fun_homotopy (A B : Type) (f : A → B) (x : Sum A Unit)
  : Id (Sum B Unit) (blind_plus_fun A B f x) (plus_map A B f x)
  ≔ match x [ inl. a ↦ refl (inl. (f a) : Sum B Unit) | inr. u ↦ match u [ star. ↦ refl (inr. star. : Sum B Unit) ] ]

def bridge_plus_hom_path (A B : Type) (f : A → B)
  : Id (BookPointedMap (plus_pointed A) (plus_pointed B)) (blind_plus_hom A B f) (plus_pointed_map A B f)
  ≔ equiv_inverse_map (Id (BookPointedMap (plus_pointed A) (plus_pointed B)) (blind_plus_hom A B f) (plus_pointed_map A B f))
      (PointedHomotopy (plus_pointed A) (plus_pointed B) (blind_plus_hom A B f) (plus_pointed_map A B f))
      (pointed_map_path_equiv (plus_pointed A) (plus_pointed B) (blind_plus_hom A B f) (plus_pointed_map A B f))
      (bridge_plus_fun_homotopy A B f,
       concat_p1 (Sum B Unit) (inr. star.) (inr. star.) (refl (inr. star. : Sum B Unit)))

def bridge_ex_plus_functor : blind_ex_plus_functor
  ≔ ((A ↦ concat (BookPointedMap (plus_pointed A) (plus_pointed A)) (blind_plus_hom A A (x ↦ x))
          (plus_pointed_map A A (x ↦ x)) (book_pointed_identity (plus_pointed A))
          (bridge_plus_hom_path A A (x ↦ x)) (plus_map_id A)),
     (A B C f g ↦
       let X ≔ plus_pointed A in let Y ≔ plus_pointed B in let Z ≔ plus_pointed C in
       concat (BookPointedMap X Z) (blind_plus_hom A C (x ↦ g (f x))) (plus_pointed_map A C (x ↦ g (f x)))
         (book_pointed_compose X Y Z (blind_plus_hom A B f) (blind_plus_hom B C g))
         (bridge_plus_hom_path A C (x ↦ g (f x)))
         (concat (BookPointedMap X Z) (plus_pointed_map A C (x ↦ g (f x)))
            (book_pointed_compose X Y Z (plus_pointed_map A B f) (plus_pointed_map B C g))
            (book_pointed_compose X Y Z (blind_plus_hom A B f) (blind_plus_hom B C g))
            (plus_map_comp A B C f g)
            (inverse (BookPointedMap X Z) (book_pointed_compose X Y Z (blind_plus_hom A B f) (blind_plus_hom B C g))
               (book_pointed_compose X Y Z (plus_pointed_map A B f) (plus_pointed_map B C g))
               (refl (book_pointed_compose X Y Z) (bridge_plus_hom_path A B f) (bridge_plus_hom_path B C g))))))

{` ex:arrow-cat. `}
def bridge_def_arrow_ob (C : BlindPrecat)
  : Id Type (BlindArrowOb (C .fst)) (ArrowPrecat (bridge_p C) .wild .ob) ≔ refl (BlindArrowOb (C .fst))

def bridge_def_arrow_hom (C : BlindPrecat) (u v : BlindArrowOb (C .fst))
  : Id Type (BlindArrowHom (C .fst) u v) (ArrowPrecat (bridge_p C) .wild .hom u v) ≔ refl (BlindArrowHom (C .fst) u v)

{` The composites differ only in the proof of the square (a proposition),
   so the identity on objects and arrows is a strict isomorphism between
   the blind arrow precategory and ours. `}
def BridgeArrowB (C : BlindPrecat) : WildPrecat ≔ bridge_w (blind_arrow_precat C .fst)

def BridgeArrowO (C : BlindPrecat) : WildPrecat ≔ ArrowPrecat (bridge_p C) .wild

def bridge_def_arrow_comp (C : BlindPrecat) (u v w : BlindArrowOb (C .fst)) (m' : BlindArrowHom (C .fst) v w)
  (m : BlindArrowHom (C .fst) u v)
  : Id (BlindArrowHom (C .fst) u w) (blind_arrow_comp (C .fst) u v w m' m) (arrow_cat_comp (bridge_w (C .fst)) u v w m' m)
  ≔ arrow_cat_hom_path (bridge_w (C .fst)) (C .snd) u w (blind_arrow_comp (C .fst) u v w m' m)
      (arrow_cat_comp (bridge_w (C .fst)) u v w m' m) (refl (blind_arrow_comp (C .fst) u v w m' m .fst))

def bridge_arrow_to (C : BlindPrecat) : WildFunctor (BridgeArrowB C) (BridgeArrowO C)
  ≔ (obj ≔ u ↦ u, mor ≔ u v m ↦ m,
     map_id ≔ u ↦ refl (arrow_cat_idn (bridge_w (C .fst)) u),
     map_comp ≔ u v w m m' ↦ bridge_def_arrow_comp C u v w m' m)

def bridge_arrow_from (C : BlindPrecat) : WildFunctor (BridgeArrowO C) (BridgeArrowB C)
  ≔ (obj ≔ u ↦ u, mor ≔ u v m ↦ m,
     map_id ≔ u ↦ refl (arrow_cat_idn (bridge_w (C .fst)) u),
     map_comp ≔ u v w m m' ↦ inverse (BlindArrowHom (C .fst) u w) (blind_arrow_comp (C .fst) u v w m' m)
       (arrow_cat_comp (bridge_w (C .fst)) u v w m' m) (bridge_def_arrow_comp C u v w m' m))

def bridge_arrow_iso_equiv (C : BlindPrecat) (u v : BlindArrowOb (C .fst))
  : Equiv (CatIso (BridgeArrowO C) u v) (CatIso (BridgeArrowB C) u v)
  ≔ quasi_inverse_equiv (CatIso (BridgeArrowO C) u v) (CatIso (BridgeArrowB C) u v)
      (functor_iso (BridgeArrowO C) (BridgeArrowB C) (bridge_arrow_from C) u v)
      (functor_iso (BridgeArrowB C) (BridgeArrowO C) (bridge_arrow_to C) u v)
      (e ↦ cat_iso_path (BridgeArrowO C) u v
         (functor_iso (BridgeArrowB C) (BridgeArrowO C) (bridge_arrow_to C) u v
           (functor_iso (BridgeArrowO C) (BridgeArrowB C) (bridge_arrow_from C) u v e)) e (refl (e .fst)))
      (e ↦ cat_iso_path (BridgeArrowB C) u v
         (functor_iso (BridgeArrowO C) (BridgeArrowB C) (bridge_arrow_from C) u v
           (functor_iso (BridgeArrowB C) (BridgeArrowO C) (bridge_arrow_to C) u v e)) e (refl (e .fst)))

def bridge_def_arrow_dom (C : BlindPrecat)
  : Id (FunctorData (ArrowPrecat (bridge_p C) .wild) (bridge_w (C .fst)))
      (functor_data (bridge_w (blind_arrow_precat C .fst)) (bridge_w (C .fst))
        (bridge_f (blind_arrow_precat C .fst) (C .fst) (blind_arrow_dom C)))
      (functor_data (ArrowPrecat (bridge_p C) .wild) (bridge_w (C .fst)) (arrow_cat_dom (bridge_w (C .fst)) (C .snd)))
  ≔ refl (functor_data (ArrowPrecat (bridge_p C) .wild) (bridge_w (C .fst)) (arrow_cat_dom (bridge_w (C .fst)) (C .snd)))

def bridge_ex_arrow_univalent : blind_ex_arrow_univalent
  ≔ C ↦ cat_univalent_from_equivalences (bridge_w (blind_arrow_precat (C .fst) .fst)) (u v ↦
      compose_equiv (Id (BlindArrowOb (C .fst .fst)) u v) (CatIso (BridgeArrowO (C .fst)) u v)
        (CatIso (BridgeArrowB (C .fst)) u v)
        (cat_idtoiso_equiv (ArrowCategory (bridge_c C) .wild) (ArrowCategory (bridge_c C) .univalent) u v)
        (bridge_arrow_iso_equiv (C .fst) u v))

{` xca:wildcat-of-precats. Isomorphisms in the blind wild precategory of
   wild precategories (for any choice of its laws) are ours (module 644)
   up to the record translation of functors; with the object translations
   (η-inverse) this transfers our univalence of PreCat and Cat (module 647). `}
def bridge_wpc_iso_to (l : BlindFunctorLunit) (r : BlindFunctorRunit) (a : BlindFunctorAssoc) (X Y : BlindWildPrecat)
  (e : CatIso WildPrecatWild (bridge_w X) (bridge_w Y)) : CatIso (bridge_w (blind_wpc_of l r a)) X Y
  ≔ (bridge_f_inv X Y (e .fst),
     ((bridge_f_inv Y X (e .snd .fst .fst), refl (bridge_f_inv Y Y) (e .snd .fst .snd)),
      (bridge_f_inv Y X (e .snd .snd .fst), refl (bridge_f_inv X X) (e .snd .snd .snd))))

def bridge_wpc_iso_from (l : BlindFunctorLunit) (r : BlindFunctorRunit) (a : BlindFunctorAssoc) (X Y : BlindWildPrecat)
  (e : CatIso (bridge_w (blind_wpc_of l r a)) X Y) : CatIso WildPrecatWild (bridge_w X) (bridge_w Y)
  ≔ (bridge_f X Y (e .fst),
     ((bridge_f Y X (e .snd .fst .fst), refl (bridge_f Y Y) (e .snd .fst .snd)),
      (bridge_f Y X (e .snd .snd .fst), refl (bridge_f X X) (e .snd .snd .snd))))

def bridge_wpc_iso (l : BlindFunctorLunit) (r : BlindFunctorRunit) (a : BlindFunctorAssoc) (X Y : BlindWildPrecat)
  : Equiv (CatIso WildPrecatWild (bridge_w X) (bridge_w Y)) (CatIso (bridge_w (blind_wpc_of l r a)) X Y)
  ≔ quasi_inverse_equiv (CatIso WildPrecatWild (bridge_w X) (bridge_w Y)) (CatIso (bridge_w (blind_wpc_of l r a)) X Y)
      (bridge_wpc_iso_to l r a X Y) (bridge_wpc_iso_from l r a X Y) (e ↦ refl e) (e ↦ refl e)

def bridge_tp (x : Σ BlindWildPrecat (C ↦ blind_is_precat_prop C .fst)) : PreCatWild .ob ≔ (bridge_w (x .fst), x .snd)

def bridge_tp_inv (x : PreCatWild .ob) : Σ BlindWildPrecat (C ↦ blind_is_precat_prop C .fst)
  ≔ (bridge_w_inv (x .fst), x .snd)

def bridge_tc (x : Σ BlindWildPrecat (C ↦ blind_is_cat_prop C .fst)) : CatWild .ob
  ≔ ((bridge_w (x .fst), x .snd .fst), x .snd .snd)

def bridge_tc_inv (x : CatWild .ob) : Σ BlindWildPrecat (C ↦ blind_is_cat_prop C .fst)
  ≔ (bridge_w_inv (x .fst .fst), (x .fst .snd, x .snd))

def bridge_xca_wildcat_of_precats : blind_xca_wildcat_of_precats
  ≔ l r a ↦
    (cat_univalent_from_equivalences (bridge_w (blind_full_subcat (blind_wpc_of l r a) blind_is_precat_prop)) (x y ↦
       compose_equiv (Id (Σ BlindWildPrecat (C ↦ blind_is_precat_prop C .fst)) x y)
         (Id (PreCatWild .ob) (bridge_tp x) (bridge_tp y))
         (CatIso (bridge_w (blind_wpc_of l r a)) (x .fst) (y .fst))
         (quasi_inverse_equiv (Id (Σ BlindWildPrecat (C ↦ blind_is_precat_prop C .fst)) x y)
            (Id (PreCatWild .ob) (bridge_tp x) (bridge_tp y)) (p ↦ refl bridge_tp p) (q ↦ refl bridge_tp_inv q)
            (p ↦ refl p) (q ↦ refl q))
         (compose_equiv (Id (PreCatWild .ob) (bridge_tp x) (bridge_tp y))
            (CatIso WildPrecatWild (bridge_w (x .fst)) (bridge_w (y .fst)))
            (CatIso (bridge_w (blind_wpc_of l r a)) (x .fst) (y .fst))
            (cat_idtoiso_equiv PreCatWild precat_wild_univalent (bridge_tp x) (bridge_tp y))
            (bridge_wpc_iso l r a (x .fst) (y .fst)))),
     cat_univalent_from_equivalences (bridge_w (blind_full_subcat (blind_wpc_of l r a) blind_is_cat_prop)) (x y ↦
       compose_equiv (Id (Σ BlindWildPrecat (C ↦ blind_is_cat_prop C .fst)) x y)
         (Id (CatWild .ob) (bridge_tc x) (bridge_tc y))
         (CatIso (bridge_w (blind_wpc_of l r a)) (x .fst) (y .fst))
         (quasi_inverse_equiv (Id (Σ BlindWildPrecat (C ↦ blind_is_cat_prop C .fst)) x y)
            (Id (CatWild .ob) (bridge_tc x) (bridge_tc y)) (p ↦ refl bridge_tc p) (q ↦ refl bridge_tc_inv q)
            (p ↦ refl p) (q ↦ refl q))
         (compose_equiv (Id (CatWild .ob) (bridge_tc x) (bridge_tc y))
            (CatIso WildPrecatWild (bridge_w (x .fst)) (bridge_w (y .fst)))
            (CatIso (bridge_w (blind_wpc_of l r a)) (x .fst) (y .fst))
            (cat_idtoiso_equiv CatWild cat_wild_univalent (bridge_tc x) (bridge_tc y))
            (bridge_wpc_iso l r a (x .fst) (y .fst)))))

{` ex:loop-functor. The book only says that the pointing path of Ω k is
   "easily remedied using the path groupoid laws". The blind statement uses
   chapter 4's loops_map_point (the inverse of loop_conjugate_unit, an
   explicit composite of path-algebra laws); ours (module 616) uses the
   inverse of loop_conj_unit, defined by path induction. The two 2-paths
   agree: by path induction it suffices to compare them at refl, which is
   a 3-dimensional coherence of concat_1p, concat_p1, inverse_refl and
   concat_inverse_right (naturality of concat_1p, λ_refl = ρ_refl from
   module 281, and the typal β-rules). The functor laws are then
   transported from ours. `}
def bridge_lp_nat (A : Type) (a y : A) (v w : Id A a y) (r : Id (Id A a y) v w)
  : Id (Id (Id A a y) (concat A a a y (refl a) v) w)
      (concat (Id A a y) (concat A a a y (refl a) v) (concat A a a y (refl a) w) w
        (refl (concat A a a y (refl a)) r) (concat_1p A a y w))
      (concat (Id A a y) (concat A a a y (refl a) v) v w (concat_1p A a y v) r)
  ≔ J (Id A a y) v
      (w r ↦ Id (Id (Id A a y) (concat A a a y (refl a) v) w)
        (concat (Id A a y) (concat A a a y (refl a) v) (concat A a a y (refl a) w) w
          (refl (concat A a a y (refl a)) r) (concat_1p A a y w))
        (concat (Id A a y) (concat A a a y (refl a) v) v w (concat_1p A a y v) r))
      (concat (Id (Id A a y) (concat A a a y (refl a) v) v)
         (concat (Id A a y) (concat A a a y (refl a) v) (concat A a a y (refl a) v) v
           (refl (concat A a a y (refl a) v)) (concat_1p A a y v))
         (concat_1p A a y v)
         (concat (Id A a y) (concat A a a y (refl a) v) v v (concat_1p A a y v) (refl v))
         (concat_1p (Id A a y) (concat A a a y (refl a) v) v (concat_1p A a y v))
         (inverse (Id (Id A a y) (concat A a a y (refl a) v) v)
            (concat (Id A a y) (concat A a a y (refl a) v) v v (concat_1p A a y v) (refl v))
            (concat_1p A a y v)
            (concat_p1 (Id A a y) (concat A a a y (refl a) v) v (concat_1p A a y v))))
      w r

def bridge_lp_s1t1 (A : Type) (a : A) (u : Id A a a)
  : Id (Id (Id A a a) (concat A a a a (refl a) (concat A a a a (refl a) u)) (concat A a a a (refl a) u))
      (refl (concat A a a a (refl a)) (concat_1p A a a u)) (concat_1p A a a (concat A a a a (refl a) u))
  ≔ concat_cancel_right (Id A a a) (concat A a a a (refl a) (concat A a a a (refl a) u)) (concat A a a a (refl a) u) u
      (refl (concat A a a a (refl a)) (concat_1p A a a u)) (concat_1p A a a (concat A a a a (refl a) u))
      (concat_1p A a a u)
      (bridge_lp_nat A a a (concat A a a a (refl a) u) u (concat_1p A a a u))

def bridge_lp_s2 (A : Type) (a : A)
  : Id (Id (Id A a a) (concat A a a a (refl a) (inverse A a a (refl a))) (refl a))
      (concat_inverse_right A a a (refl a))
      (concat (Id A a a) (concat A a a a (refl a) (inverse A a a (refl a))) (concat A a a a (refl a) (refl a)) (refl a)
        (refl (concat A a a a (refl a)) (inverse_refl A a)) (concat_p1 A a a (refl a)))
  ≔ let u ≔ inverse A a a (refl a) in
    let cu ≔ concat A a a a (refl a) u in
    let c1 ≔ concat A a a a (refl a) (refl a) in
    let apir ≔ refl (concat A a a a (refl a)) (inverse_refl A a) in
    let base ≔ concat (Id A a a) cu u (refl a) (concat_1p A a a u) (inverse_refl A a) in
    let t23 ≔ concat (Id A a a) cu c1 (refl a) apir (concat_p1 A a a (refl a)) in
    let mid ≔ concat (Id A a a) cu c1 (refl a) apir (concat_1p A a a (refl a)) in
    let e1 : Id (Id (Id A a a) cu (refl a)) t23 mid
      ≔ refl ((z ↦ concat (Id A a a) cu c1 (refl a) apir z) : Id (Id A a a) c1 (refl a) → Id (Id A a a) cu (refl a))
          (concat_p1_1p_refl A a) in
    let e2 : Id (Id (Id A a a) cu (refl a)) mid base ≔ bridge_lp_nat A a a u (refl a) (inverse_refl A a) in
    let jb : Id (Id (Id A a a) cu (refl a)) base (concat_inverse_right A a a (refl a))
      ≔ Jβ A a (y p ↦ Id (Id A a a) (concat A a y a p (inverse A a y p)) (refl a)) base in
    concat (Id (Id A a a) cu (refl a)) (concat_inverse_right A a a (refl a)) base t23
      (inverse (Id (Id A a a) cu (refl a)) base (concat_inverse_right A a a (refl a)) jb)
      (inverse (Id (Id A a a) cu (refl a)) t23 base (concat (Id (Id A a a) cu (refl a)) t23 mid base e1 e2))

def bridge_lp_base (A : Type) (a : A)
  : Id (Id (Id A a a) (pointed_loop_conjugate A a a (refl a) (refl a)) (refl a))
      (loop_conjugate_unit A a a (refl a)) (loop_conj_refl A a (refl a))
  ≔ let u ≔ inverse A a a (refl a) in
    let cu ≔ concat A a a a (refl a) u in
    let ccu ≔ concat A a a a (refl a) cu in
    let s2 ≔ concat_inverse_right A a a (refl a) in
    let t1 ≔ concat_1p A a a cu in
    let t23 ≔ concat (Id A a a) cu (concat A a a a (refl a) (refl a)) (refl a)
                (refl (concat A a a a (refl a)) (inverse_refl A a)) (concat_p1 A a a (refl a)) in
    concat (Id (Id A a a) ccu (refl a))
      (loop_conjugate_unit A a a (refl a)) (concat (Id A a a) ccu cu (refl a) t1 s2) (loop_conj_refl A a (refl a))
      (refl ((z ↦ concat (Id A a a) ccu cu (refl a) z s2) : Id (Id A a a) ccu cu → Id (Id A a a) ccu (refl a))
         (bridge_lp_s1t1 A a u))
      (refl ((z ↦ concat (Id A a a) ccu cu (refl a) t1 z) : Id (Id A a a) cu (refl a) → Id (Id A a a) ccu (refl a))
         (bridge_lp_s2 A a))

def bridge_loop_unit_agree (A : Type) (a x : A) (p : Id A a x)
  : Id (Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a))
      (loop_conjugate_unit A a x p) (loop_conj_unit A a x p)
  ≔ J A a (x p ↦ Id (Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a))
        (loop_conjugate_unit A a x p) (loop_conj_unit A a x p))
      (concat (Id (Id A a a) (pointed_loop_conjugate A a a (refl a) (refl a)) (refl a))
         (loop_conjugate_unit A a a (refl a)) (loop_conj_refl A a (refl a)) (loop_conj_unit A a a (refl a))
         (bridge_lp_base A a) (loop_conj_unit_refl A a))
      x p

def bridge_loops_hom_path (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (BookPointedMap (Omega X) (Omega Y)) (blind_loops_hom X Y k) (loop_functor_map X Y k)
  ≔ (refl (loops_map X Y k),
     refl ((z ↦ inverse (Loop Y) (loops_map X Y k (refl (X .point))) (refl (Y .point)) z)
             : Id (Loop Y) (loops_map X Y k (refl (X .point))) (refl (Y .point))
               → Id (Loop Y) (refl (Y .point)) (loops_map X Y k (refl (X .point))))
       (bridge_loop_unit_agree (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd)))

def bridge_ex_loop_functor : blind_ex_loop_functor
  ≔ ((X ↦ concat (BookPointedMap (Omega X) (Omega X)) (blind_loops_hom X X (book_pointed_identity X))
          (loop_functor_map X X (book_pointed_identity X)) (book_pointed_identity (Omega X))
          (bridge_loops_hom_path X X (book_pointed_identity X)) (LoopFunctor .map_id X)),
     (X Y Z f g ↦
       concat (BookPointedMap (Omega X) (Omega Z)) (blind_loops_hom X Z (book_pointed_compose X Y Z f g))
         (loop_functor_map X Z (book_pointed_compose X Y Z f g))
         (book_pointed_compose (Omega X) (Omega Y) (Omega Z) (blind_loops_hom X Y f) (blind_loops_hom Y Z g))
         (bridge_loops_hom_path X Z (book_pointed_compose X Y Z f g))
         (concat (BookPointedMap (Omega X) (Omega Z)) (loop_functor_map X Z (book_pointed_compose X Y Z f g))
            (book_pointed_compose (Omega X) (Omega Y) (Omega Z) (loop_functor_map X Y f) (loop_functor_map Y Z g))
            (book_pointed_compose (Omega X) (Omega Y) (Omega Z) (blind_loops_hom X Y f) (blind_loops_hom Y Z g))
            (LoopFunctor .map_comp X Y Z f g)
            (inverse (BookPointedMap (Omega X) (Omega Z))
               (book_pointed_compose (Omega X) (Omega Y) (Omega Z) (blind_loops_hom X Y f) (blind_loops_hom Y Z g))
               (book_pointed_compose (Omega X) (Omega Y) (Omega Z) (loop_functor_map X Y f) (loop_functor_map Y Z g))
               (refl (book_pointed_compose (Omega X) (Omega Y) (Omega Z))
                  (bridge_loops_hom_path X Y f) (bridge_loops_hom_path Y Z g))))))
