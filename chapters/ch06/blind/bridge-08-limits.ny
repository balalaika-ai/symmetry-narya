import "bridge-00-core"
import "../../../src/665-products-and-coproducts"
import "../../../src/666-pullbacks"

{` Bridges for cats.tex, section "Limits and colimits" (blind file
   08). Cones, cone arrows and pullbacks are ours on the nose; the
   universal properties differ only by currying the cone and by the
   orientation of contractibility (blind BookIsContr, ours native isContr). `}

def bridge_def_cone (C : BlindWildPrecat) (A B : C .ob) : Id Type (BlindCone C A B) (CatCone (bridge_w C) A B)
  ≔ refl (BlindCone C A B)

def bridge_def_cone_hom (C : BlindWildPrecat) (A B : C .ob) (x p : BlindCone C A B)
  : Id Type (BlindConeHom C A B x p) (ConeFactorization (bridge_w C) A B x p) ≔ refl (BlindConeHom C A B x p)

{` def:prod-in-a-cat. `}
def bridge_product_to_blind (C : BlindWildPrecat) (A B : C .ob) (p : BlindCone C A B)
  (h : IsProductCone (bridge_w C) A B p) : BlindIsProductCone C A B p
  ≔ X x1 x2 ↦ book_contraction (BlindConeHom C A B (X, (x1, x2)) p) (h (X, (x1, x2)))

def bridge_product_from_blind (C : BlindWildPrecat) (A B : C .ob) (p : BlindCone C A B)
  (h : BlindIsProductCone C A B p) : IsProductCone (bridge_w C) A B p
  ≔ x ↦ native_contraction (BlindConeHom C A B x p) (h (x .fst) (x .snd .fst) (x .snd .snd))

def bridge_blind_product_prop (C : BlindWildPrecat) (A B : C .ob) (p : BlindCone C A B)
  : isProp (BlindIsProductCone C A B p)
  ≔ pi_prop (C .ob) (X ↦ (x1 : C .hom X A) (x2 : C .hom X B) → BookIsContr (BlindConeHom C A B (X, (x1, x2)) p))
      (X ↦ pi_prop (C .hom X A) (x1 ↦ (x2 : C .hom X B) → BookIsContr (BlindConeHom C A B (X, (x1, x2)) p))
        (x1 ↦ pi_prop (C .hom X B) (x2 ↦ BookIsContr (BlindConeHom C A B (X, (x1, x2)) p))
          (x2 ↦ book_iscontr_isprop (BlindConeHom C A B (X, (x1, x2)) p))))

def bridge_def_is_product_cone (C : BlindWildPrecat) (A B : C .ob) (p : BlindCone C A B)
  : Equiv (IsProductCone (bridge_w C) A B p) (BlindIsProductCone C A B p)
  ≔ iff_equiv (IsProductCone (bridge_w C) A B p) (BlindIsProductCone C A B p)
      (is_product_cone_prop (bridge_w C) A B p) (bridge_blind_product_prop C A B p)
      (bridge_product_to_blind C A B p) (bridge_product_from_blind C A B p)

def bridge_def_product_cone (C : BlindWildPrecat) (A B : C .ob)
  : Equiv (ProductCone (bridge_w C) A B) (BlindProductCone C A B)
  ≔ family_equiv (BlindCone C A B) (IsProductCone (bridge_w C) A B) (BlindIsProductCone C A B)
      (bridge_def_is_product_cone C A B)

{` xca:product-cone-prop. `}
def bridge_xca_product_cone_prop : blind_xca_product_cone_prop
  ≔ C u A B ↦ prop_from_equiv (BlindProductCone C A B) (ProductCone (bridge_w C) A B)
      (canonical_inverse_equiv (ProductCone (bridge_w C) A B) (BlindProductCone C A B) (bridge_def_product_cone C A B))
      (product_cone_prop (bridge_w C) u A B)

{` def:product-cones-as-terminal. The arrows of the blind cone precategory
   are ours (ConeFactorization); ours states IsProductCone as terminality
   in cone_precat_wild (product_cone_is_terminal_cone, by refl). `}
def bridge_rem_product_cones_as_terminal : blind_rem_product_cones_as_terminal
  ≔ C A B p ↦
    (h x ↦ book_contraction (BlindConeHom (C .fst) A B x p)
       (transport Type (T ↦ T) (IsProductCone (bridge_w (C .fst)) A B p)
          ((X : cone_precat_wild (bridge_w (C .fst)) (C .snd) A B .ob)
             → isContr (cone_precat_wild (bridge_w (C .fst)) (C .snd) A B .hom X p))
          (product_cone_is_terminal_cone (bridge_w (C .fst)) (C .snd) A B p)
          (bridge_product_from_blind (C .fst) A B p h) x),
     t ↦ bridge_product_to_blind (C .fst) A B p (x ↦ native_contraction (BlindConeHom (C .fst) A B x p) (t x)))

{` def:coprod-in-a-cat. `}
def bridge_def_cocone (C : BlindWildPrecat) (A B : C .ob) : Id Type (BlindCocone C A B) (CatCocone (bridge_w C) A B)
  ≔ refl (BlindCocone C A B)

def bridge_def_is_coproduct_to_blind (C : BlindWildPrecat) (A B : C .ob) (q : BlindCocone C A B)
  (h : IsCoproductCocone (bridge_w C) A B q) : BlindIsCoproductCocone C A B q
  ≔ X x1 x2 ↦ book_contraction (CoconeFactorization (bridge_w C) A B q (X, (x1, x2))) (h (X, (x1, x2)))

def bridge_def_is_coproduct_from_blind (C : BlindWildPrecat) (A B : C .ob) (q : BlindCocone C A B)
  (h : BlindIsCoproductCocone C A B q) : IsCoproductCocone (bridge_w C) A B q
  ≔ x ↦ native_contraction (CoconeFactorization (bridge_w C) A B q x) (h (x .fst) (x .snd .fst) (x .snd .snd))

{` def:pullback, xca:univpropofpullback (corrected), example at line 1558. `}
def bridge_def_pullback (B C D : Type) (f : B → D) (g : C → D)
  : Id Type (BlindPullback B C D f g) (TypePullback B C D f g) ≔ refl (BlindPullback B C D f g)

def bridge_xca_univpropofpullback_corrected : blind_xca_univpropofpullback_corrected
  ≔ A B C D f g ↦ pullback_universal_property A B C D f g

def bridge_ex_preimage_pullback : blind_ex_preimage_pullback ≔ C D d g ↦ pullback_point_fiber_equiv C D d g
