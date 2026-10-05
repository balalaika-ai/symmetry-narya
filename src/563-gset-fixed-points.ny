export "505-gset-core-litmus"

{` Chapter 5 (actions.tex), helper for sec:gsets and sec:fixpts-orbits:
   a point x of X(sh_G) fixed by all of USym G extends to an invariant map
   (an element of X^hG) with value x at sh_G, and evaluation at sh_G is an
   equivalence from X^hG to the fixed points of X(sh_G). Used for
   xca:Ad-triv-abelian and xca:Gset-A->B. `}

{` Path algebra: (r r'⁻¹) r' = r. `}
def gset_cancel_path (A : Type) (a x : A) (r r' : Id A a x)
  : Id (Id A a x) (concat A a a x (concat A a x a r (inverse A a x r')) r') r
  ≔ calc
      concat A a a x (concat A a x a r (inverse A a x r')) r'
      = concat A a x x r (concat A x a x (inverse A a x r') r')
        by concat_assoc A a x a x r (inverse A a x r') r'
      = concat A a x x r (refl x) by refl (concat A a x x r) (concat_inverse_left A a x r')
      = r by concat_p1 A a x r ∎

{` A point x of X(sh_G) fixed by every g : USym G extends to an invariant
   map z ↦ p · x (p : sh_G = z, independent of p), with value x at sh_G. `}
def gset_fixed_point_wconst (G : Group) (X : GSet G) (x : gset_underlying G X)
  (fix : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x) (z : BG G .carrier)
  : WeaklyConstant (Id (BG G .carrier) (shape G) z) (X z .fst) (r ↦ gset_act G X (shape G) z r x)
  ≔ let B ≔ BG G .carrier in
    r r' ↦ let c ≔ concat B (shape G) z (shape G) r (inverse B (shape G) z r') in
      calc
        gset_act G X (shape G) z r x
        = gset_act G X (shape G) z (concat B (shape G) (shape G) z c r') x
          by refl ((q ↦ gset_act G X (shape G) z q x) : Id B (shape G) z → X z .fst)
            (inverse (Id B (shape G) z) (concat B (shape G) (shape G) z c r') r (gset_cancel_path B (shape G) z r r'))
        = gset_act G X (shape G) z r' (gset_act G X (shape G) (shape G) c x)
          by gset_act_concat G X (shape G) (shape G) z c r' x
        = gset_act G X (shape G) z r' x by refl (gset_act G X (shape G) z r') (fix c) ∎

def gset_fixed_point_extension (G : Group) (X : GSet G) (x : gset_underlying G X)
  (fix : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x) : InvariantMaps G X
  ≔ z ↦ weakly_constant_rec (Id (BG G .carrier) (shape G) z) (X z .fst) (r ↦ gset_act G X (shape G) z r x) (X z .snd)
      (gset_fixed_point_wconst G X x fix z) (bg_connected G .snd (shape G) z)

def gset_fixed_point_extension_beta (G : Group) (X : GSet G) (x : gset_underlying G X)
  (fix : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
  : Id (gset_underlying G X) (gset_fixed_point_extension G X x fix (shape G)) x
  ≔ let B ≔ BG G .carrier in
    let L ≔ Id B (shape G) (shape G) in
    let wrec : Mere L → gset_underlying G X
      ≔ m ↦ weakly_constant_rec L (gset_underlying G X) (r ↦ gset_act G X (shape G) (shape G) r x)
          (gset_underlying_set G X) (gset_fixed_point_wconst G X x fix (shape G)) m in
    concat (gset_underlying G X) (gset_fixed_point_extension G X x fix (shape G))
      (gset_act G X (shape G) (shape G) (refl (shape G)) x) x
      (refl wrec (mere_isprop L (bg_connected G .snd (shape G) (shape G)) (mere L (refl (shape G)))))
      (gset_act_refl G X (shape G) x)


{` The fixed points of the action on X(sh_G). `}
def GSetFixedPoints (G : Group) (X : GSet G) : Type
  ≔ Σ (gset_underlying G X) (x ↦ (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)

{` An invariant map is fixed at sh_G: g · s(sh_G) = s(sh_G) (apd of s). `}
def invariant_map_fixed (G : Group) (X : GSet G) (s : InvariantMaps G X) : GSetFixedPoints G X
  ≔ (s (shape G), g ↦ pathover_transport_equiv (BG G .carrier) (z ↦ X z .fst) (shape G) (shape G) g
      (s (shape G)) (s (shape G)) .map (refl s g))

{` Two invariant maps agreeing at sh_G agree everywhere. `}
def invariant_maps_eq_at_shape (G : Group) (X : GSet G) (s s' : InvariantMaps G X)
  (e : Id (gset_underlying G X) (s (shape G)) (s' (shape G))) : Id (InvariantMaps G X) s s'
  ≔ funext (BG G .carrier) (z ↦ X z .fst) s s'
      (connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
        (z ↦ Id (X z .fst) (s z) (s' z)) (z ↦ X z .snd (s z) (s' z)) e)

def gset_fixed_points_prop (G : Group) (X : GSet G) (x : gset_underlying G X)
  : isProp ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
  ≔ pi_prop (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)
      (g ↦ gset_underlying_set G X (gset_usym_act G X g x) x)

{` X^hG ≃ fixed points of X(sh_G), by evaluation at sh_G. `}
def invariant_maps_fixed_equiv (G : Group) (X : GSet G) : Equiv (InvariantMaps G X) (GSetFixedPoints G X)
  ≔ quasi_inverse_equiv (InvariantMaps G X) (GSetFixedPoints G X)
      (invariant_map_fixed G X) (u ↦ gset_fixed_point_extension G X (u .fst) (u .snd))
      (s ↦ invariant_maps_eq_at_shape G X
        (gset_fixed_point_extension G X (s (shape G)) (invariant_map_fixed G X s .snd)) s
        (gset_fixed_point_extension_beta G X (s (shape G)) (invariant_map_fixed G X s .snd)))
      (u ↦ subtype_equal (gset_underlying G X) (x ↦ (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
        (gset_fixed_points_prop G X)
        (invariant_map_fixed G X (gset_fixed_point_extension G X (u .fst) (u .snd))) u
        (gset_fixed_point_extension_beta G X (u .fst) (u .snd)))

{` Litmus: every point of a trivial G-set is fixed, so it extends to the
   constant invariant map. `}
def trivial_gset_fixed_point (G : Group) (S : SetTypes) (s : S .fst) : GSetFixedPoints G (gset_trivial G S)
  ≔ (s, g ↦ gset_trivial_act G S (shape G) (shape G) g s)
