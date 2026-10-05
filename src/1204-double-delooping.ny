export "1202-group-center"
export "1203-universal-cover"

{` Chapter 12, sec:abel-groups-simply (abelian.tex 345-566): pointed simply
   connected 2-types, the Eckmann-Hilton argument, the delooping
   BB G ≔ Ũ_{BG÷} U = Σ(X : U) ‖BG÷ = X‖₀ and the identification Ω(BB G) = G
   for abelian G (first half of thm:abelian-groups-weq-sc2types).

   Size: in the book BB G lives in a successor universe and the footnote
   replaces it by an essentially small copy (Replacement). Narya has a
   single universe Type, so BB G : Type directly; no replacement is used. `}

{` eq:horizontal-comp. For p, q : x = y, r, s : y = z, g : p = q, h : r = s:
   ap_{-·q}(h) · ap_{r·-}(g) = ap_{s·-}(g) · ap_{-·p}(h) (book order); in
   concatenation order (ap_{t ↦ t·r} g then ap_{q·-} h) = (ap_{p·-} h then
   ap_{t ↦ t·s} g). Proof by induction on h, as in the book. `}
def horizontal_interchange (A : Type) (x y z : A) (p q : Id A x y) (r s : Id A y z)
  (g : Id (Id A x y) p q) (h : Id (Id A y z) r s)
  : Id (Id (Id A x z) (concat A x y z p r) (concat A x y z q s))
      (concat (Id A x z) (concat A x y z p r) (concat A x y z q r) (concat A x y z q s)
        (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g) (refl (concat A x y z q) h))
      (concat (Id A x z) (concat A x y z p r) (concat A x y z p s) (concat A x y z q s)
        (refl (concat A x y z p) h) (refl ((t ↦ concat A x y z t s) : Id A x y → Id A x z) g))
  ≔ J (Id A y z) r
      (s h ↦ Id (Id (Id A x z) (concat A x y z p r) (concat A x y z q s))
        (concat (Id A x z) (concat A x y z p r) (concat A x y z q r) (concat A x y z q s)
          (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g) (refl (concat A x y z q) h))
        (concat (Id A x z) (concat A x y z p r) (concat A x y z p s) (concat A x y z q s)
          (refl (concat A x y z p) h) (refl ((t ↦ concat A x y z t s) : Id A x y → Id A x z) g)))
      (calc
        concat (Id A x z) (concat A x y z p r) (concat A x y z q r) (concat A x y z q r)
            (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g) (refl (concat A x y z q r))
          = refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g
          by concat_p1 (Id A x z) (concat A x y z p r) (concat A x y z q r)
            (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g)
        = concat (Id A x z) (concat A x y z p r) (concat A x y z p r) (concat A x y z q r)
            (refl (concat A x y z p r)) (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g)
          by inverse (Id (Id A x z) (concat A x y z p r) (concat A x y z q r))
            (concat (Id A x z) (concat A x y z p r) (concat A x y z p r) (concat A x y z q r)
              (refl (concat A x y z p r)) (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g))
            (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g)
            (concat_1p (Id A x z) (concat A x y z p r) (concat A x y z q r)
              (refl ((t ↦ concat A x y z t r) : Id A x y → Id A x z) g)) ∎)
      s h

{` Eckmann-Hilton: 2-loops commute. A 2-loop h extends by path induction to
   a homotopy K : Π(t : a = y) t = t with K(refl) = h (typal β-rule), and
   naturality of K along a 2-loop g gives g · h = h · g. (The book derives
   it from eq:horizontal-comp; here the extension trick avoids comparing the
   two unit laws of concatenation at refl, which agree only propositionally.) `}
def two_loop_extension (A : Type) (a : A) (h : Id (Id A a a) (refl a) (refl a)) (y : A) (t : Id A a y)
  : Id (Id A a y) t t
  ≔ J A a (y t ↦ Id (Id A a y) t t) h y t

def eckmann_hilton (A : Type) (a : A) (g h : Id (Id A a a) (refl a) (refl a))
  : Id (Id (Id A a a) (refl a) (refl a))
      (concat (Id A a a) (refl a) (refl a) (refl a) g h) (concat (Id A a a) (refl a) (refl a) (refl a) h g)
  ≔ let L ≔ Id (Id A a a) (refl a) (refl a) in
    let K ≔ two_loop_extension A a h a in
    let β : Id L h (K (refl a)) ≔ Jβ A a (y t ↦ Id (Id A a y) t t) h in
    calc
      concat (Id A a a) (refl a) (refl a) (refl a) g h
        = concat (Id A a a) (refl a) (refl a) (refl a) g (K (refl a))
        by refl (concat (Id A a a) (refl a) (refl a) (refl a) g) β
      = concat (Id A a a) (refl a) (refl a) (refl a) (K (refl a)) g
        by naturality (Id A a a) (Id A a a) (t ↦ t) (t ↦ t) K (refl a) (refl a) g
      = concat (Id A a a) (refl a) (refl a) (refl a) h g
        by refl ((k ↦ concat (Id A a a) (refl a) (refl a) (refl a) k g) : L → L)
          (inverse L h (K (refl a)) β) ∎

{` The type of pointed simply connected 2-types (abelian.tex 462):
   Σ((A, a) : U_*) isconn(A) × isconn(a = a) × isgrpd(a = a). `}
def SC2Structure (X : Pointed) : Type
  ≔ Product (Connected (X .carrier)) (Product (Connected (Loop X)) (isGroupoid (Loop X)))

def sc2_structure_prop (X : Pointed) : isProp (SC2Structure X)
  ≔ product_prop (Connected (X .carrier)) (Product (Connected (Loop X)) (isGroupoid (Loop X)))
      (connected_prop (X .carrier))
      (product_prop (Connected (Loop X)) (isGroupoid (Loop X)) (connected_prop (Loop X)) (isgroupoid_isprop (Loop X)))

def SimplyConnectedTwoType : Type ≔ Σ Pointed SC2Structure

def sc2_path (X Y : SimplyConnectedTwoType) (p : Id Pointed (X .fst) (Y .fst)) : Id SimplyConnectedTwoType X Y
  ≔ subtype_equal Pointed SC2Structure sc2_structure_prop X Y p

{` A pointed simply connected 2-type is a 2-type: all its identity types are
   groupoids (connectedness transports the condition at the base point). `}
def sc2_two_type (X : SimplyConnectedTwoType) (x y : X .fst .carrier) : isGroupoid (Id (X .fst .carrier) x y)
  ≔ connected_pair_elim native_truncation (X .fst .carrier) (X .snd .fst) (X .fst .point)
      (x y ↦ isGroupoid (Id (X .fst .carrier) x y)) (x y ↦ isgroupoid_isprop (Id (X .fst .carrier) x y))
      (X .snd .snd .snd) x y

{` The group Ω(A, a) with B Ω(A, a) ≔ (a = a, refl a), and its
   abelianness (Eckmann-Hilton). `}
def sc2_loop_pcg (X : SimplyConnectedTwoType) : PointedConnectedGroupoid
  ≔ (Loop (X .fst), refl (X .fst .point), X .snd .snd .fst, X .snd .snd .snd)

def sc2_loop_group (X : SimplyConnectedTwoType) : Group ≔ mkgroup (sc2_loop_pcg X)

def sc2_loop_group_abelian (X : SimplyConnectedTwoType) : IsAbelian (sc2_loop_group X)
  ≔ g h ↦ eckmann_hilton (X .fst .carrier) (X .fst .point) h g

def sc2_loops (X : SimplyConnectedTwoType) : AbelianGroup ≔ (sc2_loop_group X, sc2_loop_group_abelian X)

{` BB G ≔ Ũ_{BG÷} U = Σ(X : U) ‖BG÷ = X‖₀, pointed at (BG÷, |refl|₀). This
   does not use that G is abelian (the book's margin remark). `}
def BB (G : Group) : Pointed ≔ univ_cover_pointed Type (BG G .carrier)

def bb_point (G : Group) : BB G .carrier ≔ univ_cover_point Type (BG G .carrier)

def bb_carrier_groupoid (G : Group) (u : BB G .carrier) : isGroupoid (u .fst)
  ≔ set_trunc_rec (Id Type (BG G .carrier) (u .fst)) (isGroupoid (u .fst))
      (prop_is_set (isGroupoid (u .fst)) (isgroupoid_isprop (u .fst)))
      (p ↦ transport Type isGroupoid (BG G .carrier) (u .fst) p (bg_groupoid G)) (u .snd)

{` BB G is a 2-type. `}
def bb_two_type (G : Group) (u v : BB G .carrier) : isGroupoid (Id (BB G .carrier) u v)
  ≔ hlevel_to_groupoid (Id (BB G .carrier) u v)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (UnivCoverPath Type (BG G .carrier) u v) (Id (BB G .carrier) u v)
        (canonical_inverse_equiv (Id (BB G .carrier) u v) (UnivCoverPath Type (BG G .carrier) u v)
          (univ_cover_path_equiv Type (BG G .carrier) u v))
        (subtype_hlevel (suc. (suc. zero.)) (Id Type (u .fst) (v .fst))
          (p ↦ Id (SetTrunc (Id Type (BG G .carrier) (v .fst)))
            (trunc_path_compose Type (BG G .carrier) (u .fst) (v .fst) (set_trunc (Id Type (u .fst) (v .fst)) p) (u .snd))
            (v .snd))
          (groupoid_to_hlevel (Id Type (u .fst) (v .fst))
            (universe_paths_groupoid (u .fst) (v .fst) (bb_carrier_groupoid G v)))
          (p ↦ set_trunc_set (Id Type (BG G .carrier) (v .fst))
            (trunc_path_compose Type (BG G .carrier) (u .fst) (v .fst) (set_trunc (Id Type (u .fst) (v .fst)) p) (u .snd))
            (v .snd))))

def bb_simply_connected (G : Group) : SimplyConnected (BB G) ≔ univ_cover_simply_connected Type (BG G .carrier)

def bb_sc2 (G : Group) : SimplyConnectedTwoType
  ≔ (BB G, (bb_simply_connected G .fst, (bb_simply_connected G .snd, bb_two_type G (bb_point G) (bb_point G))))

{` Ω(BB G) and the center: (pt = pt) ≃ B Z(G) (proof of
   lemma:universal-cover-simply-connected), followed by ev_{sh_G} = B z_G. `}
def bb_loops_evaluation (G : Group) (r : Loop (BB G)) : BG G .carrier
  ≔ center_evaluation G (univ_cover_loops_component_equiv Type (BG G .carrier) .map r)

def bb_loops_evaluation_value (G : Group) (r : Loop (BB G))
  : Id (BG G .carrier) (bb_loops_evaluation G r) (r .fst .trr (shape G))
  ≔ refl (r .fst .trr (shape G))

def bb_loops_evaluation_pointed (G : Group) : BookPointedMap (Omega (BB G)) (BG G)
  ≔ (bb_loops_evaluation G, center_evaluation_point G)

def abelian_bb_loops_equiv (G : Group) (h : IsAbelian G)
  : BookIsEquiv (Loop (BB G)) (BG G .carrier) (bb_loops_evaluation G)
  ≔ book_equivalence (Loop (BB G)) (BG G .carrier)
      (compose_equiv (Loop (BB G)) (BG (group_center G) .carrier) (BG G .carrier)
        (univ_cover_loops_component_equiv Type (BG G .carrier))
        (native_equivalence (BG (group_center G) .carrier) (BG G .carrier)
          (center_evaluation G, abelian_center_inclusion_iso G h))) .equiv

{` For abelian G: Ω(BB G) ≃* BG and the group Ω(BB G) is G. `}
def abelian_bb_loops_pointed_equiv (G : Group) (h : IsAbelian G) : BookPointedEquiv (Omega (BB G)) (BG G)
  ≔ (bb_loops_evaluation_pointed G, abelian_bb_loops_equiv G h)

def abelian_bb_loop_group_path (G : Group) (h : IsAbelian G) : Id Group (sc2_loop_group (bb_sc2 G)) G
  ≔ group_path_from_pointed_equiv (sc2_loop_group (bb_sc2 G)) G (abelian_bb_loops_pointed_equiv G h)

def abelian_bb_loops_path (A : AbelianGroup) : Id AbelianGroup (sc2_loops (bb_sc2 (A .fst))) A
  ≔ abelian_group_path (sc2_loops (bb_sc2 (A .fst))) A (abelian_bb_loop_group_path (A .fst) (A .snd))
