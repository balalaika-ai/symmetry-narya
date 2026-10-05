export "843-sums-of-groups"
export "422-wedge-abelian-groups"

{` Chapter 8 (congp.tex), xca:whatAREabeliangroups (congp.tex:593).

   For a group G and any wedge signature W of BG with itself, the book's
   fold : BG ∨ BG →* BG is the pointed map corresponding to (id_G, id_G)
   under lem:univvee (wedge_fold_book; with a groupoid hypothesis hW it is
   by definition the classifying map of sum_of_groups_hom_extend applied to
   (id, id), i.e. it is "given via lem:sumofgroupsISsum by id_G"), and
   i : BG ∨ BG →* BG × BG = B(G × G) corresponds to the homomorphisms
   incl_1, incl_2 : G → G × G (wedge_incl_book).  WedgeFoldExtension G W is
   the type of pointed maps h : BG × BG →* BG with h ∘ i = fold (as pointed
   maps), i.e. extensions of fold over i.

   The statement was already proved in chapter 4 (rem:whatAREabeliangroups,
   src/422-wedge-abelian-groups.ny) for OnePointUnionSignature, a record with
   the same fields as WedgeSignature, and with fold/inclusion defined by
   recursion on the cocones (id, id, refl) and ((-, sh), (sh, -), refl).
   Here W is converted (wedge_one_point_union, fieldwise), the book's maps
   are identified with those of module 422 (wedge_fold_book_eq,
   wedge_incl_book_eq: the glue datum f_1(pt)⁻¹ · f_2(pt) of lem:univvee is
   refl⁻¹ · refl), and the result is transferred:
   wedge_fold_extension_abelian_equiv : WedgeFoldExtension G W ≃ isAb(G).
   "Abelian ⇒ extension" uses module 422's multiplication BG × BG → BG
   (built from the central loops of an abelian group), not chapter 12.

   Margin question ("is this extension problem a proposition?"): yes, the
   type of extensions is a proposition for every G (wedge_fold_extension_prop,
   from module 422), so mere existence and structure agree.  Whether i is an
   epimorphism in general is not formalized.

   The "cute aside": an UNPOINTED extension (h : BG × BG → BG with a
   homotopy h ∘ i ~ fold) already forces G to be abelian
   (unpointed_extension_abelian: it is made pointed by solving for the
   pointing path); this is how it kills the commutators of USym(G ∨ G),
   whose images under fold are the commutators g h g⁻¹ h⁻¹ of G.  The wip
   question "is this still a proposition, or do we need to truncate?" is
   answered: the type of unpointed extensions is a proposition too
   (unpointed_wedge_fold_extension_prop), equivalent to isAb(G). `}

def wedge_one_point_union (A1 A2 : Pointed) (W : WedgeSignature A1 A2) : OnePointUnionSignature A1 A2
  ≔ (W .carrier, W .incl1, W .incl2, W .glue, W .induction)

{` The book's fold and inclusion, via lem:univvee. `}
def wedge_fold_book (G : Group) (W : WedgeSignature (BG G) (BG G))
  : BookPointedMap (wedge_pointed (BG G) (BG G) W) (BG G)
  ≔ wedge_pointed_extend (BG G) (BG G) W (BG G) (hom_B G G (group_hom_id G)) (hom_B G G (group_hom_id G))

def wedge_incl_book (G : Group) (W : WedgeSignature (BG G) (BG G))
  : BookPointedMap (wedge_pointed (BG G) (BG G) W) (BG (product_group G G))
  ≔ wedge_pointed_extend (BG G) (BG G) W (BG (product_group G G))
      (hom_B G (product_group G G) (product_group_incl1 G G)) (hom_B G (product_group G G) (product_group_incl2 G G))

def wedge_fold_book_sum (G : Group) (W : WedgeSignature (BG G) (BG G)) (hW : isGroupoid (W .carrier))
  : Id (BookPointedMap (wedge_pointed (BG G) (BG G) W) (BG G))
      (hom_B (sum_of_groups G G W hW) G (sum_of_groups_hom_extend G G W hW G (group_hom_id G) (group_hom_id G)))
      (wedge_fold_book G W)
  ≔ refl (wedge_fold_book G W)

def wedge_incl_book_sum (G : Group) (W : WedgeSignature (BG G) (BG G)) (hW : isGroupoid (W .carrier))
  : Id (BookPointedMap (wedge_pointed (BG G) (BG G) W) (BG (product_group G G)))
      (hom_B (sum_of_groups G G W hW) (product_group G G)
        (sum_of_groups_hom_extend G G W hW (product_group G G) (product_group_incl1 G G) (product_group_incl2 G G)))
      (wedge_incl_book G W)
  ≔ refl (wedge_incl_book G W)

{` Comparison with module 422: the extension of (f1, refl), (f2, refl ∘ e0)
   is recursion on (f1, f2, e0), pointed by the computation rule. `}
def wsum_extend_glue (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  (f1 : A1 .carrier → T) (f2 : A2 .carrier → T) (e0 : Id T (f1 (A1 .point)) (f2 (A2 .point)))
  (q : Id T (f1 (A1 .point)) (f1 (A1 .point)))
  : BookPointedMap (wedge_pointed A1 A2 W) (T, f1 (A1 .point))
  ≔ let r ≔ wedge_rec A1 A2 W T (f1, (f2, e0)) in
    (r, concat T (f1 (A1 .point)) (f1 (A1 .point)) (r (W .incl1 (A1 .point))) q
      (inverse T (r (W .incl1 (A1 .point))) (f1 (A1 .point)) (wedge_rec_incl1 A1 A2 W T (f1, (f2, e0)) (A1 .point))))

def wsum_extend_glue_compare (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  (f1 : A1 .carrier → T) (f2 : A2 .carrier → T) (e0 : Id T (f1 (A1 .point)) (f2 (A2 .point)))
  : Id (BookPointedMap (wedge_pointed A1 A2 W) (T, f1 (A1 .point)))
      (wsum_extend_glue A1 A2 W T f1 f2
        (concat T (f1 (A1 .point)) (f1 (A1 .point)) (f2 (A2 .point)) (inverse T (f1 (A1 .point)) (f1 (A1 .point))
          (refl (f1 (A1 .point)))) e0)
        (refl (f1 (A1 .point))))
      (wedge_rec A1 A2 W T (f1, (f2, e0)),
       inverse T (wedge_rec A1 A2 W T (f1, (f2, e0)) (W .incl1 (A1 .point))) (f1 (A1 .point))
         (wedge_rec_incl1 A1 A2 W T (f1, (f2, e0)) (A1 .point)))
  ≔ let x ≔ f1 (A1 .point) in let y ≔ f2 (A2 .point) in
    let P ≔ BookPointedMap (wedge_pointed A1 A2 W) (T, x) in
    let r ≔ wedge_rec A1 A2 W T (f1, (f2, e0)) in
    let c ≔ inverse T (r (W .incl1 (A1 .point))) x (wedge_rec_incl1 A1 A2 W T (f1, (f2, e0)) (A1 .point)) in
    let e1 : Id (Id T x y) (concat T x x y (inverse T x x (refl x)) e0) e0
      ≔ concat (Id T x y) (concat T x x y (inverse T x x (refl x)) e0) (concat T x x y (refl x) e0) e0
          (refl ((s ↦ concat T x x y s e0) : Id T x x → Id T x y) (inverse_refl T x))
          (concat_1p T x y e0) in
    concat P (wsum_extend_glue A1 A2 W T f1 f2 (concat T x x y (inverse T x x (refl x)) e0) (refl x))
      (wsum_extend_glue A1 A2 W T f1 f2 e0 (refl x)) (r, c)
      (refl ((e ↦ wsum_extend_glue A1 A2 W T f1 f2 e (refl x)) : Id T x y → P) e1)
      (refl ((s ↦ (r, s)) : Id T x (r (W .incl1 (A1 .point))) → P) (concat_1p T x (r (W .incl1 (A1 .point))) c))

def wedge_fold_book_eq (G : Group) (W : WedgeSignature (BG G) (BG G))
  : Id (BookPointedMap (wedge_pointed (BG G) (BG G) W) (BG G))
      (wedge_fold_book G W) (wedge_fold_pointed G (wedge_one_point_union (BG G) (BG G) W))
  ≔ wsum_extend_glue_compare (BG G) (BG G) W (BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier))
      (refl (shape G))

def wedge_incl_book_eq (G : Group) (W : WedgeSignature (BG G) (BG G))
  : Id (BookPointedMap (wedge_pointed (BG G) (BG G) W) (square_pointed G))
      (wedge_incl_book G W) (wedge_incl_pointed G (wedge_one_point_union (BG G) (BG G) W))
  ≔ wsum_extend_glue_compare (BG G) (BG G) W (Product (BG G .carrier) (BG G .carrier))
      (z ↦ (z, shape G)) (z ↦ (shape G, z)) (refl (shape G, shape G))

{` Extensions of a pointed map f over a pointed map i. `}
def WsumPointedExtension (V S B : Pointed) (i : BookPointedMap V S) (f : BookPointedMap V B) : Type
  ≔ Σ (BookPointedMap S B) (h ↦ Id (BookPointedMap V B) (book_pointed_compose V S B i h) f)

{` xca:whatAREabeliangroups: the type of extensions of fold over i. `}
def WedgeFoldExtension (G : Group) (W : WedgeSignature (BG G) (BG G)) : Type
  ≔ WsumPointedExtension (wedge_pointed (BG G) (BG G) W) (BG (product_group G G)) (BG G)
      (wedge_incl_book G W) (wedge_fold_book G W)

def wedge_fold_extension_factorization_equiv (G : Group) (W : WedgeSignature (BG G) (BG G))
  : Equiv (WedgeFoldExtension G W) (WedgeFoldFactorization G (wedge_one_point_union (BG G) (BG G) W))
  ≔ let V ≔ wedge_pointed (BG G) (BG G) W in
    id_to_equiv (WedgeFoldExtension G W) (WedgeFoldFactorization G (wedge_one_point_union (BG G) (BG G) W))
      (refl (WsumPointedExtension V (square_pointed G) (BG G)) (wedge_incl_book_eq G W) (wedge_fold_book_eq G W))

def wedge_fold_extension_abelian_equiv (G : Group) (W : WedgeSignature (BG G) (BG G))
  : Equiv (WedgeFoldExtension G W) (IsAbelian G)
  ≔ compose_equiv (WedgeFoldExtension G W) (WedgeFoldFactorization G (wedge_one_point_union (BG G) (BG G) W))
      (IsAbelian G) (wedge_fold_extension_factorization_equiv G W)
      (wedge_factorization_abelian_equiv G (wedge_one_point_union (BG G) (BG G) W))

def wedge_fold_extension_prop (G : Group) (W : WedgeSignature (BG G) (BG G)) : isProp (WedgeFoldExtension G W)
  ≔ u v ↦ equivalence_injective (WedgeFoldExtension G W) (IsAbelian G) (wedge_fold_extension_abelian_equiv G W) u v
      (is_abelian_prop G (wedge_fold_extension_abelian_equiv G W .map u) (wedge_fold_extension_abelian_equiv G W .map v))

def abelian_wedge_fold_extension (G : Group) (W : WedgeSignature (BG G) (BG G)) (hab : IsAbelian G)
  : WedgeFoldExtension G W
  ≔ equiv_inverse_map (WedgeFoldExtension G W) (IsAbelian G) (wedge_fold_extension_abelian_equiv G W) hab

{` The cute aside: unpointed extensions. `}
def UnpointedWedgeFoldExtension (G : Group) (W : WedgeSignature (BG G) (BG G)) : Type
  ≔ Σ (Product (BG G .carrier) (BG G .carrier) → BG G .carrier) (h ↦
      Homotopy (W .carrier) (_ ↦ BG G .carrier) (w ↦ h (wedge_incl_book G W .fst w)) (wedge_fold_book G W .fst))

def wsum_solve_pointing (T : Type) (a b c d : T) (F : Id T a d) (X : Id T b c) (Y : Id T c d)
  : Id (Id T a d)
      (concat T a c d (concat T a b c (concat T a d b F (concat T d c b (inverse T c d Y) (inverse T b c X))) X) Y) F
  ≔ J T c (d Y ↦ (F : Id T a d) → Id (Id T a d)
        (concat T a c d (concat T a b c (concat T a d b F (concat T d c b (inverse T c d Y) (inverse T b c X))) X) Y) F)
      (J T b (c X ↦ (F : Id T a c) → Id (Id T a c)
          (concat T a c c (concat T a b c (concat T a c b F (concat T c c b (inverse T c c (refl c)) (inverse T b c X))) X)
            (refl c)) F)
        (F ↦ calc
          concat T a b b (concat T a b b (concat T a b b F (concat T b b b (inverse T b b (refl b)) (inverse T b b (refl b))))
            (refl b)) (refl b)
          = concat T a b b (concat T a b b F (concat T b b b (inverse T b b (refl b)) (inverse T b b (refl b)))) (refl b)
            by concat_p1 T a b (concat T a b b (concat T a b b F (concat T b b b (inverse T b b (refl b))
              (inverse T b b (refl b)))) (refl b))
          = concat T a b b F (concat T b b b (inverse T b b (refl b)) (inverse T b b (refl b)))
            by concat_p1 T a b (concat T a b b F (concat T b b b (inverse T b b (refl b)) (inverse T b b (refl b))))
          = concat T a b b F (concat T b b b (refl b) (refl b))
            by refl (concat T a b b F) (refl ((s ↦ concat T b b b s s) : Id T b b → Id T b b) (inverse_refl T b))
          = concat T a b b F (refl b)
            by refl (concat T a b b F) (concat_p1 T b b (refl b))
          = F by concat_p1 T a b F ∎)
        c X)
      d Y F

def unpointed_extension_map (G : Group) (W : WedgeSignature (BG G) (BG G)) (u : UnpointedWedgeFoldExtension G W)
  : BookPointedMap (BG (product_group G G)) (BG G)
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    let S ≔ BG (product_group G G) in
    let i ≔ wedge_incl_book G W in let f ≔ wedge_fold_book G W in
    let h ≔ u .fst in let a12 ≔ wedge_point (BG G) (BG G) W in
    (h, concat B b (f .fst a12) (h (S .point)) (f .snd)
      (concat B (f .fst a12) (h (i .fst a12)) (h (S .point)) (inverse B (h (i .fst a12)) (f .fst a12) (u .snd a12))
        (inverse B (h (S .point)) (h (i .fst a12)) (refl h (i .snd)))))

def unpointed_extension_homotopy (G : Group) (W : WedgeSignature (BG G) (BG G)) (u : UnpointedWedgeFoldExtension G W)
  : PointedHomotopy (wedge_pointed (BG G) (BG G) W) (BG G)
      (book_pointed_compose (wedge_pointed (BG G) (BG G) W) (BG (product_group G G)) (BG G) (wedge_incl_book G W)
        (unpointed_extension_map G W u))
      (wedge_fold_book G W)
  ≔ let B ≔ BG G .carrier in let S ≔ BG (product_group G G) in
    let i ≔ wedge_incl_book G W in let f ≔ wedge_fold_book G W in
    let h ≔ u .fst in let a12 ≔ wedge_point (BG G) (BG G) W in
    (u .snd, wsum_solve_pointing B (shape G) (h (S .point)) (h (i .fst a12)) (f .fst a12) (f .snd) (refl h (i .snd))
      (u .snd a12))

def unpointed_extension_pointed (G : Group) (W : WedgeSignature (BG G) (BG G)) (u : UnpointedWedgeFoldExtension G W)
  : WedgeFoldExtension G W
  ≔ let V ≔ wedge_pointed (BG G) (BG G) W in let S ≔ BG (product_group G G) in
    let k ≔ unpointed_extension_map G W u in
    let c ≔ book_pointed_compose V S (BG G) (wedge_incl_book G W) k in
    (k, equiv_inverse_map (Id (BookPointedMap V (BG G)) c (wedge_fold_book G W))
      (PointedHomotopy V (BG G) c (wedge_fold_book G W))
      (pointed_map_path_equiv V (BG G) c (wedge_fold_book G W))
      (unpointed_extension_homotopy G W u))

def pointed_extension_unpointed (G : Group) (W : WedgeSignature (BG G) (BG G)) (v : WedgeFoldExtension G W)
  : UnpointedWedgeFoldExtension G W
  ≔ let V ≔ wedge_pointed (BG G) (BG G) W in let S ≔ BG (product_group G G) in
    (v .fst .fst,
     pointed_map_path_equiv V (BG G) (book_pointed_compose V S (BG G) (wedge_incl_book G W) (v .fst))
       (wedge_fold_book G W) .map (v .snd) .fst)

{` The aside: an unpointed extension already makes G abelian. `}
def unpointed_extension_abelian (G : Group) (W : WedgeSignature (BG G) (BG G)) (u : UnpointedWedgeFoldExtension G W)
  : IsAbelian G
  ≔ wedge_fold_extension_abelian_equiv G W .map (unpointed_extension_pointed G W u)

def unpointed_extension_roundtrip (G : Group) (W : WedgeSignature (BG G) (BG G)) (u : UnpointedWedgeFoldExtension G W)
  : Id (UnpointedWedgeFoldExtension G W) (pointed_extension_unpointed G W (unpointed_extension_pointed G W u)) u
  ≔ let V ≔ wedge_pointed (BG G) (BG G) W in let S ≔ BG (product_group G G) in
    let B ≔ BG G .carrier in
    let c ≔ book_pointed_compose V S (BG G) (wedge_incl_book G W) (unpointed_extension_map G W u) in
    refl ((H ↦ (u .fst, H)) : Homotopy (W .carrier) (_ ↦ B) (w ↦ u .fst (wedge_incl_book G W .fst w))
        (wedge_fold_book G W .fst) → UnpointedWedgeFoldExtension G W)
      (equiv_counit (Id (BookPointedMap V (BG G)) c (wedge_fold_book G W))
        (PointedHomotopy V (BG G) c (wedge_fold_book G W))
        (pointed_map_path_equiv V (BG G) c (wedge_fold_book G W))
        (unpointed_extension_homotopy G W u) .fst)

{` The wip question: unpointed extensions also form a proposition. `}
def unpointed_wedge_fold_extension_prop (G : Group) (W : WedgeSignature (BG G) (BG G))
  : isProp (UnpointedWedgeFoldExtension G W)
  ≔ u v ↦
    let U ≔ UnpointedWedgeFoldExtension G W in
    let P ≔ unpointed_extension_pointed G W in let F ≔ pointed_extension_unpointed G W in
    concat U u (F (P u)) v (inverse U (F (P u)) u (unpointed_extension_roundtrip G W u))
      (concat U (F (P u)) (F (P v)) v (refl F (wedge_fold_extension_prop G W (P u) (P v)))
        (unpointed_extension_roundtrip G W v))

def unpointed_wedge_fold_extension_abelian_equiv (G : Group) (W : WedgeSignature (BG G) (BG G))
  : Equiv (UnpointedWedgeFoldExtension G W) (IsAbelian G)
  ≔ iff_equiv (UnpointedWedgeFoldExtension G W) (IsAbelian G) (unpointed_wedge_fold_extension_prop G W)
      (is_abelian_prop G) (unpointed_extension_abelian G W)
      (hab ↦ pointed_extension_unpointed G W (abelian_wedge_fold_extension G W hab))

{` Litmus: Σ_2 (abelian) has an extension for every wedge; Σ_3 has not even
   an unpointed one. `}
def sigma2_wedge_fold_extension (W : WedgeSignature (BG (symmetric_group two)) (BG (symmetric_group two)))
  : WedgeFoldExtension (symmetric_group two) W
  ≔ abelian_wedge_fold_extension (symmetric_group two) W sigma2_abelian

def sigma3_no_unpointed_wedge_fold_extension
  (W : WedgeSignature (BG (symmetric_group three)) (BG (symmetric_group three)))
  (u : UnpointedWedgeFoldExtension (symmetric_group three) W) : Empty
  ≔ symmetric_group_three_not_abelian (unpointed_extension_abelian (symmetric_group three) W u)
