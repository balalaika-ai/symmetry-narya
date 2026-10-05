export "bridge-03-geometric-objects"
export "../../../src/85-general-winding"

{` Exercise at geometry.tex 251, the literal blind statement
   blind_point_symmetry_orthogonal (an isomorphism Sym(E, {P}) ≅ O(n) as
   data, for every E of dimension n and every point P) is refuted for
   n = 2 and every field K.

   Argument. A family of group isomorphisms φ_a : Aut_C(c a) ≅ G over a
   type A (C a groupoid) forces every loop c(l), l : a = a, to be central in
   Aut_C(c a): apd φ along l identifies φ_a(h) with φ_a(c(l)⁻¹ h c(l)), and
   φ_a is injective. Apply this to A = OS_2, c(V) = (V with its principal
   torsor, {0}) (point_object_map; its loops are the loops of O(2)
   embedded by our origin_symmetry_iso): every two symmetries of O(2)
   would commute, contradicting orthogonal_two_not_abelian. So only the
   mere version (bridge_point_symmetry_orthogonal_corrected) holds; the
   book's "is isomorphic" must be read as mere existence (or for a chosen
   identification E = 𝔼ⁿ, cf. bridge_point_symmetry_origin). `}

def bridge_iso_mono (H G : Group) (f : GroupIso H G) : IsGroupMono H G (f .fst)
  ≔ let A ≔ BG H .carrier in let B ≔ BG G .carrier in let m ≔ hom_function H G (f .fst) in
    covering_group_mono H G (f .fst)
      (y ↦ prop_is_set (BookFiber A B m y)
        (contractible_prop (BookFiber A B m y) (native_contraction (BookFiber A B m y) (f .snd y))))

{` A loop r with r⁻¹ p r = p commutes with p. `}
def bridge_conj_commute (A : Type) (x : A) (r p : Id A x x)
  (e : Id (Id A x x) (loop_conjugate A x x r p) p)
  : Id (Id A x x) (concat A x x x p r) (concat A x x x r p)
  ≔ let P ≔ Id A x x in
    calc
      concat A x x x p r = concat A x x x (refl x) (concat A x x x p r)
        by inverse P (concat A x x x (refl x) (concat A x x x p r)) (concat A x x x p r) (concat_1p A x x (concat A x x x p r))
      = concat A x x x (concat A x x x r (inverse A x x r)) (concat A x x x p r)
        by refl ((y ↦ concat A x x x y (concat A x x x p r)) : P → P)
             (inverse P (concat A x x x r (inverse A x x r)) (refl x) (concat_inverse_right A x x r))
      = concat A x x x r (concat A x x x (inverse A x x r) (concat A x x x p r))
        by concat_assoc A x x x x r (inverse A x x r) (concat A x x x p r)
      = concat A x x x r p by refl (concat A x x x r) e ∎

{` The key lemma: a family of isomorphisms Aut_C(c a) ≅ G makes the image
   of every loop of A central. `}
def bridge_family_conj_trivial (A C : Type) (hC : isGroupoid C) (c : A → C) (G : Group)
  (φ : (a : A) → GroupIso (automorphism_group C hC (c a)) G) (a : A) (l : Id A a a) (h : Id C (c a) (c a))
  : Id (Id C (c a) (c a)) (loop_conjugate C (c a) (c a) (refl c l) h) h
  ≔ let x ≔ c a in
    let P ≔ Id C x x in
    let Aut ≔ automorphism_group C hC x in
    let pt ≔ component_point C x in
    let E ≔ component_path_equiv C x pt pt in
    let ψ : (y : A) → Id C (c y) (c y) → USym G
      ≔ y k ↦ usym_hom (automorphism_group C hC (c y)) G (φ y .fst)
          (component_path C (c y) (component_point C (c y)) (component_point C (c y)) k) in
    let T ≔ refl ((y ↦ Id C (c y) (c y)) : A → Type) l in
    let h1 ≔ T .trr h in
    let e : Id (USym G) (ψ a h) (ψ a h1) ≔ refl ψ l (T .liftr h) in
    let r : Id (USym Aut) (component_path C x pt pt h) (component_path C x pt pt h1)
      ≔ embedding_reflects_paths (USym Aut) (USym G) (usym_hom Aut G (φ a .fst)) (bridge_iso_mono Aut G (φ a))
          (component_path C x pt pt h) (component_path C x pt pt h1) e in
    let s : Id P h h1
      ≔ calc
          h = E .map (component_path C x pt pt h)
            by inverse P (E .map (component_path C x pt pt h)) h (equiv_counit (Id (NativeComponent C x) pt pt) P E h)
          = E .map (component_path C x pt pt h1) by refl (E .map) r
          = h1 by equiv_counit (Id (NativeComponent C x) pt pt) P E h1 ∎ in
    concat P (loop_conjugate C x x (refl c l) h) h1 h
      (inverse P h1 (loop_conjugate C x x (refl c l) h) (loop_transport_conjugate C x x (refl c l) h))
      (inverse P h h1 s)

def bridge_point_symmetry_orthogonal_refuted (K : BlindEuclideanField) (F : blind_point_symmetry_orthogonal K) : Empty
  ≔ let L ≔ bridge_ef14 K in
    let Obj ≔ EuclideanObject L propositions_settype in
    let hObj ≔ euclidean_object_groupoid L propositions_settype in
    let grpd ≔ bridge_euc_obj_groupoid K blind_prop_set in
    let connO ≔ bridge_osn_connected K 2 in let grpdO ≔ bridge_osn_groupoid K 2 in
    let O ≔ orthogonal_group L 2 in
    let A ≔ InnerProductSpaceDim L 2 in
    let pom ≔ point_object_map L 2 in
    let Eb : A → BlindEuclideanSpace K
      ≔ V ↦ bridge_es_inv K ((V .fst, abstract_principal_torsor (ip_additive_group L (V .fst))) : EuclideanSpace L) in
    let φ : (V : A) → GroupIso (automorphism_group Obj hObj (pom V)) O
      ≔ V ↦
        let Xb ≔ blind_point_object K (Eb V) (V .fst .space .zero) in
        let Sb ≔ blind_symmetry_group K blind_prop_set grpd Xb in
        let So ≔ automorphism_group Obj hObj (pom V) in
        let Ob ≔ BlindOrthogonalGroup K 2 connO grpdO in
        bridge_group_iso_of_path So O
          (concat Group So Sb O
            (inverse Group Sb So (bridge_symmetry_group K blind_prop_set grpd Xb (pom V) (refl (pom V))))
            (concat Group Sb Ob O (group_path_from_iso Sb Ob (F grpd 2 connO grpdO (Eb V) (V .snd) (V .fst .space .zero)))
              (bridge_def_orthogonal_group K 2 connO grpdO))) in
    let std ≔ standard_inner_product_space_dim L 2 in
    let o0 ≔ pom std in
    let Comp ≔ NativeComponent Obj (origin_object L 2) in
    let ι ≔ origin_symmetry_iso L 2 in
    let Sym0 ≔ geometric_object_symmetry_group L propositions_settype (origin_object L 2) in
    let em ≔ point_object_component L 2 in
    let Ec ≔ component_path_equiv Obj (origin_object L 2) (em std) (em std) in
    let ab : IsAbelian O
      ≔ g1 g2 ↦
        let q1 ≔ refl pom g1 in let q2 ≔ refl pom g2 in
        let PO ≔ Id Obj o0 o0 in
        let cm : Id PO (concat Obj o0 o0 o0 q2 q1) (concat Obj o0 o0 o0 q1 q2)
          ≔ bridge_conj_commute Obj o0 q1 q2 (bridge_family_conj_trivial A Obj hObj pom O φ std g1 q2) in
        let cm' : Id PO (refl pom (concat A std std std g2 g1)) (refl pom (concat A std std std g1 g2))
          ≔ calc
              refl pom (concat A std std std g2 g1) = concat Obj o0 o0 o0 q2 q1 by map_path_concat A Obj pom std std std g2 g1
              = concat Obj o0 o0 o0 q1 q2 by cm
              = refl pom (concat A std std std g1 g2)
                by inverse PO (refl pom (concat A std std std g1 g2)) (concat Obj o0 o0 o0 q1 q2)
                     (map_path_concat A Obj pom std std std g1 g2) ∎ in
        let PC ≔ Id Comp (em std) (em std) in
        let ρ1 ≔ refl em (concat A std std std g2 g1) in let ρ2 ≔ refl em (concat A std std std g1 g2) in
        let ρe : Id PC ρ1 ρ2
          ≔ calc
              ρ1 = equiv_inverse_map PC PO Ec (Ec .map ρ1) by equiv_unit PC PO Ec ρ1
              = equiv_inverse_map PC PO Ec (Ec .map ρ2) by refl (equiv_inverse_map PC PO Ec) cm'
              = ρ2 by inverse PC ρ2 (equiv_inverse_map PC PO Ec (Ec .map ρ2)) (equiv_unit PC PO Ec ρ2) ∎ in
        embedding_reflects_paths (USym O) (USym Sym0) (usym_hom O Sym0 (ι .fst)) (bridge_iso_mono O Sym0 ι)
          (concat A std std std g2 g1) (concat A std std std g1 g2)
          (refl ((ρ ↦ pointed_loop_conjugate Comp (shape Sym0) (em std) (hom_point O Sym0 (ι .fst)) ρ) : PC → USym Sym0) ρe) in
    orthogonal_two_not_abelian L ab
