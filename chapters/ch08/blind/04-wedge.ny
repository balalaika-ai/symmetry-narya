{` Blind statements for chapter 8 (congp.tex), section "Sums of groups".
   The wedge is a higher inductive type; it is a signature record (structure on a carrier W)
   with the induction principle and its computation rule as one Σ-path (as for CircleSignature). `}
export "01-semidirect"
export "../../../src/410-pointed-connected-groupoids"

{` def:wedge. i : A₁ + A₂ → A₁ ∨ A₂ given by i₁ and i₂. `}
def blind_wedge_inc (A1 A2 : Pointed) (W : Type) (i1 : A1 .carrier → W) (i2 : A2 .carrier → W)
  : Sum (A1 .carrier) (A2 .carrier) → W
  ≔ [ inl. x ↦ i1 x | inr. y ↦ i2 y ]

{` The data of the induction principle: s : Π_{a : A₁+A₂} C(i a) and s(a₁) = C(g⁻¹)(s(a₂)). `}
def BlindWedgeBoundary (A1 A2 : Pointed) (W : Type) (i1 : A1 .carrier → W) (i2 : A2 .carrier → W)
  (g : Id W (i1 (A1 .point)) (i2 (A2 .point))) (C : W → Type) : Type
  ≔ Σ ((a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 W i1 i2 a)) (s ↦
      Id (C (i1 (A1 .point))) (s (inl. (A1 .point)))
        (transport W C (i2 (A2 .point)) (i1 (A1 .point)) (inverse W (i1 (A1 .point)) (i2 (A2 .point)) g)
          (s (inr. (A2 .point)))))

{` The boundary datum of a section f: (f ∘ i, the identification obtained from apd_f(g)). `}
def blind_wedge_evaluate (A1 A2 : Pointed) (W : Type) (i1 : A1 .carrier → W) (i2 : A2 .carrier → W)
  (g : Id W (i1 (A1 .point)) (i2 (A2 .point))) (C : W → Type) (f : (x : W) → C x)
  : BlindWedgeBoundary A1 A2 W i1 i2 g C
  ≔ let a1 ≔ A1 .point in let a2 ≔ A2 .point in
    (a ↦ f (blind_wedge_inc A1 A2 W i1 i2 a),
     inverse (C (i1 a1)) (transport W C (i2 a2) (i1 a1) (inverse W (i1 a1) (i2 a2) g) (f (i2 a2))) (f (i1 a1))
       (pathover_transport_equiv W C (i2 a2) (i1 a1) (inverse W (i1 a1) (i2 a2) g) (f (i2 a2)) (f (i1 a1)) .map
         (pathover_inverse W C (i1 a1) (i2 a2) g (f (i1 a1)) (f (i2 a2)) (refl f g))))

def BlindWedgeStructure (A1 A2 : Pointed) (W : Type) : Type ≔ sig (
  i1 : A1 .carrier → W,
  i2 : A2 .carrier → W,
  glue : Id W (i1 (A1 .point)) (i2 (A2 .point)),
  induction : (C : W → Type) (d : BlindWedgeBoundary A1 A2 W i1 i2 glue C)
    → Σ ((x : W) → C x) (f ↦
        Id (BlindWedgeBoundary A1 A2 W i1 i2 glue C) (blind_wedge_evaluate A1 A2 W i1 i2 glue C f) d))

def BlindWedge (A1 A2 : Pointed) : Type ≔ Σ Type (W ↦ BlindWedgeStructure A1 A2 W)

{` (A₁ ∨ A₂, a₁₂) with a₁₂ ≔ i₁ a₁. `}
def blind_wedge_pointed (A1 A2 : Pointed) (W : BlindWedge A1 A2) : Pointed ≔ (W .fst, W .snd .i1 (A1 .point))

{` The induction principle exactly as printed (Σ_s where Π_s is meant; as printed it would demand
   a section s for every family C, so the signature above uses the evident Π reading). `}
def BlindWedgeInductionPrinted (A1 A2 : Pointed) (W : Type) (i1 : A1 .carrier → W) (i2 : A2 .carrier → W)
  (g : Id W (i1 (A1 .point)) (i2 (A2 .point))) : Type
  ≔ (C : W → Type)
    → Σ ((a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 W i1 i2 a)) (s ↦
        Id (C (i1 (A1 .point))) (s (inl. (A1 .point)))
          (transport W C (i2 (A2 .point)) (i1 (A1 .point)) (inverse W (i1 (A1 .point)) (i2 (A2 .point)) g)
            (s (inr. (A2 .point))))
        → (x : W) → C x)

{` i₁^g ≔ i₁ on loops; i₂^g(p) ≔ g⁻¹ i₂(p) g (first g, then i₂ p, then g⁻¹). `}
def blind_wedge_i1g (A1 A2 : Pointed) (W : BlindWedge A1 A2) (p : Loop A1) : Loop (blind_wedge_pointed A1 A2 W)
  ≔ map_path (A1 .carrier) (W .fst) (W .snd .i1) (A1 .point) (A1 .point) p

def blind_wedge_i2g (A1 A2 : Pointed) (W : BlindWedge A1 A2) (p : Loop A2) : Loop (blind_wedge_pointed A1 A2 W)
  ≔ let a12 ≔ W .snd .i1 (A1 .point) in let b ≔ W .snd .i2 (A2 .point) in
    concat (W .fst) a12 b a12 (W .snd .glue)
      (concat (W .fst) b b a12 (map_path (A2 .carrier) (W .fst) (W .snd .i2) (A2 .point) (A2 .point) p)
        (inverse (W .fst) a12 b (W .snd .glue)))

{` The structure maps as pointed maps: i₁ pointed by refl, i₂ pointed by g. `}
def blind_wedge_in1 (A1 A2 : Pointed) (W : BlindWedge A1 A2) : BookPointedMap A1 (blind_wedge_pointed A1 A2 W)
  ≔ (W .snd .i1, refl (W .snd .i1 (A1 .point)))

def blind_wedge_in2 (A1 A2 : Pointed) (W : BlindWedge A1 A2) : BookPointedMap A2 (blind_wedge_pointed A1 A2 W)
  ≔ (W .snd .i2, W .snd .glue)

def blind_wedge_restrict (A1 A2 : Pointed) (W : BlindWedge A1 A2) (B : Pointed)
  (f : BookPointedMap (blind_wedge_pointed A1 A2 W) B) : Product (BookPointedMap A1 B) (BookPointedMap A2 B)
  ≔ (book_pointed_compose A1 (blind_wedge_pointed A1 A2 W) B (blind_wedge_in1 A1 A2 W) f,
     book_pointed_compose A2 (blind_wedge_pointed A1 A2 W) B (blind_wedge_in2 A1 A2 W) f)

{` lem:univvee. i* : (A₁ ∨ A₂ →* B) → (A₁ →* B) × (A₂ →* B), f ↦ (f i₁, f i₂), is an equivalence. `}
def blind_lem_univvee : Type
  ≔ (A1 A2 : Pointed) (W : BlindWedge A1 A2) (B : Pointed)
    → BookIsEquiv (BookPointedMap (blind_wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
        (blind_wedge_restrict A1 A2 W B)

{` def:sumofgroup. G₁ ∨ G₂ ≔ Aut_{BG₁ ∨ BG₂}(a₁₂) (each group is Aut_{BG}(sh)). That the wedge is a
   groupoid is not proved in general in the book; it is a hypothesis hW here. `}
def blind_group_sum (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst)) : Group
  ≔ automorphism_group (W .fst) hW (W .snd .i1 (shape G1))

def blind_group_sum_in1 (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst))
  : GroupHom G1 (blind_group_sum G1 G2 W hW)
  ≔ let a12 ≔ W .snd .i1 (shape G1) in
    let F : BG G1 .carrier → NativeComponent (W .fst) a12
      ≔ x ↦ (W .snd .i1 x,
              mere_rec (Id (BG G1 .carrier) (shape G1) x) (Mere (Id (W .fst) a12 (W .snd .i1 x)))
                (mere_isprop (Id (W .fst) a12 (W .snd .i1 x)))
                (p ↦ mere (Id (W .fst) a12 (W .snd .i1 x)) (map_path (BG G1 .carrier) (W .fst) (W .snd .i1) (shape G1) x p))
                (connected_based_equiv (BG G1 .carrier) (shape G1) .map (bg_connected G1) x)) in
    mkhom G1 (blind_group_sum G1 G2 W hW)
      (F, component_path (W .fst) a12 (component_point (W .fst) a12) (F (shape G1)) (refl a12))

def blind_group_sum_in2 (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst))
  : GroupHom G2 (blind_group_sum G1 G2 W hW)
  ≔ let a12 ≔ W .snd .i1 (shape G1) in let b ≔ W .snd .i2 (shape G2) in
    let F : BG G2 .carrier → NativeComponent (W .fst) a12
      ≔ x ↦ (W .snd .i2 x,
              mere_rec (Id (BG G2 .carrier) (shape G2) x) (Mere (Id (W .fst) a12 (W .snd .i2 x)))
                (mere_isprop (Id (W .fst) a12 (W .snd .i2 x)))
                (p ↦ mere (Id (W .fst) a12 (W .snd .i2 x))
                  (concat (W .fst) a12 b (W .snd .i2 x) (W .snd .glue)
                    (map_path (BG G2 .carrier) (W .fst) (W .snd .i2) (shape G2) x p)))
                (connected_based_equiv (BG G2 .carrier) (shape G2) .map (bg_connected G2) x)) in
    mkhom G2 (blind_group_sum G1 G2 W hW)
      (F, component_path (W .fst) a12 (component_point (W .fst) a12) (F (shape G2)) (W .snd .glue))

{` lem:sumofgroupsISsum. Restriction along the structure maps is an equivalence. `}
def blind_lem_sumofgroupsISsum : Type
  ≔ (G1 G2 G : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst))
    → BookIsEquiv (GroupHom (blind_group_sum G1 G2 W hW) G) (Product (GroupHom G1 G) (GroupHom G2 G))
        (phi ↦ (group_hom_compose G1 (blind_group_sum G1 G2 W hW) G (blind_group_sum_in1 G1 G2 W hW) phi,
                group_hom_compose G2 (blind_group_sum G1 G2 W hW) G (blind_group_sum_in2 G1 G2 W hW) phi))

{` cor:ZplusZuniv. Hom(Z ∨ Z, G) → Hom(Z,G) × Hom(Z,G) ≃ USym G × USym G (evaluation at loop) is an
   equivalence (Z = (S¹, base) for any circle signature; groupoid-ness of S¹ ∨ S¹ as hypothesis). `}
def blind_cor_ZplusZuniv : Type
  ≔ (C : CircleSignature) (W : BlindWedge (BG (circle_group C)) (BG (circle_group C))) (hW : isGroupoid (W .fst))
    (G : Group)
    → BookIsEquiv (GroupHom (blind_group_sum (circle_group C) (circle_group C) W hW) G) (Product (USym G) (USym G))
        (phi ↦ (usym_hom (circle_group C) G
                  (group_hom_compose (circle_group C) (blind_group_sum (circle_group C) (circle_group C) W hW) G
                     (blind_group_sum_in1 (circle_group C) (circle_group C) W hW) phi) (C .loop),
                usym_hom (circle_group C) G
                  (group_hom_compose (circle_group C) (blind_group_sum (circle_group C) (circle_group C) W hW) G
                     (blind_group_sum_in2 (circle_group C) (circle_group C) W hW) phi) (C .loop)))

{` xca:whatAREabeliangroups. fold and i are any pointed maps with i*(fold) = (id, id) and
   i*(i) = (incl₁, incl₂) (they exist uniquely by lem:univvee). G is abelian iff fold extends over i. `}
def blind_pointed_id (X : Pointed) : BookPointedMap X X ≔ (identity (X .carrier), refl (X .point))

def BlindFoldExtension (G : Group) (W : BlindWedge (BG G) (BG G))
  (fold : BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG G))
  (incl : BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG (product_group G G))) : Type
  ≔ Σ (BookPointedMap (BG (product_group G G)) (BG G)) (r ↦
      Id (BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG G))
        (book_pointed_compose (blind_wedge_pointed (BG G) (BG G) W) (BG (product_group G G)) (BG G) incl r) fold)

def BlindFoldData (G : Group) (W : BlindWedge (BG G) (BG G)) : Type
  ≔ Σ (BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG G)) (fold ↦
    Σ (Id (Product (BookPointedMap (BG G) (BG G)) (BookPointedMap (BG G) (BG G)))
          (blind_wedge_restrict (BG G) (BG G) W (BG G) fold) (blind_pointed_id (BG G), blind_pointed_id (BG G))) (_ ↦
    Σ (BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG (product_group G G))) (incl ↦
      Id (Product (BookPointedMap (BG G) (BG (product_group G G))) (BookPointedMap (BG G) (BG (product_group G G))))
        (blind_wedge_restrict (BG G) (BG G) W (BG (product_group G G)) incl)
        (hom_B G (product_group G G) (product_group_incl1 G G), hom_B G (product_group G G) (product_group_incl2 G G)))))

def blind_xca_whatAREabeliangroups : Type
  ≔ (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
    → Product (IsAbelian G → Mere (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)))
              (Mere (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)) → IsAbelian G)

{` The aside: an unpointed factorisation r ∘ i = fold already kills the commutators
   g h g⁻¹ h⁻¹ of g = i₁^g(g), h = i₂^g(h) in USym(G ∨ G) (book products in composition order). `}
def blind_loop_mul (A : Type) (a : A) (u v : Id A a a) : Id A a a ≔ concat A a a a v u

def blind_xca_whatAREabeliangroups_aside : Type
  ≔ (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
    (r : BG (product_group G G) .carrier → BG G .carrier)
    (hr : Id (W .fst → BG G .carrier) (x ↦ r (D .snd .snd .fst .fst x)) (D .fst .fst))
    (g h : USym G)
    → let a12 ≔ W .snd .i1 (shape G) in
      let x ≔ blind_wedge_i1g (BG G) (BG G) W g in let y ≔ blind_wedge_i2g (BG G) (BG G) W h in
      let m ≔ blind_loop_mul (W .fst) a12 in
      Id (USym G)
        (loops_map (blind_wedge_pointed (BG G) (BG G) W) (BG G) (D .fst)
          (m x (m y (m (inverse (W .fst) a12 a12 x) (inverse (W .fst) a12 a12 y)))))
        (refl (shape G))

{` lem:wedgeofgpoidisgpoid. Decidable group: USym has decidable equality. C₁ = strings (p₀, n, p₁, …, pₙ)
   with p₀ : USym G₁ and p₁, p₂, … alternating in G₂, G₁, …, none of them refl (a nested Σ instead of the
   printed Π over 1 ≤ k ≤ n). β(p₀, n, p₁, …) ≔ i₁^g p₀ · i₂^g p₁ · i₁^g p₂ ⋯ (book product = composition). `}
def BlindNonRefl (G : Group) : Type ≔ Σ (USym G) (p ↦ Not (Id (USym G) p (refl (shape G))))

def BlindAltTail (G1 G2 : Group) (n : Nat) : Type
  ≔ match n [ zero. ↦ Unit | suc. m ↦ Σ (BlindNonRefl G2) (_ ↦ BlindAltTail G2 G1 m) ]

def BlindAltStrings (G1 G2 : Group) : Type ≔ Σ (USym G1) (_ ↦ Σ Nat (n ↦ BlindAltTail G1 G2 n))

def blind_alt_eval (G1 G2 : Group) (L : Type) (mul : L → L → L) (e : L) (j1 : USym G1 → L) (j2 : USym G2 → L)
  (n : Nat) : BlindAltTail G1 G2 n → L
  ≔ match n [
    | zero. ↦ _ ↦ e
    | suc. m ↦ t ↦ mul (j2 (t .fst .fst)) (blind_alt_eval G2 G1 L mul e j2 j1 m (t .snd)) ]

def blind_wedge_beta (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (c : BlindAltStrings G1 G2)
  : Loop (blind_wedge_pointed (BG G1) (BG G2) W)
  ≔ let a12 ≔ W .snd .i1 (shape G1) in
    blind_loop_mul (W .fst) a12 (blind_wedge_i1g (BG G1) (BG G2) W (c .fst))
      (blind_alt_eval G1 G2 (Id (W .fst) a12 a12) (blind_loop_mul (W .fst) a12) (refl a12)
        (blind_wedge_i1g (BG G1) (BG G2) W) (blind_wedge_i2g (BG G1) (BG G2) W) (c .snd .fst) (c .snd .snd))

def blind_lem_wedgeofgpoidisgpoid : Type
  ≔ (G1 G2 : Group) (d1 : DecidableEquality (USym G1)) (d2 : DecidableEquality (USym G2))
    (W : BlindWedge (BG G1) (BG G2))
    → Product
        (Product (Connected (W .fst))
          (Product (isGroupoid (W .fst)) (DecidableEquality (Loop (blind_wedge_pointed (BG G1) (BG G2) W)))))
        (BookIsEquiv (BlindAltStrings G1 G2) (Loop (blind_wedge_pointed (BG G1) (BG G2) W)) (blind_wedge_beta G1 G2 W))
