export "903-normal-subgroups"
export "1202-group-center"
export "951-kernels-of-composites"

{` Chapter 9 (subgroups.tex 1876-1936), sec:aut-group: the remark making
   USym(inn) explicit, and the running text after it (the fibers of Binn,
   Ker(inn) ≅ Z(G) with ker(inn) becoming the center inclusion).
   inn : Hom(G, Aut(G)) is module 437's (Binn(y) ≔ mkgroup(BG÷, y), pointed
   by the component path over refl_G). `}

{` "Through univalence, the path (refl, p) : (X, x) = (X, y) of pointed
   types is the equivalence id pointed by p": pointed_path_to_equiv
   (module 162) of refl_{(X,-)}(p) is pointed-homotopic to (id, p⁻¹) (book
   orientation y = id(x); the book says "pointed by the path p"). In the
   reflexive case transport along refl_X is the identity only up to
   refl_X.liftr. `}
def ch9w2_pointed_path_point_refl (X : Type) (x : X)
  : Id (Id X (refl X .trr x) x)
      (pathover_transport_equiv Type (T ↦ T) X X (refl X) x x .map (refl x))
      (inverse X x (refl X .trr x) (refl X .liftr x))
  ≔ let E ≔ Id X x x in
    let F ≔ Id X (refl X .trr x) x in
    let r ≔ inverse X (refl X .trr x) x (transport_refl Type (T ↦ T) X x) in
    let base : (v : X) → Id Type (Id X x v) (Id X (refl X .trr x) v)
      ≔ v ↦ refl ((b ↦ Id X b v) : X → Type) r in
    let motive : (Y : Type) → Id Type X Y → Type
      ≔ Y q ↦ (v : Y) → Id Type (Id (T ↦ T) q x v) (Id Y (transport Type (T ↦ T) X Y q x) v) in
    let jb : Id (Id Type E F) (pathover_transport_type Type (T ↦ T) X X (refl X) x x) (base x)
      ≔ refl ((k ↦ k x) : ((v : X) → Id Type (Id X x v) (Id X (refl X .trr x) v)) → Id Type E F)
          (inverse ((v : X) → Id Type (Id X x v) (Id X (refl X .trr x) v)) base
            (J Type X motive base X (refl X)) (Jβ Type X motive base)) in
    calc
      pathover_transport_equiv Type (T ↦ T) X X (refl X) x x .map (refl x)
      = id_to_equiv E F (base x) .map (refl x)
        by refl ((q ↦ id_to_equiv E F q .map (refl x)) : Id Type E F → F) jb
      = base x .trr (refl x) by id_to_equiv_transport E F (base x) (refl x)
      = concat X (refl X .trr x) x x (inverse X x (refl X .trr x) r) (refl x)
        by transport_path_to X x x (refl X .trr x) r (refl x)
      = inverse X x (refl X .trr x) r by concat_p1 X (refl X .trr x) x (inverse X x (refl X .trr x) r)
      = transport_refl Type (T ↦ T) X x by inverse_inverse X (refl X .trr x) x (transport_refl Type (T ↦ T) X x)
      = inverse X x (refl X .trr x) (refl X .liftr x) by refl (inverse X x (refl X .trr x) (refl X .liftr x)) ∎

def ch9w2_pointed_path_refl_homotopy (X : Type) (x y : X) (p : Id X x y)
  : PointedHomotopy (X, x) (X, y)
      (pointed_path_to_equiv (X, x) (X, y) (refl ((z ↦ ((X, z) : Pointed)) : X → Pointed) p) .fst)
      (identity X, inverse X x y p)
  ≔ J X x
      (y p ↦ PointedHomotopy (X, x) (X, y)
        (pointed_path_to_equiv (X, x) (X, y) (refl ((z ↦ ((X, z) : Pointed)) : X → Pointed) p) .fst)
        (identity X, inverse X x y p))
      ((z ↦ inverse X z (refl X .trr z) (refl X .liftr z)),
       let t ≔ refl X .trr x in let l ≔ refl X .liftr x in
       calc
         concat X x t x (inverse X t x (pathover_transport_equiv Type (T ↦ T) X X (refl X) x x .map (refl x)))
           (inverse X x t l)
         = concat X x t x (inverse X t x (inverse X x t l)) (inverse X x t l)
           by refl ((q ↦ concat X x t x (inverse X t x q) (inverse X x t l)) : Id X t x → Id X x x)
                (ch9w2_pointed_path_point_refl X x)
         = concat X x t x l (inverse X x t l)
           by refl ((q ↦ concat X x t x q (inverse X x t l)) : Id X x t → Id X x x) (inverse_inverse X x t l)
         = refl x by concat_inverse_right X x t l
         = inverse X x x (refl x) by inverse (Id X x x) (inverse X x x (refl x)) (refl x) (inverse_refl X x) ∎)
      y p

{` The remark (subgroups.tex 1887). USym(inn)(g) is an identification
   G = G (inn_usym_fst: it is ap_{y ↦ mkgroup(BG÷,y)}(g), with B-component
   (refl_{BG÷}, g) judgmentally); through univalence it is the isomorphism
   inn_symmetry_iso G g, which is the pointed equivalence (id_BG, g⁻¹)
   (conj_hom of module 437). `}
def inn_symmetry_iso (G : Group) (g : USym G) : GroupIso G G
  ≔ group_path_iso_equiv G G .map (usym_hom G (group_aut G) (inn G) g .fst)

def inn_ap_iso_hom (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : Id (GroupHom G (group_at G y)) (group_path_iso_equiv G (group_at G y) .map (refl (group_at G) p) .fst)
      (conj_hom G y p)
  ≔ ch9_hom_path G (group_at G y) (group_path_iso_equiv G (group_at G y) .map (refl (group_at G) p) .fst) (conj_hom G y p)
      (ch9w2_pointed_path_refl_homotopy (BG G .carrier) (shape G) y p)

def inn_symmetry_iso_hom (G : Group) (g : USym G)
  : Id (GroupHom G G) (inn_symmetry_iso G g .fst) (conj_hom G (shape G) g)
  ≔ concat (GroupHom G G) (inn_symmetry_iso G g .fst)
      (group_path_iso_equiv G G .map (refl (group_at G) g) .fst) (conj_hom G (shape G) g)
      (refl ((r ↦ group_path_iso_equiv G G .map r .fst) : Id Group G G → GroupHom G G) (inn_usym_fst G g))
      (inn_ap_iso_hom G (shape G) g)

{` USym(USym inn(g)) : USym G → USym G is h ↦ g·h·g⁻¹ (usym_mul
   convention, g·h = concat h g). The book prints h ↦ g⁻¹hg, which is the
   conjugation by g⁻¹, i.e. USym(USym inn(g⁻¹)); the difference comes from
   reading the pointing of "id pointed by p" as p instead of p⁻¹ (in the
   book's orientation y = id(sh_G) the pointing path must be p⁻¹). Either
   way USym inn(g) is the inner automorphism associated with g. `}
def inn_usym_usym (G : Group) (g h : USym G)
  : Id (USym G) (usym_hom G G (inn_symmetry_iso G g .fst) h) (usym_mul G (usym_mul G g h) (usym_inv G g))
  ≔ concat (USym G) (usym_hom G G (inn_symmetry_iso G g .fst) h) (usym_hom G G (conj_hom G (shape G) g) h)
      (usym_mul G (usym_mul G g h) (usym_inv G g))
      (refl ((k ↦ usym_hom G G k h) : GroupHom G G → USym G) (inn_symmetry_iso_hom G g))
      (conj_at_shape_usym G g h)

{` The fiber of Binn at G' : BAut(G):
   Binn⁻¹(G') ≡ Σ_{y:BG} (G' = Binn(y)) ≃ Σ_y Σ_{q : BG'÷ = BG÷} (sh_G' =_q y)
   ≃ (BG'÷ = BG÷) (contracting away y). The book writes the pathover as
   y = trp_q(sh_G'). `}
def ch9w2_pointed_path_sigma_equiv (X Y : Pointed)
  : Equiv (Id Pointed X Y) (Σ (Id Type (X .carrier) (Y .carrier)) (q ↦ Id (T ↦ T) q (X .point) (Y .point)))
  ≔ quasi_inverse_equiv (Id Pointed X Y) (Σ (Id Type (X .carrier) (Y .carrier)) (q ↦ Id (T ↦ T) q (X .point) (Y .point)))
      (r ↦ (r .carrier, r .point)) (s ↦ (s .fst, s .snd)) (r ↦ refl r) (s ↦ refl s)

def inn_fiber_path_equiv (G : Group) (G' : BG (group_aut G) .carrier) (y : BG G .carrier)
  : Equiv (Id (BG (group_aut G) .carrier) G' (hom_function G (group_aut G) (inn G) y))
      (Σ (Id Type (BG (G' .fst) .carrier) (BG G .carrier)) (q ↦ Id (T ↦ T) q (shape (G' .fst)) y))
  ≔ let A ≔ BG (group_aut G) .carrier in let H ≔ G' .fst in let K ≔ group_at G y in
    compose_equiv (Id A G' (hom_function G (group_aut G) (inn G) y)) (Id Group H K)
      (Σ (Id Type (BG H .carrier) (BG G .carrier)) (q ↦ Id (T ↦ T) q (shape H) y))
      (component_path_equiv Group G G' (hom_function G (group_aut G) (inn G) y))
      (compose_equiv (Id Group H K) (Id PointedConnectedGroupoid (group_B H) (group_B K))
        (Σ (Id Type (BG H .carrier) (BG G .carrier)) (q ↦ Id (T ↦ T) q (shape H) y))
        (group_path_classifying_equiv H K)
        (compose_equiv (Id PointedConnectedGroupoid (group_B H) (group_B K)) (Id Pointed (BG H) (BG K))
          (Σ (Id Type (BG H .carrier) (BG G .carrier)) (q ↦ Id (T ↦ T) q (shape H) y))
          (pcg_path_pointed_equiv (group_B H) (group_B K))
          (ch9w2_pointed_path_sigma_equiv (BG H) (BG K))))

def inn_fiber_equiv (G : Group) (G' : BG (group_aut G) .carrier)
  : Equiv (HomFiber G (group_aut G) (inn G) G') (Id Type (BG (G' .fst) .carrier) (BG G .carrier))
  ≔ let X ≔ BG G .carrier in let X' ≔ BG (G' .fst) .carrier in
    let Q : Id Type X' X → X → Type ≔ q y ↦ Id (T ↦ T) q (shape (G' .fst)) y in
    compose_equiv (HomFiber G (group_aut G) (inn G) G') (Σ X (y ↦ Σ (Id Type X' X) (q ↦ Q q y))) (Id Type X' X)
      (family_equiv X (y ↦ Id (BG (group_aut G) .carrier) G' (hom_function G (group_aut G) (inn G) y))
        (y ↦ Σ (Id Type X' X) (q ↦ Q q y)) (inn_fiber_path_equiv G G'))
      (compose_equiv (Σ X (y ↦ Σ (Id Type X' X) (q ↦ Q q y))) (Σ (Id Type X' X) (q ↦ Σ X (y ↦ Q q y))) (Id Type X' X)
        (sigma_comm X (Id Type X' X) (y q ↦ Q q y))
        (contractible_fiber_projection (Id Type X' X) (q ↦ Σ X (y ↦ Q q y))
          (q ↦ ch9w2_pathover_from_contractible Type (T ↦ T) X' X q (shape (G' .fst)))))

{` The map is (y, e) ↦ the BG÷-component of e; the point (sh_G, Binn_pt) of
   the fiber at G goes to refl_{BG÷} (judgmentally). `}
def inn_fiber_equiv_value (G : Group) (G' : BG (group_aut G) .carrier) (u : HomFiber G (group_aut G) (inn G) G')
  : Id (Id Type (BG (G' .fst) .carrier) (BG G .carrier)) (inn_fiber_equiv G G' .map u) (u .snd .fst .classifying .carrier)
  ≔ refl (u .snd .fst .classifying .carrier)

def inn_fiber_equiv_shape (G : Group)
  : Id (Id Type (BG G .carrier) (BG G .carrier)) (inn_fiber_equiv G (shape (group_aut G)) .map (kernel_shape G (group_aut G) (inn G)))
      (refl (BG G .carrier))
  ≔ refl (refl (BG G .carrier))

{` Ker(inn) ≡ Aut_{Binn⁻¹(G)}(sh_G, Binn_pt) ≅ Aut_{(BG÷ = BG÷)}(refl) ≡ Z(G)
   (group_center of module 1202, the center of sec:abelian-groups). `}
def inn_kernel_center_hom (G : Group) : GroupHom (kernel_group G (group_aut G) (inn G)) (group_center G)
  ≔ ch9w2_aut_hom (HomFiber G (group_aut G) (inn G) (shape (group_aut G))) (Id Type (BG G .carrier) (BG G .carrier))
      (hom_fiber_groupoid G (group_aut G) (inn G) (shape (group_aut G))) (center_space_groupoid G)
      (inn_fiber_equiv G (shape (group_aut G)) .map) (kernel_shape G (group_aut G) (inn G))
      (refl (BG G .carrier)) (refl (refl (BG G .carrier)))

def inn_kernel_center_iso (G : Group)
  : IsGroupIso (kernel_group G (group_aut G) (inn G)) (group_center G) (inn_kernel_center_hom G)
  ≔ book_equivalence (BG (kernel_group G (group_aut G) (inn G)) .carrier) (BG (group_center G) .carrier)
      (ch9w2_component_equiv (HomFiber G (group_aut G) (inn G) (shape (group_aut G))) (Id Type (BG G .carrier) (BG G .carrier))
        (inn_fiber_equiv G (shape (group_aut G))) (kernel_shape G (group_aut G) (inn G))) .equiv

def inn_kernel_center_path (G : Group) : Id Group (kernel_group G (group_aut G) (inn G)) (group_center G)
  ≔ group_path_from_iso (kernel_group G (group_aut G) (inn G)) (group_center G)
      (inn_kernel_center_hom G, inn_kernel_center_iso G)

{` "Under this equivalence, ker(inn) becomes the center inclusion z_G":
   ker(inn) = z_G ∘ (Ker(inn) ≅ Z(G)). Pointwise y = q.trr(sh_G) is the
   pathover (sh_G =_q y) read as a transport; at the base point this is
   refl_{BG÷}.liftr(sh_G), the pointing of z_G (module 1202). `}
def inn_kernel_inclusion_center (G : Group)
  : Id (GroupHom (kernel_group G (group_aut G) (inn G)) G) (kernel_inclusion G (group_aut G) (inn G))
      (group_hom_compose (kernel_group G (group_aut G) (inn G)) (group_center G) G
        (inn_kernel_center_hom G) (center_inclusion G))
  ≔ let X ≔ BG G .carrier in let x ≔ shape G in
    let K ≔ kernel_group G (group_aut G) (inn G) in
    let PTE : (q : Id Type X X) (y : X) → Equiv (Id (T ↦ T) q x y) (Id X (q .trr x) y)
      ≔ q y ↦ pathover_transport_equiv Type (T ↦ T) X X q x y in
    let t ≔ refl X .trr x in let l ≔ refl X .liftr x in
    ch9_hom_path K G (kernel_inclusion G (group_aut G) (inn G))
      (group_hom_compose K (group_center G) G (inn_kernel_center_hom G) (center_inclusion G))
      ((u ↦ inverse X (u .fst .snd .fst .classifying .carrier .trr x) (u .fst .fst)
             (PTE (u .fst .snd .fst .classifying .carrier) (u .fst .fst) .map (u .fst .snd .fst .classifying .point))),
       calc
         concat X x x t (refl x) (inverse X t x (PTE (refl X) x .map (refl x)))
         = inverse X t x (PTE (refl X) x .map (refl x)) by concat_1p X x t (inverse X t x (PTE (refl X) x .map (refl x)))
         = inverse X t x (inverse X x t l)
           by refl (inverse X t x) (ch9w2_pointed_path_point_refl X x)
         = l by inverse_inverse X x t l
         = concat X x t t l (refl t) by inverse (Id X x t) (concat X x t t l (refl t)) l (concat_p1 X x t l) ∎)

{` Litmus: for abelian G every symmetry is inner-trivial, Ker(inn) = G. `}
def inn_kernel_abelian_path (G : Group) (h : IsAbelian G) : Id Group (kernel_group G (group_aut G) (inn G)) G
  ≔ concat Group (kernel_group G (group_aut G) (inn G)) (group_center G) G (inn_kernel_center_path G) (abelian_center_path G h)
