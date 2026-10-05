export "186-chapter-two-remarks"

{` Chapter 4, section "The type of groups" (group.tex).

   def:pt-conn-groupoid. The book's U^{=1}_* = Σ(A : U)(A × isconn(A) × isgrpd(A)),
   as a record with the four components in the printed order. `}
def PointedConnectedGroupoid : Type ≔ sig (
  carrier : Type,
  point : carrier,
  connected : Connected carrier,
  groupoid : isGroupoid carrier)

{` The pointed type (A, a) by which the book refers to (A, a, p, q). `}
def pcg_pointed (X : PointedConnectedGroupoid) : Pointed ≔ (X .carrier, X .point)

{` def:typegroup. Group is a wrapped copy of U^{=1}_* with constructor
   mkgroup. It is a one-field record rather than the data type Copy of
   module 16: records have judgmental eta, so mkgroup (group_B G) ≡ G and
   group_B (mkgroup X) ≡ X both hold by definition (the book's Copy
   induction principle of rem:BG-convention is then trivial), and the
   identity types of Group compute fieldwise to identity types of U^{=1}_*. `}
def Group : Type ≔ sig (classifying : PointedConnectedGroupoid)

def mkgroup (X : PointedConnectedGroupoid) : Group ≔ (classifying ≔ X)

{` def:classifying-type. The destructor B : Group → U^{=1}_*. `}
def group_B (G : Group) : PointedConnectedGroupoid ≔ G .classifying

{` The classifying type BG as a pointed type, and the designated shape
   sh_G = pt_BG. `}
def BG (G : Group) : Pointed ≔ pcg_pointed (G .classifying)

def shape (G : Group) : BG G .carrier ≔ G .classifying .point

def bg_connected (G : Group) : Connected (BG G .carrier) ≔ G .classifying .connected

def bg_groupoid (G : Group) : isGroupoid (BG G .carrier) ≔ G .classifying .groupoid

{` rem:BG-convention: by eta, every group is mkgroup of its classifying type. `}
def group_eta (G : Group) : Id Group (mkgroup (group_B G)) G ≔ refl G

def group_beta (X : PointedConnectedGroupoid) : Id PointedConnectedGroupoid (group_B (mkgroup X)) X ≔ refl X

{` rem:aut: constructor and destructor form an equivalence Group ≃ U^{=1}_*. `}
def group_classifying_equiv : Equiv Group PointedConnectedGroupoid
  ≔ quasi_inverse_equiv Group PointedConnectedGroupoid group_B mkgroup (G ↦ refl G) (X ↦ refl X)

{` def:looptype. Ω X ≔ (pt_X = pt_X), pointed at refl. The type itself is
   Loop X of module 00. `}
def Omega (X : Pointed) : Pointed ≔ (Loop X, refl (X .point))

{` def:group-symmetries. USym G ≔ Ω BG, the symmetries of the designated shape. `}
def USym (G : Group) : Type ≔ Loop (BG G)

def usym_set (G : Group) : isSet (USym G) ≔ bg_groupoid G (shape G) (shape G)

{` The operations of lem:idtypesgiveabstractgroups in the book's notation:
   e ≔ refl, g⁻¹ ≔ symm g, and g · h ≔ trans(h)(g), i.e. h is followed by g;
   in concatenation order g · h = concat h g. `}
def usym_unit (G : Group) : USym G ≔ refl (shape G)

def usym_inv (G : Group) (g : USym G) : USym G ≔ inverse (BG G .carrier) (shape G) (shape G) g

def usym_mul (G : Group) (g h : USym G) : USym G
  ≔ concat (BG G .carrier) (shape G) (shape G) (shape G) h g

{` def:finite-group. G is finite if the set USym G is finite;
   Card(G) ≔ Card(USym G) with Card from def:groupoidFin. `}
def IsFiniteGroup (G : Group) : Type ≔ IsFinite (USym G)

def group_finite_set (G : Group) (h : IsFiniteGroup G) : FiniteSets ≔ ((USym G, usym_set G), h)

def group_card (G : Group) (h : IsFiniteGroup G) : Nat ≔ Card (group_finite_set G h)

def is_finite_group_prop (G : Group) : isProp (IsFiniteGroup G)
  ≔ mere_isprop (Σ Nat (n ↦ Id Type (USym G) (Fin n)))

{` def:abgp. isAb(G) ≔ Π(g, h : USym G) gh = hg, with gh = usym_mul G g h. `}
def IsAbelian (G : Group) : Type
  ≔ (g h : USym G) → Id (USym G) (usym_mul G g h) (usym_mul G h g)

def is_abelian_prop (G : Group) : isProp (IsAbelian G)
  ≔ pi_prop (USym G) (g ↦ (h : USym G) → Id (USym G) (usym_mul G g h) (usym_mul G h g))
      (g ↦ pi_prop (USym G) (h ↦ Id (USym G) (usym_mul G g h) (usym_mul G h g))
        (h ↦ usym_set G (usym_mul G g h) (usym_mul G h g)))

def AbelianGroup : Type ≔ Σ Group IsAbelian

{` Components of groupoids. A_(a) ≔ Σ(x : A) ‖a = x‖ is NativeComponent A a. `}
def component_point (A : Type) (a : A) : NativeComponent A a ≔ (a, mere (Id A a a) (refl a))

def component_groupoid (A : Type) (hA : isGroupoid A) (a : A) : isGroupoid (NativeComponent A a)
  ≔ hlevel_to_groupoid (NativeComponent A a)
      (subtype_hlevel (suc. (suc. zero.)) A (x ↦ Mere (Id A a x)) (groupoid_to_hlevel A hA)
        (x ↦ mere_isprop (Id A a x)))

def component_pcg (A : Type) (hA : isGroupoid A) (a : A) : PointedConnectedGroupoid
  ≔ (NativeComponent A a, component_point A a, native_component_connected A a, component_groupoid A hA a)

{` def:automorphism-group. Aut_A(a) ≔ mkgroup (A_(a), (a, !)) for a groupoid A. `}
def automorphism_group (A : Type) (hA : isGroupoid A) (a : A) : Group
  ≔ mkgroup (component_pcg A hA a)

{` Paths in a component are paths of first components (lem:subtype-eq-=). `}
def component_path_equiv (A : Type) (a : A) (u v : NativeComponent A a)
  : Equiv (Id (NativeComponent A a) u v) (Id A (u .fst) (v .fst))
  ≔ subtype_path_equiv A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x)) u v

{` USym Aut_A(a) ≃ (a = a): the symmetries of a in A (rem:whypointedconngpoid). `}
def automorphism_group_usym_equiv (A : Type) (hA : isGroupoid A) (a : A)
  : Equiv (USym (automorphism_group A hA a)) (Id A a a)
  ≔ component_path_equiv A a (component_point A a) (component_point A a)
