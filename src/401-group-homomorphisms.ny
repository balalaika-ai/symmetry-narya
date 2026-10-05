export "400-groups"

{` Chapter 4, section "Homomorphisms" (group.tex).

   Loops of pointed maps. All paths are in concatenation (diagrammatic) order:
   concat p q first follows p, then q. The book's composite q·p is concat p q. `}

{` def:loops-map. Ω k(p) ≔ k_pt⁻¹ · ap_{k÷}(p) · k_pt with k_pt : pt_Y = k(pt_X).
   In concatenation order this is k_pt, then ap_k(p), then k_pt⁻¹, bracketed as
   pointed_loop_conjugate (module 129): concat k_pt (concat (ap_k p) k_pt⁻¹). `}
def loops_map (X Y : Pointed) (k : BookPointedMap X Y) (l : Loop X) : Loop Y
  ≔ pointed_loop_conjugate (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd) (refl (k .fst) l)

{` Conjugation laws, for an arbitrary path p : a = x. `}
def loop_conjugate_unit (A : Type) (a x : A) (p : Id A a x)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a)
  ≔ concat (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (concat A a x a p (inverse A a x p)) (refl a)
      (refl (concat A a x a p) (concat_1p A x a (inverse A a x p)))
      (concat_inverse_right A a x p)

def loop_conjugate_at_refl (A : Type) (a : A) (l : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l
  ≔ calc
      pointed_loop_conjugate A a a (refl a) l = concat A a a a l (inverse A a a (refl a))
        by concat_1p A a a (concat A a a a l (inverse A a a (refl a)))
      = concat A a a a l (refl a) by refl (concat A a a a l) (inverse_refl A a)
      = l by concat_p1 A a a l ∎

def loop_conjugate_inverse_base (A : Type) (a : A) (l : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a a (refl a) (inverse A a a l))
      (inverse A a a (pointed_loop_conjugate A a a (refl a) l))
  ≔ concat (Id A a a) (pointed_loop_conjugate A a a (refl a) (inverse A a a l)) (inverse A a a l)
      (inverse A a a (pointed_loop_conjugate A a a (refl a) l))
      (loop_conjugate_at_refl A a (inverse A a a l))
      (refl (inverse A a a) (inverse (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l
        (loop_conjugate_at_refl A a l)))

def loop_conjugate_inverse (A : Type) (a x : A) (p : Id A a x) (l : Id A x x)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (inverse A x x l))
      (inverse A a a (pointed_loop_conjugate A a x p l))
  ≔ J A a (x p ↦ (l : Id A x x) → Id (Id A a a) (pointed_loop_conjugate A a x p (inverse A x x l))
        (inverse A a a (pointed_loop_conjugate A a x p l)))
      (loop_conjugate_inverse_base A a) x p l

def loop_conjugate_concat_base (A : Type) (a : A) (l m : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a a (refl a) (concat A a a a l m))
      (concat A a a a (pointed_loop_conjugate A a a (refl a) l) (pointed_loop_conjugate A a a (refl a) m))
  ≔ concat (Id A a a) (pointed_loop_conjugate A a a (refl a) (concat A a a a l m)) (concat A a a a l m)
      (concat A a a a (pointed_loop_conjugate A a a (refl a) l) (pointed_loop_conjugate A a a (refl a) m))
      (loop_conjugate_at_refl A a (concat A a a a l m))
      (inverse (Id A a a)
        (concat A a a a (pointed_loop_conjugate A a a (refl a) l) (pointed_loop_conjugate A a a (refl a) m))
        (concat A a a a l m)
        (refl (concat A a a a) (loop_conjugate_at_refl A a l) (loop_conjugate_at_refl A a m)))

def loop_conjugate_concat (A : Type) (a x : A) (p : Id A a x) (l m : Id A x x)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (concat A x x x l m))
      (concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m))
  ≔ J A a (x p ↦ (l m : Id A x x) → Id (Id A a a) (pointed_loop_conjugate A a x p (concat A x x x l m))
        (concat A a a a (pointed_loop_conjugate A a x p l) (pointed_loop_conjugate A a x p m)))
      (loop_conjugate_concat_base A a) x p l m

{` def:loops-map, the pointing path (Ω k)_pt : refl = Ω k(refl), by the
   inverse law. Ω k is then a pointed map Ω X →* Ω Y. `}
def loops_map_point (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (Loop Y) (refl (Y .point)) (loops_map X Y k (refl (X .point)))
  ≔ inverse (Loop Y) (loops_map X Y k (refl (X .point))) (refl (Y .point))
      (loop_conjugate_unit (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd))

def loops_pointed_map (X Y : Pointed) (k : BookPointedMap X Y) : BookPointedMap (Omega X) (Omega Y)
  ≔ (loops_map X Y k, loops_map_point X Y k)

{` rem:loops-map. If k is pointed by refl, then Ω k = ap_k. `}
def loops_map_refl_pointing (A B : Type) (f : A → B) (x : A)
  : Id (Id A x x → Id B (f x) (f x)) (loops_map (A, x) (B, f x) (f, refl (f x))) (l ↦ refl f l)
  ≔ funext (Id A x x) (_ ↦ Id B (f x) (f x)) (loops_map (A, x) (B, f x) (f, refl (f x))) (l ↦ refl f l)
      (l ↦ loop_conjugate_at_refl B (f x) (refl f l))

{` lem:grouphomomaxioms for arbitrary pointed maps: Ω k preserves refl,
   inverses and composition. `}
def loops_map_unit (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (Loop Y) (loops_map X Y k (refl (X .point))) (refl (Y .point))
  ≔ loop_conjugate_unit (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd)

def loops_map_inverse (X Y : Pointed) (k : BookPointedMap X Y) (g : Loop X)
  : Id (Loop Y) (loops_map X Y k (inverse (X .carrier) (X .point) (X .point) g))
      (inverse (Y .carrier) (Y .point) (Y .point) (loops_map X Y k g))
  ≔ let B ≔ Y .carrier in let fx ≔ k .fst (X .point) in
    concat (Loop Y) (loops_map X Y k (inverse (X .carrier) (X .point) (X .point) g))
      (pointed_loop_conjugate B (Y .point) fx (k .snd) (inverse B fx fx (refl (k .fst) g)))
      (inverse B (Y .point) (Y .point) (loops_map X Y k g))
      (refl (pointed_loop_conjugate B (Y .point) fx (k .snd))
        (map_path_inverse (X .carrier) B (k .fst) (X .point) (X .point) g))
      (loop_conjugate_inverse B (Y .point) fx (k .snd) (refl (k .fst) g))

def loops_map_concat (X Y : Pointed) (k : BookPointedMap X Y) (g h : Loop X)
  : Id (Loop Y) (loops_map X Y k (concat (X .carrier) (X .point) (X .point) (X .point) g h))
      (concat (Y .carrier) (Y .point) (Y .point) (Y .point) (loops_map X Y k g) (loops_map X Y k h))
  ≔ let B ≔ Y .carrier in let fx ≔ k .fst (X .point) in
    concat (Loop Y) (loops_map X Y k (concat (X .carrier) (X .point) (X .point) (X .point) g h))
      (pointed_loop_conjugate B (Y .point) fx (k .snd) (concat B fx fx fx (refl (k .fst) g) (refl (k .fst) h)))
      (concat B (Y .point) (Y .point) (Y .point) (loops_map X Y k g) (loops_map X Y k h))
      (refl (pointed_loop_conjugate B (Y .point) fx (k .snd))
        (map_path_concat (X .carrier) B (k .fst) (X .point) (X .point) (X .point) g h))
      (loop_conjugate_concat B (Y .point) fx (k .snd) (refl (k .fst) g) (refl (k .fst) h))

{` def:loops-compose. Ω(g ∘ f) = Ω g ∘ Ω f, by induction on the pointing
   path of f (the same argument as pointed_conjugate_compose of module 260,
   which is not imported here). `}
def loops_compose_conjugate (A B : Type) (a : A) (b : B) (g : B → A) (pg : Id A a (g b))
  (x : B) (p : Id B b x) (l : Id B x x)
  : Id (Id A a a) (pointed_loop_conjugate A a (g x) (concat A a (g b) (g x) pg (refl g p)) (refl g l))
      (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b x p l)))
  ≔ J B b
      (x p ↦ (l : Id B x x) → Id (Id A a a)
        (pointed_loop_conjugate A a (g x) (concat A a (g b) (g x) pg (refl g p)) (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b x p l))))
      (l ↦ concat (Id A a a)
        (pointed_loop_conjugate A a (g b) (concat A a (g b) (g b) pg (refl (g b))) (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b b (refl b) l)))
        (refl ((q ↦ pointed_loop_conjugate A a (g b) q (refl g l)) : Id A a (g b) → Id A a a) (concat_p1 A a (g b) pg))
        (inverse (Id A a a) (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b b (refl b) l)))
          (pointed_loop_conjugate A a (g b) pg (refl g l))
          (refl ((w ↦ pointed_loop_conjugate A a (g b) pg (refl g w)) : Id B b b → Id A a a) (loop_conjugate_at_refl B b l))))
      x p l

def loops_map_compose_pointwise (X Y Z : Pointed) (f : BookPointedMap X Y) (g : BookPointedMap Y Z) (l : Loop X)
  : Id (Loop Z) (loops_map X Z (book_pointed_compose X Y Z f g) l) (loops_map Y Z g (loops_map X Y f l))
  ≔ loops_compose_conjugate (Z .carrier) (Y .carrier) (Z .point) (Y .point) (g .fst) (g .snd)
      (f .fst (X .point)) (f .snd) (refl (f .fst) l)

def loops_map_compose (X Y Z : Pointed) (f : BookPointedMap X Y) (g : BookPointedMap Y Z)
  : Id (Loop X → Loop Z) (loops_map X Z (book_pointed_compose X Y Z f g))
      (l ↦ loops_map Y Z g (loops_map X Y f l))
  ≔ funext (Loop X) (_ ↦ Loop Z) (loops_map X Z (book_pointed_compose X Y Z f g))
      (l ↦ loops_map Y Z g (loops_map X Y f l)) (loops_map_compose_pointwise X Y Z f g)

{` lem:hom-is-set, footnote ft:ptd-decr-h-lev: X →* Y is a set when X is
   connected and Y is a groupoid. The proof follows the book: two pointed
   homotopies agree at the base point by cancelling f_pt, hence everywhere
   by connectedness. `}
def pointed_homotopy_prop (X Y : Pointed) (hX : Connected (X .carrier)) (hY : isGroupoid (Y .carrier))
  (f g : BookPointedMap X Y) : isProp (PointedHomotopy X Y f g)
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let x0 ≔ X .point in
    let H ≔ Homotopy A (_ ↦ B) (f .fst) (g .fst) in
    let P : H → Type ≔ h ↦ Id (Id B (Y .point) (g .fst x0))
      (concat B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (h x0)) (g .snd) in
    u v ↦
      let D : A → Type ≔ t ↦ Id (Id B (f .fst t) (g .fst t)) (u .fst t) (v .fst t) in
      let d0 : D x0 ≔ concat_cancel_left B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (u .fst x0) (v .fst x0)
        (concat (Id B (Y .point) (g .fst x0))
          (concat B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (u .fst x0)) (g .snd)
          (concat B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (v .fst x0))
          (u .snd) (inverse (Id B (Y .point) (g .fst x0))
            (concat B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (v .fst x0)) (g .snd) (v .snd))) in
      subtype_equal H P
        (h ↦ hY (Y .point) (g .fst x0) (concat B (Y .point) (f .fst x0) (g .fst x0) (f .snd) (h x0)) (g .snd))
        u v
        (funext A (t ↦ Id B (f .fst t) (g .fst t)) (u .fst) (v .fst)
          (t ↦ mere_rec (Id A x0 t) (D t) (hY (f .fst t) (g .fst t) (u .fst t) (v .fst t))
            (p ↦ transport A D x0 t p d0) (hX .snd x0 t)))

def pointed_maps_set (X Y : Pointed) (hX : Connected (X .carrier)) (hY : isGroupoid (Y .carrier))
  : isSet (BookPointedMap X Y)
  ≔ f g ↦ hlevel_one_to_prop (Id (BookPointedMap X Y) f g)
      (hlevel_equiv (suc. zero.) (PointedHomotopy X Y f g) (Id (BookPointedMap X Y) f g)
        (canonical_inverse_equiv (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
          (pointed_map_path_equiv X Y f g))
        (prop_to_hlevel_one (PointedHomotopy X Y f g) (pointed_homotopy_prop X Y hX hY f g)))

{` def:grouphomomorphism. Hom(G, H) is a wrapped copy of BG →* BH, again a
   one-field record (judgmental eta; rem:Bf-convention is then trivial). `}
def GroupHom (G H : Group) : Type ≔ sig (classifying_map : BookPointedMap (BG G) (BG H))

def mkhom (G H : Group) (k : BookPointedMap (BG G) (BG H)) : GroupHom G H ≔ (classifying_map ≔ k)

{` The destructor B : Hom(G, H) → (BG →* BH); Bf is the classifying map. `}
def hom_B (G H : Group) (f : GroupHom G H) : BookPointedMap (BG G) (BG H) ≔ f .classifying_map

def hom_function (G H : Group) (f : GroupHom G H) : BG G .carrier → BG H .carrier
  ≔ f .classifying_map .fst

def hom_point (G H : Group) (f : GroupHom G H) : Id (BG H .carrier) (shape H) (hom_function G H f (shape G))
  ≔ f .classifying_map .snd

def group_hom_classifying_equiv (G H : Group) : Equiv (GroupHom G H) (BookPointedMap (BG G) (BG H))
  ≔ quasi_inverse_equiv (GroupHom G H) (BookPointedMap (BG G) (BG H)) (hom_B G H) (mkhom G H)
      (f ↦ refl f) (k ↦ refl k)

{` def:USym-hom. USym f ≔ Ω Bf. `}
def usym_hom (G H : Group) (f : GroupHom G H) : USym G → USym H ≔ loops_map (BG G) (BG H) (hom_B G H f)

{` lem:grouphomomaxioms in the book's notation (usym_mul G g' g = g'·g). `}
def usym_hom_unit (G H : Group) (f : GroupHom G H)
  : Id (USym H) (usym_hom G H f (usym_unit G)) (usym_unit H)
  ≔ loops_map_unit (BG G) (BG H) (hom_B G H f)

def usym_hom_inv (G H : Group) (f : GroupHom G H) (g : USym G)
  : Id (USym H) (usym_hom G H f (usym_inv G g)) (usym_inv H (usym_hom G H f g))
  ≔ loops_map_inverse (BG G) (BG H) (hom_B G H f) g

def usym_hom_mul (G H : Group) (f : GroupHom G H) (g' g : USym G)
  : Id (USym H) (usym_hom G H f (usym_mul G g' g)) (usym_mul H (usym_hom G H f g') (usym_hom G H f g))
  ≔ loops_map_concat (BG G) (BG H) (hom_B G H f) g g'

{` def:groupisomorphism. f is an isomorphism if Bf÷ is an equivalence. `}
def IsGroupIso (G H : Group) (f : GroupHom G H) : Type
  ≔ BookIsEquiv (BG G .carrier) (BG H .carrier) (hom_function G H f)

def is_group_iso_prop (G H : Group) (f : GroupHom G H) : isProp (IsGroupIso G H f)
  ≔ pi_prop (BG H .carrier) (y ↦ BookIsContr (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) y))
      (y ↦ book_iscontr_isprop (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) y))

def GroupIso (G H : Group) : Type ≔ Σ (GroupHom G H) (IsGroupIso G H)

{` def:identity-group-homomorphism. `}
def group_hom_id (G : Group) : GroupHom G G ≔ mkhom G G (book_pointed_identity (BG G))

def group_hom_id_iso (G : Group) : IsGroupIso G G (group_hom_id G)
  ≔ identity_book_equiv (BG G .carrier) .equiv

def group_iso_id (G : Group) : GroupIso G G ≔ (group_hom_id G, group_hom_id_iso G)

{` def:group-homomorphism-composition. group_hom_compose G H K f g is the
   book's g ∘ f : G → K (f first), classified by book_pointed_compose. `}
def group_hom_compose (G H K : Group) (f : GroupHom G H) (g : GroupHom H K) : GroupHom G K
  ≔ mkhom G K (book_pointed_compose (BG G) (BG H) (BG K) (hom_B G H f) (hom_B H K g))

{` cor:USym-compose. USym(g ∘ f) = USym g ∘ USym f. `}
def usym_hom_compose (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
  : Id (USym G → USym K) (usym_hom G K (group_hom_compose G H K f g))
      (x ↦ usym_hom H K g (usym_hom G H f x))
  ≔ loops_map_compose (BG G) (BG H) (BG K) (hom_B G H f) (hom_B H K g)

{` The paragraph before lem:hom-is-set: identifications of homomorphisms
   are pointed homotopies h with h(sh_G) · Bf_pt = Bf'_pt. `}
def group_hom_path_equiv (G H : Group) (f f' : GroupHom G H)
  : Equiv (Id (GroupHom G H) f f') (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
  ≔ compose_equiv (Id (GroupHom G H) f f') (Id (BookPointedMap (BG G) (BG H)) (hom_B G H f) (hom_B G H f'))
      (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
      (quasi_inverse_equiv (Id (GroupHom G H) f f') (Id (BookPointedMap (BG G) (BG H)) (hom_B G H f) (hom_B G H f'))
        (p ↦ p .classifying_map) (q ↦ (classifying_map ≔ q)) (p ↦ refl p) (q ↦ refl q))
      (pointed_map_path_equiv (BG G) (BG H) (hom_B G H f) (hom_B G H f'))

{` lem:hom-is-set. `}
def group_hom_set (G H : Group) : isSet (GroupHom G H)
  ≔ hlevel_two_to_set (GroupHom G H)
      (hlevel_equiv (suc. (suc. zero.)) (BookPointedMap (BG G) (BG H)) (GroupHom G H)
        (canonical_inverse_equiv (GroupHom G H) (BookPointedMap (BG G) (BG H)) (group_hom_classifying_equiv G H))
        (set_to_hlevel_two (BookPointedMap (BG G) (BG H))
          (pointed_maps_set (BG G) (BG H) (bg_connected G) (bg_groupoid H))))

def group_iso_set (G H : Group) : isSet (GroupIso G H)
  ≔ sigma_set (GroupHom G H) (IsGroupIso G H) (group_hom_set G H)
      (f ↦ prop_is_set (IsGroupIso G H f) (is_group_iso_prop G H f))

{` Unit and associativity laws of composition of homomorphisms (from the
   corresponding laws of pointed maps). group_hom_compose G H K f g is g ∘ f. `}
def group_hom_id_compose (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G H) (group_hom_compose G G H (group_hom_id G) f) f
  ≔ refl (mkhom G H)
      ((refl (hom_function G H f),
        concat_p1 (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f))
       : Id (BookPointedMap (BG G) (BG H))
           (book_pointed_compose (BG G) (BG G) (BG H) (book_pointed_identity (BG G)) (hom_B G H f)) (hom_B G H f))

def group_hom_compose_id (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G H) (group_hom_compose G H H f (group_hom_id H)) f
  ≔ refl (mkhom G H)
      ((refl (hom_function G H f),
        concat_1p (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f))
       : Id (BookPointedMap (BG G) (BG H))
           (book_pointed_compose (BG G) (BG H) (BG H) (hom_B G H f) (book_pointed_identity (BG H))) (hom_B G H f))

def group_hom_compose_assoc (G H K L : Group) (f : GroupHom G H) (g : GroupHom H K) (h : GroupHom K L)
  : Id (GroupHom G L) (group_hom_compose G K L (group_hom_compose G H K f g) h)
      (group_hom_compose G H L f (group_hom_compose H K L g h))
  ≔ let C ≔ BG L .carrier in let hf ≔ hom_function K L h in let gf ≔ hom_function H K g in
    let x0 ≔ shape G in let y0 ≔ shape H in
    let fpt ≔ hom_point G H f in let gpt ≔ hom_point H K g in let hpt ≔ hom_point K L h in
    let z1 ≔ gf (hom_function G H f x0) in
    refl (mkhom G L)
      ((refl ((x ↦ hf (gf (hom_function G H f x))) : BG G .carrier → C),
        concat (Id C (shape L) (hf z1))
          (concat C (shape L) (hf (shape K)) (hf z1) hpt
            (refl hf (concat (BG K .carrier) (shape K) (gf y0) z1 gpt (refl gf fpt))))
          (concat C (shape L) (hf (shape K)) (hf z1) hpt
            (concat C (hf (shape K)) (hf (gf y0)) (hf z1) (refl hf gpt) (refl hf (refl gf fpt))))
          (concat C (shape L) (hf (gf y0)) (hf z1)
            (concat C (shape L) (hf (shape K)) (hf (gf y0)) hpt (refl hf gpt)) (refl hf (refl gf fpt)))
          (refl (concat C (shape L) (hf (shape K)) (hf z1) hpt)
            (map_path_concat (BG K .carrier) C hf (shape K) (gf y0) z1 gpt (refl gf fpt)))
          (inverse (Id C (shape L) (hf z1))
            (concat C (shape L) (hf (gf y0)) (hf z1)
              (concat C (shape L) (hf (shape K)) (hf (gf y0)) hpt (refl hf gpt)) (refl hf (refl gf fpt)))
            (concat C (shape L) (hf (shape K)) (hf z1) hpt
              (concat C (hf (shape K)) (hf (gf y0)) (hf z1) (refl hf gpt) (refl hf (refl gf fpt))))
            (concat_assoc C (shape L) (hf (shape K)) (hf (gf y0)) (hf z1) hpt (refl hf gpt) (refl hf (refl gf fpt)))))
       : Id (BookPointedMap (BG G) (BG L))
           (hom_B G L (group_hom_compose G K L (group_hom_compose G H K f g) h))
           (hom_B G L (group_hom_compose G H L f (group_hom_compose H K L g h))))

{` USym of the identity homomorphism is the identity. `}
def usym_hom_id (G : Group) (g : USym G) : Id (USym G) (usym_hom G G (group_hom_id G) g) g
  ≔ loop_conjugate_at_refl (BG G .carrier) (shape G) g
