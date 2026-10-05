export "783-heap-translations"

{` Chapter 7 (absgroup.tex), sec:heaps, xca:heap-variety (line 1408), the
   parts that do not need Group ≃ AbstractGroup: ternary sets, the heap
   equations, the ternary operation of a heap satisfies them (so every
   element of the fiber at (S, t) gives the equations), and the classical
   equivalence between abstract groups and pointed sets with a ternary
   operation satisfying the heap equations (e ↦ x·y ≔ t(x, e, y),
   x⁻¹ ≔ t(e, x, e); conversely t(x, y, z) ≔ x y⁻¹ z). Module 786 combines
   this with Group ≃ AbstractGroup. `}

{` The book's ternary operations t : S × S × S → S (uncurried, as printed),
   the type Σ_{S : Set}(S × S × S → S), and its pointed variant. `}
def Ternary (S : Type) : Type ≔ Product S (Product S S) → S

def TernarySets : Type ≔ Σ SetTypes (X ↦ Ternary (X .fst))

def PointedTernarySets : Type ≔ Σ TernarySets (X ↦ X .fst .fst)

{` The map Heap → Σ_{S : Set}(S × S × S → S), H ↦ (USym H, (p, q, r) ↦ p q⁻¹ r),
   and its lift to heaps with a chosen identification. `}
def heap_ternary_structure (H : Heap) : TernarySets
  ≔ (heap_usym_settype H, u ↦ heap_ternary H (u .fst) (u .snd .fst) (u .snd .snd))

def heap_pointed_structure (u : Σ Heap heap_usym) : PointedTernarySets ≔ (heap_ternary_structure (u .fst), u .snd)

{` The heap equations: t(x, x, y) = y, t(x, y, y) = x and
   para-associativity t(t(x, y, z), u, v) = t(x, y, t(z, u, v)). `}
def HeapEquations (S : Type) (t : Ternary S) : Type
  ≔ Product ((x y : S) → Id S (t (x, (x, y))) y)
      (Product ((x y : S) → Id S (t (x, (y, y))) x)
        ((x y z u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v)))))))

def heap_equations_prop (S : Type) (hS : isSet S) (t : Ternary S) : isProp (HeapEquations S t)
  ≔ product_prop ((x y : S) → Id S (t (x, (x, y))) y)
      (Product ((x y : S) → Id S (t (x, (y, y))) x)
        ((x y z u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v)))))))
      (pi_prop S (x ↦ (y : S) → Id S (t (x, (x, y))) y)
        (x ↦ pi_prop S (y ↦ Id S (t (x, (x, y))) y) (y ↦ hS (t (x, (x, y))) y)))
      (product_prop ((x y : S) → Id S (t (x, (y, y))) x)
        ((x y z u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
        (pi_prop S (x ↦ (y : S) → Id S (t (x, (y, y))) x)
          (x ↦ pi_prop S (y ↦ Id S (t (x, (y, y))) x) (y ↦ hS (t (x, (y, y))) x)))
        (pi_prop S (x ↦ (y z u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
          (x ↦ pi_prop S (y ↦ (z u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
            (y ↦ pi_prop S (z ↦ (u v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
              (z ↦ pi_prop S (u ↦ (v : S) → Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
                (u ↦ pi_prop S (v ↦ Id S (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))
                  (v ↦ hS (t (t (x, (y, z)), (u, v))) (t (x, (y, t (z, (u, v))))))))))))

{` The proposition describing the fiber at (S, t): S is merely inhabited
   and the heap equations hold. `}
def HeapLaws (S : Type) (t : Ternary S) : Type ≔ Product (Mere S) (HeapEquations S t)

def heap_laws_prop (S : Type) (hS : isSet S) (t : Ternary S) : isProp (HeapLaws S t)
  ≔ product_prop (Mere S) (HeapEquations S t) (mere_isprop S) (heap_equations_prop S hS t)

def TernaryHeapLaws (X : TernarySets) : Type ≔ HeapLaws (X .fst .fst) (X .snd)

{` The ternary operation of a heap satisfies the heap equations, and
   USym H is merely inhabited. `}
def heap_ternary_paraassoc (H : Heap) (x y z u v : heap_usym H)
  : Id (heap_usym H) (heap_ternary H (heap_ternary H x y z) u v) (heap_ternary H x y (heap_ternary H z u v))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let g ≔ concat A b a b (inverse A a b y) x in
    let iu ≔ inverse A a b u in
    calc
      concat A a b b v (concat A b a b iu (concat A a b b z g))
      = concat A a b b v (concat A b b b (concat A b a b iu z) g)
        by refl (concat A a b b v)
          (inverse (Id A b b) (concat A b b b (concat A b a b iu z) g) (concat A b a b iu (concat A a b b z g))
            (concat_assoc A b a b b iu z g))
      = concat A a b b (concat A a b b v (concat A b a b iu z)) g
        by inverse (Id A a b) (concat A a b b (concat A a b b v (concat A b a b iu z)) g)
          (concat A a b b v (concat A b b b (concat A b a b iu z) g))
          (concat_assoc A a b b b v (concat A b a b iu z) g) ∎

def heap_ternary_equations (H : Heap) : HeapEquations (heap_usym H) (heap_ternary_structure H .snd)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    (x y ↦ calc
        concat A a b b y (concat A b a b (inverse A a b x) x)
        = concat A a b b y (refl b) by refl (concat A a b b y) (concat_inverse_left A a b x)
        = y by concat_p1 A a b y ∎,
     (x y ↦ heap_concat_cancel_pre A a b b y x,
      x y z u v ↦ heap_ternary_paraassoc H x y z u v))

def heap_ternary_laws (H : Heap) : TernaryHeapLaws (heap_ternary_structure H)
  ≔ (heap_pair_mere_point H, heap_ternary_equations H)

{` xca:heap-variety, the implication from the fiber to the equations: if
   (S, t) = (USym H, p q⁻¹ r) for some heap H, then S is merely inhabited
   and t satisfies the heap equations. `}
def heap_fiber_laws (X : TernarySets) (w : BookFiber Heap TernarySets heap_ternary_structure X) : TernaryHeapLaws X
  ≔ transport TernarySets TernaryHeapLaws (heap_ternary_structure (w .fst)) X
      (inverse TernarySets X (heap_ternary_structure (w .fst)) (w .snd)) (heap_ternary_laws (w .fst))

{` Abstract groups as pointed heaps. The ternary operation of an abstract
   group is t(x, y, z) ≔ (x y⁻¹) z; with the unit it is a pointed ternary
   set. For a group G, the pointed ternary set of the doubled heap of G with
   the chosen identification refl agrees judgmentally with that of abstr G. `}
def abstract_group_ternary (G : AbstractGroup) : Ternary (G .carrier)
  ≔ u ↦ G .mul (G .mul (u .fst) (G .inv (u .snd .fst))) (u .snd .snd)

def abstract_group_pointed_ternary (G : AbstractGroup) : PointedTernarySets
  ≔ (((G .carrier, abstract_group_set G), abstract_group_ternary G), G .unit)

def heap_pointed_structure_double (G : Group)
  : Id PointedTernarySets (heap_pointed_structure (group_heap_lift G)) (abstract_group_pointed_ternary (abstr G))
  ≔ refl (abstract_group_pointed_ternary (abstr G))

def abstract_group_heap_equations (G : AbstractGroup) : HeapEquations (G .carrier) (abstract_group_ternary G)
  ≔ let S ≔ G .carrier in
    let m ≔ G .mul in
    let i ≔ G .inv in
    let L ≔ G .laws in
    (x y ↦ calc
        m (m x (i x)) y = m (G .unit) y by refl ((w ↦ m w y) : S → S) (L .inv_right x)
        = y by L .unit_left y ∎,
     (x y ↦ ag_mul_cancel_inv_right G x y,
      x y z u v ↦
        let c ≔ m x (i y) in
        calc
          m (m (m c z) (i u)) v = m (m c (m z (i u))) v
            by refl ((w ↦ m w v) : S → S) (inverse S (m c (m z (i u))) (m (m c z) (i u)) (L .assoc c z (i u)))
          = m c (m (m z (i u)) v)
            by inverse S (m c (m (m z (i u)) v)) (m (m c (m z (i u))) v) (L .assoc c (m z (i u)) v) ∎))

{` Pointed ternary sets satisfying the heap equations give abstract groups:
   unit e, x · y ≔ t(x, e, y), x⁻¹ ≔ t(e, x, e). `}
def PointedHeapLaws (X : PointedTernarySets) : Type ≔ HeapEquations (X .fst .fst .fst) (X .fst .snd)

def pointed_heap_laws_prop (X : PointedTernarySets) : isProp (PointedHeapLaws X)
  ≔ heap_equations_prop (X .fst .fst .fst) (X .fst .fst .snd) (X .fst .snd)

def PointedHeaps : Type ≔ Σ PointedTernarySets PointedHeapLaws

def pointed_heap_mul (X : PointedTernarySets) (x y : X .fst .fst .fst) : X .fst .fst .fst
  ≔ X .fst .snd (x, (X .snd, y))

def pointed_heap_inv (X : PointedTernarySets) (x : X .fst .fst .fst) : X .fst .fst .fst
  ≔ X .fst .snd (X .snd, (x, X .snd))

def pointed_heap_group_laws (X : PointedTernarySets) (h : PointedHeapLaws X)
  : AbstractGroupLaws (X .fst .fst .fst) (X .snd) (pointed_heap_mul X) (pointed_heap_inv X)
  ≔ let S ≔ X .fst .fst .fst in
    let t ≔ X .fst .snd in
    let e ≔ X .snd in
    let L1 ≔ h .fst in
    let L2 ≔ h .snd .fst in
    let P ≔ h .snd .snd in
    (carrier_set ≔ X .fst .fst .snd,
     unit_right ≔ x ↦ L2 x e,
     unit_left ≔ x ↦ L1 e x,
     assoc ≔ x y z ↦ inverse S (t (t (x, (e, y)), (e, z))) (t (x, (e, t (y, (e, z))))) (P x e y e z),
     inv_right ≔ x ↦ calc
         t (x, (e, t (e, (x, e)))) = t (t (x, (e, e)), (x, e))
           by inverse S (t (t (x, (e, e)), (x, e))) (t (x, (e, t (e, (x, e))))) (P x e e x e)
         = t (x, (x, e)) by refl ((w ↦ t (w, (x, e))) : S → S) (L2 x e)
         = e by L1 x e ∎)

def pointed_heap_group (X : PointedTernarySets) (h : PointedHeapLaws X) : AbstractGroup
  ≔ (X .fst .fst .fst, X .snd, pointed_heap_mul X, pointed_heap_inv X, pointed_heap_group_laws X h)

def abstract_group_to_pointed_heap (G : AbstractGroup) : PointedHeaps
  ≔ (abstract_group_pointed_ternary G, abstract_group_heap_equations G)

def pointed_heap_to_abstract_group (Y : PointedHeaps) : AbstractGroup ≔ pointed_heap_group (Y .fst) (Y .snd)

{` Round trip on abstract groups: x · e⁻¹ · y = x · y and e · x⁻¹ · e = x⁻¹. `}
def abstract_group_pointed_heap_section (G : AbstractGroup)
  : Id AbstractGroup (pointed_heap_to_abstract_group (abstract_group_to_pointed_heap G)) G
  ≔ let S ≔ G .carrier in
    let m ≔ G .mul in
    let i ≔ G .inv in
    let e ≔ G .unit in
    let L ≔ G .laws in
    let G1 ≔ pointed_heap_to_abstract_group (abstract_group_to_pointed_heap G) in
    let xe : (x : S) → Id S (m x (i e)) x
      ≔ x ↦ concat S (m x (i e)) (m x e) x (refl (m x) (ag_inv_unit G)) (L .unit_right x) in
    abstract_group_path_of_data G1 G
      (refl S,
       (refl e,
        (funext S (_ ↦ S → S) (G1 .mul) m
           (x ↦ funext S (_ ↦ S) (G1 .mul x) (m x) (y ↦ refl ((w ↦ m w y) : S → S) (xe x))),
         funext S (_ ↦ S) (G1 .inv) i
           (x ↦ concat S (m (m e (i x)) e) (m e (i x)) (i x) (L .unit_right (m e (i x))) (L .unit_left (i x))))))

{` Round trip on pointed heaps: t is recovered as x · y⁻¹ · z. `}
def pointed_heap_ternary_recover (X : PointedTernarySets) (h : PointedHeapLaws X)
  : Id (Ternary (X .fst .fst .fst)) (abstract_group_ternary (pointed_heap_group X h)) (X .fst .snd)
  ≔ let S ≔ X .fst .fst .fst in
    let t ≔ X .fst .snd in
    let e ≔ X .snd in
    let L1 ≔ h .fst in
    let L2 ≔ h .snd .fst in
    let P ≔ h .snd .snd in
    funext (Product S (Product S S)) (_ ↦ S) (abstract_group_ternary (pointed_heap_group X h)) t
      (u ↦
        let x ≔ u .fst in
        let y ≔ u .snd .fst in
        let z ≔ u .snd .snd in
        calc
          t (t (x, (e, t (e, (y, e)))), (e, z)) = t (x, (e, t (t (e, (y, e)), (e, z))))
            by P x e (t (e, (y, e))) e z
          = t (x, (e, t (e, (y, t (e, (e, z))))))
            by refl ((w ↦ t (x, (e, w))) : S → S) (P e y e e z)
          = t (x, (e, t (e, (y, z))))
            by refl ((w ↦ t (x, (e, t (e, (y, w))))) : S → S) (L1 e z)
          = t (t (x, (e, e)), (y, z))
            by inverse S (t (t (x, (e, e)), (y, z))) (t (x, (e, t (e, (y, z))))) (P x e e y z)
          = t (x, (y, z)) by refl ((w ↦ t (w, (y, z))) : S → S) (L2 x e) ∎)

def pointed_heap_abstract_group_section (Y : PointedHeaps)
  : Id PointedHeaps (abstract_group_to_pointed_heap (pointed_heap_to_abstract_group Y)) Y
  ≔ let X ≔ Y .fst in
    subtype_equal PointedTernarySets PointedHeapLaws pointed_heap_laws_prop
      (abstract_group_to_pointed_heap (pointed_heap_to_abstract_group Y)) Y
      ((refl (X .fst .fst), pointed_heap_ternary_recover X (Y .snd)), refl (X .snd))

{` Abstract groups are the same as pointed heaps (pointed ternary sets
   satisfying the heap equations). `}
def abstract_group_pointed_heap_equiv : Equiv AbstractGroup PointedHeaps
  ≔ quasi_inverse_equiv AbstractGroup PointedHeaps abstract_group_to_pointed_heap pointed_heap_to_abstract_group
      abstract_group_pointed_heap_section pointed_heap_abstract_group_section

{` Hence the fiber of G ↦ (G, x y⁻¹ z, e) over a pointed ternary set X is
   the proposition "X satisfies the heap equations". `}
def abstract_group_pointed_fiber_equiv (X : PointedTernarySets)
  : Equiv (BookFiber AbstractGroup PointedTernarySets abstract_group_pointed_ternary X) (PointedHeapLaws X)
  ≔ compose_equiv (BookFiber AbstractGroup PointedTernarySets abstract_group_pointed_ternary X)
      (BookFiber PointedHeaps PointedTernarySets (Y ↦ Y .fst) X) (PointedHeapLaws X)
      (preequivalence_fiber_equiv AbstractGroup PointedHeaps PointedTernarySets abstract_group_pointed_heap_equiv
        (Y ↦ Y .fst) X)
      (iff_equiv (BookFiber PointedHeaps PointedTernarySets (Y ↦ Y .fst) X) (PointedHeapLaws X)
        (subtype_embedding PointedTernarySets PointedHeapLaws pointed_heap_laws_prop X)
        (pointed_heap_laws_prop X)
        (w ↦ transport PointedTernarySets PointedHeapLaws (w .fst .fst) X
          (inverse PointedTernarySets X (w .fst .fst) (w .snd)) (w .fst .snd))
        (h ↦ ((X, h), refl X)))

{` Fibers of a map of total spaces (g, id) : Σ A (P ∘ g) → Σ B P over (b, u)
   are the fibers of g over b. `}
def heap_pathover_codomain_contractible (B : Type) (P : B → Type) (b c : B) (β : Id B b c) (u : P b)
  : isContr (Σ (P c) (q ↦ Id P β u q))
  ≔ J B b (c β ↦ isContr (Σ (P c) (q ↦ Id P β u q))) (iscontr_idfrom (P b) u) c β

def total_map_fiber_equiv (A B : Type) (P : B → Type) (g : A → B) (b : B) (u : P b)
  : Equiv (BookFiber (Σ A (a ↦ P (g a))) (Σ B P) (v ↦ (g (v .fst), v .snd)) (b, u)) (BookFiber A B g b)
  ≔ let F ≔ BookFiber (Σ A (a ↦ P (g a))) (Σ B P) (v ↦ (g (v .fst), v .snd)) (b, u) in
    let W ≔ BookFiber A B g b in
    let C : W → Type ≔ w ↦ Σ (P (g (w .fst))) (q ↦ Id P (w .snd) u q) in
    compose_equiv F (Σ W C) W
      (quasi_inverse_equiv F (Σ W C)
        (z ↦ ((z .fst .fst, z .snd .fst), (z .fst .snd, z .snd .snd)))
        (z ↦ ((z .fst .fst, z .snd .fst), (z .fst .snd, z .snd .snd)))
        (z ↦ refl z) (z ↦ refl z))
      (contractible_fiber_projection W C
        (w ↦ heap_pathover_codomain_contractible B P b (g (w .fst)) (w .snd) u))

{` For heaps: the fiber of (H, p) ↦ (USym H, p q⁻¹ r, p) over ((S, t), s) is
   the fiber of H ↦ (USym H, p q⁻¹ r) over (S, t), for every s : S. `}
def heap_pointed_fiber_equiv (X : TernarySets) (s : X .fst .fst)
  : Equiv (BookFiber (Σ Heap heap_usym) PointedTernarySets heap_pointed_structure (X, s))
      (BookFiber Heap TernarySets heap_ternary_structure X)
  ≔ total_map_fiber_equiv Heap TernarySets (Y ↦ Y .fst .fst) heap_ternary_structure X s
