export "700-monoids-and-group-laws"

{` Chapter 7 (absgroup.tex), rem:inverses-as-property and
   lem:group-inv-operation (with the footnote of its proof), and the book
   orientation e = g⁻¹ · g of xca:left-inv-involution.

   axiom:mere-inverse says: for all g : S there exists h : S with
   e = g · h. "There exists" is the propositional truncation Mere. The
   fiber μ(g)⁻¹(e) of the proof is BookFiber S S (mul g) e = Σ h, e = g · h
   (book orientation of fibers), so the axiom is
   (g : S) → Mere (BookFiber S S (mul g) e).

   Throughout, l : MonoidLaws S e mul (module 700: isSet S, the unit laws
   and the associativity law) and mi : MereInverses S e mul. `}

def MereInverses (S : Type) (e : S) (mul : S → S → S) : Type
  ≔ (g : S) → Mere (BookFiber S S (mul g) e)

def mere_inverses_prop (S : Type) (e : S) (mul : S → S → S) : isProp (MereInverses S e mul)
  ≔ pi_prop S (g ↦ Mere (BookFiber S S (mul g) e)) (g ↦ mere_isprop (BookFiber S S (mul g) e))

{` The proof of lem:group-inv-operation, first step: a right inverse h of
   g is also a left inverse. Take a mere k with e = h · k; then
   k = e·k = (g·h)·k = g·(h·k) = g·e = g, hence h · g = h · k = e. `}
def mere_inverse_left (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  (g h : S) (p : Id S (mul g h) e) : Id S (mul h g) e
  ≔ mere_rec (BookFiber S S (mul h) e) (Id S (mul h g) e) (l .fst (mul h g) e)
      (kq ↦
        let k ≔ kq .fst in
        let q ≔ kq .snd in
        let r : Id S k g
          ≔ calc
              k = mul e k by inverse S (mul e k) k (l .snd .fst k .snd)
              = mul (mul g h) k by refl ((x ↦ mul x k) : S → S) (inverse S (mul g h) e p)
              = mul g (mul h k) by inverse S (mul g (mul h k)) (mul (mul g h) k) (l .snd .snd g h k)
              = mul g e by refl (mul g) (inverse S e (mul h k) q)
              = g by l .snd .fst g .fst ∎ in
        calc
          mul h g = mul h k by refl (mul h) (inverse S k g r)
          = e by inverse S e (mul h k) q ∎)
      (mi h)

{` Second step: right inverses are unique,
   h = h·e = h·(g·h') = (h·g)·h' = e·h' = h'. `}
def mere_inverse_unique (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  (g h h' : S) (p : Id S (mul g h) e) (p' : Id S (mul g h') e) : Id S h h'
  ≔ calc
      h = mul h e by inverse S (mul h e) h (l .snd .fst h .fst)
      = mul h (mul g h') by refl (mul h) (inverse S (mul g h') e p')
      = mul (mul h g) h' by l .snd .snd h g h'
      = mul e h' by refl ((x ↦ mul x h') : S → S) (mere_inverse_left S e mul l mi g h p)
      = h' by l .snd .fst h' .snd ∎

def mere_inverse_fiber_prop (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  (g : S) : isProp (BookFiber S S (mul g) e)
  ≔ u v ↦ subtype_equal S (h ↦ Id S e (mul g h)) (h ↦ l .fst e (mul g h)) u v
      (mere_inverse_unique S e mul l mi g (u .fst) (v .fst)
        (inverse S e (mul g (u .fst)) (u .snd)) (inverse S e (mul g (v .fst)) (v .snd)))

{` The claim of the proof: the fiber μ(g)⁻¹(e) is contractible. `}
def mere_inverse_fiber_contractible (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul)
  (mi : MereInverses S e mul) (g : S) : BookIsContr (BookFiber S S (mul g) e)
  ≔ mere_rec (BookFiber S S (mul g) e) (BookIsContr (BookFiber S S (mul g) e))
      (book_iscontr_isprop (BookFiber S S (mul g) e))
      (u ↦ (u, v ↦ mere_inverse_fiber_prop S e mul l mi g u v)) (mi g)

{` g⁻¹ is the center of the contraction. `}
def mere_inverse_function (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  : S → S
  ≔ g ↦ mere_inverse_fiber_contractible S e mul l mi g .center .fst

def mere_inverse_law (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  : InverseLaw S e mul (mere_inverse_function S e mul l mi)
  ≔ g ↦ inverse S e (mul g (mere_inverse_function S e mul l mi g))
      (mere_inverse_fiber_contractible S e mul l mi g .center .snd)

def inverse_law_prop (S : Type) (e : S) (mul : S → S → S) (hS : isSet S) (inv : S → S)
  : isProp (InverseLaw S e mul inv)
  ≔ pi_prop S (g ↦ Id S (mul g (inv g)) e) (g ↦ hS (mul g (inv g)) e)

{` lem:group-inv-operation: there is a unique inverse function with the
   law of inverses, i.e. Σ (ι : S → S) InverseLaw(S, e, μ, ι) is
   contractible. `}
def group_inv_operation_contractible (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul)
  (mi : MereInverses S e mul) : BookIsContr (Σ (S → S) (InverseLaw S e mul))
  ≔ let inv ≔ mere_inverse_function S e mul l mi in
    let law ≔ mere_inverse_law S e mul l mi in
    ((inv, law),
     u ↦ subtype_equal (S → S) (InverseLaw S e mul) (inverse_law_prop S e mul (l .fst)) (inv, law) u
       (funext S (_ ↦ S) inv (u .fst)
         (g ↦ mere_inverse_unique S e mul l mi g (inv g) (u .fst g) (law g) (u .snd g))))

{` The footnote of the proof: g⁻¹ · g = e and (g⁻¹)⁻¹ = g. `}
def mere_inverse_left_law (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  (g : S) : Id S (mul (mere_inverse_function S e mul l mi g) g) e
  ≔ mere_inverse_left S e mul l mi g (mere_inverse_function S e mul l mi g) (mere_inverse_law S e mul l mi g)

def mere_inverse_involution (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul) (mi : MereInverses S e mul)
  (g : S) : Id S (mere_inverse_function S e mul l mi (mere_inverse_function S e mul l mi g)) g
  ≔ let inv ≔ mere_inverse_function S e mul l mi in
    mere_inverse_unique S e mul l mi (inv g) (inv (inv g)) g (mere_inverse_law S e mul l mi (inv g))
      (mere_inverse_left_law S e mul l mi g)

{` The abstract group obtained from a monoid with mere inverses. `}
def mere_inverse_abstract_group (S : Type) (e : S) (mul : S → S → S) (l : MonoidLaws S e mul)
  (mi : MereInverses S e mul) : AbstractGroup
  ≔ (S, e, mul, mere_inverse_function S e mul l mi,
     group_laws_to_record S e mul (mere_inverse_function S e mul l mi) (l, mere_inverse_law S e mul l mi))

{` rem:inverses-as-property: positing the inverse operation (with the law
   of inverses) and positing axiom:mere-inverse give equivalent notions:
   the type of abstract groups is equivalent to the type of monoids with
   mere inverses. `}
def inverse_operation_mere_inverses (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  (law : InverseLaw S e mul inv) : MereInverses S e mul
  ≔ g ↦ mere (BookFiber S S (mul g) e) (inv g, inverse S (mul g (inv g)) e (law g))

def MonoidInverseOperation (M : Monoid) : Type
  ≔ Σ (M .carrier → M .carrier) (InverseLaw (M .carrier) (M .unit) (M .mul))

def MonoidMereInverses (M : Monoid) : Type ≔ MereInverses (M .carrier) (M .unit) (M .mul)

def monoid_inverse_operation_prop (M : Monoid) : isProp (MonoidInverseOperation M)
  ≔ u v ↦
    let S ≔ M .carrier in
    let c ≔ group_inv_operation_contractible S (M .unit) (M .mul) (M .laws)
      (inverse_operation_mere_inverses S (M .unit) (M .mul) (u .fst) (u .snd)) in
    concat (MonoidInverseOperation M) u (c .center) v
      (inverse (MonoidInverseOperation M) (c .center) u (c .contract u)) (c .contract v)

def monoid_inverse_operation_mere_equiv (M : Monoid) : Equiv (MonoidInverseOperation M) (MonoidMereInverses M)
  ≔ let S ≔ M .carrier in
    iff_equiv (MonoidInverseOperation M) (MonoidMereInverses M) (monoid_inverse_operation_prop M)
      (mere_inverses_prop S (M .unit) (M .mul))
      (u ↦ inverse_operation_mere_inverses S (M .unit) (M .mul) (u .fst) (u .snd))
      (mi ↦ group_inv_operation_contractible S (M .unit) (M .mul) (M .laws) mi .center)

def abstract_group_to_monoid_inverse (G : AbstractGroup) : Σ Monoid MonoidInverseOperation
  ≔ (abstract_group_monoid G, (G .inv, G .laws .inv_right))

def abstract_group_from_monoid_inverse (t : Σ Monoid MonoidInverseOperation) : AbstractGroup
  ≔ let M ≔ t .fst in
    (M .carrier, M .unit, M .mul, t .snd .fst,
     group_laws_to_record (M .carrier) (M .unit) (M .mul) (t .snd .fst) (M .laws, t .snd .snd))

def abstract_group_monoid_inverse_equiv : Equiv AbstractGroup (Σ Monoid MonoidInverseOperation)
  ≔ quasi_inverse_equiv AbstractGroup (Σ Monoid MonoidInverseOperation)
      abstract_group_to_monoid_inverse abstract_group_from_monoid_inverse (G ↦ refl G) (t ↦ refl t)

def abstract_group_mere_inverses_equiv : Equiv AbstractGroup (Σ Monoid MonoidMereInverses)
  ≔ compose_equiv AbstractGroup (Σ Monoid MonoidInverseOperation) (Σ Monoid MonoidMereInverses)
      abstract_group_monoid_inverse_equiv
      (family_equiv Monoid MonoidInverseOperation MonoidMereInverses monoid_inverse_operation_mere_equiv)

{` xca:left-inv-involution in the printed orientation e = g⁻¹ · g (the
   second half, g = (g⁻¹)⁻¹, is ag_inv_involution of module 700). `}
def ag_inv_left_book (G : AbstractGroup) (g : G .carrier) : Id (G .carrier) (G .unit) (G .mul (G .inv g) g)
  ≔ inverse (G .carrier) (G .mul (G .inv g) g) (G .unit) (ag_inv_left G g)

{` Litmus: the integers under addition form an abstract group. `}
def int_add_abstract_group_laws : AbstractGroupLaws Int int_zero int_add int_neg
  ≔ (int_set, int_add_zero_right, int_add_zero_left,
     x y z ↦ inverse Int (int_add (int_add x y) z) (int_add x (int_add y z)) (int_add_assoc x y z),
     int_add_neg_right)

def int_add_abstract_group : AbstractGroup ≔ (Int, int_zero, int_add, int_neg, int_add_abstract_group_laws)

def int_add_monoid_laws : MonoidLaws Int int_zero int_add ≔ abstract_group_monoid int_add_abstract_group .laws

def int_add_mere_inverses : MereInverses Int int_zero int_add
  ≔ inverse_operation_mere_inverses Int int_zero int_add int_neg int_add_neg_right

{` Litmus: the inverse function obtained from mere inverses sends 1 to −1
   (neg. 0 is −1), by computation. `}
def mere_inverse_int_litmus
  : Id Int (mere_inverse_function Int int_zero int_add int_add_monoid_laws int_add_mere_inverses (pos. (suc. zero.)))
      (neg. zero.)
  ≔ refl (neg. zero. : Int)

{` Litmus: in the integers −3 + 3 = 0 (the left inverse law of the
   footnote) and −(−2) = 2 (the involution), both by the general lemmas. `}
def mere_inverse_int_left_litmus
  : Id Int (int_add (mere_inverse_function Int int_zero int_add int_add_monoid_laws int_add_mere_inverses
      (pos. (suc. (suc. (suc. zero.))))) (pos. (suc. (suc. (suc. zero.))))) int_zero
  ≔ mere_inverse_left_law Int int_zero int_add int_add_monoid_laws int_add_mere_inverses (pos. (suc. (suc. (suc. zero.))))
