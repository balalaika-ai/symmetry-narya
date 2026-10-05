export "702-abstract-group-identity"
export "721-mere-inverses"

{` Chapter 7 (absgroup.tex), xca:cheapgroup. A sheargroup is a set S with
   e : S and a * b, satisfying, with ā ≔ a * e,
     (1) e * a = a,  (2) a * a = e,  (3) c * (b * a) = (c * b̄)‾ * a.
   The hint is correct as printed: a · b ≔ b̄ * a (and a⁻¹ ≔ ā) gives an
   abstract group, a * b ≔ b · a⁻¹ goes back, and ē = e, ā̄ = a are the
   intermediate steps. The result is an equivalence from abstract groups
   to sheargroups. `}

def ShearGroupLaws (S : Type) (e : S) (op : S → S → S) : Type ≔ sig (
  carrier_set : isSet S,
  unit_left : (a : S) → Id S (op e a) a,
  self_inverse : (a : S) → Id S (op a a) e,
  shear : (a b c : S) → Id S (op c (op b a)) (op (op (op c (op b e)) e) a))

def ShearGroup : Type ≔ sig (
  carrier : Type,
  unit : carrier,
  op : carrier → carrier → carrier,
  laws : ShearGroupLaws carrier unit op)

def shear_group_laws_prop (S : Type) (e : S) (op : S → S → S) : isProp (ShearGroupLaws S e op)
  ≔ u v ↦ let hS ≔ u .carrier_set in
    (isset_isprop S (u .carrier_set) (v .carrier_set),
     pi_prop S (a ↦ Id S (op e a) a) (a ↦ hS (op e a) a) (u .unit_left) (v .unit_left),
     pi_prop S (a ↦ Id S (op a a) e) (a ↦ hS (op a a) e) (u .self_inverse) (v .self_inverse),
     pi_prop S (a ↦ (b c : S) → Id S (op c (op b a)) (op (op (op c (op b e)) e) a))
       (a ↦ pi_prop S (b ↦ (c : S) → Id S (op c (op b a)) (op (op (op c (op b e)) e) a))
         (b ↦ pi_prop S (c ↦ Id S (op c (op b a)) (op (op (op c (op b e)) e) a))
           (c ↦ hS (op c (op b a)) (op (op (op c (op b e)) e) a))))
       (u .shear) (v .shear))

{` The bar operation ā ≔ a * e; ē = e and ā̄ = a (the hint: c ≔ ā, b ≔ a
   in (3)). `}
def shear_bar (X : ShearGroup) (a : X .carrier) : X .carrier ≔ X .op a (X .unit)

def shear_bar_unit (X : ShearGroup) : Id (X .carrier) (shear_bar X (X .unit)) (X .unit)
  ≔ X .laws .self_inverse (X .unit)

def shear_bar_bar (X : ShearGroup) (a : X .carrier) : Id (X .carrier) (shear_bar X (shear_bar X a)) a
  ≔ let S ≔ X .carrier in let o ≔ X .op in let e ≔ X .unit in let L ≔ X .laws in
    let ab ≔ o a e in
    calc
      o ab e = o ab (o a a) by refl (o ab) (inverse S (o a a) e (L .self_inverse a))
      = o (o (o ab ab) e) a by L .shear a a ab
      = o (o e e) a by refl ((x ↦ o (o x e) a) : S → S) (L .self_inverse ab)
      = o e a by refl ((x ↦ o x a) : S → S) (shear_bar_unit X)
      = a by L .unit_left a ∎

{` From a sheargroup to an abstract group: a · b ≔ b̄ * a, a⁻¹ ≔ ā. `}
def shear_to_abstract_mul (X : ShearGroup) (a b : X .carrier) : X .carrier ≔ X .op (shear_bar X b) a

def shear_to_abstract_laws (X : ShearGroup)
  : AbstractGroupLaws (X .carrier) (X .unit) (shear_to_abstract_mul X) (shear_bar X)
  ≔ let S ≔ X .carrier in let o ≔ X .op in let e ≔ X .unit in let L ≔ X .laws in
    (L .carrier_set,
     a ↦ concat S (o (o e e) a) (o e a) a (refl ((x ↦ o x a) : S → S) (shear_bar_unit X)) (L .unit_left a),
     a ↦ shear_bar_bar X a,
     a b c ↦
       let cb ≔ o c e in let bb ≔ o b e in
       calc
         o (o (o cb b) e) a = o (o (o cb (o bb e)) e) a
           by refl ((x ↦ o (o (o cb x) e) a) : S → S) (inverse S (o bb e) b (shear_bar_bar X b))
         = o cb (o bb a) by inverse S (o cb (o bb a)) (o (o (o cb (o bb e)) e) a) (L .shear a bb cb) ∎,
     a ↦ concat S (o (o (o a e) e) a) (o a a) e
       (refl ((x ↦ o x a) : S → S) (shear_bar_bar X a)) (L .self_inverse a))

def shear_to_abstract (X : ShearGroup) : AbstractGroup
  ≔ (X .carrier, X .unit, shear_to_abstract_mul X, shear_bar X, shear_to_abstract_laws X)

{` From an abstract group to a sheargroup: a * b ≔ b · a⁻¹. `}
def abstract_to_shear_op (G : AbstractGroup) (a b : G .carrier) : G .carrier ≔ G .mul b (G .inv a)

{` (e · X⁻¹)⁻¹ = X. `}
def shear_inv_unit_inv (G : AbstractGroup) (x : G .carrier)
  : Id (G .carrier) (G .inv (G .mul (G .unit) (G .inv x))) x
  ≔ concat (G .carrier) (G .inv (G .mul (G .unit) (G .inv x))) (G .inv (G .inv x)) x
      (refl (G .inv) (G .laws .unit_left (G .inv x))) (ag_inv_inv G x)

def abstract_to_shear_laws (G : AbstractGroup)
  : ShearGroupLaws (G .carrier) (G .unit) (abstract_to_shear_op G)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let e ≔ G .unit in let L ≔ G .laws in
    (L .carrier_set,
     a ↦ concat S (m a (i e)) (m a e) a (refl (m a) (ag_inv_unit G)) (L .unit_right a),
     a ↦ L .inv_right a,
     a b c ↦
       inverse S (m a (i (m e (i (m (m e (i b)) (i c)))))) (m (m a (i b)) (i c))
         (calc
            m a (i (m e (i (m (m e (i b)) (i c))))) = m a (m (m e (i b)) (i c))
              by refl (m a) (shear_inv_unit_inv G (m (m e (i b)) (i c)))
            = m a (m (i b) (i c)) by refl ((y ↦ m a (m y (i c))) : S → S) (L .unit_left (i b))
            = m (m a (i b)) (i c) by L .assoc a (i b) (i c) ∎))

def abstract_to_shear (G : AbstractGroup) : ShearGroup
  ≔ (G .carrier, G .unit, abstract_to_shear_op G, abstract_to_shear_laws G)

{` Identifications of sheargroups from identifications of the data. `}
def ShearGroupData : Type ≔ Σ Type (S ↦ Σ S (e ↦ S → S → S))

def shear_group_data (X : ShearGroup) : ShearGroupData ≔ (X .carrier, (X .unit, X .op))

def ShearGroupLawsAt (d : ShearGroupData) : Type ≔ ShearGroupLaws (d .fst) (d .snd .fst) (d .snd .snd)

def shear_group_laws_pathover (d d' : ShearGroupData) (q : Id ShearGroupData d d')
  (l : ShearGroupLawsAt d) (l' : ShearGroupLawsAt d') : Id ShearGroupLawsAt q l l'
  ≔ pathover_hlevel zero. ShearGroupData ShearGroupLawsAt
      (d ↦ prop_to_hlevel_one (ShearGroupLawsAt d) (shear_group_laws_prop (d .fst) (d .snd .fst) (d .snd .snd)))
      d d' q l l' .center

def shear_group_path_of_data (X Y : ShearGroup) (q : Id ShearGroupData (shear_group_data X) (shear_group_data Y))
  : Id ShearGroup X Y
  ≔ (q .fst, q .snd .fst, q .snd .snd,
     shear_group_laws_pathover (shear_group_data X) (shear_group_data Y) q (X .laws) (Y .laws))

{` Round trips. Abstract group → sheargroup → abstract group: the
   product is a · (e · b⁻¹)⁻¹ = a · b and the inverse e · a⁻¹ = a⁻¹. `}
def shear_abstract_round_trip (G : AbstractGroup) : Id AbstractGroup (shear_to_abstract (abstract_to_shear G)) G
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let e ≔ G .unit in
    let G' ≔ shear_to_abstract (abstract_to_shear G) in
    abstract_group_path_of_data G' G
      (refl S, (refl e,
        (funext S (_ ↦ S → S) (G' .mul) m
           (a ↦ funext S (_ ↦ S) (G' .mul a) (m a) (b ↦ refl (m a) (shear_inv_unit_inv G b))),
         funext S (_ ↦ S) (G' .inv) i (a ↦ G .laws .unit_left (i a)))))

{` Sheargroup → abstract group → sheargroup: b · ā = ā̄ * b = a * b. `}
def shear_shear_round_trip (X : ShearGroup) : Id ShearGroup (abstract_to_shear (shear_to_abstract X)) X
  ≔ let S ≔ X .carrier in let o ≔ X .op in
    let X' ≔ abstract_to_shear (shear_to_abstract X) in
    shear_group_path_of_data X' X
      (refl S, (refl (X .unit),
        funext S (_ ↦ S → S) (X' .op) o
          (a ↦ funext S (_ ↦ S) (X' .op a) (o a) (b ↦ refl ((x ↦ o x b) : S → S) (shear_bar_bar X a)))))

{` xca:cheapgroup: an equivalence from abstract groups to sheargroups. `}
def abstract_shear_equiv : Equiv AbstractGroup ShearGroup
  ≔ quasi_inverse_equiv AbstractGroup ShearGroup abstract_to_shear shear_to_abstract
      shear_abstract_round_trip shear_shear_round_trip

{` Litmus: in the integers a * b = b − a, e.g. 2 * 5 = 3; the product
   recovered from the sheargroup is addition, 2 · 3 = 5, by computation. `}
def shear_int_litmus
  : Id Int (abstract_to_shear int_add_abstract_group .op (pos. (suc. (suc. zero.))) (pos. (suc. (suc. (suc. (suc. (suc. zero.)))))))
      (pos. (suc. (suc. (suc. zero.))))
  ≔ refl (pos. (suc. (suc. (suc. zero.))) : Int)

def shear_int_mul_litmus
  : Id Int (shear_to_abstract (abstract_to_shear int_add_abstract_group) .mul (pos. (suc. (suc. zero.))) (pos. (suc. (suc. (suc. zero.)))))
      (pos. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ refl (pos. (suc. (suc. (suc. (suc. (suc. zero.))))) : Int)
