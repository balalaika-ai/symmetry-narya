export "702-abstract-group-identity"
export "721-mere-inverses"

{` Chapter 7 (absgroup.tex), the exercise on Furstenberg groups (line 277).
   A Furstenberg group is a nonempty set S (Mere S) with a ∘ b such that
     (1) (a ∘ c) ∘ (b ∘ c) = a ∘ b for all a, b, c, and
     (2) for all a, c there is (Mere) b with a ∘ b = c.
   Following the hint: a ↦ a ∘ a is weakly constant (if a ∘ c = b then
   b ∘ b = (a ∘ c) ∘ (a ∘ c) = a ∘ a by (1)), so it factors through Mere S
   into the set S (weakly_constant_rec, thm:wconstant-elim, module 39) and
   gives e with a ∘ a = e for all a; then e, a · b ≔ a ∘ (e ∘ b) and
   b⁻¹ ≔ e ∘ b form an abstract group. Conversely a ∘ b ≔ a · b⁻¹.
   The two constructions are inverse, giving an equivalence from
   Furstenberg groups to abstract groups. `}

def FurstenbergLaws (S : Type) (op : S → S → S) : Type ≔ sig (
  carrier_set : isSet S,
  inhabited : Mere S,
  cancel : (a b c : S) → Id S (op (op a c) (op b c)) (op a b),
  solution : (a c : S) → Mere (Σ S (b ↦ Id S (op a b) c)))

def FurstenbergGroup : Type ≔ sig (
  carrier : Type,
  op : carrier → carrier → carrier,
  laws : FurstenbergLaws carrier op)

def furstenberg_laws_prop (S : Type) (op : S → S → S) : isProp (FurstenbergLaws S op)
  ≔ u v ↦ let hS ≔ u .carrier_set in
    (isset_isprop S (u .carrier_set) (v .carrier_set),
     mere_isprop S (u .inhabited) (v .inhabited),
     pi_prop S (a ↦ (b c : S) → Id S (op (op a c) (op b c)) (op a b))
       (a ↦ pi_prop S (b ↦ (c : S) → Id S (op (op a c) (op b c)) (op a b))
         (b ↦ pi_prop S (c ↦ Id S (op (op a c) (op b c)) (op a b))
           (c ↦ hS (op (op a c) (op b c)) (op a b))))
       (u .cancel) (v .cancel),
     pi_prop S (a ↦ (c : S) → Mere (Σ S (b ↦ Id S (op a b) c)))
       (a ↦ pi_prop S (c ↦ Mere (Σ S (b ↦ Id S (op a b) c))) (c ↦ mere_isprop (Σ S (b ↦ Id S (op a b) c))))
       (u .solution) (v .solution))

{` The hint: a ↦ a ∘ a is (weakly) constant. `}
def furstenberg_square_weakly_constant (F : FurstenbergGroup)
  : WeaklyConstant (F .carrier) (F .carrier) (a ↦ F .op a a)
  ≔ let S ≔ F .carrier in let o ≔ F .op in let L ≔ F .laws in
    a b ↦ mere_rec (Σ S (c ↦ Id S (o a c) b)) (Id S (o a a) (o b b)) (L .carrier_set (o a a) (o b b))
      (cq ↦ let c ≔ cq .fst in
        concat S (o a a) (o (o a c) (o a c)) (o b b)
          (inverse S (o (o a c) (o a c)) (o a a) (L .cancel a a c))
          (refl ((x ↦ o x x) : S → S) (cq .snd)))
      (L .solution a b)

{` The unit e: the value of a ↦ a ∘ a, obtained from Mere S. `}
def furstenberg_unit (F : FurstenbergGroup) : F .carrier
  ≔ weakly_constant_rec (F .carrier) (F .carrier) (a ↦ F .op a a) (F .laws .carrier_set)
      (furstenberg_square_weakly_constant F) (F .laws .inhabited)

def furstenberg_square (F : FurstenbergGroup) (a : F .carrier) : Id (F .carrier) (F .op a a) (furstenberg_unit F)
  ≔ inverse (F .carrier) (furstenberg_unit F) (F .op a a)
      (weakly_constant_rec_value (F .carrier) (F .carrier) (a ↦ F .op a a) (F .laws .carrier_set)
        (furstenberg_square_weakly_constant F) (F .laws .inhabited) a)

{` x ∘ e = x: pick c with x ∘ c = x; then x ∘ e = (x ∘ c) ∘ (c ∘ c) = x ∘ c = x. `}
def furstenberg_right_unit (F : FurstenbergGroup) (x : F .carrier) : Id (F .carrier) (F .op x (furstenberg_unit F)) x
  ≔ let S ≔ F .carrier in let o ≔ F .op in let L ≔ F .laws in let e ≔ furstenberg_unit F in
    mere_rec (Σ S (c ↦ Id S (o x c) x)) (Id S (o x e) x) (L .carrier_set (o x e) x)
      (cq ↦ let c ≔ cq .fst in let q ≔ cq .snd in
        calc
          o x e = o (o x c) e by refl ((y ↦ o y e) : S → S) (inverse S (o x c) x q)
          = o (o x c) (o c c) by refl (o (o x c)) (inverse S (o c c) e (furstenberg_square F c))
          = o x c by L .cancel x c c
          = x by q ∎)
      (L .solution x x)

{` e ∘ (b ∘ a) = a ∘ b, and e ∘ (e ∘ a) = a. `}
def furstenberg_swap (F : FurstenbergGroup) (a b : F .carrier)
  : Id (F .carrier) (F .op (furstenberg_unit F) (F .op b a)) (F .op a b)
  ≔ let S ≔ F .carrier in let o ≔ F .op in
    concat S (o (furstenberg_unit F) (o b a)) (o (o a a) (o b a)) (o a b)
      (refl ((y ↦ o y (o b a)) : S → S) (inverse S (o a a) (furstenberg_unit F) (furstenberg_square F a)))
      (F .laws .cancel a b a)

def furstenberg_double_inverse (F : FurstenbergGroup) (a : F .carrier)
  : Id (F .carrier) (F .op (furstenberg_unit F) (F .op (furstenberg_unit F) a)) a
  ≔ concat (F .carrier) (F .op (furstenberg_unit F) (F .op (furstenberg_unit F) a)) (F .op a (furstenberg_unit F)) a
      (furstenberg_swap F a (furstenberg_unit F)) (furstenberg_right_unit F a)

{` (u ∘ b) ∘ (e ∘ b) = u. `}
def furstenberg_cancel_unit (F : FurstenbergGroup) (u b : F .carrier)
  : Id (F .carrier) (F .op (F .op u b) (F .op (furstenberg_unit F) b)) u
  ≔ concat (F .carrier) (F .op (F .op u b) (F .op (furstenberg_unit F) b)) (F .op u (furstenberg_unit F)) u
      (F .laws .cancel u (furstenberg_unit F) b) (furstenberg_right_unit F u)

{` The abstract group of a Furstenberg group. `}
def furstenberg_mul (F : FurstenbergGroup) (a b : F .carrier) : F .carrier
  ≔ F .op a (F .op (furstenberg_unit F) b)

def furstenberg_inv (F : FurstenbergGroup) (b : F .carrier) : F .carrier ≔ F .op (furstenberg_unit F) b

def furstenberg_group_laws (F : FurstenbergGroup)
  : AbstractGroupLaws (F .carrier) (furstenberg_unit F) (furstenberg_mul F) (furstenberg_inv F)
  ≔ let S ≔ F .carrier in let o ≔ F .op in let e ≔ furstenberg_unit F in
    (F .laws .carrier_set,
     a ↦ concat S (o a (o e e)) (o a e) a (refl (o a) (furstenberg_square F e)) (furstenberg_right_unit F a),
     a ↦ furstenberg_double_inverse F a,
     a b c ↦
       calc
         o a (o e (o b (o e c))) = o a (o (o e c) b) by refl (o a) (furstenberg_swap F (o e c) b)
         = o (o a (o e b)) (o (o (o e c) b) (o e b))
           by inverse S (o (o a (o e b)) (o (o (o e c) b) (o e b))) (o a (o (o e c) b))
             (F .laws .cancel a (o (o e c) b) (o e b))
         = o (o a (o e b)) (o e c) by refl (o (o a (o e b))) (furstenberg_cancel_unit F (o e c) b) ∎,
     a ↦ concat S (o a (o e (o e a))) (o a a) e (refl (o a) (furstenberg_double_inverse F a)) (furstenberg_square F a))

def furstenberg_to_abstract (F : FurstenbergGroup) : AbstractGroup
  ≔ (F .carrier, furstenberg_unit F, furstenberg_mul F, furstenberg_inv F, furstenberg_group_laws F)

{` The Furstenberg group of an abstract group: a ∘ b ≔ a · b⁻¹. `}
def abstract_to_furstenberg_op (G : AbstractGroup) (a b : G .carrier) : G .carrier ≔ G .mul a (G .inv b)

def abstract_to_furstenberg_laws (G : AbstractGroup) : FurstenbergLaws (G .carrier) (abstract_to_furstenberg_op G)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let L ≔ G .laws in
    (L .carrier_set,
     mere S (G .unit),
     a b c ↦
       calc
         m (m a (i c)) (i (m b (i c))) = m (m a (i c)) (m (i (i c)) (i b)) by refl (m (m a (i c))) (ag_inv_mul G b (i c))
         = m (m a (i c)) (m c (i b)) by refl ((y ↦ m (m a (i c)) (m y (i b))) : S → S) (ag_inv_inv G c)
         = m a (m (i c) (m c (i b))) by inverse S (m a (m (i c) (m c (i b)))) (m (m a (i c)) (m c (i b))) (L .assoc a (i c) (m c (i b)))
         = m a (i b) by refl (m a) (ag_mul_inv_cancel_left G c (i b)) ∎,
     a c ↦ mere (Σ S (b ↦ Id S (m a (i b)) c))
       (m (i c) a,
        calc
          m a (i (m (i c) a)) = m a (m (i a) (i (i c))) by refl (m a) (ag_inv_mul G (i c) a)
          = m a (m (i a) c) by refl ((y ↦ m a (m (i a) y)) : S → S) (ag_inv_inv G c)
          = c by ag_mul_cancel_inv_left G a c ∎))

def abstract_to_furstenberg (G : AbstractGroup) : FurstenbergGroup
  ≔ (G .carrier, abstract_to_furstenberg_op G, abstract_to_furstenberg_laws G)

{` Identifications of Furstenberg groups from identifications of (S, ∘). `}
def FurstenbergData : Type ≔ Σ Type (S ↦ S → S → S)

def furstenberg_data (F : FurstenbergGroup) : FurstenbergData ≔ (F .carrier, F .op)

def FurstenbergLawsAt (d : FurstenbergData) : Type ≔ FurstenbergLaws (d .fst) (d .snd)

def furstenberg_laws_pathover (d d' : FurstenbergData) (q : Id FurstenbergData d d')
  (l : FurstenbergLawsAt d) (l' : FurstenbergLawsAt d') : Id FurstenbergLawsAt q l l'
  ≔ pathover_hlevel zero. FurstenbergData FurstenbergLawsAt
      (d ↦ prop_to_hlevel_one (FurstenbergLawsAt d) (furstenberg_laws_prop (d .fst) (d .snd)))
      d d' q l l' .center

def furstenberg_path_of_data (F F' : FurstenbergGroup) (q : Id FurstenbergData (furstenberg_data F) (furstenberg_data F'))
  : Id FurstenbergGroup F F'
  ≔ (q .fst, q .snd, furstenberg_laws_pathover (furstenberg_data F) (furstenberg_data F') q (F .laws) (F' .laws))

{` Round trips. Furstenberg → abstract → Furstenberg:
   a · b⁻¹ = a ∘ (e ∘ (e ∘ b)) = a ∘ b. `}
def furstenberg_round_trip (F : FurstenbergGroup) : Id FurstenbergGroup (abstract_to_furstenberg (furstenberg_to_abstract F)) F
  ≔ let S ≔ F .carrier in let o ≔ F .op in
    let F' ≔ abstract_to_furstenberg (furstenberg_to_abstract F) in
    furstenberg_path_of_data F' F
      (refl S,
       funext S (_ ↦ S → S) (F' .op) o
         (a ↦ funext S (_ ↦ S) (F' .op a) (o a) (b ↦ refl (o a) (furstenberg_double_inverse F b))))

{` Abstract → Furstenberg → abstract: the new unit is e · e⁻¹ = e (by
   computation of weakly_constant_rec at mere e), the new product is
   a · (e' · b⁻¹)⁻¹ = a · b and the new inverse e' · b⁻¹ = b⁻¹. `}
def furstenberg_abstract_round_trip (G : AbstractGroup)
  : Id AbstractGroup (furstenberg_to_abstract (abstract_to_furstenberg G)) G
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let i ≔ G .inv in let e ≔ G .unit in let L ≔ G .laws in
    let F ≔ abstract_to_furstenberg G in
    let e' ≔ furstenberg_unit F in
    let pe : Id S e' e ≔ L .inv_right e in
    abstract_group_path_of_data (furstenberg_to_abstract F) G
      (refl S,
       (pe,
        (funext S (_ ↦ S → S) (furstenberg_mul F) m
           (a ↦ funext S (_ ↦ S) (furstenberg_mul F a) (m a)
             (b ↦ calc
                m a (i (m e' (i b))) = m a (i (m e (i b))) by refl ((y ↦ m a (i (m y (i b)))) : S → S) pe
                = m a (i (i b)) by refl ((y ↦ m a (i y)) : S → S) (L .unit_left (i b))
                = m a b by refl (m a) (ag_inv_inv G b) ∎)),
         funext S (_ ↦ S) (furstenberg_inv F) i
           (b ↦ concat S (m e' (i b)) (m e (i b)) (i b)
              (refl ((y ↦ m y (i b)) : S → S) pe) (L .unit_left (i b))))))

{` The exercise: an equivalence from Furstenberg groups to abstract groups. `}
def furstenberg_abstract_equiv : Equiv FurstenbergGroup AbstractGroup
  ≔ quasi_inverse_equiv FurstenbergGroup AbstractGroup furstenberg_to_abstract abstract_to_furstenberg
      furstenberg_round_trip furstenberg_abstract_round_trip

{` Litmus: for the integers a ∘ b = a − b; 5 ∘ 2 = 3, e = 0, and the
   recovered product is addition (2 · 3 = 5), all by computation. The
   unit does not depend on the chosen inhabitant: with Mere S witnessed
   by 7 instead of 0, e is still 7 ∘ 7 = 0. `}
def furstenberg_int : FurstenbergGroup ≔ abstract_to_furstenberg int_add_abstract_group

def furstenberg_int_op_litmus
  : Id Int (furstenberg_int .op (pos. (suc. (suc. (suc. (suc. (suc. zero.)))))) (pos. (suc. (suc. zero.))))
      (pos. (suc. (suc. (suc. zero.))))
  ≔ refl (pos. (suc. (suc. (suc. zero.))) : Int)

def furstenberg_int_unit_litmus : Id Int (furstenberg_unit furstenberg_int) int_zero ≔ refl int_zero

def furstenberg_int_mul_litmus
  : Id Int (furstenberg_to_abstract furstenberg_int .mul (pos. (suc. (suc. zero.))) (pos. (suc. (suc. (suc. zero.)))))
      (pos. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ refl (pos. (suc. (suc. (suc. (suc. (suc. zero.))))) : Int)

def furstenberg_int_seven : FurstenbergGroup
  ≔ (Int, furstenberg_int .op,
     (int_set, mere Int (pos. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))),
      furstenberg_int .laws .cancel, furstenberg_int .laws .solution))

def furstenberg_int_seven_unit_litmus : Id Int (furstenberg_unit furstenberg_int_seven) int_zero ≔ refl int_zero
