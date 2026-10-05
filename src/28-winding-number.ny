export "27-circle-encode-decode"

{` Specialization to the family already constructed by circle recursion.
   No monodromy or encode/decode law is assumed at this point. `}
def circle_paths_integer_family_equiv (C : CircleSignature) (z : C .carrier)
  : Equiv (Id (C .carrier) (C .base) z) (circle_integer_family C z)
  ≔ circle_path_code_equiv C (circle_integer_family C) (circle_integer_monodromy C) z

def circle_winding (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base)) : Int
  ≔ equiv_inverse_map Int (circle_integer_family C (C .base))
      (circle_integer_monodromy C .enumeration)
      (code_encode C (circle_integer_family C) (circle_integer_monodromy C) (C .base) p)

{` The winding map agrees with transport of the chosen zero, followed
   by the base identification supplied by circle recursion. `}
def circle_winding_is_transport (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C p)
      (circle_integer_trivialization C
        (code_encode C (circle_integer_family C) (circle_integer_monodromy C) (C .base) p))
  ≔ let x ≔ code_encode C (circle_integer_family C) (circle_integer_monodromy C) (C .base) p in
    calc
      circle_winding C p
      = circle_integer_trivialization C (circle_integer_monodromy C .enumeration .map (circle_winding C p))
        by circle_integer_trivialization_enumeration C (circle_winding C p)
      = circle_integer_trivialization C x
        by refl (circle_integer_trivialization C)
          (equiv_counit Int (circle_integer_family C (C .base)) (circle_integer_monodromy C .enumeration) x) ∎

def circle_winding_power (C : CircleSignature) (n : Int)
  : Id Int (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) n)) n
  ≔ let R ≔ circle_integer_family C in
    let m ≔ circle_integer_monodromy C in
    let g ≔ equiv_inverse_map Int (R (C .base)) (m .enumeration) in
    concat Int (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) n))
      (g (m .enumeration .map n)) n
      (refl g (code_encode_power C R m n)) (equiv_retraction Int (R (C .base)) (m .enumeration) n)

def circle_power_winding (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base))
      (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)) p
  ≔ let R ≔ circle_integer_family C in
    let m ≔ circle_integer_monodromy C in
    calc
      loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)
      = code_decode C R m (C .base) (code_encode C R m (C .base) p)
        by code_decode_beta C R m (refl (code_encode C R m (C .base) p))
      = p by code_decode_encode C R m (C .base) p ∎

{` cor:S1groupoid and def:windingnumber: both displayed equivalences,
   with the actual power and winding maps. Conditional on CircleSignature. `}
def circle_integer_loop_equiv (C : CircleSignature)
  : BookEquiv Int (Id (C .carrier) (C .base) (C .base))
  ≔ book_quasi_inverse_equiv Int (Id (C .carrier) (C .base) (C .base))
      (loop_power (C .carrier) (C .base) (C .loop)) (circle_winding C)
      (circle_winding_power C) (circle_power_winding C)

def circle_loop_integer_equiv (C : CircleSignature)
  : BookEquiv (Id (C .carrier) (C .base) (C .base)) Int
  ≔ book_quasi_inverse_equiv (Id (C .carrier) (C .base) (C .base)) Int
      (circle_winding C) (loop_power (C .carrier) (C .base) (C .loop))
      (circle_power_winding C) (circle_winding_power C)

def circle_based_paths_set (C : CircleSignature) (z : C .carrier)
  : isSet (Id (C .carrier) (C .base) z)
  ≔ hlevel_two_to_set (Id (C .carrier) (C .base) z)
      (hlevel_equiv (suc. (suc. zero.)) (circle_integer_family C z) (Id (C .carrier) (C .base) z)
        (canonical_inverse_equiv (Id (C .carrier) (C .base) z) (circle_integer_family C z)
          (circle_paths_integer_family_equiv C z))
        (set_to_hlevel_two (circle_integer_family C z)
          (code_is_set C (circle_integer_family C) (circle_integer_monodromy C) z)))

def circle_groupoid (C : CircleSignature) : isGroupoid (C .carrier)
  ≔ circle_ind_prop C (x ↦ (y : C .carrier) → isSet (Id (C .carrier) x y))
      (x ↦ pi_prop (C .carrier) (y ↦ isSet (Id (C .carrier) x y))
        (y ↦ isset_isprop (Id (C .carrier) x y)))
      (circle_based_paths_set C)

def circle_integer_cover (C : CircleSignature) : Coverings (C .carrier)
  ≔ let c ≔ setfamily_to_covering (C .carrier)
      (z ↦ (circle_integer_family C z, code_is_set C (circle_integer_family C) (circle_integer_monodromy C) z)) in
    (c .fst .fst, (c .fst .snd, c .snd))

def circle_integer_total_contractible (C : CircleSignature)
  : BookIsContr (Σ (C .carrier) (circle_integer_family C))
  ≔ book_contraction (Σ (C .carrier) (circle_integer_family C))
      (hlevel_equiv zero.
        (Σ (C .carrier) (z ↦ Id (C .carrier) (C .base) z))
        (Σ (C .carrier) (circle_integer_family C))
        (family_equiv (C .carrier) (z ↦ Id (C .carrier) (C .base) z)
          (circle_integer_family C) (circle_paths_integer_family_equiv C))
        (iscontr_idfrom (C .carrier) (C .base)))

def circle_pointed (C : CircleSignature) : Pointed ≔ (C .carrier, C .base)

def circle_integer_total_pointed (C : CircleSignature) : Pointed
  ≔ (Σ (C .carrier) (circle_integer_family C),
      (C .base, code_root C (circle_integer_family C) (circle_integer_monodromy C)))

def circle_exponential_map (C : CircleSignature)
  : PointedMap (circle_integer_total_pointed C) (circle_pointed C)
  ≔ (t ↦ t .fst, refl (C .base))

def circle_winding_refl (C : CircleSignature) : Id Int (circle_winding C (refl (C .base))) int_zero
  ≔ circle_winding_power C int_zero

def circle_winding_loop (C : CircleSignature)
  : Id Int (circle_winding C (C .loop)) (pos. (suc. zero.))
  ≔ calc
      circle_winding C (C .loop)
      = circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))
        by refl (circle_winding C) (concat_1p (C .carrier) (C .base) (C .base) (C .loop))
      = pos. (suc. zero.) by circle_winding_power C (pos. (suc. zero.)) ∎

def circle_winding_inverse_loop (C : CircleSignature)
  : Id Int (circle_winding C (inverse (C .carrier) (C .base) (C .base) (C .loop))) (neg. zero.)
  ≔ calc
      circle_winding C (inverse (C .carrier) (C .base) (C .base) (C .loop))
      = circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (neg. zero.))
        by refl (circle_winding C)
          (concat_1p (C .carrier) (C .base) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop)))
      = neg. zero. by circle_winding_power C (neg. zero.) ∎

def circle_winding_successor (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p (C .loop)))
      (int_succ (circle_winding C p))
  ≔ calc
      circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p (C .loop))
      = circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base)
          (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)) (C .loop))
        by refl ((q ↦ circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) q (C .loop)))
          : Id (C .carrier) (C .base) (C .base) → Int) (circle_power_winding C p)
      = circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (int_succ (circle_winding C p)))
        by refl (circle_winding C) (loop_power_succ (C .carrier) (C .base) (C .loop) (circle_winding C p))
      = int_succ (circle_winding C p) by circle_winding_power C (int_succ (circle_winding C p)) ∎

def circle_encode_composition (C : CircleSignature)
  (p q : Id (C .carrier) (C .base) (C .base))
  : Id (circle_integer_family C (C .base))
      (code_encode C (circle_integer_family C) (circle_integer_monodromy C) (C .base)
        (concat (C .carrier) (C .base) (C .base) (C .base) p q))
      (circle_integer_monodromy C .enumeration .map (int_add (circle_winding C p) (circle_winding C q)))
  ≔ let R ≔ circle_integer_family C in
    let m ≔ circle_integer_monodromy C in
    let enc ≔ code_encode C R m (C .base) in
    let tr ≔ transport (C .carrier) R (C .base) (C .base) in
    let powers ≔ loop_power (C .carrier) (C .base) (C .loop) in
    calc
      enc (concat (C .carrier) (C .base) (C .base) (C .base) p q)
      = tr q (enc p)
        by transport_concat (C .carrier) R (C .base) (C .base) (C .base) p q (code_root C R m)
      = tr (powers (circle_winding C q)) (enc p)
        by refl ((r ↦ tr r (enc p)) : Id (C .carrier) (C .base) (C .base) → R (C .base)) (circle_power_winding C q)
      = tr (powers (circle_winding C q)) (m .enumeration .map (circle_winding C p))
        by refl (tr (powers (circle_winding C q))) (equiv_counit Int (R (C .base)) (m .enumeration) (enc p))
      = m .enumeration .map (int_add (circle_winding C p) (circle_winding C q))
        by transport_power_at (C .carrier) R (C .base) (C .loop) (m .enumeration .map) (m .step)
          (circle_winding C p) (circle_winding C q) ∎

def circle_winding_composition (C : CircleSignature)
  (p q : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q))
      (int_add (circle_winding C p) (circle_winding C q))
  ≔ let e ≔ circle_integer_monodromy C .enumeration in
    let g ≔ equiv_inverse_map Int (circle_integer_family C (C .base)) e in
    concat Int (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q))
      (g (e .map (int_add (circle_winding C p) (circle_winding C q))))
      (int_add (circle_winding C p) (circle_winding C q))
      (refl g (circle_encode_composition C p q))
      (equiv_retraction Int (circle_integer_family C (C .base)) e
        (int_add (circle_winding C p) (circle_winding C q)))

def circle_winding_predecessor (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p
        (inverse (C .carrier) (C .base) (C .base) (C .loop)))) (int_pred (circle_winding C p))
  ≔ concat Int
      (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p
        (inverse (C .carrier) (C .base) (C .base) (C .loop))))
      (int_add (circle_winding C p) (circle_winding C (inverse (C .carrier) (C .base) (C .base) (C .loop))))
      (int_pred (circle_winding C p))
      (circle_winding_composition C p (inverse (C .carrier) (C .base) (C .base) (C .loop)))
      (refl (int_add (circle_winding C p)) (circle_winding_inverse_loop C))
