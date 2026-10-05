export "26-loop-powers"

{` This is data about an already supplied family, not an additional
   circle or code axiom. It will be constructed from circle_integer_family_beta. `}
def IntegerMonodromy (d : FreeLoop Type) : Type ≔ sig (
  enumeration : Equiv Int (d .fst),
  step : (n : Int) → Id (d .fst) (d .snd .trr (enumeration .map n)) (enumeration .map (int_succ n)))

def standard_integer_monodromy : IntegerMonodromy (Int, int_universe_loop)
  ≔ (identity_equiv Int, n ↦ refl (int_succ n))

def circle_integer_monodromy (C : CircleSignature)
  : IntegerMonodromy (circle_eval C Type (circle_integer_family C))
  ≔ refl IntegerMonodromy (circle_integer_family_beta C) .trl standard_integer_monodromy

def circle_integer_enumeration_coherence (C : CircleSignature) (n : Int)
  : Id (d ↦ d .fst) (circle_integer_family_beta C)
      (circle_integer_monodromy C .enumeration .map n) n
  ≔ refl IntegerMonodromy (circle_integer_family_beta C) .liftl standard_integer_monodromy
      .enumeration .map (refl n)

def circle_integer_trivialization (C : CircleSignature) : circle_integer_family C (C .base) → Int
  ≔ circle_integer_family_beta C .fst .trr

def circle_integer_trivialization_enumeration (C : CircleSignature) (n : Int)
  : Id Int (circle_integer_trivialization C (circle_integer_monodromy C .enumeration .map n)) n
  ≔ pathover_transport_equiv (FreeLoop Type) (d ↦ d .fst)
      (circle_eval C Type (circle_integer_family C)) (Int, int_universe_loop)
      (circle_integer_family_beta C) (circle_integer_monodromy C .enumeration .map n) n
      .map (circle_integer_enumeration_coherence C n)

def CircleCode (C : CircleSignature) (R : C .carrier → Type) : Type
  ≔ IntegerMonodromy (circle_eval C Type R)

def code_root (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R) : R (C .base)
  ≔ m .enumeration .map int_zero

def code_encode (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (z : C .carrier) (p : Id (C .carrier) (C .base) z) : R z
  ≔ transport (C .carrier) R (C .base) z p (code_root C R m)

def code_encode_power (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R) (n : Int)
  : Id (R (C .base))
      (code_encode C R m (C .base) (loop_power (C .carrier) (C .base) (C .loop) n))
      (m .enumeration .map n)
  ≔ transport_loop_power (C .carrier) R (C .base) (C .loop) (m .enumeration .map) (m .step) n

def code_decode_base (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (x : R (C .base)) : Id (C .carrier) (C .base) (C .base)
  ≔ loop_power (C .carrier) (C .base) (C .loop)
      (equiv_inverse_map Int (R (C .base)) (m .enumeration) x)

def code_path_index (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (x y : R (C .base)) (q : Id R (C .loop) x y)
  : Id Int (int_succ (equiv_inverse_map Int (R (C .base)) (m .enumeration) x))
      (equiv_inverse_map Int (R (C .base)) (m .enumeration) y)
  ≔ let e ≔ m .enumeration in
    let g ≔ equiv_inverse_map Int (R (C .base)) e in
    equivalence_injective Int (R (C .base)) e (int_succ (g x)) (g y)
      (calc
        e .map (int_succ (g x))
        = transport (C .carrier) R (C .base) (C .base) (C .loop) (e .map (g x))
          by m .step (g x)
        = transport (C .carrier) R (C .base) (C .base) (C .loop) x
          by refl (transport (C .carrier) R (C .base) (C .base) (C .loop))
            (equiv_counit Int (R (C .base)) e x)
        = y by pathover_transport_equiv (C .carrier) R (C .base) (C .base) (C .loop) x y .map q
        = e .map (g y) by equiv_counit Int (R (C .base)) e y ∎)

def pathover_from_triangle (A : Type) (a x y : A) (r : Id A x y)
  (p : Id A a x) (q : Id A a y) (h : Id (Id A a y) (concat A a x y p r) q)
  : Id (z ↦ Id A a z) r p q
  ≔ equiv_inverse_map (Id (z ↦ Id A a z) r p q) (Id (Id A a y) (concat A a x y p r) q)
      (id_to_equiv (Id (z ↦ Id A a z) r p q) (Id (Id A a y) (concat A a x y p r) q)
        (pathover_mapped_paths_type A A (identity A) a x y r p q)) h

def code_decode_loop (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : Id (z ↦ R z → Id (C .carrier) (C .base) z) (C .loop)
      (code_decode_base C R m) (code_decode_base C R m)
  ≔ x ⤇ pathover_from_triangle (C .carrier) (C .base) (C .base) (C .base) (C .loop)
      (code_decode_base C R m x.0) (code_decode_base C R m x.1)
      (concat (Id (C .carrier) (C .base) (C .base))
        (concat (C .carrier) (C .base) (C .base) (C .base) (code_decode_base C R m x.0) (C .loop))
        (loop_power (C .carrier) (C .base) (C .loop)
          (int_succ (equiv_inverse_map Int (R (C .base)) (m .enumeration) x.0)))
        (code_decode_base C R m x.1)
        (loop_power_succ (C .carrier) (C .base) (C .loop)
          (equiv_inverse_map Int (R (C .base)) (m .enumeration) x.0))
        (refl (loop_power (C .carrier) (C .base) (C .loop)) (code_path_index C R m x.0 x.1 x.2)))

def code_decode (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : (z : C .carrier) → R z → Id (C .carrier) (C .base) z
  ≔ C .induction (z ↦ R z → Id (C .carrier) (C .base) z)
      (code_decode_base C R m, code_decode_loop C R m) .fst

def code_decode_beta (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : Id (R (C .base) → Id (C .carrier) (C .base) (C .base))
      (code_decode C R m (C .base)) (code_decode_base C R m)
  ≔ C .induction (z ↦ R z → Id (C .carrier) (C .base) z)
      (code_decode_base C R m, code_decode_loop C R m) .snd .fst

def code_decode_root (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : Id (Id (C .carrier) (C .base) (C .base))
      (code_decode C R m (C .base) (code_root C R m)) (refl (C .base))
  ≔ concat (Id (C .carrier) (C .base) (C .base))
      (code_decode C R m (C .base) (code_root C R m)) (code_decode_base C R m (code_root C R m))
      (refl (C .base))
      (code_decode_beta C R m (refl (code_root C R m)))
      (refl (loop_power (C .carrier) (C .base) (C .loop))
        (equiv_retraction Int (R (C .base)) (m .enumeration) int_zero))

def code_decode_encode (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (z : C .carrier) (p : Id (C .carrier) (C .base) z)
  : Id (Id (C .carrier) (C .base) z) (code_decode C R m z (code_encode C R m z p)) p
  ≔ J (C .carrier) (C .base)
      (z p ↦ Id (Id (C .carrier) (C .base) z) (code_decode C R m z (code_encode C R m z p)) p)
      (concat (Id (C .carrier) (C .base) (C .base))
        (code_decode C R m (C .base) (code_encode C R m (C .base) (refl (C .base))))
        (code_decode C R m (C .base) (code_root C R m)) (refl (C .base))
        (refl (code_decode C R m (C .base)) (transport_refl (C .carrier) R (C .base) (code_root C R m)))
        (code_decode_root C R m)) z p

def code_is_set (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : (z : C .carrier) → isSet (R z)
  ≔ circle_ind_prop C (z ↦ isSet (R z)) (z ↦ isset_isprop (R z))
      (hlevel_two_to_set (R (C .base))
        (hlevel_equiv (suc. (suc. zero.)) Int (R (C .base)) (m .enumeration) (set_to_hlevel_two Int int_set)))

def code_encode_decode_base (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (x : R (C .base))
  : Id (R (C .base)) (code_encode C R m (C .base) (code_decode C R m (C .base) x)) x
  ≔ calc
      code_encode C R m (C .base) (code_decode C R m (C .base) x)
      = code_encode C R m (C .base) (code_decode_base C R m x)
        by refl (code_encode C R m (C .base)) (code_decode_beta C R m (refl x))
      = m .enumeration .map (equiv_inverse_map Int (R (C .base)) (m .enumeration) x)
        by code_encode_power C R m (equiv_inverse_map Int (R (C .base)) (m .enumeration) x)
      = x by equiv_counit Int (R (C .base)) (m .enumeration) x ∎

def code_encode_decode (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  : (z : C .carrier) (x : R z) → Id (R z) (code_encode C R m z (code_decode C R m z x)) x
  ≔ circle_ind_prop C
      (z ↦ (x : R z) → Id (R z) (code_encode C R m z (code_decode C R m z x)) x)
      (z ↦ pi_prop (R z) (x ↦ Id (R z) (code_encode C R m z (code_decode C R m z x)) x)
        (x ↦ code_is_set C R m z (code_encode C R m z (code_decode C R m z x)) x))
      (code_encode_decode_base C R m)

def circle_path_code_equiv (C : CircleSignature) (R : C .carrier → Type) (m : CircleCode C R)
  (z : C .carrier) : Equiv (Id (C .carrier) (C .base) z) (R z)
  ≔ quasi_inverse_equiv (Id (C .carrier) (C .base) z) (R z)
      (code_encode C R m z) (code_decode C R m z) (code_decode_encode C R m z) (code_encode_decode C R m z)
