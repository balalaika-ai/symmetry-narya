export "581-symmetric-group-inclusions"

{` Chapter 5, xca:A-is-A-1+1, xca:n-is-ptd-n+1 and exa:fix1subSGn: splitting off
   a point of a set with decidable equality (Without of module 30), n-element
   sets are pointed (n+1)-element sets, and the subgroups (X, k) of Σ_n. `}

{` A ≃ (A ∖ {a}) + 1 for decidable A, sending a to the new point. `}
def point_split_dec (A : Type) (a x : A) (d : Decidable (Id A x a)) : Sum (Without A a) Unit
  ≔ match d [ inl. _ ↦ inr. star. | inr. n ↦ inl. (x, n) ]

def point_merge (A : Type) (a : A) (u : Sum (Without A a) Unit) : A
  ≔ match u [ inl. c ↦ c .fst | inr. _ ↦ a ]

def point_merge_split (A : Type) (a x : A) (d : Decidable (Id A x a))
  : Id A (point_merge A a (point_split_dec A a x d)) x
  ≔ match d [ inl. p ↦ inverse A x a p | inr. n ↦ refl x ]

def point_split_without (A : Type) (a : A) (c : Without A a) (d : Decidable (Id A (c .fst) a))
  : Id (Sum (Without A a) Unit) (point_split_dec A a (c .fst) d) (inl. c)
  ≔ match d [
  | inl. p ↦ absurd (Id (Sum (Without A a) Unit) (inr. star.) (inl. c)) (c .snd p)
  | inr. n ↦ refl ((w ↦ inl. w) : Without A a → Sum (Without A a) Unit)
      (without_ext A a (c .fst, n) c (refl (c .fst))) ]

def point_split_self (A : Type) (a : A) (d : Decidable (Id A a a))
  : Id (Sum (Without A a) Unit) (point_split_dec A a a d) (inr. star.)
  ≔ match d [
  | inl. _ ↦ refl (inr. star. : Sum (Without A a) Unit)
  | inr. n ↦ absurd (Id (Sum (Without A a) Unit) (inl. (a, n)) (inr. star.)) (n (refl a)) ]

def point_split_equiv (A : Type) (dA : DecidableEquality A) (a : A) : Equiv A (Sum (Without A a) Unit)
  ≔ quasi_inverse_equiv A (Sum (Without A a) Unit) (x ↦ point_split_dec A a x (dA x a)) (point_merge A a)
      (x ↦ point_merge_split A a x (dA x a))
      [ inl. c ↦ point_split_without A a c (dA (c .fst) a)
      | inr. s ↦ match s [ star. ↦ point_split_self A a (dA a a) ] ]

{` Paths of types are determined by their transport functions. `}
def type_path_ext (X Y : Type) (q q' : Id Type X Y) (h : (x : X) → Id Y (q .trr x) (q' .trr x)) : Id (Id Type X Y) q q'
  ≔ equivalence_injective (Id Type X Y) (Equiv X Y) (transport_univalence_equiv X Y) q q'
      (equiv_path X Y (transport_univalence_equiv X Y .map q) (transport_univalence_equiv X Y .map q')
        (funext X (_ ↦ Y) (q .trr) (q' .trr) h))

{` xca:A-is-A-1+1. For a set A with decidable equality,
   a ↦ (A ∖ {a}, ua(A ≃ (A ∖ {a}) + 1)) is an equivalence A ≃ Σ_{B:U} (A = B + 1),
   with inverse (B, p) ↦ p⁻¹(inr ★). `}
def PointRemovals (A : Type) : Type ≔ Σ Type (B ↦ Id Type A (Sum B Unit))

def point_removal (A : Type) (dA : DecidableEquality A) (a : A) : PointRemovals A
  ≔ (Without A a, ua A (Sum (Without A a) Unit) (point_split_equiv A dA a))

def point_removal_inverse (A : Type) (u : PointRemovals A) : A
  ≔ transport Type (Y ↦ Y) (Sum (u .fst) Unit) A (inverse Type A (Sum (u .fst) Unit) (u .snd)) (inr. star.)

def point_removal_retraction (A : Type) (dA : DecidableEquality A) (a : A)
  : Id A (point_removal_inverse A (point_removal A dA a)) a
  ≔ let W ≔ Sum (Without A a) Unit in
    let p ≔ ua A W (point_split_equiv A dA a) in
    concat A (transport Type (Y ↦ Y) W A (inverse Type A W p) (inr. star.))
      (transport Type (Y ↦ Y) W A (inverse Type A W p) (transport Type (Y ↦ Y) A W p a)) a
      (map_path W A (transport Type (Y ↦ Y) W A (inverse Type A W p)) (inr. star.) (transport Type (Y ↦ Y) A W p a)
        (inverse W (transport Type (Y ↦ Y) A W p a) (inr. star.) (point_split_self A a (dA a a))))
      (transport_inverse_roundtrip Type (Y ↦ Y) A W p a)

{` The other round trip: for (B, p) with a ≔ p⁻¹(inr ★), A ∖ {a} ≃ B and the
   identification ua(split) · ap_{−+1}(ua) is p (compared by transport). `}
def ch5_transport_inverse_section (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B y)
  : Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b
  ≔ J A x (y p ↦ (b : B y) → Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b)
      (b ↦ calc
        transport A B x x (refl x) (transport A B x x (inverse A x x (refl x)) b)
        = transport A B x x (inverse A x x (refl x)) b by transport_refl A B x (transport A B x x (inverse A x x (refl x)) b)
        = transport A B x x (refl x) b
          by map_path (Id A x x) (B x) (r ↦ transport A B x x r b) (inverse A x x (refl x)) (refl x) (inverse_refl A x)
        = b by transport_refl A B x b ∎)
      y p b

def removal_complement_nonpoint (A B : Type) (p : Id Type A (Sum B Unit)) (c : Without A (point_removal_inverse A (B, p)))
  : Id (Sum B Unit) (p .trr (c .fst)) (inr. star.) → Empty
  ≔ e ↦ c .snd
      (calc
        c .fst = transport Type (Y ↦ Y) (Sum B Unit) A (inverse Type A (Sum B Unit) p) (p .trr (c .fst))
          by inverse A (transport Type (Y ↦ Y) (Sum B Unit) A (inverse Type A (Sum B Unit) p) (p .trr (c .fst))) (c .fst)
               (transport_inverse_roundtrip Type (Y ↦ Y) A (Sum B Unit) p (c .fst))
        = point_removal_inverse A (B, p)
          by map_path (Sum B Unit) A (transport Type (Y ↦ Y) (Sum B Unit) A (inverse Type A (Sum B Unit) p))
               (p .trr (c .fst)) (inr. star.) e ∎)

def removal_complement_map (A B : Type) (p : Id Type A (Sum B Unit)) (c : Without A (point_removal_inverse A (B, p))) : B
  ≔ without_last_to B (p .trr (c .fst)) (removal_complement_nonpoint A B p c)

def removal_complement_inv (A B : Type) (p : Id Type A (Sum B Unit)) (b : B) : Without A (point_removal_inverse A (B, p))
  ≔ let q ≔ inverse Type A (Sum B Unit) p in
    (transport Type (Y ↦ Y) (Sum B Unit) A q (inl. b),
     e ↦ sum_encode B Unit (inl. b) (inr. star.)
       (calc
         (inl. b : Sum B Unit)
         = p .trr (transport Type (Y ↦ Y) (Sum B Unit) A q (inl. b))
           by inverse (Sum B Unit) (p .trr (transport Type (Y ↦ Y) (Sum B Unit) A q (inl. b))) (inl. b)
                (ch5_transport_inverse_section Type (Y ↦ Y) A (Sum B Unit) p (inl. b))
         = p .trr (point_removal_inverse A (B, p))
           by map_path A (Sum B Unit) (p .trr) (transport Type (Y ↦ Y) (Sum B Unit) A q (inl. b))
                (point_removal_inverse A (B, p)) e
         = inr. star. by ch5_transport_inverse_section Type (Y ↦ Y) A (Sum B Unit) p (inr. star.) ∎))

def removal_complement_equiv (A B : Type) (p : Id Type A (Sum B Unit))
  : Equiv (Without A (point_removal_inverse A (B, p))) B
  ≔ let a ≔ point_removal_inverse A (B, p) in
    let q ≔ inverse Type A (Sum B Unit) p in
    quasi_inverse_equiv (Without A a) B (removal_complement_map A B p) (removal_complement_inv A B p)
      (c ↦ without_ext A a (removal_complement_inv A B p (removal_complement_map A B p c)) c
        (calc
          transport Type (Y ↦ Y) (Sum B Unit) A q (inl. (removal_complement_map A B p c))
          = transport Type (Y ↦ Y) (Sum B Unit) A q (p .trr (c .fst))
            by map_path (Sum B Unit) A (transport Type (Y ↦ Y) (Sum B Unit) A q)
                 (inl. (removal_complement_map A B p c)) (p .trr (c .fst))
                 (option_value_inl B (p .trr (c .fst)) (removal_complement_nonpoint A B p c))
          = c .fst by transport_inverse_roundtrip Type (Y ↦ Y) A (Sum B Unit) p (c .fst) ∎))
      (b ↦ inl_injective B (removal_complement_map A B p (removal_complement_inv A B p b)) b
        (calc
          (inl. (removal_complement_map A B p (removal_complement_inv A B p b)) : Sum B Unit)
          = p .trr (removal_complement_inv A B p b .fst)
            by option_value_inl B (p .trr (removal_complement_inv A B p b .fst))
                 (removal_complement_nonpoint A B p (removal_complement_inv A B p b))
          = inl. b by ch5_transport_inverse_section Type (Y ↦ Y) A (Sum B Unit) p (inl. b) ∎))

def removal_family_transport (A C C' : Type) (r : Id Type C C') (q : Id Type A (Sum C Unit)) (x : A)
  : Id (Sum C' Unit) ((transport Type (D ↦ Id Type A (Sum D Unit)) C C' r q) .trr x)
      (transport Type (Y ↦ Y) (Sum C Unit) (Sum C' Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (q .trr x))
  ≔ J Type C
      (C' r ↦ Id (Sum C' Unit) ((transport Type (D ↦ Id Type A (Sum D Unit)) C C' r q) .trr x)
        (transport Type (Y ↦ Y) (Sum C Unit) (Sum C' Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (q .trr x)))
      (concat (Sum C Unit) ((transport Type (D ↦ Id Type A (Sum D Unit)) C C (refl C) q) .trr x) (q .trr x)
        (transport Type (Y ↦ Y) (Sum C Unit) (Sum C Unit) (refl (Sum C Unit)) (q .trr x))
        (map_path (Id Type A (Sum C Unit)) (Sum C Unit) (s ↦ s .trr x)
          (transport Type (D ↦ Id Type A (Sum D Unit)) C C (refl C) q) q
          (transport_refl Type (D ↦ Id Type A (Sum D Unit)) C q))
        (inverse (Sum C Unit) (transport Type (Y ↦ Y) (Sum C Unit) (Sum C Unit) (refl (Sum C Unit)) (q .trr x)) (q .trr x)
          (transport_refl Type (Y ↦ Y) (Sum C Unit) (q .trr x))))
      C' r

def removal_split_transport (A B : Type) (p : Id Type A (Sum B Unit)) (x : A)
  (d : Decidable (Id A x (point_removal_inverse A (B, p))))
  : Id (Sum B Unit)
      (transport Type (Y ↦ Y) (Sum (Without A (point_removal_inverse A (B, p))) Unit) (Sum B Unit)
        (refl ((Y ↦ Sum Y Unit) : Type → Type)
          (ua (Without A (point_removal_inverse A (B, p))) B (removal_complement_equiv A B p)))
        (point_split_dec A (point_removal_inverse A (B, p)) x d))
      (p .trr x)
  ≔ let a ≔ point_removal_inverse A (B, p) in
    let W ≔ Without A a in
    let r ≔ ua W B (removal_complement_equiv A B p) in
    match d [
    | inl. e ↦ calc
        transport Type (Y ↦ Y) (Sum W Unit) (Sum B Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (inr. star.)
        = inr. star. by transport_sum_right_inr Unit W B r star.
        = p .trr a by inverse (Sum B Unit) (p .trr a) (inr. star.) (ch5_transport_inverse_section Type (Y ↦ Y) A (Sum B Unit) p (inr. star.))
        = p .trr x by map_path A (Sum B Unit) (p .trr) a x (inverse A x a e) ∎
    | inr. n ↦ calc
        transport Type (Y ↦ Y) (Sum W Unit) (Sum B Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (inl. (x, n))
        = inl. (removal_complement_map A B p (x, n)) by transport_sum_right_inl Unit W B r (x, n)
        = p .trr x by option_value_inl B (p .trr x) (removal_complement_nonpoint A B p (x, n)) ∎ ]

def point_removal_section (A : Type) (dA : DecidableEquality A) (u : PointRemovals A)
  : Id (PointRemovals A) (point_removal A dA (point_removal_inverse A u)) u
  ≔ let B ≔ u .fst in
    let p ≔ u .snd in
    let a ≔ point_removal_inverse A (B, p) in
    let W ≔ Without A a in
    let r ≔ ua W B (removal_complement_equiv A B p) in
    let q ≔ ua A (Sum W Unit) (point_split_equiv A dA a) in
    (r, pathover_of_eq Type (C ↦ Id Type A (Sum C Unit)) W B r q p
      (type_path_ext A (Sum B Unit) (transport Type (C ↦ Id Type A (Sum C Unit)) W B r q) p
        (x ↦ concat (Sum B Unit) ((transport Type (C ↦ Id Type A (Sum C Unit)) W B r q) .trr x)
          (transport Type (Y ↦ Y) (Sum W Unit) (Sum B Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (q .trr x))
          (p .trr x)
          (removal_family_transport A W B r q x)
          (removal_split_transport A B p x (dA x a)))))

def point_removal_equiv (A : Type) (dA : DecidableEquality A) : BookEquiv A (PointRemovals A)
  ≔ book_quasi_inverse_equiv A (PointRemovals A) (point_removal A dA) (point_removal_inverse A)
      (point_removal_retraction A dA) (point_removal_section A dA)
