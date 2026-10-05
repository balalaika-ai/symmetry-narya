export "19-types-and-maps"

{` The J-defined equivalence has the same map as native transport. `}
def id_to_equiv_transport (A B : Type) (p : Id Type A B) (a : A)
  : Id B (id_to_equiv A B p .map a) (p .trr a)
  ≔ J Type A
      (B p ↦ (a : A) → Id B (id_to_equiv A B p .map a) (p .trr a))
      (a ↦ concat A (id_to_equiv A A (refl A) .map a) a
        (transport Type (T ↦ T) A A (refl A) a)
        (inverse A a (id_to_equiv A A (refl A) .map a)
          (refl ((e ↦ e .map a) : Equiv A A → A)
            (Jβ Type A (B _ ↦ Equiv A B) (identity_equiv A))))
        (inverse A (transport Type (T ↦ T) A A (refl A) a) a
          (transport_refl Type (T ↦ T) A a))) B p a

def ua_beta (A B : Type) (e : Equiv A B)
  : Id (Equiv A B) (id_to_equiv A B (ua A B e)) e
  ≔ equiv_homotopy A B (id_to_equiv A B (ua A B e)) e
      (id_to_equiv_transport A B (ua A B e))

def transport_inverse_roundtrip (A : Type) (B : A → Type)
  (x y : A) (p : Id A x y) (b : B x)
  : Id (B x) (transport A B y x (inverse A x y p) (transport A B x y p b)) b
  ≔ calc
      transport A B y x (inverse A x y p) (transport A B x y p b)
      = transport A B x x (concat A x y x p (inverse A x y p)) b
        by transport_concat A B x y x p (inverse A x y p) b
      = transport A B x x (refl x) b
        by refl ((q ↦ transport A B x x q b) : Id A x x → B x) (concat_inverse_right A x y p)
      = b by transport_refl A B x b ∎

{` Normalize ua at the identity only as an intermediate construction.
   Path induction then supplies its left inverse law. `}
def normalized_ua (A B : Type) (e : Equiv A B) : Id Type A B
  ≔ concat Type A A B (inverse Type A A (ua A A (identity_equiv A))) (ua A B e)

def normalized_ua_eta (A B : Type) (p : Id Type A B)
  : Id (Id Type A B) (normalized_ua A B (id_to_equiv A B p)) p
  ≔ J Type A
      (B p ↦ Id (Id Type A B) (normalized_ua A B (id_to_equiv A B p)) p)
      (calc
        normalized_ua A A (id_to_equiv A A (refl A))
        = normalized_ua A A (identity_equiv A)
          by refl (normalized_ua A A) (Jβ Type A (B _ ↦ Equiv A B) (identity_equiv A))
        = refl A by concat_inverse_left Type A A (ua A A (identity_equiv A)) ∎) B p

def normalized_ua_transport (A B : Type) (e : Equiv A B) (a : A)
  : Id B (normalized_ua A B e .trr a) (e .map a)
  ≔ calc
      normalized_ua A B e .trr a
      = ua A B e .trr (inverse Type A A (ua A A (identity_equiv A)) .trr a)
        by transport_concat Type (T ↦ T) A A B
          (inverse Type A A (ua A A (identity_equiv A))) (ua A B e) a
      = e .map a by refl (e .map)
          (transport_inverse_roundtrip Type (T ↦ T) A A (ua A A (identity_equiv A)) a) ∎

def normalized_ua_beta (A B : Type) (e : Equiv A B)
  : Id (Equiv A B) (id_to_equiv A B (normalized_ua A B e)) e
  ≔ equiv_homotopy A B (id_to_equiv A B (normalized_ua A B e)) e
      (a ↦ concat B (id_to_equiv A B (normalized_ua A B e) .map a)
        (normalized_ua A B e .trr a) (e .map a)
        (id_to_equiv_transport A B (normalized_ua A B e) a)
        (normalized_ua_transport A B e a))

{` The original computational ua also satisfies the left inverse law.
   This follows from the normalized left inverse and the original beta. `}
def ua_eta (A B : Type) (p : Id Type A B)
  : Id (Id Type A B) (ua A B (id_to_equiv A B p)) p
  ≔ calc
      ua A B (id_to_equiv A B p)
      = normalized_ua A B (id_to_equiv A B (ua A B (id_to_equiv A B p)))
        by normalized_ua_eta A B (ua A B (id_to_equiv A B p))
      = normalized_ua A B (id_to_equiv A B p)
        by refl (normalized_ua A B) (ua_beta A B (id_to_equiv A B p))
      = p by normalized_ua_eta A B p ∎

{` def:univalence, using native Id and the original glue construction. `}
def univalence_equiv (A B : Type) : Equiv (Id Type A B) (Equiv A B)
  ≔ quasi_inverse_equiv (Id Type A B) (Equiv A B)
      (id_to_equiv A B) (ua A B) (ua_eta A B) (ua_beta A B)

def equiv_change_map (A B : Type) (e : Equiv A B) (f : A → B)
  (h : (a : A) → Id B (e .map a) (f a)) : Equiv A B
  ≔ (f, transport (A → B) (isEquiv A B) (e .map) f
      (funext A (_ ↦ B) (e .map) f h) (e .equiv))

def transport_equiv (A B : Type) (p : Id Type A B) : Equiv A B
  ≔ equiv_change_map A B (id_to_equiv A B p) (p .trr) (id_to_equiv_transport A B p)

def id_transport_equiv_path (A B : Type) (p : Id Type A B)
  : Id (Equiv A B) (id_to_equiv A B p) (transport_equiv A B p)
  ≔ equiv_homotopy A B (id_to_equiv A B p) (transport_equiv A B p) (id_to_equiv_transport A B p)

{` The underlying map is now exactly transport in the identity family. `}
def transport_univalence_equiv (A B : Type) : Equiv (Id Type A B) (Equiv A B)
  ≔ equiv_change_map (Id Type A B) (Equiv A B) (univalence_equiv A B)
      (transport_equiv A B) (id_transport_equiv_path A B)

def book_equiv_path (A B : Type) (e d : BookEquiv A B)
  (p : Id (A → B) (e .map) (d .map)) : Id (BookEquiv A B) e d
  ≔ (p, pathover_of_eq (A → B) (BookIsEquiv A B) (e .map) (d .map) p (e .equiv) (d .equiv)
      (book_isequiv_isprop A B (d .map)
        (transport (A → B) (BookIsEquiv A B) (e .map) (d .map) p (e .equiv)) (d .equiv)))

def equivalence_conventions_equiv (A B : Type) : Equiv (Equiv A B) (BookEquiv A B)
  ≔ quasi_inverse_equiv (Equiv A B) (BookEquiv A B) (book_equivalence A B) (native_equivalence A B)
      (e ↦ equiv_path A B (native_equivalence A B (book_equivalence A B e)) e (refl (e .map)))
      (e ↦ book_equiv_path A B (book_equivalence A B (native_equivalence A B e)) e (refl (e .map)))

{` def:univalence with both the exact transport map and the book's
   fiber/contraction conventions. Narya still has only Type:Type. `}
def book_univalence (A B : Type) : BookEquiv (Id Type A B) (BookEquiv A B)
  ≔ book_equivalence (Id Type A B) (BookEquiv A B)
      (compose_equiv (Id Type A B) (Equiv A B) (BookEquiv A B)
        (transport_univalence_equiv A B) (equivalence_conventions_equiv A B))

def ua_identity (A : Type)
  : Id (Id Type A A) (ua A A (identity_equiv A)) (refl A)
  ≔ concat (Id Type A A) (ua A A (identity_equiv A))
      (ua A A (id_to_equiv A A (refl A))) (refl A)
      (refl (ua A A) (Jβ Type A (B _ ↦ Equiv A B) (identity_equiv A)))
      (ua_eta A A (refl A))

def id_to_equiv_ua_concat (A B C : Type) (e : Equiv A B) (d : Equiv B C)
  : Id (Equiv A C) (id_to_equiv A C (concat Type A B C (ua A B e) (ua B C d)))
      (compose_equiv A B C e d)
  ≔ equiv_homotopy A C (id_to_equiv A C (concat Type A B C (ua A B e) (ua B C d)))
      (compose_equiv A B C e d)
      (a ↦ concat C
        (id_to_equiv A C (concat Type A B C (ua A B e) (ua B C d)) .map a)
        (concat Type A B C (ua A B e) (ua B C d) .trr a) (d .map (e .map a))
        (id_to_equiv_transport A C (concat Type A B C (ua A B e) (ua B C d)) a)
        (transport_concat Type (T ↦ T) A B C (ua A B e) (ua B C d) a))

def ua_compose (A B C : Type) (e : Equiv A B) (d : Equiv B C)
  : Id (Id Type A C) (ua A C (compose_equiv A B C e d))
      (concat Type A B C (ua A B e) (ua B C d))
  ≔ calc
      ua A C (compose_equiv A B C e d)
      = ua A C (id_to_equiv A C (concat Type A B C (ua A B e) (ua B C d)))
        by refl (ua A C) (id_to_equiv_ua_concat A B C e d)
      = concat Type A B C (ua A B e) (ua B C d)
        by ua_eta A C (concat Type A B C (ua A B e) (ua B C d)) ∎

{` A derived induction principle for equivalences, with an explicit
   adjustment for the propositional computation of J. `}
def equivalence_induction (A : Type) (P : (B : Type) → Equiv A B → Type)
  (base : P A (identity_equiv A)) (B : Type) (e : Equiv A B) : P B e
  ≔ transport (Equiv A B) (P B) (id_to_equiv A B (ua A B e)) e (ua_beta A B e)
      (J Type A (B p ↦ P B (id_to_equiv A B p))
        (transport (Equiv A A) (P A) (identity_equiv A) (id_to_equiv A A (refl A))
          (Jβ Type A (B _ ↦ Equiv A B) (identity_equiv A)) base) B (ua A B e))

def equivalence_on_paths (A B : Type) (e : Equiv A B) (x y : A)
  : Equiv (Id A x y) (Id B (e .map x) (e .map y))
  ≔ (map_path A B (e .map) x y,
      equivalence_induction A
        (B e ↦ (x y : A) → isEquiv (Id A x y) (Id B (e .map x) (e .map y))
          (map_path A B (e .map) x y))
        (x y ↦ identity_equiv (Id A x y) .equiv) B e x y)
