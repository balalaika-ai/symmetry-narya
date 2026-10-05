export "841-wedge-signatures"

{` def:bfree (congp.tex:738).  The classifying type B F_S of the free group
   on a set S is the higher inductive type with a point base and loops
   loop_s : base = base for s : S; its induction principle asks for a : A(base)
   and dependent paths l_s over loop_s, with f(base) ≡ a and apd_f(loop_s) = l_s.

   The pinned Narya has no higher inductive types, so FreeGroupSignature S is
   a PARAMETER (as CircleSignature, module 05): the computation rules are ONE
   identification of boundary data, so the book's judgmental base rule
   f(base) ≡ a becomes the proved identification free_ind_base.  Module 87x
   constructs an instance for every decidable set S (no HITs, no axioms).
   Results here hold for every signature and every type S. `}

def FreeGroupBoundary (S : Type) (X : Type) (base : X) (loop : S → Id X base base)
  (P : X → Type) : Type
  ≔ Σ (P base) (a ↦ (s : S) → Id P (loop s) a a)

def free_group_evaluate (S : Type) (X : Type) (base : X) (loop : S → Id X base base)
  (P : X → Type) (h : (x : X) → P x) : FreeGroupBoundary S X base loop P
  ≔ (h base, s ↦ refl h (loop s))

def FreeGroupSignature (S : Type) : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop : S → Id carrier base base,
  induction : (P : carrier → Type) (d : FreeGroupBoundary S carrier base loop P)
    → Σ ((x : carrier) → P x) (h ↦
        Id (FreeGroupBoundary S carrier base loop P) (free_group_evaluate S carrier base loop P h) d))

def free_pointed (S : Type) (F : FreeGroupSignature S) : Pointed ≔ (F .carrier, F .base)

def free_boundary (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) : Type
  ≔ FreeGroupBoundary S (F .carrier) (F .base) (F .loop) P

def free_eval (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) (h : (x : F .carrier) → P x)
  : free_boundary S F P
  ≔ free_group_evaluate S (F .carrier) (F .base) (F .loop) P h

def free_ind (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) (d : free_boundary S F P)
  : (x : F .carrier) → P x
  ≔ F .induction P d .fst

def free_ind_beta (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) (d : free_boundary S F P)
  : Id (free_boundary S F P) (free_eval S F P (free_ind S F P d)) d
  ≔ F .induction P d .snd

{` The base computation rule f(base) = a (judgmental in the book). `}
def free_ind_base (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) (d : free_boundary S F P)
  : Id (P (F .base)) (free_ind S F P d (F .base)) (d .fst)
  ≔ free_ind_beta S F P d .fst

def free_sections_equal (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type)
  (h k : (x : F .carrier) → P x)
  (e : Id (free_boundary S F P) (free_eval S F P h) (free_eval S F P k))
  : Id ((x : F .carrier) → P x) h k
  ≔ funext (F .carrier) P h k
      (F .induction (x ↦ Id (P x) (h x) (k x)) (e .fst, s ↦ sym (e .snd (refl s))) .fst)

def free_ind_eta (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type) (h : (x : F .carrier) → P x)
  : Id ((x : F .carrier) → P x) (free_ind S F P (free_eval S F P h)) h
  ≔ free_sections_equal S F P (free_ind S F P (free_eval S F P h)) h (free_ind_beta S F P (free_eval S F P h))

def free_dependent_universal_property (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type)
  : Equiv ((x : F .carrier) → P x) (free_boundary S F P)
  ≔ quasi_inverse_equiv ((x : F .carrier) → P x) (free_boundary S F P)
      (free_eval S F P) (free_ind S F P) (free_ind_eta S F P) (free_ind_beta S F P)

def free_ind_prop (S : Type) (F : FreeGroupSignature S) (P : F .carrier → Type)
  (hP : (x : F .carrier) → isProp (P x)) (b : P (F .base)) : (x : F .carrier) → P x
  ≔ F .induction P
      (b, s ↦ pathover_of_eq (F .carrier) P (F .base) (F .base) (F .loop s) b b
        (hP (F .base) (transport (F .carrier) P (F .base) (F .base) (F .loop s) b) b)) .fst

{` Nondependent data: a point with an S-indexed family of loops. `}
def BouquetData (S : Type) (T : Type) : Type ≔ Σ T (t ↦ S → Id T t t)

def free_bouquet (S : Type) (F : FreeGroupSignature S) (T : Type) (h : F .carrier → T) : BouquetData S T
  ≔ (h (F .base), s ↦ refl h (F .loop s))

def free_rec (S : Type) (F : FreeGroupSignature S) (T : Type) (d : BouquetData S T) : F .carrier → T
  ≔ F .induction (_ ↦ T) d .fst

def free_rec_beta (S : Type) (F : FreeGroupSignature S) (T : Type) (d : BouquetData S T)
  : Id (BouquetData S T) (free_bouquet S F T (free_rec S F T d)) d
  ≔ F .induction (_ ↦ T) d .snd

def free_maps_equal (S : Type) (F : FreeGroupSignature S) (T : Type) (h k : F .carrier → T)
  (e : Id (BouquetData S T) (free_bouquet S F T h) (free_bouquet S F T k))
  : Id (F .carrier → T) h k
  ≔ funext (F .carrier) (_ ↦ T) h k
      (F .induction (x ↦ Id T (h x) (k x)) (e .fst, s ↦ sym (e .snd (refl s))) .fst)

def free_rec_eta (S : Type) (F : FreeGroupSignature S) (T : Type) (h : F .carrier → T)
  : Id (F .carrier → T) (free_rec S F T (free_bouquet S F T h)) h
  ≔ free_maps_equal S F T (free_rec S F T (free_bouquet S F T h)) h (free_rec_beta S F T (free_bouquet S F T h))

{` (B F_S → T) ≃ Σ (t : T) (S → t = t), by evaluation, for every type T. `}
def free_universal_property (S : Type) (F : FreeGroupSignature S) (T : Type)
  : Equiv (F .carrier → T) (BouquetData S T)
  ≔ quasi_inverse_equiv (F .carrier → T) (BouquetData S T)
      (free_bouquet S F T) (free_rec S F T) (free_rec_eta S F T) (free_rec_beta S F T)

{` B F_S is connected (for every type S). `}
def free_merely_based (S : Type) (F : FreeGroupSignature S)
  : (x : F .carrier) → Mere (Id (F .carrier) (F .base) x)
  ≔ free_ind_prop S F (x ↦ Mere (Id (F .carrier) (F .base) x)) (x ↦ mere_isprop (Id (F .carrier) (F .base) x))
      (mere (Id (F .carrier) (F .base) (F .base)) (refl (F .base)))

def free_connected (S : Type) (F : FreeGroupSignature S) : Connected (F .carrier)
  ≔ let X ≔ F .carrier in let m ≔ free_merely_based S F in
    (mere X (F .base),
     x y ↦ mere_rec (Id X (F .base) x) (Mere (Id X x y)) (mere_isprop (Id X x y))
       (p ↦ mere_rec (Id X (F .base) y) (Mere (Id X x y)) (mere_isprop (Id X x y))
         (q ↦ mere (Id X x y) (concat X x (F .base) y (inverse X (F .base) x p) q)) (m y))
       (m x))

{` Pointed universal property ("Hom(F_S, G) ≃ (S → USym G) for every
   ∞-group G", congp.tex:762): pointed maps (B F_S, base) →* (A, a) are
   equivalent to S-indexed loops at a, by evaluation s ↦ Ω f (loop_s). `}
def bouquet_loop_boundary (S : Type) (A : Type) (a x : A) (p : Id A a x) (l : S → Id A x x)
  : Id (BouquetData S A) (a, s ↦ pointed_loop_conjugate A a x p (l s)) (x, l)
  ≔ J A a
      (x p ↦ (l : S → Id A x x) → Id (BouquetData S A) (a, s ↦ pointed_loop_conjugate A a x p (l s)) (x, l))
      (l ↦ (refl a, funext S (_ ↦ Id A a a) (s ↦ pointed_loop_conjugate A a a (refl a) (l s)) l
        (s ↦ loop_conjugate_at_refl A a (l s))))
      x p l

def free_pointed_loop_eval (S : Type) (F : FreeGroupSignature S) (A : Type) (a : A)
  (u : BookPointedMap (free_pointed S F) (A, a)) (s : S) : Id A a a
  ≔ loops_map (free_pointed S F) (A, a) u (F .loop s)

def free_pointed_total_equiv (S : Type) (F : FreeGroupSignature S) (A : Type)
  : Equiv (Σ A (a ↦ BookPointedMap (free_pointed S F) (A, a))) (BouquetData S A)
  ≔ let T ≔ Σ A (a ↦ BookPointedMap (free_pointed S F) (A, a)) in
    equiv_change_map T (BouquetData S A)
      (compose_equiv T (F .carrier → A) (BouquetData S A)
        (pointed_map_chosen_target_equiv (free_pointed S F) A) (free_universal_property S F A))
      (totalize A (a ↦ BookPointedMap (free_pointed S F) (A, a)) (a ↦ S → Id A a a)
        (free_pointed_loop_eval S F A))
      (u ↦ inverse (BouquetData S A) (u .fst, free_pointed_loop_eval S F A (u .fst) (u .snd))
        (free_bouquet S F A (u .snd .fst))
        (bouquet_loop_boundary S A (u .fst) (u .snd .fst (F .base)) (u .snd .snd)
          (s ↦ refl (u .snd .fst) (F .loop s))))

def free_pointed_universal_property (S : Type) (F : FreeGroupSignature S) (A : Type) (a : A)
  : Equiv (BookPointedMap (free_pointed S F) (A, a)) (S → Id A a a)
  ≔ (free_pointed_loop_eval S F A a,
      fiberwise_from_total A (a ↦ BookPointedMap (free_pointed S F) (A, a)) (a ↦ S → Id A a a)
        (free_pointed_loop_eval S F A) (free_pointed_total_equiv S F A .equiv) a)
