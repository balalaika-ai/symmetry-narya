export "644-wild-precategory-of-wild-precategories"
import "280-book-equivalence-maps"

{` Chapter 6, xca:wildprecat-of-wildprecats, preparation for the pentagon
   in the general wild case (module 693). A strictly associative model of
   wild functors: the functor laws are stored in Yoneda form, as maps
   sending a path u = id_a (resp. u = g ∘ f) to a path F(u) = id_{F a}
   (resp. F(u) = F g ∘ F f). Composition of such "Yoneda wild functors"
   is composition of functions, so it is associative on the nose. The
   Yoneda lemma for paths into a point makes the comparison map from wild
   functors an equivalence, and it turns composition of wild functors into
   composition of Yoneda wild functors up to an explicit identification. `}

{` Path induction for paths into a fixed point, derived from J. `}
def ywf_J_left (A : Type) (x : A) (P : (u : A) → Id A u x → Type) (d : P x (refl x)) (u : A) (t : Id A u x)
  : P u t
  ≔ transport (Id A u x) (P u) (inverse A x u (inverse A u x t)) t (inverse_inverse A u x t)
      (J A x (v s ↦ P v (inverse A x v s))
        (transport (Id A x x) (P x) (refl x) (inverse A x x (refl x))
          (inverse (Id A x x) (inverse A x x (refl x)) (refl x) (inverse_refl A x)) d)
        u (inverse A u x t))

{` The Yoneda lemma for paths into x: a map φ out of the paths into x is
   determined by φ x refl. `}
def ywf_yoneda (A B : Type) (m : A → B) (x : A) (y : B) (φ : (u : A) → Id A u x → Id B (m u) y)
  (u : A) (t : Id A u x)
  : Id (Id B (m u) y) (concat B (m u) (m x) y (refl m t) (φ x (refl x))) (φ u t)
  ≔ ywf_J_left A x (v s ↦ Id (Id B (m v) y) (concat B (m v) (m x) y (refl m s) (φ x (refl x))) (φ v s))
      (concat_1p B (m x) y (φ x (refl x))) u t

def YonedaWildFunctor (C D : WildPrecat) : Type ≔ sig (
  yobj : C .ob → D .ob,
  ymor : (a b : C .ob) → C .hom a b → D .hom (yobj a) (yobj b),
  yid : (a : C .ob) (u : C .hom a a) → Id (C .hom a a) u (C .idn a)
    → Id (D .hom (yobj a) (yobj a)) (ymor a a u) (D .idn (yobj a)),
  ycomp : (a b c : C .ob) (f : C .hom a b) (g : C .hom b c) (u : C .hom a c)
    → Id (C .hom a c) u (C .comp a b c g f)
    → Id (D .hom (yobj a) (yobj c)) (ymor a c u) (D .comp (yobj a) (yobj b) (yobj c) (ymor b c g) (ymor a b f)) )

def yoneda_wild_functor_compose (C D E : WildPrecat) (G : YonedaWildFunctor D E) (F : YonedaWildFunctor C D)
  : YonedaWildFunctor C E
  ≔ (yobj ≔ x ↦ G .yobj (F .yobj x),
     ymor ≔ a b f ↦ G .ymor (F .yobj a) (F .yobj b) (F .ymor a b f),
     yid ≔ a u t ↦ G .yid (F .yobj a) (F .ymor a a u) (F .yid a u t),
     ycomp ≔ a b c f g u t ↦ G .ycomp (F .yobj a) (F .yobj b) (F .yobj c) (F .ymor a b f) (F .ymor b c g)
       (F .ymor a c u) (F .ycomp a b c f g u t))

{` Litmus: composition of Yoneda wild functors is associative by refl. `}
def yoneda_wild_functor_assoc (C0 C1 C2 C3 : WildPrecat) (F : YonedaWildFunctor C0 C1)
  (G : YonedaWildFunctor C1 C2) (H : YonedaWildFunctor C2 C3)
  : Id (YonedaWildFunctor C0 C3)
      (yoneda_wild_functor_compose C0 C2 C3 H (yoneda_wild_functor_compose C0 C1 C2 G F))
      (yoneda_wild_functor_compose C0 C1 C3 (yoneda_wild_functor_compose C1 C2 C3 H G) F)
  ≔ refl (yoneda_wild_functor_compose C0 C2 C3 H (yoneda_wild_functor_compose C0 C1 C2 G F))

{` The comparison map Φ and its inverse. `}
def wild_functor_yoneda (C D : WildPrecat) (F : WildFunctor C D) : YonedaWildFunctor C D
  ≔ (yobj ≔ F .obj,
     ymor ≔ F .mor,
     yid ≔ a u t ↦ concat (D .hom (F .obj a) (F .obj a)) (F .mor a a u) (F .mor a a (C .idn a))
       (D .idn (F .obj a)) (refl (F .mor a a) t) (F .map_id a),
     ycomp ≔ a b c f g u t ↦ concat (D .hom (F .obj a) (F .obj c)) (F .mor a c u)
       (F .mor a c (C .comp a b c g f))
       (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f))
       (refl (F .mor a c) t) (F .map_comp a b c f g))

def yoneda_wild_functor (C D : WildPrecat) (Y : YonedaWildFunctor C D) : WildFunctor C D
  ≔ (obj ≔ Y .yobj,
     mor ≔ Y .ymor,
     map_id ≔ a ↦ Y .yid a (C .idn a) (refl (C .idn a)),
     map_comp ≔ a b c f g ↦ Y .ycomp a b c f g (C .comp a b c g f) (refl (C .comp a b c g f)))

{` Ψ(Φ F) is F ∘ id on the nose, so ρ is the retraction. `}
def yoneda_wild_functor_retraction (C D : WildPrecat) (F : WildFunctor C D)
  : Id (WildFunctor C D) (yoneda_wild_functor C D (wild_functor_yoneda C D F)) F
  ≔ functor_right_unit C D F

def yoneda_wild_functor_section (C D : WildPrecat) (Y : YonedaWildFunctor C D)
  : Id (YonedaWildFunctor C D) (wild_functor_yoneda C D (yoneda_wild_functor C D Y)) Y
  ≔ let Z ≔ wild_functor_yoneda C D (yoneda_wild_functor C D Y) in
    (yobj ≔ refl (Y .yobj),
     ymor ≔ refl (Y .ymor),
     yid ≔ funext3 (C .ob) (a ↦ C .hom a a) (a u ↦ Id (C .hom a a) u (C .idn a))
       (a u t ↦ Id (D .hom (Y .yobj a) (Y .yobj a)) (Y .ymor a a u) (D .idn (Y .yobj a)))
       (Z .yid) (Y .yid)
       (a u t ↦ ywf_yoneda (C .hom a a) (D .hom (Y .yobj a) (Y .yobj a)) (Y .ymor a a) (C .idn a)
         (D .idn (Y .yobj a)) (Y .yid a) u t),
     ycomp ≔ funext3 (C .ob) (_ ↦ C .ob) (_ _ ↦ C .ob)
       (a b c ↦ (f : C .hom a b) (g : C .hom b c) (u : C .hom a c) (t : Id (C .hom a c) u (C .comp a b c g f))
         → Id (D .hom (Y .yobj a) (Y .yobj c)) (Y .ymor a c u)
             (D .comp (Y .yobj a) (Y .yobj b) (Y .yobj c) (Y .ymor b c g) (Y .ymor a b f)))
       (Z .ycomp) (Y .ycomp)
       (a b c ↦ funext2 (C .hom a b) (_ ↦ C .hom b c)
         (f g ↦ (u : C .hom a c) (t : Id (C .hom a c) u (C .comp a b c g f))
           → Id (D .hom (Y .yobj a) (Y .yobj c)) (Y .ymor a c u)
               (D .comp (Y .yobj a) (Y .yobj b) (Y .yobj c) (Y .ymor b c g) (Y .ymor a b f)))
         (Z .ycomp a b c) (Y .ycomp a b c)
         (f g ↦ funext2 (C .hom a c) (u ↦ Id (C .hom a c) u (C .comp a b c g f))
           (u t ↦ Id (D .hom (Y .yobj a) (Y .yobj c)) (Y .ymor a c u)
             (D .comp (Y .yobj a) (Y .yobj b) (Y .yobj c) (Y .ymor b c g) (Y .ymor a b f)))
           (Z .ycomp a b c f g) (Y .ycomp a b c f g)
           (u t ↦ ywf_yoneda (C .hom a c) (D .hom (Y .yobj a) (Y .yobj c)) (Y .ymor a c) (C .comp a b c g f)
             (D .comp (Y .yobj a) (Y .yobj b) (Y .yobj c) (Y .ymor b c g) (Y .ymor a b f))
             (Y .ycomp a b c f g) u t))))

def wild_functor_yoneda_equiv (C D : WildPrecat) : Equiv (WildFunctor C D) (YonedaWildFunctor C D)
  ≔ quasi_inverse_equiv (WildFunctor C D) (YonedaWildFunctor C D) (wild_functor_yoneda C D)
      (yoneda_wild_functor C D) (yoneda_wild_functor_retraction C D) (yoneda_wild_functor_section C D)

{` Φ is an equivalence, so ap Φ is an equivalence on paths. `}
def wild_functor_yoneda_paths (C D : WildPrecat) (F F' : WildFunctor C D)
  : BookEquiv (Id (WildFunctor C D) F F')
      (Id (YonedaWildFunctor C D) (wild_functor_yoneda C D F) (wild_functor_yoneda C D F'))
  ≔ embedding_on_paths (WildFunctor C D) (YonedaWildFunctor C D) (wild_functor_yoneda C D)
      (book_isequiv_embedding (WildFunctor C D) (YonedaWildFunctor C D) (wild_functor_yoneda C D)
        (book_equivalence (WildFunctor C D) (YonedaWildFunctor C D) (wild_functor_yoneda_equiv C D) .equiv))
      F F'

{` The maps of a book equivalence are injective. `}
def ywf_book_equiv_injective (A B : Type) (e : BookEquiv A B) (x y : A) (h : Id B (e .map x) (e .map y))
  : Id A x y
  ≔ let c ≔ e .equiv (e .map y) in
    let u : BookFiber A B (e .map) (e .map y) ≔ (x, inverse B (e .map x) (e .map y) h) in
    let v : BookFiber A B (e .map) (e .map y) ≔ (y, refl (e .map y)) in
    refl ((z ↦ z .fst) : BookFiber A B (e .map) (e .map y) → A)
      (concat (BookFiber A B (e .map) (e .map y)) u (c .center) v
        (inverse (BookFiber A B (e .map) (e .map y)) (c .center) u (c .contract u)) (c .contract v))

{` μ : Φ G ∘ Φ F = Φ (G ∘ F), from ap h (p · q) · r = ap h p · (ap h q · r). `}
def wild_functor_yoneda_compose (C D E : WildPrecat) (G : WildFunctor D E) (F : WildFunctor C D)
  : Id (YonedaWildFunctor C E)
      (yoneda_wild_functor_compose C D E (wild_functor_yoneda D E G) (wild_functor_yoneda C D F))
      (wild_functor_yoneda C E (functor_compose C D E G F))
  ≔ let L ≔ yoneda_wild_functor_compose C D E (wild_functor_yoneda D E G) (wild_functor_yoneda C D F) in
    let R ≔ wild_functor_yoneda C E (functor_compose C D E G F) in
    let o ≔ (x ↦ G .obj (F .obj x)) : C .ob → E .ob in
    (yobj ≔ refl (R .yobj),
     ymor ≔ refl (R .ymor),
     yid ≔ funext3 (C .ob) (a ↦ C .hom a a) (a u ↦ Id (C .hom a a) u (C .idn a))
       (a u t ↦ Id (E .hom (o a) (o a)) (R .ymor a a u) (E .idn (o a)))
       (L .yid) (R .yid)
       (a u t ↦ ch6c_ap_concat_assoc (D .hom (F .obj a) (F .obj a)) (E .hom (o a) (o a))
         (G .mor (F .obj a) (F .obj a)) (F .mor a a u) (F .mor a a (C .idn a)) (D .idn (F .obj a))
         (E .idn (o a)) (refl (F .mor a a) t) (F .map_id a) (G .map_id (F .obj a))),
     ycomp ≔ funext3 (C .ob) (_ ↦ C .ob) (_ _ ↦ C .ob)
       (a b c ↦ (f : C .hom a b) (g : C .hom b c) (u : C .hom a c) (t : Id (C .hom a c) u (C .comp a b c g f))
         → Id (E .hom (o a) (o c)) (R .ymor a c u)
             (E .comp (o a) (o b) (o c) (R .ymor b c g) (R .ymor a b f)))
       (L .ycomp) (R .ycomp)
       (a b c ↦ funext2 (C .hom a b) (_ ↦ C .hom b c)
         (f g ↦ (u : C .hom a c) (t : Id (C .hom a c) u (C .comp a b c g f))
           → Id (E .hom (o a) (o c)) (R .ymor a c u)
               (E .comp (o a) (o b) (o c) (R .ymor b c g) (R .ymor a b f)))
         (L .ycomp a b c) (R .ycomp a b c)
         (f g ↦ funext2 (C .hom a c) (u ↦ Id (C .hom a c) u (C .comp a b c g f))
           (u t ↦ Id (E .hom (o a) (o c)) (R .ymor a c u)
             (E .comp (o a) (o b) (o c) (R .ymor b c g) (R .ymor a b f)))
           (L .ycomp a b c f g) (R .ycomp a b c f g)
           (u t ↦
             let Fa ≔ F .obj a in let Fb ≔ F .obj b in let Fc ≔ F .obj c in
             ch6c_ap_concat_assoc (D .hom Fa Fc) (E .hom (o a) (o c)) (G .mor Fa Fc)
               (F .mor a c u) (F .mor a c (C .comp a b c g f))
               (D .comp Fa Fb Fc (F .mor b c g) (F .mor a b f))
               (E .comp (o a) (o b) (o c) (R .ymor b c g) (R .ymor a b f))
               (refl (F .mor a c) t) (F .map_comp a b c f g)
               (G .map_comp Fa Fb Fc (F .mor a b f) (F .mor b c g))))))
