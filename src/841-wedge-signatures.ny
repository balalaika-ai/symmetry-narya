export "840-pushout-signatures"

{` def:wedge (congp.tex:522).  The wedge of pointed types (A1, a1) and
   (A2, a2) is the higher inductive type with i1 : A1 → A1∨A2,
   i2 : A2 → A1∨A2 and g : i1 a1 = i2 a2, pointed at a12 ≔ i1 a1.

   As for pushouts (module 840), a WedgeSignature is a PARAMETER recording
   the constructors and the dependent eliminator; the computation laws
   (point laws for i1, i2 and the path law for g) form one identification of
   boundary data, not judgmental equalities.  The book's displayed induction
   principle asks for s : Π_{a : A1+A2} C(i a) and s(a1) = C(g⁻¹) s(a2); here
   the latter is the equivalent dependent path over g (wedge_book_boundary_equiv).
   wedge_from_pushout shows that a pushout of the span A1 ← 1 → A2 is a
   wedge. `}

def WedgeBoundary (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) : Type
  ≔ Σ ((a : A1 .carrier) → P (i1 a)) (s1 ↦ Σ ((a : A2 .carrier) → P (i2 a)) (s2 ↦
      Id P g (s1 (A1 .point)) (s2 (A2 .point))))

def wedge_evaluate (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (h : (x : X) → P x)
  : WedgeBoundary A1 A2 X i1 i2 g P
  ≔ (a ↦ h (i1 a), (a ↦ h (i2 a), refl h g))

def WedgeSignature (A1 A2 : Pointed) : Type ≔ sig (
  carrier : Type,
  incl1 : A1 .carrier → carrier,
  incl2 : A2 .carrier → carrier,
  glue : Id carrier (incl1 (A1 .point)) (incl2 (A2 .point)),
  induction : (P : carrier → Type) (d : WedgeBoundary A1 A2 carrier incl1 incl2 glue P)
    → Σ ((x : carrier) → P x) (h ↦
        Id (WedgeBoundary A1 A2 carrier incl1 incl2 glue P)
          (wedge_evaluate A1 A2 carrier incl1 incl2 glue P h) d))

{` The pointed type (A1 ∨ A2, a12), a12 ≔ i1 a1. `}
def wedge_point (A1 A2 : Pointed) (W : WedgeSignature A1 A2) : W .carrier ≔ W .incl1 (A1 .point)

def wedge_pointed (A1 A2 : Pointed) (W : WedgeSignature A1 A2) : Pointed
  ≔ (W .carrier, W .incl1 (A1 .point))

{` The structure maps as pointed maps (book orientation pt = f(pt)):
   i1 is pointed by refl, i2 by the glue g : a12 = i2 a2. `}
def wedge_incl1_pointed (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  : BookPointedMap A1 (wedge_pointed A1 A2 W)
  ≔ (W .incl1, refl (W .incl1 (A1 .point)))

def wedge_incl2_pointed (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  : BookPointedMap A2 (wedge_pointed A1 A2 W)
  ≔ (W .incl2, W .glue)

{` i1^g ≔ i1 on loops, and i2^g(p) ≔ g⁻¹ i2(p) g (first g, then i2 p, then
   g⁻¹), which is Ω of the pointed map (i2, g) (def:loops-map). `}
def wedge_loop1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p : Loop A1)
  : Loop (wedge_pointed A1 A2 W)
  ≔ refl (W .incl1) p

def wedge_loop2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p : Loop A2)
  : Loop (wedge_pointed A1 A2 W)
  ≔ concat (W .carrier) (W .incl1 (A1 .point)) (W .incl2 (A2 .point)) (W .incl1 (A1 .point)) (W .glue)
      (concat (W .carrier) (W .incl2 (A2 .point)) (W .incl2 (A2 .point)) (W .incl1 (A1 .point))
        (refl (W .incl2) p)
        (inverse (W .carrier) (W .incl1 (A1 .point)) (W .incl2 (A2 .point)) (W .glue)))

def wedge_loop2_loops_map (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p : Loop A2)
  : Id (Loop (wedge_pointed A1 A2 W)) (wedge_loop2 A1 A2 W p)
      (loops_map A2 (wedge_pointed A1 A2 W) (wedge_incl2_pointed A1 A2 W) p)
  ≔ refl (wedge_loop2 A1 A2 W p)

def wedge_loop1_loops_map (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p : Loop A1)
  : Id (Loop (wedge_pointed A1 A2 W)) (wedge_loop1 A1 A2 W p)
      (loops_map A1 (wedge_pointed A1 A2 W) (wedge_incl1_pointed A1 A2 W) p)
  ≔ inverse (Loop (wedge_pointed A1 A2 W))
      (loops_map A1 (wedge_pointed A1 A2 W) (wedge_incl1_pointed A1 A2 W) p) (wedge_loop1 A1 A2 W p)
      (loop_conjugate_at_refl (W .carrier) (W .incl1 (A1 .point)) (refl (W .incl1) p))

{` Induction and its laws. `}
def wedge_boundary (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type) : Type
  ≔ WedgeBoundary A1 A2 (W .carrier) (W .incl1) (W .incl2) (W .glue) P

def wedge_eval (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (h : (x : W .carrier) → P x) : wedge_boundary A1 A2 W P
  ≔ wedge_evaluate A1 A2 (W .carrier) (W .incl1) (W .incl2) (W .glue) P h

def wedge_ind (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (d : wedge_boundary A1 A2 W P) : (x : W .carrier) → P x
  ≔ W .induction P d .fst

def wedge_ind_beta (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (d : wedge_boundary A1 A2 W P)
  : Id (wedge_boundary A1 A2 W P) (wedge_eval A1 A2 W P (wedge_ind A1 A2 W P d)) d
  ≔ W .induction P d .snd

def wedge_ind_incl1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (d : wedge_boundary A1 A2 W P) (a : A1 .carrier)
  : Id (P (W .incl1 a)) (wedge_ind A1 A2 W P d (W .incl1 a)) (d .fst a)
  ≔ wedge_ind_beta A1 A2 W P d .fst (refl a)

def wedge_ind_incl2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (d : wedge_boundary A1 A2 W P) (a : A2 .carrier)
  : Id (P (W .incl2 a)) (wedge_ind A1 A2 W P d (W .incl2 a)) (d .snd .fst a)
  ≔ wedge_ind_beta A1 A2 W P d .snd .fst (refl a)

def wedge_sections_equal (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (h k : (x : W .carrier) → P x)
  (e : Id (wedge_boundary A1 A2 W P) (wedge_eval A1 A2 W P h) (wedge_eval A1 A2 W P k))
  : Id ((x : W .carrier) → P x) h k
  ≔ funext (W .carrier) P h k
      (W .induction (x ↦ Id (P x) (h x) (k x))
        (a ↦ e .fst (refl a), (a ↦ e .snd .fst (refl a), sym (e .snd .snd))) .fst)

def wedge_ind_eta (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (h : (x : W .carrier) → P x)
  : Id ((x : W .carrier) → P x) (wedge_ind A1 A2 W P (wedge_eval A1 A2 W P h)) h
  ≔ wedge_sections_equal A1 A2 W P (wedge_ind A1 A2 W P (wedge_eval A1 A2 W P h)) h
      (wedge_ind_beta A1 A2 W P (wedge_eval A1 A2 W P h))

def wedge_dependent_universal_property (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (P : W .carrier → Type)
  : Equiv ((x : W .carrier) → P x) (wedge_boundary A1 A2 W P)
  ≔ quasi_inverse_equiv ((x : W .carrier) → P x) (wedge_boundary A1 A2 W P)
      (wedge_eval A1 A2 W P) (wedge_ind A1 A2 W P) (wedge_ind_eta A1 A2 W P) (wedge_ind_beta A1 A2 W P)

def wedge_ind_prop (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  (hP : (x : W .carrier) → isProp (P x))
  (s1 : (a : A1 .carrier) → P (W .incl1 a)) (s2 : (a : A2 .carrier) → P (W .incl2 a))
  : (x : W .carrier) → P x
  ≔ W .induction P
      (s1, (s2, pathover_of_eq (W .carrier) P (W .incl1 (A1 .point)) (W .incl2 (A2 .point)) (W .glue)
        (s1 (A1 .point)) (s2 (A2 .point))
        (hP (W .incl2 (A2 .point))
          (transport (W .carrier) P (W .incl1 (A1 .point)) (W .incl2 (A2 .point)) (W .glue) (s1 (A1 .point)))
          (s2 (A2 .point))))) .fst

{` The book's form of the path datum: s(a1) = C(g⁻¹)(s(a2)), i.e. transport
   backwards along g, is equivalent to a dependent path over g. `}
def pathover_backward_equiv (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y)
  : Equiv (Id P g u v) (Id (P x) u (transport X P y x (inverse X x y g) v))
  ≔ J X x (y g ↦ (v : P y) → Equiv (Id P g u v) (Id (P x) u (transport X P y x (inverse X x y g) v)))
      (v ↦ id_to_equiv (Id (P x) u v) (Id (P x) u (transport X P x x (inverse X x x (refl x)) v))
        (refl ((w ↦ Id (P x) u w) : P x → Type)
          (inverse (P x) (transport X P x x (inverse X x x (refl x)) v) v
            (concat (P x) (transport X P x x (inverse X x x (refl x)) v) (transport X P x x (refl x) v) v
              (transport2 X P x x (inverse X x x (refl x)) (refl x) (inverse_refl X x) v)
              (transport_refl X P x v)))))
      y g v

def WedgeBookBoundary (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type) : Type
  ≔ Σ ((a : A1 .carrier) → P (W .incl1 a)) (s1 ↦ Σ ((a : A2 .carrier) → P (W .incl2 a)) (s2 ↦
      Id (P (W .incl1 (A1 .point))) (s1 (A1 .point))
        (transport (W .carrier) P (W .incl2 (A2 .point)) (W .incl1 (A1 .point))
          (inverse (W .carrier) (W .incl1 (A1 .point)) (W .incl2 (A2 .point)) (W .glue)) (s2 (A2 .point)))))

def wedge_book_boundary_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (P : W .carrier → Type)
  : Equiv (wedge_boundary A1 A2 W P) (WedgeBookBoundary A1 A2 W P)
  ≔ let X ≔ W .carrier in let x ≔ W .incl1 (A1 .point) in let y ≔ W .incl2 (A2 .point) in
    family_equiv ((a : A1 .carrier) → P (W .incl1 a))
      (s1 ↦ Σ ((a : A2 .carrier) → P (W .incl2 a)) (s2 ↦ Id P (W .glue) (s1 (A1 .point)) (s2 (A2 .point))))
      (s1 ↦ Σ ((a : A2 .carrier) → P (W .incl2 a)) (s2 ↦
        Id (P x) (s1 (A1 .point)) (transport X P y x (inverse X x y (W .glue)) (s2 (A2 .point)))))
      (s1 ↦ family_equiv ((a : A2 .carrier) → P (W .incl2 a))
        (s2 ↦ Id P (W .glue) (s1 (A1 .point)) (s2 (A2 .point)))
        (s2 ↦ Id (P x) (s1 (A1 .point)) (transport X P y x (inverse X x y (W .glue)) (s2 (A2 .point))))
        (s2 ↦ pathover_backward_equiv X P x y (W .glue) (s1 (A1 .point)) (s2 (A2 .point))))

{` Nondependent data: cocones (f1, f2, f1 a1 = f2 a2). `}
def WedgeCocone (A1 A2 : Pointed) (T : Type) : Type
  ≔ Σ (A1 .carrier → T) (f1 ↦ Σ (A2 .carrier → T) (f2 ↦ Id T (f1 (A1 .point)) (f2 (A2 .point))))

def wedge_cocone (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (h : W .carrier → T)
  : WedgeCocone A1 A2 T
  ≔ (a ↦ h (W .incl1 a), (a ↦ h (W .incl2 a), refl h (W .glue)))

def wedge_rec (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (d : WedgeCocone A1 A2 T)
  : W .carrier → T
  ≔ W .induction (_ ↦ T) d .fst

def wedge_rec_beta (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (d : WedgeCocone A1 A2 T)
  : Id (WedgeCocone A1 A2 T) (wedge_cocone A1 A2 W T (wedge_rec A1 A2 W T d)) d
  ≔ W .induction (_ ↦ T) d .snd

def wedge_rec_incl1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (d : WedgeCocone A1 A2 T)
  (a : A1 .carrier) : Id T (wedge_rec A1 A2 W T d (W .incl1 a)) (d .fst a)
  ≔ wedge_rec_beta A1 A2 W T d .fst (refl a)

def wedge_rec_incl2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (d : WedgeCocone A1 A2 T)
  (a : A2 .carrier) : Id T (wedge_rec A1 A2 W T d (W .incl2 a)) (d .snd .fst a)
  ≔ wedge_rec_beta A1 A2 W T d .snd .fst (refl a)

def wedge_maps_equal (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (h k : W .carrier → T)
  (e : Id (WedgeCocone A1 A2 T) (wedge_cocone A1 A2 W T h) (wedge_cocone A1 A2 W T k))
  : Id (W .carrier → T) h k
  ≔ funext (W .carrier) (_ ↦ T) h k
      (W .induction (x ↦ Id T (h x) (k x))
        (a ↦ e .fst (refl a), (a ↦ e .snd .fst (refl a), sym (e .snd .snd))) .fst)

def wedge_rec_eta (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type) (h : W .carrier → T)
  : Id (W .carrier → T) (wedge_rec A1 A2 W T (wedge_cocone A1 A2 W T h)) h
  ≔ wedge_maps_equal A1 A2 W T (wedge_rec A1 A2 W T (wedge_cocone A1 A2 W T h)) h
      (wedge_rec_beta A1 A2 W T (wedge_cocone A1 A2 W T h))

{` Unpointed universal property: (A1∨A2 → T) ≃ cocones, by evaluation. `}
def wedge_universal_property (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  : Equiv (W .carrier → T) (WedgeCocone A1 A2 T)
  ≔ quasi_inverse_equiv (W .carrier → T) (WedgeCocone A1 A2 T)
      (wedge_cocone A1 A2 W T) (wedge_rec A1 A2 W T) (wedge_rec_eta A1 A2 W T) (wedge_rec_beta A1 A2 W T)

{` The wedge of connected types is connected (proof of lem:wedgeofgpoidisgpoid,
   first sentence): every point is merely connected to a12. `}
def wedge_merely_based (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier))
  : (x : W .carrier) → Mere (Id (W .carrier) (W .incl1 (A1 .point)) x)
  ≔ let X ≔ W .carrier in let a12 ≔ W .incl1 (A1 .point) in
    wedge_ind_prop A1 A2 W (x ↦ Mere (Id X a12 x)) (x ↦ mere_isprop (Id X a12 x))
      (a ↦ mere_rec (Id (A1 .carrier) (A1 .point) a) (Mere (Id X a12 (W .incl1 a)))
        (mere_isprop (Id X a12 (W .incl1 a)))
        (p ↦ mere (Id X a12 (W .incl1 a)) (refl (W .incl1) p))
        (h1 .snd (A1 .point) a))
      (a ↦ mere_rec (Id (A2 .carrier) (A2 .point) a) (Mere (Id X a12 (W .incl2 a)))
        (mere_isprop (Id X a12 (W .incl2 a)))
        (p ↦ mere (Id X a12 (W .incl2 a))
          (concat X a12 (W .incl2 (A2 .point)) (W .incl2 a) (W .glue) (refl (W .incl2) p)))
        (h2 .snd (A2 .point) a))

def wedge_connected (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier))
  : Connected (W .carrier)
  ≔ let X ≔ W .carrier in let a12 ≔ W .incl1 (A1 .point) in
    let m ≔ wedge_merely_based A1 A2 W h1 h2 in
    (mere X a12,
     x y ↦ mere_rec (Id X a12 x) (Mere (Id X x y)) (mere_isprop (Id X x y))
       (p ↦ mere_rec (Id X a12 y) (Mere (Id X x y)) (mere_isprop (Id X x y))
         (q ↦ mere (Id X x y) (concat X x a12 y (inverse X a12 x p) q)) (m y))
       (m x))

{` A pushout of the span A1 ← 1 → A2 (the base points) is a wedge. `}
def wedge_pushout_boundary (A1 A2 : Pointed)
  (P : PushoutSignature (A1 .carrier) (A2 .carrier) Unit (_ ↦ A1 .point) (_ ↦ A2 .point))
  (Q : P .carrier → Type)
  (d : PushoutBoundary (A1 .carrier) (A2 .carrier) Unit (_ ↦ A1 .point) (_ ↦ A2 .point)
    (P .carrier) (P .incl_left) (P .incl_right) (P .glue) Q)
  : WedgeBoundary A1 A2 (P .carrier) (P .incl_left) (P .incl_right) (P .glue star.) Q
  ≔ (d .fst, (d .snd .fst, d .snd .snd star.))

def pushout_wedge_boundary (A1 A2 : Pointed)
  (P : PushoutSignature (A1 .carrier) (A2 .carrier) Unit (_ ↦ A1 .point) (_ ↦ A2 .point))
  (Q : P .carrier → Type)
  (d : WedgeBoundary A1 A2 (P .carrier) (P .incl_left) (P .incl_right) (P .glue star.) Q)
  : PushoutBoundary (A1 .carrier) (A2 .carrier) Unit (_ ↦ A1 .point) (_ ↦ A2 .point)
    (P .carrier) (P .incl_left) (P .incl_right) (P .glue) Q
  ≔ (d .fst, (d .snd .fst, u ↦ match u [ star. ↦ d .snd .snd ]))

def wedge_from_pushout (A1 A2 : Pointed)
  (P : PushoutSignature (A1 .carrier) (A2 .carrier) Unit (_ ↦ A1 .point) (_ ↦ A2 .point))
  : WedgeSignature A1 A2
  ≔ (P .carrier, P .incl_left, P .incl_right, P .glue star.,
     Q d ↦ (P .induction Q (pushout_wedge_boundary A1 A2 P Q d) .fst,
       refl (wedge_pushout_boundary A1 A2 P Q) (P .induction Q (pushout_wedge_boundary A1 A2 P Q d) .snd)))
