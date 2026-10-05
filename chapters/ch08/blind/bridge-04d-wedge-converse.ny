export "bridge-04a-wedge"

{` Converse of bridge_wedge_signature (def:wedge): every wedge signature of
   ours is a blind wedge on the same carrier, constructors and glue.

   The blind induction principle is obtained from ours: the blind boundary b
   is converted by bw_back_boundary, our induction gives f, and the blind
   evaluation of f is b. For this, bw_conv ∘ bw_back = id on the book's path
   datum (b04d_conv_back): bw_back is injective (each step is: transport,
   pathover_inverse at g⁻¹ — left-invertible by
   pathover_inverse_inverse_strong —, the inverse of an equivalence, and
   path inversion), and bw_back ∘ bw_conv = id (bw_back_conv). The two
   functions on A₁ + A₂ (a match and the given one) are identified by funext;
   paths in the Σ-type of the blind boundary over a path of functions are
   computed by b04d_sigma (path induction) and the typal β-rule of funext. `}

def b04d_transport_injective (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (u u' : B x)
  (e : Id (B y) (transport A B x y p u) (transport A B x y p u')) : Id (B x) u u'
  ≔ J A x (y p ↦ (u u' : B x) → Id (B y) (transport A B x y p u) (transport A B x y p u') → Id (B x) u u')
      (u u' e ↦ concat (B x) u (transport A B x x (refl x) u) u'
        (inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u))
        (concat (B x) (transport A B x x (refl x) u) (transport A B x x (refl x) u') u' e (transport_refl A B x u')))
      y p u u' e

def b04d_left_inverse_injective (A B : Type) (f : A → B) (l : B → A) (h : (a : A) → Id A (l (f a)) a)
  (a a' : A) (e : Id B (f a) (f a')) : Id A a a'
  ≔ concat A a (l (f a)) a' (inverse A (l (f a)) a (h a)) (concat A (l (f a)) (l (f a')) a' (refl l e) (h a'))

{` bw_back is injective. `}
def b04d_back_injective (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y)
  (r1 r2 : Id (P x) u (transport X P y x (inverse X x y g) v))
  (e : Id (Id P g u v) (bw_back X P x y g u v r1) (bw_back X P x y g u v r2))
  : Id (Id (P x) u (transport X P y x (inverse X x y g) v)) r1 r2
  ≔ let gi ≔ inverse X x y g in
    let tr ≔ transport X P y x gi v in
    let E ≔ pathover_transport_equiv X P y x gi v u in
    let Ei ≔ equiv_inverse_map (Id P gi v u) (Id (P x) tr u) E in
    let PIp ≔ pathover_inverse X P y x gi v u in
    let L ≔ ((w ↦ transport (Id X y x) (t ↦ Id P t v u) (inverse X x y (inverse X y x gi)) gi (inverse_inverse X y x gi)
                 (pathover_inverse X P x y (inverse X y x gi) u v w)) : Id P (inverse X y x gi) u v → Id P gi v u) in
    let LP ≔ ((w ↦ pathover_transport_equiv (Id X y x) (t ↦ Id P t v u) (inverse X x y (inverse X y x gi)) gi
                  (inverse_inverse X y x gi) (pathover_inverse X P x y (inverse X y x gi) u v (PIp w)) w .map
                  (pathover_inverse_inverse_strong X P y x gi v u w)) : (w : Id P gi v u) → Id (Id P gi v u) (L (PIp w)) w) in
    let i1 ≔ inverse (P x) u tr r1 in let i2 ≔ inverse (P x) u tr r2 in
    let e1 ≔ b04d_transport_injective (Id X x y) (t ↦ Id P t u v) (inverse X y x gi) g (inverse_inverse X x y g)
               (PIp (Ei i1)) (PIp (Ei i2)) e in
    let e2 ≔ b04d_left_inverse_injective (Id P gi v u) (Id P (inverse X y x gi) u v) PIp L LP (Ei i1) (Ei i2) e1 in
    let e3 : Id (Id (P x) tr u) i1 i2
      ≔ concat (Id (P x) tr u) i1 (E .map (Ei i1)) i2
          (inverse (Id (P x) tr u) (E .map (Ei i1)) i1 (equiv_counit (Id P gi v u) (Id (P x) tr u) E i1))
          (concat (Id (P x) tr u) (E .map (Ei i1)) (E .map (Ei i2)) i2 (refl (E .map) e2)
            (equiv_counit (Id P gi v u) (Id (P x) tr u) E i2)) in
    concat (Id (P x) u tr) r1 (inverse (P x) tr u i1) r2
      (inverse (Id (P x) u tr) (inverse (P x) tr u i1) r1 (inverse_inverse (P x) u tr r1))
      (concat (Id (P x) u tr) (inverse (P x) tr u i1) (inverse (P x) tr u i2) r2
        (refl (inverse (P x) tr u) e3) (inverse_inverse (P x) u tr r2))

{` bw_conv ∘ bw_back = id. `}
def b04d_conv_back (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y)
  (r : Id (P x) u (transport X P y x (inverse X x y g) v))
  : Id (Id (P x) u (transport X P y x (inverse X x y g) v)) (bw_conv X P x y g u v (bw_back X P x y g u v r)) r
  ≔ b04d_back_injective X P x y g u v (bw_conv X P x y g u v (bw_back X P x y g u v r)) r
      (bw_back_conv X P x y g u v (bw_back X P x y g u v r))

{` Paths in the blind boundary type over a path of functions on A₁ + A₂. `}
def b04d_K (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type)
  (s s' : (a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 X i1 i2 a))
  (p : Id ((a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 X i1 i2 a)) s s')
  (t : Id (C (i1 (A1 .point))) (s (inl. (A1 .point)))
         (transport X C (i2 (A2 .point)) (i1 (A1 .point)) (inverse X (i1 (A1 .point)) (i2 (A2 .point)) g) (s (inr. (A2 .point)))))
  : Id (C (i1 (A1 .point))) (s' (inl. (A1 .point)))
      (transport X C (i2 (A2 .point)) (i1 (A1 .point)) (inverse X (i1 (A1 .point)) (i2 (A2 .point)) g) (s' (inr. (A2 .point))))
  ≔ let x1 ≔ i1 (A1 .point) in let x2 ≔ i2 (A2 .point) in
    let tr ≔ transport X C x2 x1 (inverse X x1 x2 g) in
    concat (C x1) (s' (inl. (A1 .point))) (s (inl. (A1 .point))) (tr (s' (inr. (A2 .point))))
      (inverse (C x1) (s (inl. (A1 .point))) (s' (inl. (A1 .point))) (p (refl (inl. (A1 .point) : Sum (A1 .carrier) (A2 .carrier)))))
      (concat (C x1) (s (inl. (A1 .point))) (tr (s (inr. (A2 .point)))) (tr (s' (inr. (A2 .point)))) t
        (refl tr (p (refl (inr. (A2 .point) : Sum (A1 .carrier) (A2 .carrier))))))

def b04d_unit (A B : Type) (z : A) (w : B) (tr : B → A) (t : Id A z (tr w))
  : Id (Id A z (tr w)) t (concat A z z (tr w) (inverse A z z (refl z)) (concat A z (tr w) (tr w) t (refl tr (refl w))))
  ≔ concat (Id A z (tr w)) t (concat A z (tr w) (tr w) t (refl (tr w)))
      (concat A z z (tr w) (inverse A z z (refl z)) (concat A z (tr w) (tr w) t (refl (tr w))))
      (inverse (Id A z (tr w)) (concat A z (tr w) (tr w) t (refl (tr w))) t (concat_p1 A z (tr w) t))
      (concat (Id A z (tr w)) (concat A z (tr w) (tr w) t (refl (tr w)))
        (concat A z z (tr w) (refl z) (concat A z (tr w) (tr w) t (refl (tr w))))
        (concat A z z (tr w) (inverse A z z (refl z)) (concat A z (tr w) (tr w) t (refl (tr w))))
        (inverse (Id A z (tr w)) (concat A z z (tr w) (refl z) (concat A z (tr w) (tr w) t (refl (tr w))))
          (concat A z (tr w) (tr w) t (refl (tr w))) (concat_1p A z (tr w) (concat A z (tr w) (tr w) t (refl (tr w)))))
        (refl ((a ↦ concat A z z (tr w) a (concat A z (tr w) (tr w) t (refl (tr w)))) : Id A z z → Id A z (tr w))
          (inverse (Id A z z) (inverse A z z (refl z)) (refl z) (inverse_refl A z))))

{` K along loops that are refl (by given paths) is the identity. `}
def b04d_K_refl (A B : Type) (z : A) (w : B) (tr : B → A) (al : Id A z z) (be : Id B w w)
  (eal : Id (Id A z z) al (refl z)) (ebe : Id (Id B w w) be (refl w)) (t : Id A z (tr w))
  : Id (Id A z (tr w)) (concat A z z (tr w) (inverse A z z al) (concat A z (tr w) (tr w) t (refl tr be))) t
  ≔ concat (Id A z (tr w)) (concat A z z (tr w) (inverse A z z al) (concat A z (tr w) (tr w) t (refl tr be)))
      (concat A z z (tr w) (inverse A z z (refl z)) (concat A z (tr w) (tr w) t (refl tr (refl w)))) t
      (refl ((a b ↦ concat A z z (tr w) (inverse A z z a) (concat A z (tr w) (tr w) t (refl tr b)))
              : Id A z z → Id B w w → Id A z (tr w)) eal ebe)
      (inverse (Id A z (tr w)) t (concat A z z (tr w) (inverse A z z (refl z)) (concat A z (tr w) (tr w) t (refl tr (refl w))))
        (b04d_unit A B z w tr t))

def b04d_sigma (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type)
  (s s' : (a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 X i1 i2 a))
  (p : Id ((a : Sum (A1 .carrier) (A2 .carrier)) → C (blind_wedge_inc A1 A2 X i1 i2 a)) s s')
  (t : Id (C (i1 (A1 .point))) (s (inl. (A1 .point)))
         (transport X C (i2 (A2 .point)) (i1 (A1 .point)) (inverse X (i1 (A1 .point)) (i2 (A2 .point)) g) (s (inr. (A2 .point)))))
  : Id (BlindWedgeBoundary A1 A2 X i1 i2 g C) (s, t) (s', b04d_K A1 A2 X i1 i2 g C s s' p t)
  ≔ let F ≔ ((a ↦ C (blind_wedge_inc A1 A2 X i1 i2 a)) : Sum (A1 .carrier) (A2 .carrier) → Type) in
    let x1 ≔ i1 (A1 .point) in let x2 ≔ i2 (A2 .point) in
    let tr ≔ transport X C x2 x1 (inverse X x1 x2 g) in
    let BB ≔ BlindWedgeBoundary A1 A2 X i1 i2 g C in
    J ((a : Sum (A1 .carrier) (A2 .carrier)) → F a) s
      (s'' p' ↦ (t : Id (C x1) (s (inl. (A1 .point))) (tr (s (inr. (A2 .point)))))
         → Id BB (s, t) (s'', b04d_K A1 A2 X i1 i2 g C s s'' p' t))
      (t ↦ (refl s, b04d_unit (C x1) (C x2) (s (inl. (A1 .point))) (s (inr. (A2 .point))) tr t))
      s' p t

{` From a homotopy h : s1 ~ s whose values at the two base points are refl
   (judgmentally, s1 and s agreeing there), (s1, t) = (s, t). The two uses
   (evaluation, back-and-forth) supply s1, s, h. `}
def b04d_htpy_eval (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type) (f : (x : X) → C x)
  (a : Sum (A1 .carrier) (A2 .carrier))
  : Id (C (blind_wedge_inc A1 A2 X i1 i2 a))
      (bw_to_boundary A1 A2 X i1 i2 g C (wedge_evaluate A1 A2 X i1 i2 g C f) .fst a) (f (blind_wedge_inc A1 A2 X i1 i2 a))
  ≔ match a [ inl. a ↦ refl (f (i1 a)) | inr. a ↦ refl (f (i2 a)) ]

def b04d_htpy_back (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type) (b : BlindWedgeBoundary A1 A2 X i1 i2 g C)
  (a : Sum (A1 .carrier) (A2 .carrier))
  : Id (C (blind_wedge_inc A1 A2 X i1 i2 a))
      (bw_to_boundary A1 A2 X i1 i2 g C (bw_back_boundary A1 A2 X i1 i2 g C b) .fst a) (b .fst a)
  ≔ match a [ inl. a ↦ refl (b .fst (inl. a)) | inr. a ↦ refl (b .fst (inr. a)) ]

{` The blind evaluation of f is the conversion of ours. `}
def b04d_eval (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type) (f : (x : X) → C x)
  : Id (BlindWedgeBoundary A1 A2 X i1 i2 g C) (blind_wedge_evaluate A1 A2 X i1 i2 g C f)
      (bw_to_boundary A1 A2 X i1 i2 g C (wedge_evaluate A1 A2 X i1 i2 g C f))
  ≔ let Dom ≔ Sum (A1 .carrier) (A2 .carrier) in
    let F ≔ ((a ↦ C (blind_wedge_inc A1 A2 X i1 i2 a)) : Dom → Type) in
    let x1 ≔ i1 (A1 .point) in let x2 ≔ i2 (A2 .point) in
    let tr ≔ transport X C x2 x1 (inverse X x1 x2 g) in
    let BB ≔ BlindWedgeBoundary A1 A2 X i1 i2 g C in
    let s1 ≔ bw_to_boundary A1 A2 X i1 i2 g C (wedge_evaluate A1 A2 X i1 i2 g C f) .fst in
    let s ≔ ((a ↦ f (blind_wedge_inc A1 A2 X i1 i2 a)) : (a : Dom) → F a) in
    let h ≔ b04d_htpy_eval A1 A2 X i1 i2 g C f in
    let p ≔ funext Dom F s1 s h in
    let t ≔ bw_conv X C x1 x2 g (f x1) (f x2) (refl f g) in
    inverse BB (s1, t) (s, t)
      (concat BB (s1, t) (s, b04d_K A1 A2 X i1 i2 g C s1 s p t) (s, t)
        (b04d_sigma A1 A2 X i1 i2 g C s1 s p t)
        (refl s, b04d_K_refl (C x1) (C x2) (f x1) (f x2) tr
           (p (refl (inl. (A1 .point) : Dom))) (p (refl (inr. (A2 .point) : Dom)))
           (inverse (Id (C x1) (f x1) (f x1)) (h (inl. (A1 .point))) (p (refl (inl. (A1 .point) : Dom)))
             (funext_beta Dom F s1 s h (inl. (A1 .point))))
           (inverse (Id (C x2) (f x2) (f x2)) (h (inr. (A2 .point))) (p (refl (inr. (A2 .point) : Dom)))
             (funext_beta Dom F s1 s h (inr. (A2 .point))))
           t))

{` Converting back and forth is the identity on blind boundaries. `}
def b04d_to_back (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (C : X → Type) (b : BlindWedgeBoundary A1 A2 X i1 i2 g C)
  : Id (BlindWedgeBoundary A1 A2 X i1 i2 g C) (bw_to_boundary A1 A2 X i1 i2 g C (bw_back_boundary A1 A2 X i1 i2 g C b)) b
  ≔ let Dom ≔ Sum (A1 .carrier) (A2 .carrier) in
    let F ≔ ((a ↦ C (blind_wedge_inc A1 A2 X i1 i2 a)) : Dom → Type) in
    let x1 ≔ i1 (A1 .point) in let x2 ≔ i2 (A2 .point) in
    let tr ≔ transport X C x2 x1 (inverse X x1 x2 g) in
    let BB ≔ BlindWedgeBoundary A1 A2 X i1 i2 g C in
    let u ≔ b .fst (inl. (A1 .point)) in let v ≔ b .fst (inr. (A2 .point)) in
    let s1 ≔ bw_to_boundary A1 A2 X i1 i2 g C (bw_back_boundary A1 A2 X i1 i2 g C b) .fst in
    let s ≔ b .fst in
    let h ≔ b04d_htpy_back A1 A2 X i1 i2 g C b in
    let p ≔ funext Dom F s1 s h in
    let cb ≔ bw_conv X C x1 x2 g u v (bw_back X C x1 x2 g u v (b .snd)) in
    concat BB (s1, cb) (s, cb) b
      (concat BB (s1, cb) (s, b04d_K A1 A2 X i1 i2 g C s1 s p cb) (s, cb)
        (b04d_sigma A1 A2 X i1 i2 g C s1 s p cb)
        (refl s, b04d_K_refl (C x1) (C x2) u v tr
           (p (refl (inl. (A1 .point) : Dom))) (p (refl (inr. (A2 .point) : Dom)))
           (inverse (Id (C x1) u u) (h (inl. (A1 .point))) (p (refl (inl. (A1 .point) : Dom)))
             (funext_beta Dom F s1 s h (inl. (A1 .point))))
           (inverse (Id (C x2) v v) (h (inr. (A2 .point))) (p (refl (inr. (A2 .point) : Dom)))
             (funext_beta Dom F s1 s h (inr. (A2 .point))))
           cb))
      (refl s, b04d_conv_back X C x1 x2 g u v (b .snd))

{` The blind induction principle from ours. `}
def b04d_induction (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (C : W .carrier → Type)
  (b : BlindWedgeBoundary A1 A2 (W .carrier) (W .incl1) (W .incl2) (W .glue) C)
  : Σ ((x : W .carrier) → C x) (f ↦
      Id (BlindWedgeBoundary A1 A2 (W .carrier) (W .incl1) (W .incl2) (W .glue) C)
        (blind_wedge_evaluate A1 A2 (W .carrier) (W .incl1) (W .incl2) (W .glue) C f) b)
  ≔ let X ≔ W .carrier in let i1 ≔ W .incl1 in let i2 ≔ W .incl2 in let g ≔ W .glue in
    let BB ≔ BlindWedgeBoundary A1 A2 X i1 i2 g C in
    let to ≔ bw_to_boundary A1 A2 X i1 i2 g C in
    let d ≔ bw_back_boundary A1 A2 X i1 i2 g C b in
    let r ≔ W .induction C d in
    (r .fst,
     concat BB (blind_wedge_evaluate A1 A2 X i1 i2 g C (r .fst)) (to (wedge_evaluate A1 A2 X i1 i2 g C (r .fst))) b
       (b04d_eval A1 A2 X i1 i2 g C (r .fst))
       (concat BB (to (wedge_evaluate A1 A2 X i1 i2 g C (r .fst))) (to d) b
         (refl to (r .snd)) (b04d_to_back A1 A2 X i1 i2 g C b)))

{` def:wedge: every wedge signature of ours is a blind wedge. `}
def bridge_wedge_signature_converse (A1 A2 : Pointed) (W : WedgeSignature A1 A2) : BlindWedge A1 A2
  ≔ (W .carrier, (i1 ≔ W .incl1, i2 ≔ W .incl2, glue ≔ W .glue, induction ≔ C b ↦ b04d_induction A1 A2 W C b))

{` Round trips on carriers, constructors and glue are refl. `}
def bridge_wedge_converse_roundtrip (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  : Id Pointed (wedge_pointed A1 A2 (bridge_wedge_signature A1 A2 (bridge_wedge_signature_converse A1 A2 W)))
      (wedge_pointed A1 A2 W)
  ≔ refl (wedge_pointed A1 A2 W)

def bridge_wedge_converse_roundtrip_data (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  : Id (Σ Type (Z ↦ Σ (A1 .carrier → Z) (j1 ↦ Σ (A2 .carrier → Z) (j2 ↦ Id Z (j1 (A1 .point)) (j2 (A2 .point))))))
      (let V ≔ bridge_wedge_signature A1 A2 (bridge_wedge_signature_converse A1 A2 W) in
       (V .carrier, (V .incl1, (V .incl2, V .glue))))
      (W .carrier, (W .incl1, (W .incl2, W .glue)))
  ≔ refl ((W .carrier, (W .incl1, (W .incl2, W .glue)))
          : Σ Type (Z ↦ Σ (A1 .carrier → Z) (j1 ↦ Σ (A2 .carrier → Z) (j2 ↦ Id Z (j1 (A1 .point)) (j2 (A2 .point))))))

def bridge_wedge_converse_roundtrip_blind (A1 A2 : Pointed) (W : BlindWedge A1 A2)
  : Id (Σ Type (Z ↦ Σ (A1 .carrier → Z) (j1 ↦ Σ (A2 .carrier → Z) (j2 ↦ Id Z (j1 (A1 .point)) (j2 (A2 .point))))))
      (let V ≔ bridge_wedge_signature_converse A1 A2 (bridge_wedge_signature A1 A2 W) in
       (V .fst, (V .snd .i1, (V .snd .i2, V .snd .glue))))
      (W .fst, (W .snd .i1, (W .snd .i2, W .snd .glue)))
  ≔ refl ((W .fst, (W .snd .i1, (W .snd .i2, W .snd .glue)))
          : Σ Type (Z ↦ Σ (A1 .carrier → Z) (j1 ↦ Σ (A2 .carrier → Z) (j2 ↦ Id Z (j1 (A1 .point)) (j2 (A2 .point))))))
