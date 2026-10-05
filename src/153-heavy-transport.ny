export "152-inductive-universal-properties"

{` sec:heavy-transport. The book composes q·p = concat p q. `}

{` def:function-type-families `}
def FunctionFamily (X : Type) (Y Z : X → Type) : X → Type ≔ x ↦ (Y x → Z x)

{` lem:trp-in-function-type `}
def transport_function_family (X : Type) (Y Z : X → Type) (x x' : X) (e : Id X x x')
  (f : Y x → Z x) (y' : Y x')
  : Id (Z x') (transport X (FunctionFamily X Y Z) x x' e f y')
      (transport X Z x x' e (f (transport X Y x' x (inverse X x x' e) y')))
  ≔ J X x
      (x' e ↦ (y' : Y x') → Id (Z x') (transport X (FunctionFamily X Y Z) x x' e f y')
        (transport X Z x x' e (f (transport X Y x' x (inverse X x x' e) y'))))
      (y ↦ calc
        transport X (FunctionFamily X Y Z) x x (refl x) f y
        = f y by refl ((φ ↦ φ y) : (Y x → Z x) → Z x) (transport_refl X (FunctionFamily X Y Z) x f)
        = f (transport X Y x x (refl x) y)
          by refl f (inverse (Y x) (transport X Y x x (refl x) y) y (transport_refl X Y x y))
        = f (transport X Y x x (inverse X x x (refl x)) y)
          by refl ((r ↦ f (transport X Y x x r y)) : Id X x x → Z x)
            (inverse (Id X x x) (inverse X x x (refl x)) (refl x) (inverse_refl X x))
        = transport X Z x x (refl x) (f (transport X Y x x (inverse X x x (refl x)) y))
          by inverse (Z x) (transport X Z x x (refl x) (f (transport X Y x x (inverse X x x (refl x)) y)))
            (f (transport X Y x x (inverse X x x (refl x)) y))
            (transport_refl X Z x (f (transport X Y x x (inverse X x x (refl x)) y))) ∎) x' e y'

{` The special case after lem:trp-in-function-type: transport of an
   endomorphism along ua(g) is conjugation by g. `}
def transport_inverse_ua (A B : Type) (g : Equiv A B) (y : B)
  : Id A (transport Type (T ↦ T) B A (inverse Type A B (ua A B g)) y) (equiv_inverse_map A B g y)
  ≔ calc
      transport Type (T ↦ T) B A (inverse Type A B (ua A B g)) y
      = transport Type (T ↦ T) B A (inverse Type A B (ua A B g)) (g .map (equiv_inverse_map A B g y))
        by refl (transport Type (T ↦ T) B A (inverse Type A B (ua A B g)))
          (inverse B (g .map (equiv_inverse_map A B g y)) y (equiv_counit A B g y))
      = equiv_inverse_map A B g y
        by transport_inverse_roundtrip Type (T ↦ T) A B (ua A B g) (equiv_inverse_map A B g y) ∎

def transport_endomorphism_ua (A B : Type) (g : Equiv A B) (f : A → A)
  : Id (B → B) (transport Type (T ↦ T → T) A B (ua A B g) f)
      (y ↦ g .map (f (equiv_inverse_map A B g y)))
  ≔ funext B (_ ↦ B) (transport Type (T ↦ T → T) A B (ua A B g) f)
      (y ↦ g .map (f (equiv_inverse_map A B g y)))
      (y ↦ concat B (transport Type (T ↦ T → T) A B (ua A B g) f y)
        (g .map (f (transport Type (T ↦ T) B A (inverse Type A B (ua A B g)) y)))
        (g .map (f (equiv_inverse_map A B g y)))
        (transport_function_family Type (T ↦ T) (T ↦ T) A B (ua A B g) f y)
        (refl ((a ↦ g .map (f a)) : A → B) (transport_inverse_ua A B g y)))

{` lem:trp-in-fx=Ygx: trp(e)(i) = ap_g(e) · i · ap_f(e)⁻¹. `}
def transport_path_family (X Y : Type) (f g : X → Y) (x x' : X) (e : Id X x x')
  (i : Id Y (f x) (g x))
  : Id (Id Y (f x') (g x')) (transport X (z ↦ Id Y (f z) (g z)) x x' e i)
      (concat Y (f x') (f x) (g x') (inverse Y (f x) (f x') (refl f e))
        (concat Y (f x) (g x) (g x') i (refl g e)))
  ≔ J X x
      (x' e ↦ Id (Id Y (f x') (g x')) (transport X (z ↦ Id Y (f z) (g z)) x x' e i)
        (concat Y (f x') (f x) (g x') (inverse Y (f x) (f x') (refl f e))
          (concat Y (f x) (g x) (g x') i (refl g e))))
      (calc
        transport X (z ↦ Id Y (f z) (g z)) x x (refl x) i
        = i by transport_refl X (z ↦ Id Y (f z) (g z)) x i
        = concat Y (f x) (g x) (g x) i (refl (g x))
          by inverse (Id Y (f x) (g x)) (concat Y (f x) (g x) (g x) i (refl (g x))) i
            (concat_p1 Y (f x) (g x) i)
        = concat Y (f x) (f x) (g x) (refl (f x)) (concat Y (f x) (g x) (g x) i (refl (g x)))
          by inverse (Id Y (f x) (g x))
            (concat Y (f x) (f x) (g x) (refl (f x)) (concat Y (f x) (g x) (g x) i (refl (g x))))
            (concat Y (f x) (g x) (g x) i (refl (g x)))
            (concat_1p Y (f x) (g x) (concat Y (f x) (g x) (g x) i (refl (g x))))
        = concat Y (f x) (f x) (g x) (inverse Y (f x) (f x) (refl (f x)))
            (concat Y (f x) (g x) (g x) i (refl (g x)))
          by refl ((r ↦ concat Y (f x) (f x) (g x) r (concat Y (f x) (g x) (g x) i (refl (g x))))
              : Id Y (f x) (f x) → Id Y (f x) (g x))
            (inverse (Id Y (f x) (f x)) (inverse Y (f x) (f x) (refl (f x))) (refl (f x))
              (inverse_refl Y (f x))) ∎) x' e

{` xca:trp-in-a/x=b/x, all four cases. `}
def transport_constant_path (X : Type) (a b x x' : X) (e : Id X x x') (i : Id X a b)
  : Id (Id X a b) (transport X (_ ↦ Id X a b) x x' e i) i
  ≔ transport_constant X (Id X a b) x x' e i

{` trp-in-a=x holds judgmentally: concat is defined by this transport. `}
def transport_path_from (X : Type) (a x x' : X) (e : Id X x x') (i : Id X a x)
  : Id (Id X a x') (transport X (z ↦ Id X a z) x x' e i) (concat X a x x' i e)
  ≔ refl (concat X a x x' i e)

def transport_path_to (X : Type) (b x x' : X) (e : Id X x x') (i : Id X x b)
  : Id (Id X x' b) (transport X (z ↦ Id X z b) x x' e i) (concat X x' x b (inverse X x x' e) i)
  ≔ calc
      transport X (z ↦ Id X z b) x x' e i
      = concat X x' x b (inverse X x x' e) (concat X x b b i (refl b))
        by transport_path_family X X (identity X) (constant X X b) x x' e i
      = concat X x' x b (inverse X x x' e) i
        by refl (concat X x' x b (inverse X x x' e)) (concat_p1 X x b i) ∎

def transport_conjugation (X : Type) (x x' : X) (e : Id X x x') (i : Id X x x)
  : Id (Id X x' x') (transport X (z ↦ Id X z z) x x' e i)
      (concat X x' x x' (inverse X x x' e) (concat X x x x' i e))
  ≔ transport_path_family X X (identity X) (identity X) x x' e i

{` The conversion po of def:pathover-trp sends refl to the typal
   computation law of transport at refl. `}
def pathover_transport_refl (X : Type) (Y : X → Type) (x : X) (u : Y x)
  : Id (Id (Y x) (transport X Y x x (refl x) u) u)
      (pathover_transport_equiv X Y x x (refl x) u u .map (refl u))
      (transport_refl X Y x u)
  ≔ let c ≔ transport_refl X Y x u in
    let s ≔ inverse (Y x) (transport X Y x x (refl x) u) u c in
    let base : (v : Y x) → Id Type (Id (Y x) u v) (Id (Y x) (transport X Y x x (refl x) u) v)
      ≔ v ↦ refl ((b ↦ Id (Y x) b v) : Y x → Type) s in
    calc
      pathover_transport_equiv X Y x x (refl x) u u .map (refl u)
      = pathover_transport_type X Y x x (refl x) u u .trr (refl u)
        by id_to_equiv_transport (Id (Y x) u u) (Id (Y x) (transport X Y x x (refl x) u) u)
          (pathover_transport_type X Y x x (refl x) u u) (refl u)
      = base u .trr (refl u)
        by refl ((r ↦ r .trr (refl u))
            : Id Type (Id (Y x) u u) (Id (Y x) (transport X Y x x (refl x) u) u)
              → Id (Y x) (transport X Y x x (refl x) u) u)
          (inverse (Id Type (Id (Y x) u u) (Id (Y x) (transport X Y x x (refl x) u) u))
            (base u) (pathover_transport_type X Y x x (refl x) u u)
            (Jβ X x (y p ↦ (v : Y y) → Id Type (Id Y p u v) (Id (Y y) (transport X Y x y p u) v))
              base (refl u)))
      = concat (Y x) (transport X Y x x (refl x) u) u u (inverse (Y x) u (transport X Y x x (refl x) u) s)
          (refl u)
        by transport_path_to (Y x) u u (transport X Y x x (refl x) u) s (refl u)
      = inverse (Y x) u (transport X Y x x (refl x) u) s
        by concat_p1 (Y x) (transport X Y x x (refl x) u) u
          (inverse (Y x) u (transport X Y x x (refl x) u) s)
      = c by inverse_inverse (Y x) (transport X Y x x (refl x) u) u c ∎

{` lem:trp-in-fx=Yxgx: trp(e)(i) = po_e(apd_g(e)) · ap_{trp(e)}(i) · po_e(apd_f(e))⁻¹,
   with po the conversion of def:pathover-trp. `}
def pathover_transport_section (X : Type) (Y : X → Type) (h : (x : X) → Y x)
  (x x' : X) (e : Id X x x') : Id (Y x') (transport X Y x x' e (h x)) (h x')
  ≔ pathover_transport_equiv X Y x x' e (h x) (h x') .map (apd X Y h x x' e)

def transport_section_path_family (X : Type) (Y : X → Type) (f g : (x : X) → Y x)
  (x x' : X) (e : Id X x x') (i : Id (Y x) (f x) (g x))
  : Id (Id (Y x') (f x') (g x')) (transport X (z ↦ Id (Y z) (f z) (g z)) x x' e i)
      (concat (Y x') (f x') (transport X Y x x' e (f x)) (g x')
        (inverse (Y x') (transport X Y x x' e (f x)) (f x') (pathover_transport_section X Y f x x' e))
        (concat (Y x') (transport X Y x x' e (f x)) (transport X Y x x' e (g x)) (g x')
          (refl (transport X Y x x' e) i) (pathover_transport_section X Y g x x' e)))
  ≔ J X x
      (x' e ↦ Id (Id (Y x') (f x') (g x')) (transport X (z ↦ Id (Y z) (f z) (g z)) x x' e i)
        (concat (Y x') (f x') (transport X Y x x' e (f x)) (g x')
          (inverse (Y x') (transport X Y x x' e (f x)) (f x') (pathover_transport_section X Y f x x' e))
          (concat (Y x') (transport X Y x x' e (f x)) (transport X Y x x' e (g x)) (g x')
            (refl (transport X Y x x' e) i) (pathover_transport_section X Y g x x' e))))
      (let t ≔ transport X Y x x (refl x) in
       let cf ≔ transport_refl X Y x (f x) in
       let cg ≔ transport_refl X Y x (g x) in
       calc
        transport X (z ↦ Id (Y z) (f z) (g z)) x x (refl x) i
        = i by transport_refl X (z ↦ Id (Y z) (f z) (g z)) x i
        = concat (Y x) (f x) (f x) (g x) (refl (f x)) i
          by inverse (Id (Y x) (f x) (g x)) (concat (Y x) (f x) (f x) (g x) (refl (f x)) i) i
            (concat_1p (Y x) (f x) (g x) i)
        = concat (Y x) (f x) (f x) (g x) (concat (Y x) (f x) (t (f x)) (f x) (inverse (Y x) (t (f x)) (f x) cf) cf) i
          by refl ((r ↦ concat (Y x) (f x) (f x) (g x) r i) : Id (Y x) (f x) (f x) → Id (Y x) (f x) (g x))
            (inverse (Id (Y x) (f x) (f x))
              (concat (Y x) (f x) (t (f x)) (f x) (inverse (Y x) (t (f x)) (f x) cf) cf) (refl (f x))
              (concat_inverse_left (Y x) (t (f x)) (f x) cf))
        = concat (Y x) (f x) (t (f x)) (g x) (inverse (Y x) (t (f x)) (f x) cf)
            (concat (Y x) (t (f x)) (f x) (g x) cf i)
          by concat_assoc (Y x) (f x) (t (f x)) (f x) (g x) (inverse (Y x) (t (f x)) (f x) cf) cf i
        = concat (Y x) (f x) (t (f x)) (g x) (inverse (Y x) (t (f x)) (f x) cf)
            (concat (Y x) (t (f x)) (t (g x)) (g x) (refl t i) cg)
          by refl (concat (Y x) (f x) (t (f x)) (g x) (inverse (Y x) (t (f x)) (f x) cf))
            (inverse (Id (Y x) (t (f x)) (g x))
              (concat (Y x) (t (f x)) (t (g x)) (g x) (refl t i) cg)
              (concat (Y x) (t (f x)) (f x) (g x) cf i)
              (naturality (Y x) (Y x) t (identity (Y x)) (transport_refl X Y x) (f x) (g x) i))
        = concat (Y x) (f x) (t (f x)) (g x)
            (inverse (Y x) (t (f x)) (f x) (pathover_transport_section X Y f x x (refl x)))
            (concat (Y x) (t (f x)) (t (g x)) (g x) (refl t i) (pathover_transport_section X Y g x x (refl x)))
          by refl ((a b ↦ concat (Y x) (f x) (t (f x)) (g x) (inverse (Y x) (t (f x)) (f x) a)
                (concat (Y x) (t (f x)) (t (g x)) (g x) (refl t i) b))
              : Id (Y x) (t (f x)) (f x) → Id (Y x) (t (g x)) (g x) → Id (Y x) (f x) (g x))
            (inverse (Id (Y x) (t (f x)) (f x)) (pathover_transport_section X Y f x x (refl x)) cf
              (pathover_transport_refl X Y x (f x)))
            (inverse (Id (Y x) (t (g x)) (g x)) (pathover_transport_section X Y g x x (refl x)) cg
              (pathover_transport_refl X Y x (g x))) ∎) x' e

{` def:Dan's-lemma. The printed "e" in the path-over type is the path p. `}
def dans_lemma_equiv (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : Equiv (Id Y p (f x) (f x')) (Id (Y x) (f x) (f x))
  ≔ J X x (x' p ↦ Equiv (Id Y p (f x) (f x')) (Id (Y x) (f x) (f x)))
      (identity_equiv (Id (Y x) (f x) (f x))) x' p

{` xca:trp-in-y=_(x), pointwise transport. The book defines it by induction
   on e; for native Id it holds judgmentally. `}
def pointwise_transport (X Y : Type) (x : X) (y : Y) (f g : X → Y) (e : Id (X → Y) f g)
  (p : Id Y y (f x))
  : Id (Id Y y (g x)) (transport (X → Y) (h ↦ Id Y y (h x)) f g e p)
      (concat Y y (f x) (g x) p (happly X (_ ↦ Y) f g e x))
  ≔ refl (concat Y y (f x) (g x) p (happly X (_ ↦ Y) f g e x))
