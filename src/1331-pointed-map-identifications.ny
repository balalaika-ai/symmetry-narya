export "1330-pointed-homotopy-composition"
export "400-groups"
export "281-pathover-groupoid-laws"

{` Chapter 13 (fields.tex 281-381): identifying pointed maps through their
   underlying maps, given a section of the evaluation map
   ev : (id_A = id_A) → (pt_A = pt_A), and such a section for loop types. `}

{` The evaluation map ev(i) ≔ ptw(i)(pt_A) = happly(i)(pt_A). `}
def identity_path_evaluation (A : Pointed) (i : Id (A .carrier → A .carrier) (identity (A .carrier)) (identity (A .carrier)))
  : Loop A
  ≔ i (refl (A .point))

{` Sections of ev, with identifications ev(s(p)) = p. `}
def IdentityPathEvSection (A : Pointed) : Type
  ≔ Σ (Loop A → Id (A .carrier → A .carrier) (identity (A .carrier)) (identity (A .carrier)))
      (s ↦ (p : Loop A) → Id (Loop A) (identity_path_evaluation A (s p)) p)

{` The pointed homotopy of con:Id-(B->*A) for f÷ ≡ f'÷: h(b) ≔ ptw(s(ℓ))(f b)
   with ℓ ≔ f'_pt · f_pt⁻¹ read as a loop at pt_A (concatenation order: f'_pt,
   then f_pt⁻¹). The book first does path induction on f_pt to move the base
   point to f(pt_B) and uses r = f_pt⁻¹ · f'_pt there; using the conjugate
   loop ℓ at pt_A avoids transporting the section. The pointing condition
   f_pt · h(pt_B) = f'_pt comes from naturality of ptw(s ℓ) along f_pt and
   ev(s ℓ) = ℓ. `}
def section_pointed_homotopy (A : Pointed) (S : IdentityPathEvSection A) (B : Pointed)
  (f : B .carrier → A .carrier) (fp fp' : Id (A .carrier) (A .point) (f (B .point)))
  : PointedHomotopy B A (f, fp) (f, fp')
  ≔ let X ≔ A .carrier in let a ≔ A .point in let fb ≔ f (B .point) in
    let l ≔ concat X a fb a fp' (inverse X a fb fp) in
    let H ≔ (x ↦ S .fst l (refl x)) : (x : X) → Id X x x in
    ((b ↦ H (f b)),
     calc
       concat X a fb fb fp (H fb) = concat X a a fb (H a) fp
         by naturality X X (identity X) (identity X) H a fb fp
       = concat X a a fb l fp by refl ((r ↦ concat X a a fb r fp) : Loop A → Id X a fb) (S .snd l)
       = concat X a fb fb fp' (concat X fb a fb (inverse X a fb fp) fp)
         by concat_assoc X a fb a fb fp' (inverse X a fb fp) fp
       = concat X a fb fb fp' (refl fb) by refl (concat X a fb fb fp') (concat_inverse_left X a fb fp)
       = fp' by concat_p1 X a fb fp' ∎)

{` con:Id-(B->*A): given a section s of ev, a map (f÷ = f'÷) → (f = f')
   for all pointed maps f, f' : B →* A; by path induction on f÷ = f'÷ and
   ptw_*⁻¹ (con:identity-ptd-maps) of the pointed homotopy above. `}
def pointed_map_path_from_underlying (A : Pointed) (S : IdentityPathEvSection A) (B : Pointed)
  (f f' : BookPointedMap B A) (e : Id (B .carrier → A .carrier) (f .fst) (f' .fst))
  : Id (BookPointedMap B A) f f'
  ≔ J (B .carrier → A .carrier) (f .fst)
      (k _ ↦ (kp : Id (A .carrier) (A .point) (k (B .point))) → Id (BookPointedMap B A) f (k, kp))
      (kp ↦ equiv_inverse_map (Id (BookPointedMap B A) f (f .fst, kp)) (PointedHomotopy B A f (f .fst, kp))
        (pointed_map_path_equiv B A f (f .fst, kp))
        (section_pointed_homotopy A S B (f .fst) (f .snd) kp))
      (f' .fst) e (f' .snd)

{` xca:ev-section-loopsA. For q : a = x, ρ_q : q·refl_a = q is
   concat_1p q (the book's q·refl_a is concat (refl a) q). For p : a = a
   and β : p = refl_a, i(β) : ap_{(-·refl_a)}(β) = β·ρ_p; in Narya
   refl_a·refl_a is not judgmentally refl_a, so the left side is followed by
   ρ_{refl_a}: ap_{(-·refl)}(β) · ρ_refl = ρ_p · β (concatenation order),
   the naturality of ρ. `}
def ev_section_i (A : Type) (a : A) (p : Id A a a) (β : Id (Id A a a) p (refl a))
  : Id (Id (Id A a a) (concat A a a a (refl a) p) (refl a))
      (concat (Id A a a) (concat A a a a (refl a) p) (concat A a a a (refl a) (refl a)) (refl a)
        (refl (concat A a a a (refl a)) β) (concat_1p A a a (refl a)))
      (concat (Id A a a) (concat A a a a (refl a) p) p (refl a) (concat_1p A a a p) β)
  ≔ naturality (Id A a a) (Id A a a) (concat A a a a (refl a)) (identity (Id A a a)) (concat_1p A a a) p (refl a) β

{` xca:ev-section-loopsA, last part: ap_{(-·refl_a)}(α) is identified with α
   for α : refl_a = refl_a, after conjugation by ρ_{refl_a} (needed for the
   types to match in Narya). `}
def ev_section_whisker_refl (A : Type) (a : A) (α : Id (Id A a a) (refl a) (refl a))
  : Id (Id (Id A a a) (refl a) (refl a))
      (concat (Id A a a) (refl a) (concat A a a a (refl a) (refl a)) (refl a)
        (inverse (Id A a a) (concat A a a a (refl a) (refl a)) (refl a) (concat_1p A a a (refl a)))
        (concat (Id A a a) (concat A a a a (refl a) (refl a)) (concat A a a a (refl a) (refl a)) (refl a)
          (refl (concat A a a a (refl a)) α) (concat_1p A a a (refl a))))
      α
  ≔ let L ≔ Id A a a in let r ≔ refl a in let rr ≔ concat A a a a r r in let ρ ≔ concat_1p A a a r in
    calc
      concat L r rr r (inverse L rr r ρ) (concat L rr rr r (refl (concat A a a a r) α) ρ)
        = concat L r rr r (inverse L rr r ρ) (concat L rr r r ρ α)
        by refl (concat L r rr r (inverse L rr r ρ)) (ev_section_i A a r α)
      = concat L r r r (concat L r rr r (inverse L rr r ρ) ρ) α
        by inverse (Id L r r) (concat L r r r (concat L r rr r (inverse L rr r ρ) ρ) α)
          (concat L r rr r (inverse L rr r ρ) (concat L rr r r ρ α))
          (concat_assoc L r rr r r (inverse L rr r ρ) ρ α)
      = concat L r r r (refl r) α by refl ((z ↦ concat L r r r z α) : Id L r r → Id L r r) (concat_inverse_left L rr r ρ)
      = α by concat_1p L r r α ∎

{` con:ev-section-loopsA. s_α(p) ≔ ap_{(-·p)}(α) : p = p, where the book's
   -·p is r ↦ concat p r and rfl·p ≡ p is judgmental in the book; here
   ap_{(-·p)}(α) : p·rfl = p·rfl is conjugated by ρ'_p = concat_p1 p.
   s(α) ≔ ptw⁻¹(s_α) = funext(s_α). `}
def loops_ev_section_component (A : Pointed) (α : Id (Loop A) (refl (A .point)) (refl (A .point))) (p : Loop A)
  : Id (Loop A) p p
  ≔ let X ≔ A .carrier in let a ≔ A .point in
    concat (Loop A) p (concat X a a a p (refl a)) p
      (inverse (Loop A) (concat X a a a p (refl a)) p (concat_p1 X a a p))
      (concat (Loop A) (concat X a a a p (refl a)) (concat X a a a p (refl a)) p
        (refl (concat X a a a p) α) (concat_p1 X a a p))

def loops_ev_section (A : Pointed) (α : Id (Loop A) (refl (A .point)) (refl (A .point)))
  : Id (Loop A → Loop A) (identity (Loop A)) (identity (Loop A))
  ≔ funext (Loop A) (_ ↦ Loop A) (identity (Loop A)) (identity (Loop A)) (loops_ev_section_component A α)

def loops_ev_section_beta (A : Pointed) (α : Id (Loop A) (refl (A .point)) (refl (A .point)))
  : Id (Id (Loop A) (refl (A .point)) (refl (A .point)))
      (identity_path_evaluation (Omega A) (loops_ev_section A α)) α
  ≔ let X ≔ A .carrier in let a ≔ A .point in let L ≔ Id X a a in let r ≔ refl a in
    let rr ≔ concat X a a a r r in
    calc
      identity_path_evaluation (Omega A) (loops_ev_section A α) = loops_ev_section_component A α r
        by inverse (Id L r r) (loops_ev_section_component A α r) (loops_ev_section A α (refl r))
          (funext_beta L (_ ↦ L) (identity L) (identity L) (loops_ev_section_component A α) r)
      = concat L r rr r (inverse L rr r (concat_1p X a a r)) (concat L rr rr r (refl (concat X a a a r) α) (concat_1p X a a r))
        by refl ((ρ ↦ concat L r rr r (inverse L rr r ρ) (concat L rr rr r (refl (concat X a a a r) α) ρ))
            : Id L rr r → Id L r r)
          (concat_p1_1p_refl X a)
      = α by ev_section_whisker_refl X a α ∎

def loops_identity_ev_section (A : Pointed) : IdentityPathEvSection (Omega A)
  ≔ (loops_ev_section A, loops_ev_section_beta A)

{` cor:Id-(B->*loopsA): for pointed maps f, f' : B →* ΩA, a map
   (f÷ = f'÷) → (f = f'). `}
def loops_pointed_map_path_from_underlying (A B : Pointed) (f f' : BookPointedMap B (Omega A))
  (e : Id (B .carrier → Loop A) (f .fst) (f' .fst))
  : Id (BookPointedMap B (Omega A)) f f'
  ≔ pointed_map_path_from_underlying (Omega A) (loops_identity_ev_section A) B f f' e
