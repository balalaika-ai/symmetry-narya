export "03-ptd-homotopies"

{` Blind statements, chapter 13 (fields.tex): con:Id-(B->*A),
   con:ev-section-loopsA, xca:ev-section-loopsA, cor:Id-(B->*loopsA). `}

{` ev : (id_A = id_A) → (pt_A = pt_A), i ↦ ptw(i)(pt_A) = happly i pt_A. `}
def blind_ev_id (A : Pointed)
  (i : Id (A .carrier → A .carrier) (identity (A .carrier)) (identity (A .carrier))) : Loop A
  ≔ happly (A .carrier) (_ ↦ A .carrier) (identity (A .carrier)) (identity (A .carrier)) i (A .point)

{` con:Id-(B->*A): given a section s of ev (with ev(s p) = p for all p) and
   pointed maps f, f' : B →* A, there is a map (f÷ = f'÷) → (f = f'). `}
def blind_con_Id_B_ptd_A : Type
  ≔ (A : Pointed) (s : Loop A → Id (A .carrier → A .carrier) (identity (A .carrier)) (identity (A .carrier)))
    (hs : (p : Loop A) → Id (Loop A) (blind_ev_id A (s p)) p)
    (B : Pointed) (f f' : BookPointedMap B A)
    → Id (B .carrier → A .carrier) (f .fst) (f' .fst) → Id (BookPointedMap B A) f f'

{` con:ev-section-loopsA: ev : (id_{ΩA} = id_{ΩA}) → (rfl = rfl), i ↦ ptw(i)(rfl),
   has a section. This ev is blind_ev_id at the pointed type ΩA. `}
def blind_con_ev_section_loopsA : Type
  ≔ (A : Pointed)
    → Σ (Loop (Omega A) → Id (Loop A → Loop A) (identity (Loop A)) (identity (Loop A)))
        (s ↦ (α : Loop (Omega A)) → Id (Loop (Omega A)) (blind_ev_id (Omega A) (s α)) α)

{` xca:ev-section-loopsA, part 1: ρ_q : q·refl_a = q (q·refl_a is concat refl q). `}
def blind_xca_ev_section_rho : Type
  ≔ (A : Type) (a x : A) (q : Id A a x) → Id (Id A a x) (concat A a a x (refl a) q) q

{` The book defines ρ by induction with ρ_refl ≔ refl; in Narya
   concat refl refl is not judgmentally refl, so we take for ρ the library
   proof concat_1p of the same type (part 1 is thereby inhabited). `}
def blind_rho (A : Type) (a x : A) (q : Id A a x) : Id (Id A a x) (concat A a a x (refl a) q) q
  ≔ concat_1p A a x q

{` xca:ev-section-loopsA, part 2: for p : a = a and β : p = refl_a,
   i(β) : ap_{-·refl}(β) = β·ρ_p. The book's endpoints refl·refl and refl
   coincide judgmentally; here ap_{-·refl}(β) ends at concat refl refl, so
   ρ_refl is appended to it. `}
def blind_xca_ev_section_i : Type
  ≔ (A : Type) (a : A) (p : Id A a a) (β : Id (Id A a a) p (refl a))
    → Id (Id (Id A a a) (concat A a a a (refl a) p) (refl a))
        (concat (Id A a a) (concat A a a a (refl a) p) (concat A a a a (refl a) (refl a)) (refl a)
          (refl ((r : Id A a a) ↦ concat A a a a (refl a) r) β) (blind_rho A a a (refl a)))
        (concat (Id A a a) (concat A a a a (refl a) p) p (refl a) (blind_rho A a a p) β)

{` xca:ev-section-loopsA, part 3: ap_{-·refl}(α) is identified with α for
   α : refl_a = refl_a; the two live in different identity types in Narya
   (endpoints concat refl refl vs refl), so ap_{-·refl}(α) is conjugated
   by ρ_refl. `}
def blind_xca_ev_section_loopsA : Type
  ≔ (A : Type) (a : A) (α : Id (Id A a a) (refl a) (refl a))
    → Id (Id (Id A a a) (refl a) (refl a))
        (concat (Id A a a) (refl a) (concat A a a a (refl a) (refl a)) (refl a)
          (inverse (Id A a a) (concat A a a a (refl a) (refl a)) (refl a) (blind_rho A a a (refl a)))
          (concat (Id A a a) (concat A a a a (refl a) (refl a)) (concat A a a a (refl a) (refl a)) (refl a)
            (refl ((r : Id A a a) ↦ concat A a a a (refl a) r) α) (blind_rho A a a (refl a))))
        α

{` cor:Id-(B->*loopsA): for all pointed A, B and f, f' : B →* ΩA there is a
   function (f÷ = f'÷) → (f = f'). `}
def blind_cor_Id_B_ptd_loopsA : Type
  ≔ (A B : Pointed) (f f' : BookPointedMap B (Omega A))
    → Id (B .carrier → Loop A) (f .fst) (f' .fst) → Id (BookPointedMap B (Omega A)) f f'
