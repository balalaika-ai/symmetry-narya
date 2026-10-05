export "904-normal-quotients"

{` Chapter 9 (subgroups.tex), the remark after def:normalquotient: the
   quotient homomorphism in the torsor interpretation of BG. For a G-type
   Y : BG → U, Y/N(y) ≔ Σ_{z:BG} Y(z) × X_z(y). Then P_y/N ≃ X_y for every y
   (in particular P_G/N ≃ X_{sh_G}), so (-/N) ∘ (y ↦ P_y) is Bq_N on the
   underlying families, and for a G-torsor Y the family Y/N lies in the
   component of X_{sh_G}. `}

def normal_quotient_family (G : Group) (N : NormalSubgroups G) (Y : BG G .carrier → Type) (y : BG G .carrier) : Type
  ≔ Σ (BG G .carrier) (z ↦ Product (Y z) (normal_family G N z y .fst))

def normal_quotient_paths_equiv (G : Group) (N : NormalSubgroups G) (y w : BG G .carrier)
  : Equiv (normal_quotient_family G N (z ↦ Id (BG G .carrier) y z) w) (normal_family G N y w .fst)
  ≔ contract_away_equiv (BG G .carrier) y (z p ↦ normal_family G N z w .fst)

{` P_y/N = X_y as families of types; for y ≡ sh_G: P_G/N = X_{sh_G}. `}
def normal_quotient_paths_path (G : Group) (N : NormalSubgroups G) (y : BG G .carrier)
  : Id (BG G .carrier → Type) (normal_quotient_family G N (z ↦ Id (BG G .carrier) y z)) (w ↦ normal_family G N y w .fst)
  ≔ funext (BG G .carrier) (_ ↦ Type) (normal_quotient_family G N (z ↦ Id (BG G .carrier) y z))
      (w ↦ normal_family G N y w .fst)
      (w ↦ ua (normal_quotient_family G N (z ↦ Id (BG G .carrier) y z) w) (normal_family G N y w .fst)
        (normal_quotient_paths_equiv G N y w))

{` q_N is the composite of y ↦ P_y (lem:BGbytorsor) with -/N: the family
   underlying (bg_to_torsors G y)/N is the one underlying Bq_N(y). `}
def normal_quotient_torsor_factorization (G : Group) (N : NormalSubgroups G) (y : BG G .carrier)
  : Id (BG G .carrier → Type) (normal_quotient_family G N (z ↦ bg_to_torsors G y .fst z .fst))
      (w ↦ normal_quotient_map G N y .fst w .fst)
  ≔ normal_quotient_paths_path G N y

{` If Y is a G-torsor, then Y/N is (merely) X_{sh_G}. `}
def torsor_quotient_component (G : Group) (N : NormalSubgroups G) (T : Torsors G)
  : Mere (Id (BG G .carrier → Type) (normal_quotient_family G N (z ↦ T .fst z .fst))
      (w ↦ normal_family G N (shape G) w .fst))
  ≔ let B ≔ BG G .carrier in
    let Fam ≔ B → Type in
    let quo : GSet G → Fam ≔ Y ↦ normal_quotient_family G N (z ↦ Y z .fst) in
    mere_rec (Id (GSet G) (principal_gset G) (T .fst))
      (Mere (Id Fam (quo (T .fst)) (w ↦ normal_family G N (shape G) w .fst)))
      (mere_isprop (Id Fam (quo (T .fst)) (w ↦ normal_family G N (shape G) w .fst)))
      (e ↦ mere (Id Fam (quo (T .fst)) (w ↦ normal_family G N (shape G) w .fst))
        (concat Fam (quo (T .fst)) (quo (principal_gset G)) (w ↦ normal_family G N (shape G) w .fst)
          (map_path (GSet G) Fam quo (T .fst) (principal_gset G) (inverse (GSet G) (principal_gset G) (T .fst) e))
          (normal_quotient_paths_path G N (shape G))))
      (T .snd)
