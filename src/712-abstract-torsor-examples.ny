export "708-concr-of-abstr"
export "127-symmetries-of-circle"

{` Chapter 7 (absgroup.tex), around def:abstrGtorsors and ex:BqG:
   xca:absprtorsor (the principal torsor and the right action through
   inverses are identified, via ι), the unfolding example after it
   (absgroup.tex 505), and footnote ft:shG=z (z ↦ (sh_G = z) with preinv is
   also an abstr(G)-set, identified with the principal torsor at sh_G only
   through xca:absprtorsor). `}

{` The G-set (S, g ↦ (s ↦ μ(s, ι(g)))). `}
def agset_principal_right (G : AbstractGroup) : AbstractGSet G
  ≔ let S ≔ G .carrier in let m ≔ G .mul in
    agset_from_action G (S, abstract_group_set G) (g s ↦ m s (G .inv g))
      (g h s ↦ calc
         m s (G .inv (m g h)) = m s (m (G .inv h) (G .inv g)) by refl (m s) (ag_inv_mul G g h)
         = m (m s (G .inv h)) (G .inv g) by G .laws .assoc s (G .inv h) (G .inv g) ∎)
      (s ↦ concat S (m s (G .inv (G .unit))) (m s (G .unit)) s (refl (m s) (ag_inv_unit G)) (G .laws .unit_right s))

{` xca:absprtorsor: ι is an isomorphism (S, μ(g, -)) ≅ (S, μ(-, ι g)),
   hence an identification in GSet. `}
def agset_principal_right_iso (G : AbstractGroup) : AbstractGSetIso G (agset_principal G) (agset_principal_right G)
  ≔ (quasi_inverse_equiv (G .carrier) (G .carrier) (G .inv) (G .inv) (ag_inv_inv G) (ag_inv_inv G),
     g s ↦ ag_inv_mul G g s)

def agset_principal_right_path (G : AbstractGroup) : Id (AbstractGSet G) (agset_principal G) (agset_principal_right G)
  ≔ agset_path_from_iso G (agset_principal G) (agset_principal_right G) (agset_principal_right_iso G)

{` absgroup.tex 505 (example): unravelling, an abstr(G)-set is a set S with
   f : USym G → USym(Σ_S) such that f(p q) = f(p) f(q) (the symmetries of
   S in Σ_S are the identifications S = S of sets, automorphism_group_usym_equiv). `}
def abstr_gset_unfold (G : Group)
  : Id Type (AbstractGSet (abstr G))
      (Σ SetTypes (S ↦ Σ (USym G → USym (permutation_group S)) (f ↦
        (p q : USym G) → Id (USym (permutation_group S)) (f (usym_mul G p q))
          (usym_mul (permutation_group S) (f p) (f q)))))
  ≔ refl (AbstractGSet (abstr G))

def abstr_gset_symmetries_paths (S : SetTypes) : Equiv (USym (permutation_group S)) (Id SetTypes S S)
  ≔ automorphism_group_usym_equiv SetTypes sets_groupoid S

{` ft:shG=z: (sh_G = z) with preinv_z(p)(r) = r p⁻¹ is an abstr(G)-set. `}
def preinv_gset (G : Group) (z : BG G .carrier) : AbstractGSet (abstr G)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    agset_from_action (abstr G) (Id A a z, bg_groupoid G a z) (g r ↦ path_preinv A a a z g r)
      (g h r ↦ calc
         concat A a a z (inverse A a a (concat A a a a h g)) r
           = concat A a a z (concat A a a a (inverse A a a g) (inverse A a a h)) r
           by refl ((q ↦ concat A a a z q r) : Id A a a → Id A a z) (inverse_concat A a a a h g)
         = concat A a a z (inverse A a a g) (concat A a a z (inverse A a a h) r)
           by concat_assoc A a a a z (inverse A a a g) (inverse A a a h) r ∎)
      (r ↦ concat (Id A a z) (concat A a a z (inverse A a a (refl a)) r) (concat A a a z (refl a) r) r
         (refl ((q ↦ concat A a a z q r) : Id A a a → Id A a z) (inverse_refl A a))
         (concat_1p A a z r))

{` At z ≡ sh_G it has the same action as the right action through
   inverses (definitionally), so it is identified with the principal
   torsor only through xca:absprtorsor. `}
def preinv_gset_principal_iso (G : Group)
  : AbstractGSetIso (abstr G) (agset_principal_right (abstr G)) (preinv_gset G (shape G))
  ≔ (identity_equiv (USym G), g r ↦ refl (path_preinv (BG G .carrier) (shape G) (shape G) (shape G) g r))

def preinv_gset_principal_path (G : Group)
  : Id (AbstractGSet (abstr G)) (agset_principal (abstr G)) (preinv_gset G (shape G))
  ≔ concat (AbstractGSet (abstr G)) (agset_principal (abstr G)) (agset_principal_right (abstr G)) (preinv_gset G (shape G))
      (agset_principal_right_path (abstr G))
      (agset_path_from_iso (abstr G) (agset_principal_right (abstr G)) (preinv_gset G (shape G)) (preinv_gset_principal_iso G))

{` Litmus: in preinv_gset, g acts by r ↦ r g⁻¹ (= concat g⁻¹ r), by refl. `}
def preinv_gset_act (G : Group) (z : BG G .carrier) (g : USym G) (r : Id (BG G .carrier) (shape G) z)
  : Id (Id (BG G .carrier) (shape G) z) (agset_act (abstr G) (preinv_gset G z) g r)
      (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) g) r)
  ≔ refl (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) g) r)
