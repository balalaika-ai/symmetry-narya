export "1202-group-center"

{` Chapter 12, running-text claims of sec:center-group not covered by the
   block modules. `}

{` abelian.tex 56-58: for p : refl = φ in BG÷ = BG÷, ap_φ is conjugation by
   p(sh_G). Here p is read as the homotopy K = p(-) : refl.trr ~ φ.trr, and
   the claim is its naturality square K(sh)·ap_φ(q) = ap_{refl.trr}(q)·K(sh)
   (book order; in concatenation order ap_{refl.trr}(q) then K(sh) equals
   K(sh) then ap_φ(q)); ap_{refl.trr}(q) is q up to the lifting path
   (loops_map_homotopic_identity). `}
def center_path_naturality (G : Group) (φ : Id Type (BG G .carrier) (BG G .carrier))
  (σ : Id (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)) φ) (q : USym G)
  : Id (Id (BG G .carrier) (refl (BG G .carrier) .trr (shape G)) (φ .trr (shape G)))
      (concat (BG G .carrier) (refl (BG G .carrier) .trr (shape G)) (refl (BG G .carrier) .trr (shape G)) (φ .trr (shape G))
        (refl (refl (BG G .carrier) .trr) q)
        (universe_path_homotopy_equiv (BG G .carrier) (BG G .carrier) (refl (BG G .carrier)) φ .map σ (shape G)))
      (concat (BG G .carrier) (refl (BG G .carrier) .trr (shape G)) (φ .trr (shape G)) (φ .trr (shape G))
        (universe_path_homotopy_equiv (BG G .carrier) (BG G .carrier) (refl (BG G .carrier)) φ .map σ (shape G))
        (refl (φ .trr) q))
  ≔ naturality (BG G .carrier) (BG G .carrier) (refl (BG G .carrier) .trr) (φ .trr)
      (universe_path_homotopy_equiv (BG G .carrier) (BG G .carrier) (refl (BG G .carrier)) φ .map σ)
      (shape G) (shape G) q

{` Transport along refl acts trivially on symmetries, up to the lifting path:
   conj_{liftr}(ap_{refl.trr}(q)) = q. With center_path_naturality this is
   the book's ap_{refl} = id at φ = refl. `}
def refl_transport_symmetry (G : Group) (q : USym G)
  : Id (USym G)
      (pointed_loop_conjugate (BG G .carrier) (shape G) (refl (BG G .carrier) .trr (shape G))
        (refl (BG G .carrier) .liftr (shape G)) (refl (refl (BG G .carrier) .trr) q))
      q
  ≔ loops_map_homotopic_identity (BG G .carrier) (refl (BG G .carrier) .trr) (x ↦ refl (BG G .carrier) .liftr x)
      (shape G) q

{` Margin note at the definition of the center: (BG÷ = BG÷) ≃ (BG ≃ BG). `}
def center_space_equivalences (G : Group)
  : Equiv (Id Type (BG G .carrier) (BG G .carrier)) (Equiv (BG G .carrier) (BG G .carrier))
  ≔ transport_univalence_equiv (BG G .carrier) (BG G .carrier)

{` Litmus for the center: the transposition τ of Σ₃ is not in the image of
   abstr(z_{Σ₃}), because images are central (center_symmetry_central) and
   τσ ≠ στ (module 406). `}
def sigma3_tau_not_central_image (p : USym (group_center (symmetric_group three)))
  (e : Id (USym (symmetric_group three))
    (usym_hom (group_center (symmetric_group three)) (symmetric_group three) (center_inclusion (symmetric_group three)) p)
    sigma3_tau)
  : Empty
  ≔ let S ≔ symmetric_group three in
    let z ≔ usym_hom (group_center S) S (center_inclusion S) p in
    sigma3_tau_sigma_noncommuting
      (inverse (USym S) (usym_mul S sigma3_tau sigma3_sigma) (usym_mul S sigma3_sigma sigma3_tau)
        (transport (USym S) (g ↦ Id (USym S) (usym_mul S g sigma3_sigma) (usym_mul S sigma3_sigma g)) z sigma3_tau e
          (center_symmetry_central S p sigma3_sigma)))
