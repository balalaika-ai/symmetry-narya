export "bridge-06-actions"
export "bridge-04-phi-functors"
export "../../../src/753-induction-comparison"

{` Bridges bridge for xca:f_!-abs(f)_! (absgroup.tex 1277): for every ok,
   ev_sh(f_! X) = ev_gset(f_! X) = abstr(f)_!(ev_gset X)
   = abstr(f)_!(ev_sh X) = blind φ_!(ev_sh X), from bridge_ev_path,
   induce_ev_path (module 753) and bridge_phi_shriek_path. `}

def bridge_xca_induce_abs : blind_xca_induce_abs
  ≔ G H f ok X ↦
    let A ≔ AbstractGSet (abstr H) in
    let φ ≔ abstr_hom G H f in
    let Y ≔ gset_induce G H f X in
    let ind ≔ agset_induce (abstr G) (abstr H) φ in
    let B ≔ blind_phi_shriek (blind_abstr G) (blind_abstr H) (blind_abstr_hom G H f) ok (blind_ev_sh G X) in
    concat A (blind_ev_sh H Y) (ev_gset H Y) B (bridge_ev_path H Y)
      (concat A (ev_gset H Y) (ind (ev_gset G X)) B (induce_ev_path G H f X)
        (concat A (ind (ev_gset G X)) (ind (blind_ev_sh G X)) B
          (refl ind (inverse (AbstractGSet (abstr G)) (blind_ev_sh G X) (ev_gset G X) (bridge_ev_path G X)))
          (inverse A B (ind (blind_ev_sh G X))
            (bridge_phi_shriek_path (blind_abstr G) (blind_abstr H) (blind_abstr_hom G H f) ok (blind_ev_sh G X)))))
