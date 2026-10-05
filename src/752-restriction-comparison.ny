export "750-abstract-concrete-gsets"
export "740-abstract-restriction-induction"

{` Chapter 7 (absgroup.tex), sec:Gsetsabstrconcr, xca:f^*-abs(f)^*: for a
   homomorphism f : G → H the square
     ev_{sh_G} ∘ f^* = abstr(f)^* ∘ ev_{sh_H} : GSet(H) → absGSet(abstr G)
   commutes. For an H-set Y, ev_{sh_G}(f^* Y) has underlying set
   Y(Bf(sh_G)) and abstr(f)^*(ev_{sh_H} Y) has underlying set Y(sh_H); the
   isomorphism is transport in Y along the pointing path Bf_pt : sh_H = Bf(sh_G)
   ("both are defined by precomposition": the action of g on f^*Y is transport
   along ap_Bf(g), and USym f(g) = Bf_pt · ap_Bf(g) · Bf_pt⁻¹). `}

def restrict_ev_iso_equivariant (G H : Group) (f : GroupHom G H) (Y : GSet H) (g : USym G) (y : gset_underlying H Y)
  : Id (Y (hom_function G H f (shape G)) .fst)
      (gset_act H Y (shape H) (hom_function G H f (shape G)) (hom_point G H f)
        (agset_act (abstr G) (agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (ev_gset H Y)) g y))
      (agset_act (abstr G) (ev_gset G (gset_restrict G H f Y)) g
        (gset_act H Y (shape H) (hom_function G H f (shape G)) (hom_point G H f) y))
  ≔ let B ≔ BG H .carrier in let s ≔ shape H in let b ≔ hom_function G H f (shape G) in
    let p ≔ hom_point G H f in
    let c : Id B b b ≔ refl (hom_function G H f) g in
    let F : B → Type ≔ v ↦ Y v .fst in
    let T ≔ transport B F in
    let fg ≔ usym_hom G H f g in
    let y1 ≔ T s b p y in
    calc
      T s b p (agset_act (abstr H) (ev_gset H Y) fg y) = T s b p (T s s fg y)
        by refl (T s b p) (ev_gset_act H Y fg y)
      = T s b p (T b s (concat B b b s c (inverse B s b p)) y1)
        by refl (T s b p) (transport_concat B F s b s p (concat B b b s c (inverse B s b p)) y)
      = T s b p (T b s (inverse B s b p) (T b b c y1))
        by refl (T s b p) (transport_concat B F b b s c (inverse B s b p) y1)
      = T b b c y1 by gset_act_inverse_right H Y s b p (T b b c y1)
      = agset_act (abstr G) (ev_gset G (gset_restrict G H f Y)) g y1
        by inverse (F b) (agset_act (abstr G) (ev_gset G (gset_restrict G H f Y)) g y1) (T b b c y1)
          (ev_gset_act G (gset_restrict G H f Y) g y1) ∎

{` The isomorphism abstr(f)^*(ev_{sh_H} Y) ≅ ev_{sh_G}(f^* Y): transport along Bf_pt. `}
def restrict_ev_iso (G H : Group) (f : GroupHom G H) (Y : GSet H)
  : AbstractGSetIso (abstr G) (agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (ev_gset H Y))
      (ev_gset G (gset_restrict G H f Y))
  ≔ (gset_act_equiv H Y (shape H) (hom_function G H f (shape G)) (hom_point G H f),
     g y ↦ restrict_ev_iso_equivariant G H f Y g y)

def restrict_ev_path (G H : Group) (f : GroupHom G H) (Y : GSet H)
  : Id (AbstractGSet (abstr G)) (ev_gset G (gset_restrict G H f Y))
      (agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (ev_gset H Y))
  ≔ inverse (AbstractGSet (abstr G)) (agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (ev_gset H Y))
      (ev_gset G (gset_restrict G H f Y))
      (agset_path_from_iso (abstr G) (agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (ev_gset H Y))
        (ev_gset G (gset_restrict G H f Y)) (restrict_ev_iso G H f Y))

{` xca:f^*-abs(f)^*: the filled square ev_{sh_G} ∘ f^* = abstr(f)^* ∘ ev_{sh_H}. `}
def restrict_ev_square (G H : Group) (f : GroupHom G H)
  : Id (GSet H → AbstractGSet (abstr G))
      (Y ↦ gset_abstract_gset_equiv G .map (gset_restrict G H f Y))
      (Y ↦ agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (gset_abstract_gset_equiv H .map Y))
  ≔ funext (GSet H) (_ ↦ AbstractGSet (abstr G))
      (Y ↦ gset_abstract_gset_equiv G .map (gset_restrict G H f Y))
      (Y ↦ agset_restrict (abstr G) (abstr H) (abstr_hom G H f) (gset_abstract_gset_equiv H .map Y))
      (restrict_ev_path G H f)

{` Litmus: for f = id_G the comparison map is transport along refl, the identity. `}
def restrict_ev_iso_id_map (G : Group) (Y : GSet G) (y : gset_underlying G Y)
  : Id (gset_underlying G Y) (restrict_ev_iso G G (group_hom_id G) Y .fst .map y) y
  ≔ gset_act_refl G Y (shape G) y
