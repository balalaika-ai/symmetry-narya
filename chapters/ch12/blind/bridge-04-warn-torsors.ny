export "04-warn-torsors"
export "../../../src/1209-warn-torsors"

{` Bridges for abelian.tex, subsection "Higher deloopings" (blocks 678, 688, 707, 730). The blind torsor types
   and sections are ours by refl. The blind reading of "delooping" also asks TX to be connected; ours
   (warn_delooping) gives only Ω(TX, t) ≃* X, which is how the book glosses "delooping" at abelian.tex:671-673.
   Connectedness is derived here from the contractibility of TX_* (bridge_warn_torsor_connected). `}

{` Definition (Wärn) (abelian.tex:678). `}
def bridge_def_torsors (X : Pointed) : Id Type (BlindTorsors X) (WarnTorsor X) ≔ refl (WarnTorsor X)

def bridge_def_pointed_torsors (X : Pointed) : Id Type (BlindPointedTorsors X) (PointedWarnTorsor X)
  ≔ refl (PointedWarnTorsor X)

{` Lemma (Wärn) (abelian.tex:688). `}
def bridge_contr_path (A : Type) (h : BookIsContr A) (a b : A) : Id A a b
  ≔ concat A a (h .center) b (inverse A (h .center) a (h .contract a)) (h .contract b)

def bridge_warn_torsor_connected (X : Pointed) (h : BookIsContr (PointedWarnTorsor X)) (t : WarnTorsor X) (y : t .fst)
  : Connected (WarnTorsor X)
  ≔ connected_from_point (WarnTorsor X) t
      (x ↦ mere_rec (x .fst) (Mere (Id (WarnTorsor X) t x)) (mere_isprop (Id (WarnTorsor X) t x))
        (y' ↦ mere (Id (WarnTorsor X) t x)
          (map_path (PointedWarnTorsor X) (WarnTorsor X) (v ↦ v .fst) (t, y) (x, y')
            (bridge_contr_path (PointedWarnTorsor X) h (t, y) (x, y'))))
        (x .snd .fst))

def bridge_warn_delooping : blind_warn_delooping
  ≔ X h ty ↦ (bridge_warn_torsor_connected X h (ty .fst) (ty .snd), warn_delooping X h (ty .fst) (ty .snd))

def bridge_warn_delooping_converse (b : blind_warn_delooping) (X : Pointed) (h : BookIsContr (PointedWarnTorsor X))
  (t : WarnTorsor X) (y : t .fst)
  : BookPointedEquiv (Omega (WarnTorsor X, t)) X
  ≔ b X h (t, y) .snd

{` xca:sections-as-dependent-functions (abelian.tex:707); same orientation b = f(a) as printed. `}
def bridge_def_sections (A B : Type) (f : A → B) : Id Type (BlindSections A B f) (SectionsOf A B f)
  ≔ refl (SectionsOf A B f)

def bridge_sections_as_dependent_functions : blind_sections_as_dependent_functions
  ≔ A B f ↦ book_equivalence (SectionsOf A B f) ((b : B) → Σ A (a ↦ Id B b (f a))) (sections_dependent_equiv A B f)

{` lem:warn-abelian-group (abelian.tex:730). `}
def bridge_warn_abelian_group : blind_warn_abelian_group
  ≔ G ↦ book_equivalence (WarnTorsor (BG (G .fst))) (BB (G .fst) .carrier) (warn_abelian_torsor_equiv (G .fst) (G .snd))
