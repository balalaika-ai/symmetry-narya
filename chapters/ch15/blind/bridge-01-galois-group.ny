export "01-galois-group"
export "../../../src/1501-field-extensions"

{` Bridges for galois.tex, section "Covering spaces and field
   extensions": field extensions, the Galois group, rem:sip-univalence.
   The blind field homomorphisms, k\Fields, Iso(K, L) and the transport
   formulas are ours definitionally (checked by refl / by typing our terms
   at the blind types). BlindGaloisGroup and galois_group differ only in the
   proof that k\Fields is a groupoid (a proposition); USym of both is the same
   type. `}

def bridge_def_field_hom (k K : Field) : Id Type (BlindFieldHom k K) (RingHom (k .fst) (K .fst))
  ≔ refl (RingHom (k .fst) (K .fst))

def bridge_def_field_ext (k : Field) : Id Type (BlindFieldExt k) (FieldExt k) ≔ refl (FieldExt k)

def bridge_def_field_ext_groupoid (k : Field)
  : Id (isGroupoid (FieldExt k)) (blind_field_ext_groupoid k) (field_ext_groupoid k)
  ≔ isgroupoid_isprop (FieldExt k) (blind_field_ext_groupoid k) (field_ext_groupoid k)

def bridge_def_galois_group (k : Field) (E : FieldExt k) : Id Group (BlindGaloisGroup k E) (galois_group k E)
  ≔ refl ((h ↦ automorphism_group (FieldExt k) h E) : isGroupoid (FieldExt k) → Group) (bridge_def_field_ext_groupoid k)

{` USym of both groups is the same type (the identity map typechecks both ways). `}
{` USym of both groups is the type of loops at the base point of the
   component of E in k\Fields. (Narya's conversion check comparing the two
   USym types directly raises bug E0500 while comparing the groupoid
   fields of the two group records, so the identification goes through the
   explicit loop type.) `}
def ComponentLoop (k : Field) (E : FieldExt k) : Type
  ≔ Id (NativeComponent (FieldExt k) E) (component_point (FieldExt k) E) (component_point (FieldExt k) E)

def bridge_usym_blind_out (k : Field) (E : FieldExt k) (g : USym (BlindGaloisGroup k E)) : ComponentLoop k E ≔ g

def bridge_usym_blind_in (k : Field) (E : FieldExt k) (g : ComponentLoop k E) : USym (BlindGaloisGroup k E) ≔ g

def bridge_usym_ours_out (k : Field) (E : FieldExt k) (g : USym (galois_group k E)) : ComponentLoop k E ≔ g

def bridge_usym_ours_in (k : Field) (E : FieldExt k) (g : ComponentLoop k E) : USym (galois_group k E) ≔ g

def bridge_usym_to_ours (k : Field) (E : FieldExt k) (g : USym (BlindGaloisGroup k E)) : USym (galois_group k E)
  ≔ bridge_usym_ours_in k E (bridge_usym_blind_out k E g)

def bridge_usym_to_blind (k : Field) (E : FieldExt k) (g : USym (galois_group k E)) : USym (BlindGaloisGroup k E)
  ≔ bridge_usym_blind_in k E (bridge_usym_ours_out k E g)

def bridge_def_galois_usym (k : Field) (E : FieldExt k) : Equiv (USym (BlindGaloisGroup k E)) (USym (galois_group k E))
  ≔ quasi_inverse_equiv (USym (BlindGaloisGroup k E)) (USym (galois_group k E))
      (bridge_usym_to_ours k E) (bridge_usym_to_blind k E) (g ↦ refl g) (g ↦ refl g)

def bridge_def_field_iso (K L : Field) : Id Type (BlindFieldIso K L) (FieldIso K L) ≔ refl (FieldIso K L)

{` rem:sip-univalence, first display. `}
def bridge_field_paths_structure : blind_field_paths_structure
  ≔ K L ↦ field_path_transport_structure_equiv K L

{` rem:sip-univalence, second display (transport along ua(φ) is conjugation by φ). `}
def bridge_field_transport_structure : blind_field_transport_structure
  ≔ K L φ ↦ (field_transport_add_ua K L φ,
             (field_transport_mul_ua K L φ, (field_transport_zero_ua K L φ, field_transport_one_ua K L φ)))

{` rem:sip-univalence: (K = L) ≃ Iso(K, L). Converse: our statement is the blind one. `}
def bridge_field_sip : blind_field_sip ≔ K L ↦ field_path_iso_equiv K L

def bridge_field_sip_converse (h : blind_field_sip) (K L : Field) : Equiv (Id Field K L) (FieldIso K L) ≔ h K L

{` rem:sip-univalence, last display, first form. `}
def bridge_galois_usym_paths : blind_galois_usym_paths
  ≔ k E ↦ compose_equiv (USym (BlindGaloisGroup k E)) (USym (galois_group k E)) (GaloisTransportForm k E)
      (bridge_def_galois_usym k E) (galois_usym_transport_equiv k E)

{` Last display, second form: our FieldExtIso states σ ∘ i = i as an
   identification of ring homomorphisms, the blind one of the underlying
   functions; both are propositions and imply each other. `}
def bridge_kaut_condition_equiv (k : Field) (E : FieldExt k) (σ : FieldIso (E .fst) (E .fst))
  : Equiv (Id (RingHom (k .fst) (E .fst .fst)) (field_iso_after k (E .fst) (E .fst) (E .snd) σ) (E .snd))
      (Id (k .fst .carrier → E .fst .fst .carrier) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst))
  ≔ let H ≔ RingHom (k .fst) (E .fst .fst) in let A ≔ k .fst .carrier in let B ≔ E .fst .fst .carrier in
    let a ≔ field_iso_after k (E .fst) (E .fst) (E .snd) σ in
    iff_equiv (Id H a (E .snd)) (Id (A → B) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst))
      (ring_hom_set (k .fst) (E .fst .fst) a (E .snd))
      (pi_set A (_ ↦ B) (_ ↦ ring_set (E .fst .fst)) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst))
      (e ↦ refl ((χ ↦ χ .fst .fst) : H → (A → B)) e)
      (e ↦ ring_hom_ext (k .fst) (E .fst .fst) a (E .snd) (x ↦ refl ((f ↦ f x) : (A → B) → B) e))

def BlindKAutForm (k : Field) (E : FieldExt k) : Type
  ≔ Σ (BlindFieldIso (E .fst) (E .fst)) (σ ↦
      Id (k .fst .carrier → E .fst .fst .carrier) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst))

def bridge_kaut_form_equiv (k : Field) (E : FieldExt k) : Equiv (FieldExtIso k E E) (BlindKAutForm k E)
  ≔ let K ≔ E .fst in
    family_equiv (FieldIso K K)
      (σ ↦ Id (RingHom (k .fst) (K .fst)) (field_iso_after k K K (E .snd) σ) (E .snd))
      (σ ↦ Id (k .fst .carrier → K .fst .carrier) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst))
      (σ ↦ bridge_kaut_condition_equiv k E σ)

def bridge_usym_kaut_equiv (k : Field) (E : FieldExt k) : Equiv (USym (BlindGaloisGroup k E)) (FieldExtIso k E E)
  ≔ compose_equiv (USym (BlindGaloisGroup k E)) (USym (galois_group k E)) (FieldExtIso k E E)
      (bridge_def_galois_usym k E) (galois_usym_kaut_equiv k E)

def bridge_galois_usym_isos_at (k : Field) (E : FieldExt k) : Equiv (USym (BlindGaloisGroup k E)) (BlindKAutForm k E)
  ≔ compose_equiv (USym (BlindGaloisGroup k E)) (FieldExtIso k E E) (BlindKAutForm k E)
      (bridge_usym_kaut_equiv k E) (bridge_kaut_form_equiv k E)

def bridge_galois_usym_isos : blind_galois_usym_isos ≔ k E ↦ bridge_galois_usym_isos_at k E
