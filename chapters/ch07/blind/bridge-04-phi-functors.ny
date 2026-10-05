export "bridge-00-core"
export "04-phi-functors"
export "../../../src/743-abstract-coinduction"

{` Bridges for absgroup.tex, subsection "The left and right adjoint
   of restriction, abstractly" (lines 733-900).

   Blind G-sets over G are our G-sets over bridge_ag7 G on the nose, and so
   are restriction, G-set maps, the relation on T × X, its quotient, the
   classes and the φ_* carrier. The blind φ_! and φ_* take the data of
   xca:phi_!-OK / def:phi_* as a parameter `ok`; for EVERY ok they are
   identified with our agset_induce / agset_coinduce. For φ_! the carrier
   component of the identification is refl (a quotient depends only on the
   predicate of the relation) and the action is pinned by action_induced;
   for φ_* the identification comes from the identity isomorphism (the
   proofs that the carrier is a set differ). `}

{` def:phi^*. `}
def bridge_def_phi_star (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (Y : BlindAbsGSet H)
  : Id (AbstractGSet (bridge_ag7 G)) (blind_phi_star G H phi Y) (agset_restrict (bridge_ag7 G) (bridge_ag7 H) phi Y)
  ≔ refl (blind_phi_star G H phi Y)

{` def:Hom-absG. `}
def bridge_def_gset_hom (G : BlindAbsGroup) (X Y : BlindAbsGSet G)
  : Id Type (BlindAbsGSetHom G X Y) (AbstractGSetHom (bridge_ag7 G) X Y)
  ≔ refl (BlindAbsGSetHom G X Y)

{` def:phi_!: the type T × X, the witnesses of the relation, the quotient
   (for any proofs that the relation is an equivalence relation) and the
   classes. `}
def bridge_def_phi_tx (G H : BlindAbsGroup) (X : BlindAbsGSet G)
  : Id Type (BlindTX H G X) (Product (bridge_ag7 H .carrier) (agset_carrier (bridge_ag7 G) X))
  ≔ refl (BlindTX H G X)

def bridge_def_phi_rel_witness (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) (a b : BlindTX H G X)
  : Id Type (blind_phi_rel_witness G H phi X a b) (AgsetInduceWitness (bridge_ag7 G) (bridge_ag7 H) phi X a b)
  ≔ refl (blind_phi_rel_witness G H phi X a b)

def bridge_def_phi_quotient (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (r : (a : BlindTX H G X) → blind_phi_rel G H phi X a a)
  (s : (a b : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b a)
  (t : (a b c : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b c → blind_phi_rel G H phi X a c)
  : Id Type (Quotient (BlindTX H G X) (blind_phi_eqrel G H phi X r s t)) (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
  ≔ refl (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)

def bridge_def_phi_class (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (ok : BlindPhiShriekOK G H phi X) (t : H .carrier) (x : X .fst .fst)
  : Id (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X) (blind_phi_class G H phi X ok t x)
      (agset_induce_class (bridge_ag7 G) (bridge_ag7 H) phi X t x)
  ≔ refl (agset_induce_class (bridge_ag7 G) (bridge_ag7 H) phi X t x)

{` The induced permutation agrees with ours, for any proofs. `}
def bridge_phi_induced_path (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  (r : (a : BlindTX H G X) → blind_phi_rel G H phi X a a)
  (s : (a b : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b a)
  (t : (a b c : BlindTX H G X) → blind_phi_rel G H phi X a b → blind_phi_rel G H phi X b c → blind_phi_rel G H phi X a c)
  (resp : (h : H .carrier) (a b : BlindTX H G X) → blind_phi_rel G H phi X a b
    → blind_phi_rel G H phi X (H .mul h (a .fst), a .snd) (H .mul h (b .fst), b .snd))
  (h : H .carrier) (q : AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
  : Id (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
      (blind_phi_induced G H phi X (blind_phi_eqrel G H phi X r s t) resp h q)
      (agset_induce_act (bridge_ag7 G) (bridge_ag7 H) phi X h q)
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let C ≔ AgsetInduceCarrier G' H' phi X in
    quotient_prop_induction (BlindTX H G X) (agset_induce_relation G' H' phi X)
      (q ↦ Id C (blind_phi_induced G H phi X (blind_phi_eqrel G H phi X r s t) resp h q) (agset_induce_act G' H' phi X h q))
      (q ↦ agset_induce_carrier_set G' H' phi X (blind_phi_induced G H phi X (blind_phi_eqrel G H phi X r s t) resp h q)
        (agset_induce_act G' H' phi X h q))
      (u ↦ refl (agset_induce_class G' H' phi X (H .mul h (u .fst)) (u .snd)))
      q

{` xca:phi_!-OK, from our relation proofs, shift witness and agset_induce. `}
def bridge_phi_shriek_respects (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) (h : H .carrier)
  (a b : BlindTX H G X) (r : blind_phi_rel G H phi X a b)
  : blind_phi_rel G H phi X (H .mul h (a .fst), a .snd) (H .mul h (b .fst), b .snd)
  ≔ let W ≔ AgsetInduceWitness (bridge_ag7 G) (bridge_ag7 H) phi X in
    let a' : BlindTX H G X ≔ (H .mul h (a .fst), a .snd) in
    let b' : BlindTX H G X ≔ (H .mul h (b .fst), b .snd) in
    mere_rec (W a b) (Mere (W a' b')) (mere_isprop (W a' b'))
      (w ↦ mere (W a' b') (agset_induce_shift_witness (bridge_ag7 G) (bridge_ag7 H) phi X h a b w)) r

def bridge_phi_shriek_ok_at (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  : BlindPhiShriekOK G H phi X
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let R ≔ agset_induce_relation G' H' phi X in
    (rel_refl ≔ R .reflexive,
     rel_sym ≔ R .symmetric,
     rel_trans ≔ R .transitive,
     respects ≔ bridge_phi_shriek_respects G H phi X,
     action ≔ agset_induce G' H' phi X .snd,
     action_induced ≔ h q ↦
       inverse (AgsetInduceCarrier G' H' phi X)
         (blind_phi_induced G H phi X (blind_phi_eqrel G H phi X (R .reflexive) (R .symmetric) (R .transitive))
           (bridge_phi_shriek_respects G H phi X) h q)
         (agset_induce_act G' H' phi X h q)
         (bridge_phi_induced_path G H phi X (R .reflexive) (R .symmetric) (R .transitive)
           (bridge_phi_shriek_respects G H phi X) h q))

def bridge_xca_phi_shriek_ok : blind_xca_phi_shriek_ok ≔ G H phi X ↦ bridge_phi_shriek_ok_at G H phi X

{` def:phi_!: for every ok, the blind φ_!(X) is our agset_induce (carrier
   component refl). `}
def bridge_phi_shriek_path (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (ok : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (X : BlindAbsGSet G)
  : Id (AbstractGSet (bridge_ag7 H)) (blind_phi_shriek G H phi ok X) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi X)
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let I ≔ agset_induce G' H' phi X in
    let o ≔ ok X in
    let C ≔ AgsetInduceCarrier G' H' phi X in
    let ind ≔ blind_phi_induced G H phi X (blind_phi_eqrel G H phi X (o .rel_refl) (o .rel_sym) (o .rel_trans)) (o .respects) in
    (refl (I .fst),
     agset_structure_ext H' (I .fst) (o .action) (I .snd)
       (h q ↦ concat C (permutation_action (I .fst) (o .action .fst h) q) (ind h q) (agset_induce_act G' H' phi X h q)
         (o .action_induced h q)
         (bridge_phi_induced_path G H phi X (o .rel_refl) (o .rel_sym) (o .rel_trans) (o .respects) h q)))

{` Transport of carriers along bridge_phi_shriek_path sends the blind class
   of (t, x) to our class [t, x]. `}
def bridge_phi_shriek_path_class (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (ok : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (X : BlindAbsGSet G) (t : H .carrier) (x : X .fst .fst)
  : Id (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
      (transport (AbstractGSet (bridge_ag7 H)) (Z ↦ agset_carrier (bridge_ag7 H) Z) (blind_phi_shriek G H phi ok X)
        (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi X) (bridge_phi_shriek_path G H phi ok X)
        (blind_phi_class G H phi X (ok X) t x))
      (agset_induce_class (bridge_ag7 G) (bridge_ag7 H) phi X t x)
  ≔ transport_refl Type (A ↦ A) (AgsetInduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
      (agset_induce_class (bridge_ag7 G) (bridge_ag7 H) phi X t x)

{` xca:phi_!-|phi^*, for every ok. `}
def bridge_xca_phi_shriek_adj : blind_xca_phi_shriek_adj
  ≔ G H phi ok X Y ↦
    let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let A ≔ AbstractGSetHom H' (blind_phi_shriek G H phi ok X) Y in
    let B ≔ AbstractGSetHom H' (agset_induce G' H' phi X) Y in
    let C ≔ AbstractGSetHom G' X (agset_restrict G' H' phi Y) in
    bridge_book_equiv_of A C
      (compose_equiv A B C
        (transport_equiv A B
          (refl ((Z ↦ AbstractGSetHom H' Z Y) : AbstractGSet H' → Type) (bridge_phi_shriek_path G H phi ok X)))
        (induce_restrict_abstract_adjunction G' H' phi X Y))

{` def:phi_*: the carrier is ours; the data asked for by the blind
   definition (closure, action laws) is ours. `}
def bridge_def_phi_lower_set (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G)
  : Id Type (BlindPhiLowerSet G H phi X) (AgsetCoinduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
  ≔ refl (BlindPhiLowerSet G H phi X)

def bridge_phi_lower_ok_at (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) : BlindPhiLowerOK G H phi X
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    (closed ≔ h b s ↦ agset_coinduce_act G' H' phi X h b .snd s,
     act_mul ≔ h h' b ↦ agset_coinduce_act_mul G' H' phi X h h' b,
     act_unit ≔ b ↦ agset_coinduce_act_unit G' H' phi X b)

def bridge_def_phi_lower_ok : blind_def_phi_lower_ok ≔ G H phi X ↦ bridge_phi_lower_ok_at G H phi X

{` For every ok, the blind action is ours (pointwise on functions). `}
def bridge_phi_lower_act_path (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (ok : (X : BlindAbsGSet G) → BlindPhiLowerOK G H phi X) (X : BlindAbsGSet G) (h : H .carrier)
  (b : BlindPhiLowerSet G H phi X)
  : Id (AgsetCoinduceCarrier (bridge_ag7 G) (bridge_ag7 H) phi X)
      (agset_act (bridge_ag7 H) (blind_phi_lower G H phi ok X) h b)
      (agset_coinduce_act (bridge_ag7 G) (bridge_ag7 H) phi X h b)
  ≔ agset_coinduce_path (bridge_ag7 G) (bridge_ag7 H) phi X
      (agset_act (bridge_ag7 H) (blind_phi_lower G H phi ok X) h b)
      (agset_coinduce_act (bridge_ag7 G) (bridge_ag7 H) phi X h b)
      (t ↦ refl (b .fst (H .mul (H .inv h) t)))

def bridge_phi_lower_path (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (ok : (X : BlindAbsGSet G) → BlindPhiLowerOK G H phi X) (X : BlindAbsGSet G)
  : Id (AbstractGSet (bridge_ag7 H)) (blind_phi_lower G H phi ok X) (agset_coinduce (bridge_ag7 G) (bridge_ag7 H) phi X)
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    agset_path_from_iso H' (blind_phi_lower G H phi ok X) (agset_coinduce G' H' phi X)
      (identity_equiv (AgsetCoinduceCarrier G' H' phi X), h b ↦ bridge_phi_lower_act_path G H phi ok X h b)

{` xca:phi^*-|phi_*, for every ok. `}
def bridge_xca_phi_lower_adj : blind_xca_phi_lower_adj
  ≔ G H phi ok X Y ↦
    let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let A ≔ AbstractGSetHom G' (agset_restrict G' H' phi Y) X in
    let B ≔ AbstractGSetHom H' Y (agset_coinduce G' H' phi X) in
    let C ≔ AbstractGSetHom H' Y (blind_phi_lower G H phi ok X) in
    bridge_book_equiv_of A C
      (compose_equiv A B C (restrict_coinduce_abstract_adjunction G' H' phi X Y)
        (transport_equiv B C
          (refl ((Z ↦ AbstractGSetHom H' Y Z) : AbstractGSet H' → Type)
            (inverse (AbstractGSet H') (blind_phi_lower G H phi ok X) (agset_coinduce G' H' phi X)
              (bridge_phi_lower_path G H phi ok X)))))
