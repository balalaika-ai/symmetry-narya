export "1158-fgauto-finite-index"

{` Chapter 11, automata part 10: the theorem at fggroups.tex:946, second
   sentence ("a f.g. subgroup H is normal iff S(H) is vertex-transitive").

   As printed this is false: for H = <a> in F(a, b), S(H) has a single
   vertex (with an a-loop), so it is vertex-transitive, but H is not normal
   since b a b^-1 is not in H (fgauto_normal_vertex_transitive_counterexample,
   computed with the decision procedure of 932).  The statement becomes
   true for subgroups of finite index, i.e. when S(H) is total (844): then
   H is normal iff S(H) is vertex-transitive
   (fgauto_total_normal_iff_vertex_transitive).  (A nontrivial normal f.g.
   subgroup always has finite index, a further theorem not formalized here;
   the trivial subgroup is normal and S(1) is a single vertex.)

   The first sentence (conjugacy of f.g. subgroups is decidable, "G, H are
   conjugate iff their cores are equal") is not formalized; see the
   inventory note.

   Vertex-transitivity: for any two vertices p, q there is an automorphism
   of S(H) (a bijection of the vertex set preserving and reflecting labelled
   edges) taking p to q.  Normality: w h w^-1 in H for all words w and all
   h in H. `}

def FgautoNormal (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : Type
  ≔ (w h : SignedWord S) → FgautoInSubgroup S dec gens h
    → FgautoInSubgroup S dec gens (append (SignedLetter S) (append (SignedLetter S) w h) (word_inverse S w))

def FgautoStallingsEdgePreserving (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (f : FgautoStallingsVertex S dec gens → FgautoStallingsVertex S dec gens) : Type
  ≔ (p q : FgautoStallingsVertex S dec gens) (x : SignedLetter S)
    → Product (FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (p .fst) x (q .fst)
                → FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (f p .fst) x (f q .fst))
        (FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (f p .fst) x (f q .fst)
                → FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (p .fst) x (q .fst))

def FgautoStallingsAutomorphism (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : Type
  ≔ Σ (Equiv (FgautoStallingsVertex S dec gens) (FgautoStallingsVertex S dec gens))
      (e ↦ FgautoStallingsEdgePreserving S dec gens (e .map))

def FgautoVertexTransitive (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) : Type
  ≔ (p q : FgautoStallingsVertex S dec gens)
    → Mere (Σ (FgautoStallingsAutomorphism S dec gens) (a ↦ Id (FgautoStallingsVertex S dec gens) (a .fst .map p) q))

{` The counterexample H = <a> in F(Bool). `}
def fgauto_litmus_bab_not_in_a
  : Id Bool (fgauto_member_bool Bool fw_bool_decidable_equality fgauto_gens_a
      (fgauto_w3 fw_letter_b fw_letter_a fw_letter_B)) false.
  ≔ refl (false. : Bool)

def fgauto_stallings_vertices_a
  : Id (List (SignedWord Bool)) (fgauto_stallings_vertices Bool fw_bool_decidable_equality fgauto_gens_a)
      (cons. (nil. : SignedWord Bool) nil.)
  ≔ refl (cons. (nil. : SignedWord Bool) nil. : List (SignedWord Bool))

def fgauto_vertex_a_unique (p : FgautoStallingsVertex Bool fw_bool_decidable_equality fgauto_gens_a)
  : Id (SignedWord Bool) (p .fst) nil.
  ≔ mere_rec (FgautoMem (SignedWord Bool) (p .fst) (fgauto_stallings_vertices Bool fw_bool_decidable_equality fgauto_gens_a))
      (Id (SignedWord Bool) (p .fst) nil.) (signed_word_set Bool fw_bool_decidable_equality (p .fst) nil.)
      (m ↦ match m [ inl. e ↦ e | inr. k ↦ match k [] ]) (p .snd)

def fgauto_identity_automorphism (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  : FgautoStallingsAutomorphism S dec gens
  ≔ (quasi_inverse_equiv (FgautoStallingsVertex S dec gens) (FgautoStallingsVertex S dec gens) (v ↦ v) (v ↦ v)
       (v ↦ refl v) (v ↦ refl v),
     p q x ↦ (s ↦ s, s ↦ s))

def fgauto_normal_vertex_transitive_counterexample
  : Product (FgautoVertexTransitive Bool fw_bool_decidable_equality fgauto_gens_a)
      (Not (FgautoNormal Bool fw_bool_decidable_equality fgauto_gens_a))
  ≔ let dec ≔ fw_bool_decidable_equality in
    let gens ≔ fgauto_gens_a in
    (p q ↦ mere (Σ (FgautoStallingsAutomorphism Bool dec gens) (a ↦
          Id (FgautoStallingsVertex Bool dec gens) (a .fst .map p) q))
       (fgauto_identity_automorphism Bool dec gens,
        fgauto_list_set_path (SignedWord Bool) (fgauto_stallings_vertices Bool dec gens) p q
          (fgauto_wtrans Bool (p .fst) nil. (q .fst) (fgauto_vertex_a_unique p)
            (fgauto_wsym Bool (q .fst) nil. (fgauto_vertex_a_unique q)))),
     hn ↦ bool_encode true. false.
       (concat Bool true.
         (fgauto_member_bool Bool dec gens
           (append (SignedLetter Bool) (append (SignedLetter Bool) (fgauto_w1 fw_letter_b) (fgauto_w1 fw_letter_a))
             (word_inverse Bool (fgauto_w1 fw_letter_b))))
         false.
         (inverse Bool (fgauto_member_bool Bool dec gens
             (append (SignedLetter Bool) (append (SignedLetter Bool) (fgauto_w1 fw_letter_b) (fgauto_w1 fw_letter_a))
               (word_inverse Bool (fgauto_w1 fw_letter_b)))) true.
           (fgauto_decision_bool_true (FgautoInSubgroup Bool dec gens
               (append (SignedLetter Bool) (append (SignedLetter Bool) (fgauto_w1 fw_letter_b) (fgauto_w1 fw_letter_a))
                 (word_inverse Bool (fgauto_w1 fw_letter_b)))) (fgauto_generalized_word_problem Bool dec gens
               (append (SignedLetter Bool) (append (SignedLetter Bool) (fgauto_w1 fw_letter_b) (fgauto_w1 fw_letter_a))
                 (word_inverse Bool (fgauto_w1 fw_letter_b))))
             (hn (fgauto_w1 fw_letter_b) (fgauto_w1 fw_letter_a)
               (fgauto_in_subgroup_generator Bool dec gens (fgauto_w1 fw_letter_a) (inl. (refl (fgauto_w1 fw_letter_a)))))))
         fgauto_litmus_bab_not_in_a))

{` Corrected version (S(H) total).  Normality lets left multiplication
   respect right cosets. `}
def fgauto_normal_left (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S)) (hn : FgautoNormal S dec gens)
  (g x y : SignedWord S) (h : FgautoSameCoset S dec gens x y)
  : FgautoSameCoset S dec gens (append (SignedLetter S) g x) (append (SignedLetter S) g y)
  ≔ let iy ≔ word_inverse S y in
    let ig ≔ word_inverse S g in
    fgauto_in_subgroup_red S dec gens
      (append (SignedLetter S) (append (SignedLetter S) g (append (SignedLetter S) x iy)) ig)
      (append (SignedLetter S) (append (SignedLetter S) g x) (word_inverse S (append (SignedLetter S) g y)))
      (refl (word_reduction S dec)
        (calc
          append (SignedLetter S) (append (SignedLetter S) g (append (SignedLetter S) x iy)) ig
          = append (SignedLetter S) g (append (SignedLetter S) (append (SignedLetter S) x iy) ig)
            by append_assoc (SignedLetter S) g (append (SignedLetter S) x iy) ig
          = append (SignedLetter S) g (append (SignedLetter S) x (append (SignedLetter S) iy ig))
            by refl ((z ↦ append (SignedLetter S) g z) : SignedWord S → SignedWord S) (append_assoc (SignedLetter S) x iy ig)
          = append (SignedLetter S) (append (SignedLetter S) g x) (append (SignedLetter S) iy ig)
            by fgauto_wsym S (append (SignedLetter S) (append (SignedLetter S) g x) (append (SignedLetter S) iy ig))
                 (append (SignedLetter S) g (append (SignedLetter S) x (append (SignedLetter S) iy ig)))
                 (append_assoc (SignedLetter S) g x (append (SignedLetter S) iy ig))
          = append (SignedLetter S) (append (SignedLetter S) g x) (word_inverse S (append (SignedLetter S) g y))
            by refl ((z ↦ append (SignedLetter S) (append (SignedLetter S) g x) z) : SignedWord S → SignedWord S)
                 (fgauto_wsym S (word_inverse S (append (SignedLetter S) g y)) (append (SignedLetter S) iy ig)
                   (fgauto_word_inverse_append S g y)) ∎))
      (hn g (append (SignedLetter S) x iy) h)

{` Words leading to the vertex reached by z are in the coset of z. `}
def fgauto_vertex_word_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (z : SignedWord S)
  : FgautoSameCoset S dec gens (fgauto_vertex_word S dec gens (fgauto_total_vertex S dec gens tot z) .fst) z
  ≔ let v ≔ fgauto_total_vertex S dec gens tot z in
    let w ≔ fgauto_vertex_word S dec gens v in
    fgauto_total_vertex_reflects S dec gens tot (w .fst) z (fgauto_total_vertex_of_run S dec gens tot (w .fst) v (w .snd))

def fgauto_word_of_vertex (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (v : FgautoStallingsVertex S dec gens) : SignedWord S
  ≔ fgauto_vertex_word S dec gens v .fst

def fgauto_vertex_of_word_of_vertex (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (v : FgautoStallingsVertex S dec gens)
  : Id (FgautoStallingsVertex S dec gens) (fgauto_total_vertex S dec gens tot (fgauto_word_of_vertex S dec gens v)) v
  ≔ fgauto_total_vertex_of_run S dec gens tot (fgauto_word_of_vertex S dec gens v) v (fgauto_vertex_word S dec gens v .snd)

{` The translation r |-> [g t_r] for a word g (g = v u^-1 below). `}
def fgauto_translate (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (g : SignedWord S) (r : FgautoStallingsVertex S dec gens)
  : FgautoStallingsVertex S dec gens
  ≔ fgauto_total_vertex S dec gens tot (append (SignedLetter S) g (fgauto_word_of_vertex S dec gens r))

def fgauto_translate_coset (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hn : FgautoNormal S dec gens) (g z : SignedWord S)
  : Id (FgautoStallingsVertex S dec gens) (fgauto_translate S dec gens tot g (fgauto_total_vertex S dec gens tot z))
      (fgauto_total_vertex S dec gens tot (append (SignedLetter S) g z))
  ≔ fgauto_total_vertex_respects S dec gens tot
      (append (SignedLetter S) g (fgauto_word_of_vertex S dec gens (fgauto_total_vertex S dec gens tot z)))
      (append (SignedLetter S) g z)
      (fgauto_normal_left S dec gens hn g (fgauto_word_of_vertex S dec gens (fgauto_total_vertex S dec gens tot z)) z
        (fgauto_vertex_word_coset S dec gens tot z))

{` Composition of translations: translate g (translate g' r) = translate (g g') r. `}
def fgauto_translate_compose (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hn : FgautoNormal S dec gens) (g g' : SignedWord S)
  (r : FgautoStallingsVertex S dec gens)
  : Id (FgautoStallingsVertex S dec gens) (fgauto_translate S dec gens tot g (fgauto_translate S dec gens tot g' r))
      (fgauto_translate S dec gens tot (append (SignedLetter S) g g') r)
  ≔ let V ≔ FgautoStallingsVertex S dec gens in
    let t ≔ fgauto_word_of_vertex S dec gens r in
    concat V (fgauto_translate S dec gens tot g (fgauto_translate S dec gens tot g' r))
      (fgauto_total_vertex S dec gens tot (append (SignedLetter S) g (append (SignedLetter S) g' t)))
      (fgauto_translate S dec gens tot (append (SignedLetter S) g g') r)
      (fgauto_translate_coset S dec gens tot hn g (append (SignedLetter S) g' t))
      (refl (fgauto_total_vertex S dec gens tot)
        (fgauto_wsym S (append (SignedLetter S) (append (SignedLetter S) g g') t)
          (append (SignedLetter S) g (append (SignedLetter S) g' t)) (append_assoc (SignedLetter S) g g' t)))

{` Translating by a word with trivial reduction is the identity. `}
def fgauto_translate_trivial (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (g : SignedWord S) (hg : Id (SignedWord S) (word_reduction S dec g) nil.)
  (r : FgautoStallingsVertex S dec gens)
  : Id (FgautoStallingsVertex S dec gens) (fgauto_translate S dec gens tot g r) r
  ≔ let V ≔ FgautoStallingsVertex S dec gens in
    let t ≔ fgauto_word_of_vertex S dec gens r in
    concat V (fgauto_translate S dec gens tot g r) (fgauto_total_vertex S dec gens tot t) r
      (fgauto_total_vertex_respects S dec gens tot (append (SignedLetter S) g t) t
        (fgauto_in_subgroup_red S dec gens nil. (append (SignedLetter S) (append (SignedLetter S) g t) (word_inverse S t))
          (fgauto_wsym S (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) g t) (word_inverse S t))) nil.
            (fgauto_wtrans S (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) g t) (word_inverse S t)))
              (word_reduction S dec (append (SignedLetter S) g (append (SignedLetter S) t (word_inverse S t))))
              nil.
              (fgauto_red_assoc S dec g t (word_inverse S t))
              (fgauto_wtrans S (word_reduction S dec (append (SignedLetter S) g (append (SignedLetter S) t (word_inverse S t))))
                (word_reduction S dec g) nil.
                (fgauto_red_drop_right S dec g (append (SignedLetter S) t (word_inverse S t)) (fgauto_red_inverse_right S dec t))
                hg)))
          (fgauto_in_subgroup_unit S dec gens)))
      (fgauto_vertex_of_word_of_vertex S dec gens tot r)

{` Steps of a total S(H): the vertex reached by z x is a step from the
   vertex reached by z. `}
def fgauto_total_step (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (z : SignedWord S) (x : SignedLetter S)
  : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (fgauto_total_vertex S dec gens tot z .fst) x
      (fgauto_total_vertex S dec gens tot (append (SignedLetter S) z (cons. x nil.)) .fst)
  ≔ let E ≔ fgauto_stallings_edges S dec gens in
    let b ≔ fgauto_stallings_base S dec gens in
    let hd ≔ fgauto_stallings_deterministic S dec gens in
    let rz ≔ fgauto_stallings_total_run S dec gens tot z in
    let rzx ≔ fgauto_stallings_total_run S dec gens tot (append (SignedLetter S) z (cons. x nil.)) in
    let sp ≔ fgauto_run_split S (SignedWord S) E b z (cons. x nil.) (rzx .fst) (rzx .snd .snd) in
    let em ≔ fgauto_run_unique S (SignedWord S) E hd b z (sp .fst) (rz .fst) (sp .snd .fst) (rz .snd .snd) in
    let last ≔ sp .snd .snd in
    fgauto_step_transport S (SignedWord S) E (sp .fst) (rz .fst) x x (last .fst) (rzx .fst) em (refl x) (last .snd .snd)
      (last .snd .fst)

def fgauto_step_vertex_of_word (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (r r' : FgautoStallingsVertex S dec gens) (x : SignedLetter S)
  (s : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (r .fst) x (r' .fst))
  : Id (FgautoStallingsVertex S dec gens)
      (fgauto_total_vertex S dec gens tot (append (SignedLetter S) (fgauto_word_of_vertex S dec gens r) (cons. x nil.))) r'
  ≔ let w ≔ fgauto_vertex_word S dec gens r in
    fgauto_total_vertex_of_run S dec gens tot (append (SignedLetter S) (w .fst) (cons. x nil.)) r'
      (fgauto_run_append S (SignedWord S) (fgauto_stallings_edges S dec gens) (fgauto_stallings_base S dec gens) (w .fst)
        (r .fst) (cons. x nil.) (r' .fst) (w .snd)
        (fgauto_run_single S (SignedWord S) (fgauto_stallings_edges S dec gens) (r .fst) x (r' .fst) s))

def fgauto_vertex_step_transport (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (a a' c c' : FgautoStallingsVertex S dec gens) (x : SignedLetter S)
  (e1 : Id (FgautoStallingsVertex S dec gens) a a') (e2 : Id (FgautoStallingsVertex S dec gens) c c')
  (s : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (a .fst) x (c .fst))
  : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (a' .fst) x (c' .fst)
  ≔ fgauto_step_transport S (SignedWord S) (fgauto_stallings_edges S dec gens) (a .fst) (a' .fst) x x (c .fst) (c' .fst)
      (refl ((z ↦ z .fst) : FgautoStallingsVertex S dec gens → SignedWord S) e1) (refl x)
      (refl ((z ↦ z .fst) : FgautoStallingsVertex S dec gens → SignedWord S) e2) s

{` Translations preserve steps. `}
def fgauto_translate_step (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hn : FgautoNormal S dec gens) (g : SignedWord S)
  (r r' : FgautoStallingsVertex S dec gens) (x : SignedLetter S)
  (s : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (r .fst) x (r' .fst))
  : FgautoStep S (SignedWord S) (fgauto_stallings_edges S dec gens) (fgauto_translate S dec gens tot g r .fst) x
      (fgauto_translate S dec gens tot g r' .fst)
  ≔ let V ≔ FgautoStallingsVertex S dec gens in
    let t ≔ fgauto_word_of_vertex S dec gens r in
    let gt ≔ append (SignedLetter S) g t in
    let tx ≔ append (SignedLetter S) t (cons. x nil.) in
    fgauto_vertex_step_transport S dec gens (fgauto_total_vertex S dec gens tot gt) (fgauto_translate S dec gens tot g r)
      (fgauto_total_vertex S dec gens tot (append (SignedLetter S) gt (cons. x nil.))) (fgauto_translate S dec gens tot g r') x
      (refl (fgauto_total_vertex S dec gens tot gt))
      (concat V (fgauto_total_vertex S dec gens tot (append (SignedLetter S) gt (cons. x nil.)))
        (fgauto_total_vertex S dec gens tot (append (SignedLetter S) g tx))
        (fgauto_translate S dec gens tot g r')
        (refl (fgauto_total_vertex S dec gens tot) (append_assoc (SignedLetter S) g t (cons. x nil.)))
        (concat V (fgauto_total_vertex S dec gens tot (append (SignedLetter S) g tx))
          (fgauto_translate S dec gens tot g (fgauto_total_vertex S dec gens tot tx))
          (fgauto_translate S dec gens tot g r')
          (inverse V (fgauto_translate S dec gens tot g (fgauto_total_vertex S dec gens tot tx))
            (fgauto_total_vertex S dec gens tot (append (SignedLetter S) g tx))
            (fgauto_translate_coset S dec gens tot hn g tx))
          (refl (fgauto_translate S dec gens tot g) (fgauto_step_vertex_of_word S dec gens tot r r' x s))))
      (fgauto_total_step S dec gens tot gt x)

{` The translation by g as an automorphism (inverse: translation by g^-1). `}
def fgauto_translate_automorphism (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hn : FgautoNormal S dec gens) (g : SignedWord S)
  : FgautoStallingsAutomorphism S dec gens
  ≔ let V ≔ FgautoStallingsVertex S dec gens in
    let ig ≔ word_inverse S g in
    let f ≔ fgauto_translate S dec gens tot g in
    let f' ≔ fgauto_translate S dec gens tot ig in
    let back : (r : V) → Id V (f' (f r)) r
      ≔ r ↦ concat V (f' (f r)) (fgauto_translate S dec gens tot (append (SignedLetter S) ig g) r) r
          (fgauto_translate_compose S dec gens tot hn ig g r)
          (fgauto_translate_trivial S dec gens tot (append (SignedLetter S) ig g) (fgauto_red_inverse_left S dec g) r) in
    let forth : (r : V) → Id V (f (f' r)) r
      ≔ r ↦ concat V (f (f' r)) (fgauto_translate S dec gens tot (append (SignedLetter S) g ig) r) r
          (fgauto_translate_compose S dec gens tot hn g ig r)
          (fgauto_translate_trivial S dec gens tot (append (SignedLetter S) g ig) (fgauto_red_inverse_right S dec g) r) in
    (quasi_inverse_equiv V V f f' back forth,
     p q x ↦ (s ↦ fgauto_translate_step S dec gens tot hn g p q x s,
              s ↦ fgauto_vertex_step_transport S dec gens (f' (f p)) p (f' (f q)) q x (back p) (back q)
                (fgauto_translate_step S dec gens tot hn ig (f p) (f q) x s)))

{` Normal => vertex-transitive (S(H) total): translate by t_q t_p^-1. `}
def fgauto_total_normal_vertex_transitive (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hn : FgautoNormal S dec gens) : FgautoVertexTransitive S dec gens
  ≔ p q ↦
    let V ≔ FgautoStallingsVertex S dec gens in
    let tp ≔ fgauto_word_of_vertex S dec gens p in
    let tq ≔ fgauto_word_of_vertex S dec gens q in
    let g ≔ append (SignedLetter S) tq (word_inverse S tp) in
    mere (Σ (FgautoStallingsAutomorphism S dec gens) (a ↦ Id V (a .fst .map p) q))
      (fgauto_translate_automorphism S dec gens tot hn g,
       concat V (fgauto_translate S dec gens tot g p) (fgauto_total_vertex S dec gens tot tq) q
         (fgauto_total_vertex_respects S dec gens tot (append (SignedLetter S) g tp) tq
           (fgauto_in_subgroup_red S dec gens nil.
             (append (SignedLetter S) (append (SignedLetter S) g tp) (word_inverse S tq))
             (fgauto_wsym S (word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) g tp) (word_inverse S tq))) nil.
               (calc
                 word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) g tp) (word_inverse S tq))
                 = word_reduction S dec (append (SignedLetter S) (append (SignedLetter S) tq (append (SignedLetter S) (word_inverse S tp) tp))
                     (word_inverse S tq))
                   by refl ((z ↦ word_reduction S dec (append (SignedLetter S) z (word_inverse S tq))) : SignedWord S → SignedWord S)
                        (append_assoc (SignedLetter S) tq (word_inverse S tp) tp)
                 = word_reduction S dec (append (SignedLetter S) tq (word_inverse S tq))
                   by fgauto_red_congr_left S dec (append (SignedLetter S) tq (append (SignedLetter S) (word_inverse S tp) tp)) tq
                        (word_inverse S tq)
                        (fgauto_red_drop_right S dec tq (append (SignedLetter S) (word_inverse S tp) tp) (fgauto_red_inverse_left S dec tp))
                 = nil.
                   by fgauto_red_inverse_right S dec tq ∎))
             (fgauto_in_subgroup_unit S dec gens)))
         (fgauto_vertex_of_word_of_vertex S dec gens tot q))

{` Automorphisms carry runs. `}
def fgauto_automorphism_run (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (a : FgautoStallingsAutomorphism S dec gens) (p : FgautoStallingsVertex S dec gens) (w : SignedWord S)
  (q : FgautoStallingsVertex S dec gens)
  (r : FgautoRun S (SignedWord S) (fgauto_stallings_edges S dec gens) (p .fst) w (q .fst))
  : FgautoRun S (SignedWord S) (fgauto_stallings_edges S dec gens) (a .fst .map p .fst) w (a .fst .map q .fst)
  ≔ let V ≔ FgautoStallingsVertex S dec gens in
    let E ≔ fgauto_stallings_edges S dec gens in
    match w [
    | nil. ↦ refl ((z ↦ a .fst .map z .fst) : V → SignedWord S)
        (fgauto_list_set_path (SignedWord S) (fgauto_stallings_vertices S dec gens) p q r)
    | cons. x w' ↦
      let m ≔ fgauto_stallings_endpoint_vertex S dec gens (p .fst) x (r .fst) (r .snd .fst) .snd in
      let rv : V ≔ (r .fst, mere (FgautoMem (SignedWord S) (r .fst) (fgauto_stallings_vertices S dec gens)) m) in
      (a .fst .map rv .fst, (a .snd p rv x .fst (r .snd .fst), fgauto_automorphism_run S dec gens a rv w' q (r .snd .snd))) ]

{` Vertex-transitive => normal (S(H) total). `}
def fgauto_total_vertex_transitive_normal (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens) (hv : FgautoVertexTransitive S dec gens) : FgautoNormal S dec gens
  ≔ w h mh ↦
    let V ≔ FgautoStallingsVertex S dec gens in
    let E ≔ fgauto_stallings_edges S dec gens in
    let b ≔ fgauto_stallings_base S dec gens in
    let hd ≔ fgauto_stallings_deterministic S dec gens in
    let hs ≔ fgauto_stallings_symmetric S dec gens in
    let bv : V ≔ (b, mere (FgautoMem (SignedWord S) b (fgauto_stallings_vertices S dec gens)) (fgauto_stallings_base_vertex S dec gens)) in
    let rw ≔ fgauto_stallings_total_run S dec gens tot w in
    let pv : V ≔ fgauto_total_vertex S dec gens tot w in
    let goal ≔ FgautoInSubgroup S dec gens (append (SignedLetter S) (append (SignedLetter S) w h) (word_inverse S w)) in
    let rh ≔ fgauto_stallings_total_run S dec gens tot h in
    let acc ≔ fgauto_delta_sound S (SignedWord S) dec (signed_word_decidable_equality S dec) E b (word_reduction S dec h) b
      (fgauto_member_accepted S dec gens (word_reduction S dec h) (word_reduction_reduced S dec h)
        (fgauto_in_subgroup_red S dec gens h (word_reduction S dec h)
          (fgauto_wsym S (word_reduction S dec (word_reduction S dec h)) (word_reduction S dec h) (word_reduction_idempotent S dec h)) mh)) in
    let eh ≔ fgauto_run_unique S (SignedWord S) E hd b (word_reduction S dec h) (rh .fst) b
      (fgauto_run_reduction S (SignedWord S) dec E hs hd b h (rh .fst) (rh .snd .snd)) acc in
    let hloop ≔ fgauto_run_end S (SignedWord S) E b h (rh .fst) b eh (rh .snd .snd) in
    mere_rec (Σ (FgautoStallingsAutomorphism S dec gens) (a ↦ Id V (a .fst .map bv) pv)) goal
      (fgauto_in_subgroup_prop S dec gens (append (SignedLetter S) (append (SignedLetter S) w h) (word_inverse S w)))
      (z ↦
        let a ≔ z .fst in
        let ep ≔ refl ((y ↦ y .fst) : V → SignedWord S) (z .snd) in
        let hp ≔ fgauto_run_end S (SignedWord S) E (rw .fst) h (a .fst .map bv .fst) (rw .fst) ep
          (fgauto_run_start S (SignedWord S) E (a .fst .map bv .fst) (rw .fst) h (a .fst .map bv .fst) ep
            (fgauto_automorphism_run S dec gens a bv h bv hloop)) in
        fgauto_run_loop_member S dec gens E (fgauto_stallings_coset_inv S dec gens .fst) b
          (fgauto_stallings_coset_inv S dec gens .snd)
          (append (SignedLetter S) (append (SignedLetter S) w h) (word_inverse S w))
          (fgauto_run_append S (SignedWord S) E b (append (SignedLetter S) w h) (rw .fst) (word_inverse S w) b
            (fgauto_run_append S (SignedWord S) E b w (rw .fst) h (rw .fst) (rw .snd .snd) hp)
            (fgauto_run_inverse S (SignedWord S) E hs b w (rw .fst) (rw .snd .snd))))
      (hv bv pv)

def fgauto_total_normal_iff_vertex_transitive (S : Type) (dec : DecidableEquality S) (gens : List (SignedWord S))
  (tot : FgautoStallingsTotal S dec gens)
  : Product (FgautoNormal S dec gens → FgautoVertexTransitive S dec gens)
      (FgautoVertexTransitive S dec gens → FgautoNormal S dec gens)
  ≔ (fgauto_total_normal_vertex_transitive S dec gens tot, fgauto_total_vertex_transitive_normal S dec gens tot)
