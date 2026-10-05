export "1166-fgauto-thompson"

{` Chapter 11, automata part 18: correctness of Thompson's construction:
   for every rational expression r over a monoid M (with its laws), the
   values of the runs from the start to the end state of
   fgauto_thompson r are exactly the elements of the rational subset of r
   (fgauto_thompson_correct). `}

def fgauto_allin_map (A : Type) (P Q : A → Type) (f : (a : A) → P a → Q a) (l : List A) (h : FgautoAllIn A P l) : FgautoAllIn A Q l
  ≔ match l [ nil. ↦ star. | cons. a t ↦ (f a (h .fst), fgauto_allin_map A P Q f t (h .snd)) ]

{` Small monoid computations. `}
def fgauto_eval_eps (M : FgautoMonoid) (L : FgautoMonoidLaws M) (w : SignedWord (M .mcarrier))
  : Id (M .mcarrier) (fgauto_path_eval M (cons. (fgauto_teps M) w)) (fgauto_path_eval M w)
  ≔ L .ml_unit_left (fgauto_path_eval M w)

def fgauto_eval_join (M : FgautoMonoid) (L : FgautoMonoidLaws M) (w1 w2 : SignedWord (M .mcarrier))
  : Id (M .mcarrier) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) w2)))
      (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M w2))
  ≔ concat (M .mcarrier) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) w2)))
      (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M (cons. (fgauto_teps M) w2)))
      (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M w2))
      (fgauto_path_eval_append M L w1 (cons. (fgauto_teps M) w2))
      (refl (M .mmul (fgauto_path_eval M w1)) (fgauto_eval_eps M L w2))

def fgauto_eval_join_end (M : FgautoMonoid) (L : FgautoMonoidLaws M) (w1 : SignedWord (M .mcarrier))
  : Id (M .mcarrier) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) nil.)))
      (fgauto_path_eval M w1)
  ≔ concat (M .mcarrier) (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) nil.)))
      (M .mmul (fgauto_path_eval M w1) (M .munit)) (fgauto_path_eval M w1)
      (fgauto_eval_join M L w1 nil.) (L .ml_unit_right (fgauto_path_eval M w1))

{` Finite sets. `}
def fgauto_tfin_step (M : FgautoMonoid) (l : List (M .mcarrier)) (p : List Nat) (x : SignedLetter (M .mcarrier)) (q : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_tfin_edges M l) p x q)
  : Σ (M .mcarrier) (m ↦ Product (FgautoMem (M .mcarrier) m l)
      (Product (Id (List Nat) p (cons. zero. nil.)) (Product (Id (SignedLetter (M .mcarrier)) x (inl. m)) (Id (List Nat) q (cons. fgauto_n1 nil.)))))
  ≔ match l [
  | nil. ↦ match s []
  | cons. m t ↦ match s [
    | inl. e ↦ (m, (inl. (refl m), (e .fst, (e .snd .fst, e .snd .snd))))
    | inr. s' ↦ let z ≔ fgauto_tfin_step M t p x q s' in (z .fst, (inr. (z .snd .fst), z .snd .snd)) ] ]

def fgauto_tfin_no_step_end (M : FgautoMonoid) (l : List (M .mcarrier)) (x : SignedLetter (M .mcarrier)) (q : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_tfin_edges M l) (cons. fgauto_n1 nil.) x q) : Empty
  ≔ fgauto_tag_clash fgauto_n1 zero. nil. nil. (fgauto_tfin_step M l (cons. fgauto_n1 nil.) x q s .snd .snd .fst)

def fgauto_thompson_fin_run (M : FgautoMonoid) (L : FgautoMonoidLaws M) (l : List (M .mcarrier)) (m : M .mcarrier)
  (w : SignedWord (M .mcarrier))
  (r : FgautoRun (M .mcarrier) (List Nat) (fgauto_tfin_edges M l) (cons. zero. nil.) w (cons. fgauto_n1 nil.))
  (e : Id (M .mcarrier) (fgauto_path_eval M w) m) : Mere (FgautoMem (M .mcarrier) m l)
  ≔ match w [
  | nil. ↦ match fgauto_tag_clash zero. fgauto_n1 nil. nil. r []
  | cons. x w' ↦
    let z ≔ fgauto_tfin_step M l (cons. zero. nil.) x (r .fst) (r .snd .fst) in
    match w' [
    | cons. y w'' ↦ match fgauto_tfin_no_step_end M l y (r .snd .snd .fst)
        (fgauto_step_transport (M .mcarrier) (List Nat) (fgauto_tfin_edges M l) (r .fst) (cons. fgauto_n1 nil.) y y
           (r .snd .snd .fst) (r .snd .snd .fst) (z .snd .snd .snd .snd) (refl y) (refl (r .snd .snd .fst)) (r .snd .snd .snd .fst)) []
    | nil. ↦ mere (FgautoMem (M .mcarrier) m l)
        (fgauto_mem_transport (M .mcarrier) (z .fst) m l
          (calc
            z .fst = M .mmul (z .fst) (M .munit) by inverse (M .mcarrier) (M .mmul (z .fst) (M .munit)) (z .fst) (L .ml_unit_right (z .fst))
            = M .mmul (fgauto_label_eval M x) (M .munit)
              by refl ((y ↦ M .mmul (fgauto_label_eval M y) (M .munit)) : SignedLetter (M .mcarrier) → M .mcarrier)
                   (inverse (SignedLetter (M .mcarrier)) x (inl. (z .fst)) (z .snd .snd .snd .fst))
            = m by e ∎)
          (z .snd .fst)) ] ]

def fgauto_thompson_fin (M : FgautoMonoid) (L : FgautoMonoidLaws M) (l : List (M .mcarrier)) (m : M .mcarrier)
  : FgautoIff (fgauto_rat_mem M (rat_fin. l) m) (FgautoThompsonLang M (fgauto_thompson M (rat_fin. l)) m)
  ≔ let C ≔ M .mcarrier in
    let E ≔ fgauto_tfin_edges M l in
    let T ≔ Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) E (cons. zero. nil.) w (cons. fgauto_n1 nil.))
       (Id C (fgauto_path_eval M w) m)) in
    (h ↦ mere_rec (FgautoMem C m l) (FgautoThompsonLang M (fgauto_thompson M (rat_fin. l)) m) (mere_isprop T)
       (k ↦ mere T (cons. (inl. m) nil.,
         (fgauto_run_single C (List Nat) E (cons. zero. nil.) (inl. m) (cons. fgauto_n1 nil.)
            (fgauto_mem_edge_step C (List Nat) E (cons. zero. nil., inl. m, cons. fgauto_n1 nil.)
              (fgauto_mem_map C (FgautoEdge C (List Nat)) (m0 ↦ (cons. zero. nil., inl. m0, cons. fgauto_n1 nil.)) m l k)),
          L .ml_unit_right m))) h,
     h ↦ mere_rec T (Mere (FgautoMem C m l)) (mere_isprop (FgautoMem C m l))
       (z ↦ fgauto_thompson_fin_run M L l m (z .fst) (z .snd .fst) (z .snd .snd)) h)

{` Leaving a region through its unique exit edge. `}
def FgautoExitData (M : FgautoMonoid) (G E : List (FgautoEdge (M .mcarrier) (List Nat))) (p te zx : List Nat)
  (w : SignedWord (M .mcarrier)) (q : List Nat) : Type
  ≔ Σ (SignedWord (M .mcarrier)) (w1 ↦ Σ (SignedWord (M .mcarrier)) (w2 ↦
      Product (Id (SignedWord (M .mcarrier)) w (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) w2)))
        (Product (FgautoRun (M .mcarrier) (List Nat) E p w1 te) (FgautoRun (M .mcarrier) (List Nat) G zx w2 q))))

def fgauto_region_exit_unique (M : FgautoMonoid) (G E R : List (FgautoEdge (M .mcarrier) (List Nat))) (k : Nat)
  (hc : FgautoRegionClassify M G E R k) (te zx : List Nat)
  (hx : (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat) → FgautoStep (M .mcarrier) (List Nat) R (cons. k pe) y z
    → Product (Id (List Nat) pe te) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z zx)))
  (p : List Nat) (w : SignedWord (M .mcarrier)) (q : List Nat) (nq : (q' : List Nat) → Not (Id (List Nat) q (cons. k q')))
  (r : FgautoRun (M .mcarrier) (List Nat) G (cons. k p) w q) : FgautoExitData M G E p te zx w q
  ≔ let ex ≔ fgauto_region_exit M G E R k hc p w q nq r in
    let w1 ≔ ex .fst in
    let y ≔ ex .snd .fst in
    let w2 ≔ ex .snd .snd .fst in
    let pe ≔ ex .snd .snd .snd .fst in
    let z ≔ ex .snd .snd .snd .snd .fst in
    let a ≔ hx pe y z (ex .snd .snd .snd .snd .snd .snd .snd .fst) in
    (w1, (w2,
      (concat (SignedWord (M .mcarrier)) w (append (SignedLetter (M .mcarrier)) w1 (cons. y w2))
         (append (SignedLetter (M .mcarrier)) w1 (cons. (fgauto_teps M) w2))
         (ex .snd .snd .snd .snd .snd .fst)
         (refl ((u ↦ append (SignedLetter (M .mcarrier)) w1 (cons. u w2)) : SignedLetter (M .mcarrier) → SignedWord (M .mcarrier)) (a .snd .fst)),
       (fgauto_run_end (M .mcarrier) (List Nat) E p w1 pe te (a .fst) (ex .snd .snd .snd .snd .snd .snd .fst),
        fgauto_run_start (M .mcarrier) (List Nat) G z zx w2 q (a .snd .snd) (ex .snd .snd .snd .snd .snd .snd .snd .snd)))))

def fgauto_exit_eval (M : FgautoMonoid) (L : FgautoMonoidLaws M) (G E : List (FgautoEdge (M .mcarrier) (List Nat)))
  (p te zx : List Nat) (w : SignedWord (M .mcarrier)) (q : List Nat) (d : FgautoExitData M G E p te zx w q)
  : Id (M .mcarrier) (fgauto_path_eval M w) (M .mmul (fgauto_path_eval M (d .fst)) (fgauto_path_eval M (d .snd .fst)))
  ≔ concat (M .mcarrier) (fgauto_path_eval M w)
      (fgauto_path_eval M (append (SignedLetter (M .mcarrier)) (d .fst) (cons. (fgauto_teps M) (d .snd .fst))))
      (M .mmul (fgauto_path_eval M (d .fst)) (fgauto_path_eval M (d .snd .fst)))
      (refl (fgauto_path_eval M) (d .snd .snd .fst)) (fgauto_eval_join M L (d .fst) (d .snd .fst))

{` A run from a state without outgoing steps is empty. `}
def fgauto_run_from_sink (M : FgautoMonoid) (G : List (FgautoEdge (M .mcarrier) (List Nat))) (s : List Nat)
  (hs : (x : SignedLetter (M .mcarrier)) (z : List Nat) → Not (FgautoStep (M .mcarrier) (List Nat) G s x z))
  (w : SignedWord (M .mcarrier)) (q : List Nat) (r : FgautoRun (M .mcarrier) (List Nat) G s w q)
  : Id (SignedWord (M .mcarrier)) w nil.
  ≔ match w [ nil. ↦ refl (nil. : SignedWord (M .mcarrier)) | cons. x w' ↦ match hs x (r .fst) (r .snd .fst) [] ]

{` Union. `}
def fgauto_union_glue_from2 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_union_glue M A B) (cons. fgauto_n2 nil.) x z)
  : Product (Id (SignedLetter (M .mcarrier)) x (fgauto_teps M))
      (Sum (Id (List Nat) z (cons. zero. (A .tstart))) (Id (List Nat) z (cons. fgauto_n1 (B .tstart))))
  ≔ match s [
  | inl. e ↦ (e .snd .fst, inl. (e .snd .snd))
  | inr. s1 ↦ match s1 [
    | inl. e ↦ (e .snd .fst, inr. (e .snd .snd))
    | inr. s2 ↦ match s2 [
      | inl. e ↦ match fgauto_tag_clash fgauto_n2 zero. nil. (A .tend) (e .fst) []
      | inr. s3 ↦ match s3 [
        | inl. e ↦ match fgauto_tag_clash fgauto_n2 fgauto_n1 nil. (B .tend) (e .fst) []
        | inr. s4 ↦ match s4 [] ] ] ] ]

def fgauto_union_from2 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_join2 M A B (fgauto_union_glue M A B)) (cons. fgauto_n2 nil.) x z)
  : Product (Id (SignedLetter (M .mcarrier)) x (fgauto_teps M))
      (Sum (Id (List Nat) z (cons. zero. (A .tstart))) (Id (List Nat) z (cons. fgauto_n1 (B .tstart))))
  ≔ let E1 ≔ fgauto_tpre M zero. (A .tedges) in
    let E2 ≔ fgauto_tpre M fgauto_n1 (B .tedges) in
    let C ≔ M .mcarrier in
    match fgauto_step_append_split C (List Nat) E1 (append (FgautoEdge C (List Nat)) E2 (fgauto_union_glue M A B)) (cons. fgauto_n2 nil.) x z s [
    | inl. s1 ↦ match fgauto_tpre_step_other M fgauto_n2 zero. (e ↦ e) (A .tedges) nil. x z s1 []
    | inr. s2 ↦ match fgauto_step_append_split C (List Nat) E2 (fgauto_union_glue M A B) (cons. fgauto_n2 nil.) x z s2 [
      | inl. s3 ↦ match fgauto_tpre_step_other M fgauto_n2 fgauto_n1 (e ↦ e) (B .tedges) nil. x z s3 []
      | inr. s4 ↦ fgauto_union_glue_from2 M A B x z s4 ] ]

def fgauto_union_sink (M : FgautoMonoid) (A B : FgautoThompsonAut M) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_join2 M A B (fgauto_union_glue M A B)) (cons. fgauto_n3 nil.) x z) : Empty
  ≔ let E1 ≔ fgauto_tpre M zero. (A .tedges) in
    let E2 ≔ fgauto_tpre M fgauto_n1 (B .tedges) in
    let C ≔ M .mcarrier in
    match fgauto_step_append_split C (List Nat) E1 (append (FgautoEdge C (List Nat)) E2 (fgauto_union_glue M A B)) (cons. fgauto_n3 nil.) x z s [
    | inl. s1 ↦ fgauto_tpre_step_other M fgauto_n3 zero. (e ↦ e) (A .tedges) nil. x z s1
    | inr. s2 ↦ match fgauto_step_append_split C (List Nat) E2 (fgauto_union_glue M A B) (cons. fgauto_n3 nil.) x z s2 [
      | inl. s3 ↦ fgauto_tpre_step_other M fgauto_n3 fgauto_n1 (e ↦ e) (B .tedges) nil. x z s3
      | inr. s4 ↦ match s4 [
        | inl. e ↦ fgauto_tag_clash fgauto_n3 fgauto_n2 nil. nil. (e .fst)
        | inr. s5 ↦ match s5 [
          | inl. e ↦ fgauto_tag_clash fgauto_n3 fgauto_n2 nil. nil. (e .fst)
          | inr. s6 ↦ match s6 [
            | inl. e ↦ fgauto_tag_clash fgauto_n3 zero. nil. (A .tend) (e .fst)
            | inr. s7 ↦ match s7 [
              | inl. e ↦ fgauto_tag_clash fgauto_n3 fgauto_n1 nil. (B .tend) (e .fst)
              | inr. s8 ↦ match s8 [] ] ] ] ] ] ]

def fgauto_union_exit0 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_union_glue M A B) (cons. zero. pe) y z)
  : Product (Id (List Nat) pe (A .tend)) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z (cons. fgauto_n3 nil.)))
  ≔ match s [
  | inl. e ↦ match fgauto_tag_clash zero. fgauto_n2 pe nil. (e .fst) []
  | inr. s1 ↦ match s1 [
    | inl. e ↦ match fgauto_tag_clash zero. fgauto_n2 pe nil. (e .fst) []
    | inr. s2 ↦ match s2 [
      | inl. e ↦ (fgauto_tag_tail zero. pe (A .tend) (e .fst), (e .snd .fst, e .snd .snd))
      | inr. s3 ↦ match s3 [
        | inl. e ↦ match fgauto_tag_clash zero. fgauto_n1 pe (B .tend) (e .fst) []
        | inr. s4 ↦ match s4 [] ] ] ] ]

def fgauto_union_exit1 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_union_glue M A B) (cons. fgauto_n1 pe) y z)
  : Product (Id (List Nat) pe (B .tend)) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z (cons. fgauto_n3 nil.)))
  ≔ match s [
  | inl. e ↦ match fgauto_tag_clash fgauto_n1 fgauto_n2 pe nil. (e .fst) []
  | inr. s1 ↦ match s1 [
    | inl. e ↦ match fgauto_tag_clash fgauto_n1 fgauto_n2 pe nil. (e .fst) []
    | inr. s2 ↦ match s2 [
      | inl. e ↦ match fgauto_tag_clash fgauto_n1 zero. pe (A .tend) (e .fst) []
      | inr. s3 ↦ match s3 [
        | inl. e ↦ (fgauto_tag_tail fgauto_n1 pe (B .tend) (e .fst), (e .snd .fst, e .snd .snd))
        | inr. s4 ↦ match s4 [] ] ] ] ]

{` Runs through one branch of a union, in both directions. `}
def fgauto_union_branch_lang (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A B : FgautoThompsonAut M) (k : Nat)
  (AB : FgautoThompsonAut M) (hc : FgautoRegionClassify M (fgauto_join2 M A B (fgauto_union_glue M A B)) (AB .tedges) (fgauto_union_glue M A B) k)
  (hx : (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat) → FgautoStep (M .mcarrier) (List Nat) (fgauto_union_glue M A B) (cons. k pe) y z
    → Product (Id (List Nat) pe (AB .tend)) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z (cons. fgauto_n3 nil.))))
  (nk : (q' : List Nat) → Not (Id (List Nat) (cons. fgauto_n3 nil.) (cons. k q')))
  (w : SignedWord (M .mcarrier)) (m : M .mcarrier) (em : Id (M .mcarrier) (fgauto_path_eval M (cons. (fgauto_teps M) w)) m)
  (r : FgautoRun (M .mcarrier) (List Nat) (fgauto_join2 M A B (fgauto_union_glue M A B)) (cons. k (AB .tstart)) w (cons. fgauto_n3 nil.))
  : FgautoThompsonLang M AB m
  ≔ let C ≔ M .mcarrier in
    let G ≔ fgauto_join2 M A B (fgauto_union_glue M A B) in
    let d ≔ fgauto_region_exit_unique M G (AB .tedges) (fgauto_union_glue M A B) k hc (AB .tend) (cons. fgauto_n3 nil.) hx
      (AB .tstart) w (cons. fgauto_n3 nil.) nk r in
    let w2nil ≔ fgauto_run_from_sink M G (cons. fgauto_n3 nil.) (fgauto_union_sink M A B) (d .snd .fst) (cons. fgauto_n3 nil.) (d .snd .snd .snd .snd) in
    mere (Σ (SignedWord C) (w0 ↦ Product (FgautoRun C (List Nat) (AB .tedges) (AB .tstart) w0 (AB .tend)) (Id C (fgauto_path_eval M w0) m)))
      (d .fst, (d .snd .snd .snd .fst,
        calc
          fgauto_path_eval M (d .fst)
          = M .mmul (fgauto_path_eval M (d .fst)) (M .munit)
            by inverse C (M .mmul (fgauto_path_eval M (d .fst)) (M .munit)) (fgauto_path_eval M (d .fst)) (L .ml_unit_right (fgauto_path_eval M (d .fst)))
          = M .mmul (fgauto_path_eval M (d .fst)) (fgauto_path_eval M (d .snd .fst))
            by refl ((u ↦ M .mmul (fgauto_path_eval M (d .fst)) (fgauto_path_eval M u)) : SignedWord C → C)
                 (inverse (SignedWord C) (d .snd .fst) nil. w2nil)
          = fgauto_path_eval M w
            by inverse C (fgauto_path_eval M w) (M .mmul (fgauto_path_eval M (d .fst)) (fgauto_path_eval M (d .snd .fst)))
                 (fgauto_exit_eval M L G (AB .tedges) (AB .tstart) (AB .tend) (cons. fgauto_n3 nil.) w (cons. fgauto_n3 nil.) d)
          = fgauto_path_eval M (cons. (fgauto_teps M) w)
            by inverse C (fgauto_path_eval M (cons. (fgauto_teps M) w)) (fgauto_path_eval M w) (fgauto_eval_eps M L w)
          = m by em ∎))

def fgauto_thompson_union_out (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A B : FgautoThompsonAut M) (m : M .mcarrier)
  (w : SignedWord (M .mcarrier))
  (r : FgautoRun (M .mcarrier) (List Nat) (fgauto_join2 M A B (fgauto_union_glue M A B)) (cons. fgauto_n2 nil.) w (cons. fgauto_n3 nil.))
  (em : Id (M .mcarrier) (fgauto_path_eval M w) m)
  : Mere (Sum (FgautoThompsonLang M A m) (FgautoThompsonLang M B m))
  ≔ let C ≔ M .mcarrier in
    let G ≔ fgauto_join2 M A B (fgauto_union_glue M A B) in
    match w [
    | nil. ↦ match fgauto_tag_clash fgauto_n2 fgauto_n3 nil. nil. r []
    | cons. x w' ↦
      let f ≔ fgauto_union_from2 M A B x (r .fst) (r .snd .fst) in
      let em' : Id C (fgauto_path_eval M (cons. (fgauto_teps M) w')) m
        ≔ concat C (fgauto_path_eval M (cons. (fgauto_teps M) w')) (fgauto_path_eval M (cons. x w')) m
            (refl ((u ↦ fgauto_path_eval M (cons. u w')) : SignedLetter C → C) (inverse (SignedLetter C) x (fgauto_teps M) (f .fst))) em in
      match f .snd [
      | inl. ez ↦ mere (Sum (FgautoThompsonLang M A m) (FgautoThompsonLang M B m))
          (inl. (fgauto_union_branch_lang M L A B zero. A (fgauto_join2_classify0 M A B (fgauto_union_glue M A B))
            (fgauto_union_exit0 M A B) (q' e ↦ fgauto_tag_clash fgauto_n3 zero. nil. q' e) w' m em'
            (fgauto_run_start C (List Nat) G (r .fst) (cons. zero. (A .tstart)) w' (cons. fgauto_n3 nil.) ez (r .snd .snd))))
      | inr. ez ↦ mere (Sum (FgautoThompsonLang M A m) (FgautoThompsonLang M B m))
          (inr. (fgauto_union_branch_lang M L A B fgauto_n1 B (fgauto_join2_classify1 M A B (fgauto_union_glue M A B))
            (fgauto_union_exit1 M A B) (q' e ↦ fgauto_tag_clash fgauto_n3 fgauto_n1 nil. q' e) w' m em'
            (fgauto_run_start C (List Nat) G (r .fst) (cons. fgauto_n1 (B .tstart)) w' (cons. fgauto_n3 nil.) ez (r .snd .snd)))) ] ]

def fgauto_glue_step_head (M : FgautoMonoid) (e : FgautoEdge (M .mcarrier) (List Nat)) (rest : List (FgautoEdge (M .mcarrier) (List Nat)))
  : FgautoStep (M .mcarrier) (List Nat) (cons. e rest) (e .src) (e .lab) (e .tgt)
  ≔ fgauto_step_head (M .mcarrier) (List Nat) e rest

def fgauto_thompson_union_in (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A B : FgautoThompsonAut M) (m : M .mcarrier)
  (h : Sum (FgautoThompsonLang M A m) (FgautoThompsonLang M B m))
  : FgautoThompsonLang M (fgauto_join2 M A B (fgauto_union_glue M A B), cons. fgauto_n2 nil., cons. fgauto_n3 nil.) m
  ≔ let C ≔ M .mcarrier in
    let glue ≔ fgauto_union_glue M A B in
    let G ≔ fgauto_join2 M A B glue in
    let ep ≔ fgauto_teps M in
    let T ≔ Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n3 nil.)) (Id C (fgauto_path_eval M w) m)) in
    let ev : (w : SignedWord C) → Id C (fgauto_path_eval M w) m → Id C (fgauto_path_eval M (cons. ep (append (SignedLetter C) w (cons. ep nil.)))) m
      ≔ w e ↦ concat C (fgauto_path_eval M (cons. ep (append (SignedLetter C) w (cons. ep nil.))))
          (fgauto_path_eval M (append (SignedLetter C) w (cons. ep nil.))) m
          (fgauto_eval_eps M L (append (SignedLetter C) w (cons. ep nil.)))
          (concat C (fgauto_path_eval M (append (SignedLetter C) w (cons. ep nil.))) (fgauto_path_eval M w) m (fgauto_eval_join_end M L w) e) in
    match h [
    | inl. a ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) (A .tedges) (A .tstart) w (A .tend)) (Id C (fgauto_path_eval M w) m)))
        (Mere T) (mere_isprop T)
        (z ↦ mere T (cons. ep (append (SignedLetter C) (z .fst) (cons. ep nil.)),
          ((cons. zero. (A .tstart), (fgauto_join2_glue M A B glue (cons. fgauto_n2 nil.) ep (cons. zero. (A .tstart))
              (inl. (refl (cons. fgauto_n2 nil. : List Nat), (refl ep, refl (cons. zero. (A .tstart) : List Nat)))),
            fgauto_run_append C (List Nat) G (cons. zero. (A .tstart)) (z .fst) (cons. zero. (A .tend)) (cons. ep nil.) (cons. fgauto_n3 nil.)
              (fgauto_run_mono C (List Nat) (fgauto_tpre M zero. (A .tedges)) G (fgauto_join2_left M A B glue)
                (cons. zero. (A .tstart)) (z .fst) (cons. zero. (A .tend)) (fgauto_tpre_embed M zero. (A .tedges) (A .tstart) (z .fst) (A .tend) (z .snd .fst)))
              (fgauto_run_single C (List Nat) G (cons. zero. (A .tend)) ep (cons. fgauto_n3 nil.)
                (fgauto_join2_glue M A B glue (cons. zero. (A .tend)) ep (cons. fgauto_n3 nil.)
                  (inr. (inr. (inl. (refl (cons. zero. (A .tend) : List Nat), (refl ep, refl (cons. fgauto_n3 nil. : List Nat)))))))))),
           ev (z .fst) (z .snd .snd)))) a
    | inr. b ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) (B .tedges) (B .tstart) w (B .tend)) (Id C (fgauto_path_eval M w) m)))
        (Mere T) (mere_isprop T)
        (z ↦ mere T (cons. ep (append (SignedLetter C) (z .fst) (cons. ep nil.)),
          ((cons. fgauto_n1 (B .tstart), (fgauto_join2_glue M A B glue (cons. fgauto_n2 nil.) ep (cons. fgauto_n1 (B .tstart))
              (inr. (inl. (refl (cons. fgauto_n2 nil. : List Nat), (refl ep, refl (cons. fgauto_n1 (B .tstart) : List Nat))))),
            fgauto_run_append C (List Nat) G (cons. fgauto_n1 (B .tstart)) (z .fst) (cons. fgauto_n1 (B .tend)) (cons. ep nil.) (cons. fgauto_n3 nil.)
              (fgauto_run_mono C (List Nat) (fgauto_tpre M fgauto_n1 (B .tedges)) G (fgauto_join2_right M A B glue)
                (cons. fgauto_n1 (B .tstart)) (z .fst) (cons. fgauto_n1 (B .tend)) (fgauto_tpre_embed M fgauto_n1 (B .tedges) (B .tstart) (z .fst) (B .tend) (z .snd .fst)))
              (fgauto_run_single C (List Nat) G (cons. fgauto_n1 (B .tend)) ep (cons. fgauto_n3 nil.)
                (fgauto_join2_glue M A B glue (cons. fgauto_n1 (B .tend)) ep (cons. fgauto_n3 nil.)
                  (inr. (inr. (inr. (inl. (refl (cons. fgauto_n1 (B .tend) : List Nat), (refl ep, refl (cons. fgauto_n3 nil. : List Nat))))))))))),
           ev (z .fst) (z .snd .snd)))) b ]

{` Products. `}
def fgauto_prod_exit0 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_prod_glue M A B) (cons. zero. pe) y z)
  : Product (Id (List Nat) pe (A .tend)) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z (cons. fgauto_n1 (B .tstart))))
  ≔ match s [
  | inl. e ↦ (fgauto_tag_tail zero. pe (A .tend) (e .fst), (e .snd .fst, e .snd .snd))
  | inr. s1 ↦ match s1 [] ]

def fgauto_prod_noexit1 (M : FgautoMonoid) (A B : FgautoThompsonAut M) (p : List Nat) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_prod_glue M A B) (cons. fgauto_n1 p) x z) : Empty
  ≔ match s [ inl. e ↦ fgauto_tag_clash fgauto_n1 zero. p (A .tend) (e .fst) | inr. s1 ↦ match s1 [] ]

def fgauto_thompson_prod_out (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A B : FgautoThompsonAut M) (m : M .mcarrier)
  (w : SignedWord (M .mcarrier))
  (r : FgautoRun (M .mcarrier) (List Nat) (fgauto_join2 M A B (fgauto_prod_glue M A B)) (cons. zero. (A .tstart)) w (cons. fgauto_n1 (B .tend)))
  (em : Id (M .mcarrier) (fgauto_path_eval M w) m)
  : Mere (Σ (M .mcarrier) (a ↦ Σ (M .mcarrier) (b ↦ Product (FgautoThompsonLang M A a)
      (Product (FgautoThompsonLang M B b) (Id (M .mcarrier) m (M .mmul a b))))))
  ≔ let C ≔ M .mcarrier in
    let glue ≔ fgauto_prod_glue M A B in
    let G ≔ fgauto_join2 M A B glue in
    let d ≔ fgauto_region_exit_unique M G (A .tedges) glue zero. (fgauto_join2_classify0 M A B glue) (A .tend) (cons. fgauto_n1 (B .tstart))
      (fgauto_prod_exit0 M A B) (A .tstart) w (cons. fgauto_n1 (B .tend)) (q' e ↦ fgauto_tag_clash fgauto_n1 zero. (B .tend) q' e) r in
    let rB ≔ fgauto_region_stay M G (B .tedges) glue fgauto_n1 (fgauto_join2_classify1 M A B glue) (fgauto_prod_noexit1 M A B)
      (B .tstart) (d .snd .fst) (B .tend) (d .snd .snd .snd .snd) in
    let a ≔ fgauto_path_eval M (d .fst) in
    let b ≔ fgauto_path_eval M (d .snd .fst) in
    mere (Σ C (a0 ↦ Σ C (b0 ↦ Product (FgautoThompsonLang M A a0) (Product (FgautoThompsonLang M B b0) (Id C m (M .mmul a0 b0))))))
      (a, (b, (mere (Σ (SignedWord C) (w0 ↦ Product (FgautoRun C (List Nat) (A .tedges) (A .tstart) w0 (A .tend)) (Id C (fgauto_path_eval M w0) a)))
                  (d .fst, (d .snd .snd .snd .fst, refl a)),
               (mere (Σ (SignedWord C) (w0 ↦ Product (FgautoRun C (List Nat) (B .tedges) (B .tstart) w0 (B .tend)) (Id C (fgauto_path_eval M w0) b)))
                  (d .snd .fst, (rB, refl b)),
                concat C m (fgauto_path_eval M w) (M .mmul a b) (inverse C (fgauto_path_eval M w) m em)
                  (fgauto_exit_eval M L G (A .tedges) (A .tstart) (A .tend) (cons. fgauto_n1 (B .tstart)) w (cons. fgauto_n1 (B .tend)) d)))))

def fgauto_thompson_prod_in (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A B : FgautoThompsonAut M) (m : M .mcarrier)
  (a b : M .mcarrier) (ha : FgautoThompsonLang M A a) (hb : FgautoThompsonLang M B b) (e : Id (M .mcarrier) m (M .mmul a b))
  : FgautoThompsonLang M (fgauto_join2 M A B (fgauto_prod_glue M A B), cons. zero. (A .tstart), cons. fgauto_n1 (B .tend)) m
  ≔ let C ≔ M .mcarrier in
    let glue ≔ fgauto_prod_glue M A B in
    let G ≔ fgauto_join2 M A B glue in
    let ep ≔ fgauto_teps M in
    let T ≔ Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. zero. (A .tstart)) w (cons. fgauto_n1 (B .tend))) (Id C (fgauto_path_eval M w) m)) in
    mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) (A .tedges) (A .tstart) w (A .tend)) (Id C (fgauto_path_eval M w) a)))
      (Mere T) (mere_isprop T)
      (za ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) (B .tedges) (B .tstart) w (B .tend)) (Id C (fgauto_path_eval M w) b)))
        (Mere T) (mere_isprop T)
        (zb ↦ mere T (append (SignedLetter C) (za .fst) (cons. ep (zb .fst)),
          (fgauto_run_append C (List Nat) G (cons. zero. (A .tstart)) (za .fst) (cons. zero. (A .tend)) (cons. ep (zb .fst)) (cons. fgauto_n1 (B .tend))
             (fgauto_run_mono C (List Nat) (fgauto_tpre M zero. (A .tedges)) G (fgauto_join2_left M A B glue)
               (cons. zero. (A .tstart)) (za .fst) (cons. zero. (A .tend)) (fgauto_tpre_embed M zero. (A .tedges) (A .tstart) (za .fst) (A .tend) (za .snd .fst)))
             (cons. fgauto_n1 (B .tstart),
              (fgauto_join2_glue M A B glue (cons. zero. (A .tend)) ep (cons. fgauto_n1 (B .tstart))
                 (inl. (refl (cons. zero. (A .tend) : List Nat), (refl ep, refl (cons. fgauto_n1 (B .tstart) : List Nat)))),
               fgauto_run_mono C (List Nat) (fgauto_tpre M fgauto_n1 (B .tedges)) G (fgauto_join2_right M A B glue)
                 (cons. fgauto_n1 (B .tstart)) (zb .fst) (cons. fgauto_n1 (B .tend)) (fgauto_tpre_embed M fgauto_n1 (B .tedges) (B .tstart) (zb .fst) (B .tend) (zb .snd .fst)))),
           concat C (fgauto_path_eval M (append (SignedLetter C) (za .fst) (cons. ep (zb .fst))))
             (M .mmul (fgauto_path_eval M (za .fst)) (fgauto_path_eval M (zb .fst))) m
             (fgauto_eval_join M L (za .fst) (zb .fst))
             (concat C (M .mmul (fgauto_path_eval M (za .fst)) (fgauto_path_eval M (zb .fst))) (M .mmul a b) m
               (refl ((u v ↦ M .mmul u v) : C → C → C) (za .snd .snd) (zb .snd .snd)) (inverse C m (M .mmul a b) e))))) hb) ha

{` Stars. `}
def fgauto_length_suffix (A : Type) (u : List A) (y : A) (v : List A) : Le (suc. (length A v)) (length A (append A u (cons. y v)))
  ≔ match u [ nil. ↦ le_refl (length A v) | cons. a t ↦ le_step (suc. (length A v)) (length A (append A t (cons. y v))) (fgauto_length_suffix A t y v) ]

def fgauto_star_from2 (M : FgautoMonoid) (A : FgautoThompsonAut M) (x : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_join1 M A (fgauto_star_glue M A)) (cons. fgauto_n2 nil.) x z)
  : Product (Id (SignedLetter (M .mcarrier)) x (fgauto_teps M)) (Id (List Nat) z (cons. zero. (A .tstart)))
  ≔ match fgauto_step_append_split (M .mcarrier) (List Nat) (fgauto_tpre M zero. (A .tedges)) (fgauto_star_glue M A) (cons. fgauto_n2 nil.) x z s [
  | inl. s1 ↦ match fgauto_tpre_step_other M fgauto_n2 zero. (e ↦ e) (A .tedges) nil. x z s1 []
  | inr. s2 ↦ match s2 [
    | inl. e ↦ (e .snd .fst, e .snd .snd)
    | inr. s3 ↦ match s3 [
      | inl. e ↦ match fgauto_tag_clash fgauto_n2 zero. nil. (A .tend) (e .fst) []
      | inr. s4 ↦ match s4 [] ] ] ]

def fgauto_star_exit0 (M : FgautoMonoid) (A : FgautoThompsonAut M) (pe : List Nat) (y : SignedLetter (M .mcarrier)) (z : List Nat)
  (s : FgautoStep (M .mcarrier) (List Nat) (fgauto_star_glue M A) (cons. zero. pe) y z)
  : Product (Id (List Nat) pe (A .tend)) (Product (Id (SignedLetter (M .mcarrier)) y (fgauto_teps M)) (Id (List Nat) z (cons. fgauto_n2 nil.)))
  ≔ match s [
  | inl. e ↦ match fgauto_tag_clash zero. fgauto_n2 pe nil. (e .fst) []
  | inr. s1 ↦ match s1 [
    | inl. e ↦ (fgauto_tag_tail zero. pe (A .tend) (e .fst), (e .snd .fst, e .snd .snd))
    | inr. s2 ↦ match s2 [] ] ]

def FgautoStarDecomp (M : FgautoMonoid) (A : FgautoThompsonAut M) (v : M .mcarrier) : Type
  ≔ Mere (Σ (List (M .mcarrier)) (l ↦ Product (FgautoAllIn (M .mcarrier) (FgautoThompsonLang M A) l)
       (Id (M .mcarrier) v (fgauto_list_product M l))))

def fgauto_thompson_star_out (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A : FgautoThompsonAut M) (n : Nat)
  (w : SignedWord (M .mcarrier)) (hl : Le (length (SignedLetter (M .mcarrier)) w) n)
  (r : FgautoRun (M .mcarrier) (List Nat) (fgauto_join1 M A (fgauto_star_glue M A)) (cons. fgauto_n2 nil.) w (cons. fgauto_n2 nil.))
  : FgautoStarDecomp M A (fgauto_path_eval M w)
  ≔ let C ≔ M .mcarrier in
    let glue ≔ fgauto_star_glue M A in
    let G ≔ fgauto_join1 M A glue in
    match w [
    | nil. ↦ mere (Σ (List C) (l ↦ Product (FgautoAllIn C (FgautoThompsonLang M A) l) (Id C (M .munit) (fgauto_list_product M l))))
        (nil., (star., refl (M .munit)))
    | cons. x w' ↦ match n [
      | zero. ↦ match hl []
      | suc. n' ↦
        let f ≔ fgauto_star_from2 M A x (r .fst) (r .snd .fst) in
        let d ≔ fgauto_region_exit_unique M G (A .tedges) glue zero. (fgauto_join1_classify0 M A glue) (A .tend) (cons. fgauto_n2 nil.)
          (fgauto_star_exit0 M A) (A .tstart) w' (cons. fgauto_n2 nil.) (q' e ↦ fgauto_tag_clash fgauto_n2 zero. nil. q' e)
          (fgauto_run_start C (List Nat) G (r .fst) (cons. zero. (A .tstart)) w' (cons. fgauto_n2 nil.) (f .snd) (r .snd .snd)) in
        let w1 ≔ d .fst in
        let w2 ≔ d .snd .fst in
        let len2 : Le (length (SignedLetter C) w2) n'
          ≔ lt_le (length (SignedLetter C) w2) n'
              (le_trans (suc. (length (SignedLetter C) w2)) (length (SignedLetter C) (append (SignedLetter C) w1 (cons. (fgauto_teps M) w2))) n'
                (fgauto_length_suffix (SignedLetter C) w1 (fgauto_teps M) w2)
                (transport (SignedWord C) (u ↦ Le (length (SignedLetter C) u) n') w' (append (SignedLetter C) w1 (cons. (fgauto_teps M) w2))
                  (d .snd .snd .fst) hl)) in
        let ev : Id C (fgauto_path_eval M (cons. x w')) (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M w2))
          ≔ concat C (fgauto_path_eval M (cons. x w')) (fgauto_path_eval M w') (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M w2))
              (concat C (fgauto_path_eval M (cons. x w')) (fgauto_path_eval M (cons. (fgauto_teps M) w')) (fgauto_path_eval M w')
                (refl ((u ↦ fgauto_path_eval M (cons. u w')) : SignedLetter C → C) (f .fst)) (fgauto_eval_eps M L w'))
              (fgauto_exit_eval M L G (A .tedges) (A .tstart) (A .tend) (cons. fgauto_n2 nil.) w' (cons. fgauto_n2 nil.) d) in
        mere_rec (Σ (List C) (l ↦ Product (FgautoAllIn C (FgautoThompsonLang M A) l) (Id C (fgauto_path_eval M w2) (fgauto_list_product M l))))
          (FgautoStarDecomp M A (fgauto_path_eval M (cons. x w')))
          (mere_isprop (Σ (List C) (l ↦ Product (FgautoAllIn C (FgautoThompsonLang M A) l)
            (Id C (fgauto_path_eval M (cons. x w')) (fgauto_list_product M l)))))
          (y ↦ mere (Σ (List C) (l ↦ Product (FgautoAllIn C (FgautoThompsonLang M A) l)
                (Id C (fgauto_path_eval M (cons. x w')) (fgauto_list_product M l))))
            (cons. (fgauto_path_eval M w1) (y .fst),
             ((mere (Σ (SignedWord C) (w0 ↦ Product (FgautoRun C (List Nat) (A .tedges) (A .tstart) w0 (A .tend))
                   (Id C (fgauto_path_eval M w0) (fgauto_path_eval M w1)))) (w1, (d .snd .snd .snd .fst, refl (fgauto_path_eval M w1))),
               y .snd .fst),
              concat C (fgauto_path_eval M (cons. x w')) (M .mmul (fgauto_path_eval M w1) (fgauto_path_eval M w2))
                (M .mmul (fgauto_path_eval M w1) (fgauto_list_product M (y .fst)))
                ev (refl (M .mmul (fgauto_path_eval M w1)) (y .snd .snd)))))
          (fgauto_thompson_star_out M L A n' w2 len2 (d .snd .snd .snd .snd)) ] ]

def fgauto_thompson_star_in (M : FgautoMonoid) (L : FgautoMonoidLaws M) (A : FgautoThompsonAut M) (l : List (M .mcarrier))
  (h : FgautoAllIn (M .mcarrier) (FgautoThompsonLang M A) l)
  : FgautoThompsonLang M (fgauto_join1 M A (fgauto_star_glue M A), cons. fgauto_n2 nil., cons. fgauto_n2 nil.) (fgauto_list_product M l)
  ≔ let C ≔ M .mcarrier in
    let glue ≔ fgauto_star_glue M A in
    let G ≔ fgauto_join1 M A glue in
    let ep ≔ fgauto_teps M in
    let T ≔ (v : C) ↦ Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n2 nil.)) (Id C (fgauto_path_eval M w) v)) in
    match l [
    | nil. ↦ mere (T (M .munit)) (nil., (refl (cons. fgauto_n2 nil. : List Nat), refl (M .munit)))
    | cons. a t ↦
      mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) (A .tedges) (A .tstart) w (A .tend)) (Id C (fgauto_path_eval M w) a)))
        (Mere (T (M .mmul a (fgauto_list_product M t)))) (mere_isprop (T (M .mmul a (fgauto_list_product M t))))
        (za ↦ mere_rec (T (fgauto_list_product M t)) (Mere (T (M .mmul a (fgauto_list_product M t)))) (mere_isprop (T (M .mmul a (fgauto_list_product M t))))
          (zt ↦ mere (T (M .mmul a (fgauto_list_product M t)))
            (cons. ep (append (SignedLetter C) (za .fst) (cons. ep (zt .fst))),
             ((cons. zero. (A .tstart),
               (fgauto_join1_glue M A glue (cons. fgauto_n2 nil.) ep (cons. zero. (A .tstart))
                  (inl. (refl (cons. fgauto_n2 nil. : List Nat), (refl ep, refl (cons. zero. (A .tstart) : List Nat)))),
                fgauto_run_append C (List Nat) G (cons. zero. (A .tstart)) (za .fst) (cons. zero. (A .tend)) (cons. ep (zt .fst)) (cons. fgauto_n2 nil.)
                  (fgauto_run_mono C (List Nat) (fgauto_tpre M zero. (A .tedges)) G (fgauto_join1_left M A glue)
                    (cons. zero. (A .tstart)) (za .fst) (cons. zero. (A .tend)) (fgauto_tpre_embed M zero. (A .tedges) (A .tstart) (za .fst) (A .tend) (za .snd .fst)))
                  (cons. fgauto_n2 nil.,
                   (fgauto_join1_glue M A glue (cons. zero. (A .tend)) ep (cons. fgauto_n2 nil.)
                      (inr. (inl. (refl (cons. zero. (A .tend) : List Nat), (refl ep, refl (cons. fgauto_n2 nil. : List Nat))))),
                    zt .snd .fst)))),
              concat C (fgauto_path_eval M (cons. ep (append (SignedLetter C) (za .fst) (cons. ep (zt .fst)))))
                (fgauto_path_eval M (append (SignedLetter C) (za .fst) (cons. ep (zt .fst)))) (M .mmul a (fgauto_list_product M t))
                (fgauto_eval_eps M L (append (SignedLetter C) (za .fst) (cons. ep (zt .fst))))
                (concat C (fgauto_path_eval M (append (SignedLetter C) (za .fst) (cons. ep (zt .fst))))
                  (M .mmul (fgauto_path_eval M (za .fst)) (fgauto_path_eval M (zt .fst))) (M .mmul a (fgauto_list_product M t))
                  (fgauto_eval_join M L (za .fst) (zt .fst))
                  (refl ((u v ↦ M .mmul u v) : C → C → C) (za .snd .snd) (zt .snd .snd))))))
          (fgauto_thompson_star_in M L A t (h .snd))) (h .fst) ]

{` Thompson's construction is correct. `}
def fgauto_thompson_correct (M : FgautoMonoid) (L : FgautoMonoidLaws M) (r : FgautoRatExpr (M .mcarrier)) (m : M .mcarrier)
  : FgautoIff (fgauto_rat_mem M r m) (FgautoThompsonLang M (fgauto_thompson M r) m)
  ≔ let C ≔ M .mcarrier in
    match r [
    | rat_fin. l ↦ fgauto_thompson_fin M L l m
    | rat_union. r1 r2 ↦
      let A ≔ fgauto_thompson M r1 in
      let B ≔ fgauto_thompson M r2 in
      let G ≔ fgauto_join2 M A B (fgauto_union_glue M A B) in
      (h ↦ mere_rec (Sum (fgauto_rat_mem M r1 m) (fgauto_rat_mem M r2 m)) (FgautoThompsonLang M (fgauto_thompson M (rat_union. r1 r2)) m)
         (mere_isprop (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n3 nil.)) (Id C (fgauto_path_eval M w) m))))
         (k ↦ fgauto_thompson_union_in M L A B m (match k [
           | inl. a ↦ inl. (fgauto_thompson_correct M L r1 m .fst a)
           | inr. b ↦ inr. (fgauto_thompson_correct M L r2 m .fst b) ])) h,
       h ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n3 nil.)) (Id C (fgauto_path_eval M w) m)))
         (fgauto_rat_mem M (rat_union. r1 r2) m) (fgauto_rat_mem_prop M (rat_union. r1 r2) m)
         (z ↦ mere_rec (Sum (FgautoThompsonLang M A m) (FgautoThompsonLang M B m)) (fgauto_rat_mem M (rat_union. r1 r2) m)
           (fgauto_rat_mem_prop M (rat_union. r1 r2) m)
           (k ↦ mere (Sum (fgauto_rat_mem M r1 m) (fgauto_rat_mem M r2 m)) (match k [
             | inl. a ↦ inl. (fgauto_thompson_correct M L r1 m .snd a)
             | inr. b ↦ inr. (fgauto_thompson_correct M L r2 m .snd b) ]))
           (fgauto_thompson_union_out M L A B m (z .fst) (z .snd .fst) (z .snd .snd))) h)
    | rat_prod. r1 r2 ↦
      let A ≔ fgauto_thompson M r1 in
      let B ≔ fgauto_thompson M r2 in
      let G ≔ fgauto_join2 M A B (fgauto_prod_glue M A B) in
      (h ↦ mere_rec (Σ C (a ↦ Σ C (b ↦ Product (fgauto_rat_mem M r1 a) (Product (fgauto_rat_mem M r2 b) (Id C m (M .mmul a b))))))
         (FgautoThompsonLang M (fgauto_thompson M (rat_prod. r1 r2)) m)
         (mere_isprop (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. zero. (A .tstart)) w (cons. fgauto_n1 (B .tend))) (Id C (fgauto_path_eval M w) m))))
         (z ↦ fgauto_thompson_prod_in M L A B m (z .fst) (z .snd .fst)
           (fgauto_thompson_correct M L r1 (z .fst) .fst (z .snd .snd .fst))
           (fgauto_thompson_correct M L r2 (z .snd .fst) .fst (z .snd .snd .snd .fst)) (z .snd .snd .snd .snd)) h,
       h ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. zero. (A .tstart)) w (cons. fgauto_n1 (B .tend))) (Id C (fgauto_path_eval M w) m)))
         (fgauto_rat_mem M (rat_prod. r1 r2) m) (fgauto_rat_mem_prop M (rat_prod. r1 r2) m)
         (z ↦ mere_rec (Σ C (a ↦ Σ C (b ↦ Product (FgautoThompsonLang M A a) (Product (FgautoThompsonLang M B b) (Id C m (M .mmul a b))))))
           (fgauto_rat_mem M (rat_prod. r1 r2) m) (fgauto_rat_mem_prop M (rat_prod. r1 r2) m)
           (y ↦ mere (Σ C (a ↦ Σ C (b ↦ Product (fgauto_rat_mem M r1 a) (Product (fgauto_rat_mem M r2 b) (Id C m (M .mmul a b))))))
             (y .fst, (y .snd .fst, (fgauto_thompson_correct M L r1 (y .fst) .snd (y .snd .snd .fst),
               (fgauto_thompson_correct M L r2 (y .snd .fst) .snd (y .snd .snd .snd .fst), y .snd .snd .snd .snd)))))
           (fgauto_thompson_prod_out M L A B m (z .fst) (z .snd .fst) (z .snd .snd))) h)
    | rat_star. r1 ↦
      let A ≔ fgauto_thompson M r1 in
      let G ≔ fgauto_join1 M A (fgauto_star_glue M A) in
      (h ↦ mere_rec (Σ (List C) (l ↦ Product (FgautoAllIn C (fgauto_rat_mem M r1) l) (Id C m (fgauto_list_product M l))))
         (FgautoThompsonLang M (fgauto_thompson M (rat_star. r1)) m)
         (mere_isprop (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n2 nil.)) (Id C (fgauto_path_eval M w) m))))
         (z ↦ transport C (v ↦ FgautoThompsonLang M (fgauto_thompson M (rat_star. r1)) v) (fgauto_list_product M (z .fst)) m
           (inverse C m (fgauto_list_product M (z .fst)) (z .snd .snd))
           (fgauto_thompson_star_in M L A (z .fst)
             (fgauto_allin_map C (fgauto_rat_mem M r1) (FgautoThompsonLang M A) (v ↦ fgauto_thompson_correct M L r1 v .fst) (z .fst) (z .snd .fst)))) h,
       h ↦ mere_rec (Σ (SignedWord C) (w ↦ Product (FgautoRun C (List Nat) G (cons. fgauto_n2 nil.) w (cons. fgauto_n2 nil.)) (Id C (fgauto_path_eval M w) m)))
         (fgauto_rat_mem M (rat_star. r1) m) (fgauto_rat_mem_prop M (rat_star. r1) m)
         (z ↦ mere_rec (Σ (List C) (l ↦ Product (FgautoAllIn C (FgautoThompsonLang M A) l) (Id C (fgauto_path_eval M (z .fst)) (fgauto_list_product M l))))
           (fgauto_rat_mem M (rat_star. r1) m) (fgauto_rat_mem_prop M (rat_star. r1) m)
           (y ↦ mere (Σ (List C) (l ↦ Product (FgautoAllIn C (fgauto_rat_mem M r1) l) (Id C m (fgauto_list_product M l))))
             (y .fst, (fgauto_allin_map C (FgautoThompsonLang M A) (fgauto_rat_mem M r1) (v ↦ fgauto_thompson_correct M L r1 v .snd) (y .fst) (y .snd .fst),
               concat C m (fgauto_path_eval M (z .fst)) (fgauto_list_product M (y .fst)) (inverse C (fgauto_path_eval M (z .fst)) m (z .snd .snd)) (y .snd .snd))))
           (fgauto_thompson_star_out M L A (length (SignedLetter C) (z .fst)) (z .fst) (le_refl (length (SignedLetter C) (z .fst))) (z .snd .fst))) h) ]
