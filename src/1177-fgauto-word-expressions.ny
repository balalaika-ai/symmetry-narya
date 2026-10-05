export "1176-fgauto-epsilon-removal"

{` Chapter 11, automata part 28 (towards Benois, fggroups.tex:874):
   rational expressions over F(S) as images of rational expressions over
   the free monoid S~*.

   F(S) is the monoid of reduced words with product rho(u v) (laws:
   fgauto_free_group_monoid_laws).  fgauto_lift_expr r replaces every
   element g of an atom of r by the expression a1 . a2 ... am of single
   letters of the word g (and eps by the star of the empty set).  The
   elements of the subset of r are exactly the reductions of the words of
   the subset of fgauto_lift_expr r (fgauto_lift_expr_correct). `}

def fgauto_free_monoid_laws (S : Type) : FgautoMonoidLaws (fgauto_free_monoid S)
  ≔ (u ↦ refl u, u ↦ append_nil (SignedLetter S) u,
     a b c ↦ inverse (SignedWord S) (append (SignedLetter S) (append (SignedLetter S) a b) c) (append (SignedLetter S) a (append (SignedLetter S) b c))
       (append_assoc (SignedLetter S) a b c))

def fgauto_free_group_monoid_laws (S : Type) (dec : DecidableEquality S) : FgautoMonoidLaws (fgauto_free_group_monoid S dec)
  ≔ let L ≔ SignedLetter S in
    let red ≔ word_reduction S dec in
    (u ↦ reduced_word_path S (fgauto_reduced_mul S dec (reduced_word_empty S) u) u (word_reduction_of_reduced S dec (u .fst) (u .snd)),
     u ↦ reduced_word_path S (fgauto_reduced_mul S dec u (reduced_word_empty S)) u
       (fgauto_wtrans S (red (append L (u .fst) nil.)) (red (u .fst)) (u .fst)
         (refl red (append_nil L (u .fst))) (word_reduction_of_reduced S dec (u .fst) (u .snd))),
     a b c ↦ reduced_word_path S (fgauto_reduced_mul S dec a (fgauto_reduced_mul S dec b c)) (fgauto_reduced_mul S dec (fgauto_reduced_mul S dec a b) c)
       (calc
         red (append L (a .fst) (red (append L (b .fst) (c .fst))))
         = red (append L (a .fst) (append L (b .fst) (c .fst)))
           by fgauto_wsym S (red (append L (a .fst) (append L (b .fst) (c .fst)))) (red (append L (a .fst) (red (append L (b .fst) (c .fst)))))
                (word_reduction_append_right S dec (a .fst) (append L (b .fst) (c .fst)))
         = red (append L (append L (a .fst) (b .fst)) (c .fst))
           by fgauto_wsym S (red (append L (append L (a .fst) (b .fst)) (c .fst))) (red (append L (a .fst) (append L (b .fst) (c .fst))))
                (fgauto_red_assoc S dec (a .fst) (b .fst) (c .fst))
         = red (append L (red (append L (a .fst) (b .fst))) (c .fst))
           by word_reduction_append_left S dec (append L (a .fst) (b .fst)) (c .fst) ∎))

{` Expressions for single words and finite sets of words. `}
def fgauto_word_expr (S : Type) (w : SignedWord S) : FgautoRatExpr (SignedWord S)
  ≔ match w [
  | nil. ↦ rat_star. (rat_fin. nil.)
  | cons. x t ↦ rat_prod. (rat_fin. (cons. (cons. x nil.) nil.)) (fgauto_word_expr S t) ]

def fgauto_words_expr (S : Type) (l : List (SignedWord S)) : FgautoRatExpr (SignedWord S)
  ≔ match l [ nil. ↦ rat_fin. nil. | cons. g t ↦ rat_union. (fgauto_word_expr S g) (fgauto_words_expr S t) ]

def fgauto_lift_expr (S : Type) (r : FgautoRatExpr (ReducedWord S)) : FgautoRatExpr (SignedWord S)
  ≔ match r [
  | rat_fin. l ↦ fgauto_words_expr S (fgauto_list_map (ReducedWord S) (SignedWord S) (g ↦ g .fst) l)
  | rat_union. r1 r2 ↦ rat_union. (fgauto_lift_expr S r1) (fgauto_lift_expr S r2)
  | rat_prod. r1 r2 ↦ rat_prod. (fgauto_lift_expr S r1) (fgauto_lift_expr S r2)
  | rat_star. r1 ↦ rat_star. (fgauto_lift_expr S r1) ]

{` The words of fgauto_word_expr g: only g. `}
def fgauto_star_empty_list (S : Type) (dec : DecidableEquality S) (w : SignedWord S) (l : List (SignedWord S))
  (a : FgautoAllIn (SignedWord S) (fgauto_rat_mem (fgauto_free_monoid S) (rat_fin. nil.)) l)
  (e : Id (SignedWord S) w (fgauto_list_product (fgauto_free_monoid S) l)) : Id (SignedWord S) w nil.
  ≔ match l [
  | nil. ↦ e
  | cons. g t ↦ mere_rec (FgautoMem (SignedWord S) g nil.) (Id (SignedWord S) w nil.) (signed_word_set S dec w nil.)
      (m ↦ match m []) (a .fst) ]

def fgauto_star_empty_only (S : Type) (dec : DecidableEquality S) (w : SignedWord S)
  (h : fgauto_rat_mem (fgauto_free_monoid S) (rat_star. (rat_fin. nil.)) w) : Id (SignedWord S) w nil.
  ≔ let M ≔ fgauto_free_monoid S in
    mere_rec (Σ (List (SignedWord S)) (l ↦ Product (FgautoAllIn (SignedWord S) (fgauto_rat_mem M (rat_fin. nil.)) l)
        (Id (SignedWord S) w (fgauto_list_product M l))))
      (Id (SignedWord S) w nil.) (signed_word_set S dec w nil.)
      (z ↦ fgauto_star_empty_list S dec w (z .fst) (z .snd .fst) (z .snd .snd)) h

def fgauto_word_expr_mem (S : Type) (dec : DecidableEquality S) (g w : SignedWord S)
  : FgautoIff (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_word_expr S g) w) (Id (SignedWord S) w g)
  ≔ let M ≔ fgauto_free_monoid S in
    let L ≔ SignedLetter S in
    match g [
    | nil. ↦ (h ↦ fgauto_star_empty_only S dec w h,
        e ↦ mere (Σ (List (SignedWord S)) (l ↦ Product (FgautoAllIn (SignedWord S) (fgauto_rat_mem M (rat_fin. nil.)) l)
              (Id (SignedWord S) w (fgauto_list_product M l)))) (nil., (star., e)))
    | cons. x t ↦
      let T ≔ Σ (SignedWord S) (a ↦ Σ (SignedWord S) (b ↦ Product (fgauto_rat_mem M (rat_fin. (cons. (cons. x nil.) nil.)) a)
          (Product (fgauto_rat_mem M (fgauto_word_expr S t) b) (Id (SignedWord S) w (append L a b))))) in
      (h ↦ mere_rec T (Id (SignedWord S) w (cons. x t)) (signed_word_set S dec w (cons. x t))
         (z ↦ mere_rec (FgautoMem (SignedWord S) (z .fst) (cons. (cons. x nil.) nil.)) (Id (SignedWord S) w (cons. x t))
           (signed_word_set S dec w (cons. x t))
           (m ↦ match m [
             | inl. ea ↦ concat (SignedWord S) w (append L (z .fst) (z .snd .fst)) (cons. x t) (z .snd .snd .snd .snd)
                 (refl ((u v ↦ append L u v) : SignedWord S → SignedWord S → SignedWord S) ea
                   (fgauto_word_expr_mem S dec t (z .snd .fst) .fst (z .snd .snd .snd .fst)))
             | inr. m' ↦ match m' [] ])
           (z .snd .snd .fst)) h,
       e ↦ mere T (cons. x nil., (t, (mere (FgautoMem (SignedWord S) (cons. x nil.) (cons. (cons. x nil.) nil.)) (inl. (refl (cons. x nil. : SignedWord S))),
             (fgauto_word_expr_mem S dec t t .snd (refl t), e))))) ]

def fgauto_words_expr_mem (S : Type) (dec : DecidableEquality S) (l : List (SignedWord S)) (w : SignedWord S)
  : FgautoIff (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_words_expr S l) w) (Mere (FgautoMem (SignedWord S) w l))
  ≔ let M ≔ fgauto_free_monoid S in
    match l [
    | nil. ↦ (h ↦ h, h ↦ h)
    | cons. g t ↦
      (h ↦ mere_rec (Sum (fgauto_rat_mem M (fgauto_word_expr S g) w) (fgauto_rat_mem M (fgauto_words_expr S t) w))
         (Mere (FgautoMem (SignedWord S) w (cons. g t))) (mere_isprop (FgautoMem (SignedWord S) w (cons. g t)))
         (k ↦ match k [
           | inl. a ↦ mere (FgautoMem (SignedWord S) w (cons. g t)) (inl. (fgauto_word_expr_mem S dec g w .fst a))
           | inr. b ↦ mere_rec (FgautoMem (SignedWord S) w t) (Mere (FgautoMem (SignedWord S) w (cons. g t)))
               (mere_isprop (FgautoMem (SignedWord S) w (cons. g t)))
               (m ↦ mere (FgautoMem (SignedWord S) w (cons. g t)) (inr. m)) (fgauto_words_expr_mem S dec t w .fst b) ]) h,
       h ↦ mere_rec (FgautoMem (SignedWord S) w (cons. g t))
         (fgauto_rat_mem M (fgauto_words_expr S (cons. g t)) w) (fgauto_rat_mem_prop M (fgauto_words_expr S (cons. g t)) w)
         (m ↦ match m [
           | inl. e ↦ mere (Sum (fgauto_rat_mem M (fgauto_word_expr S g) w) (fgauto_rat_mem M (fgauto_words_expr S t) w))
               (inl. (fgauto_word_expr_mem S dec g w .snd e))
           | inr. m' ↦ mere (Sum (fgauto_rat_mem M (fgauto_word_expr S g) w) (fgauto_rat_mem M (fgauto_words_expr S t) w))
               (inr. (fgauto_words_expr_mem S dec t w .snd (mere (FgautoMem (SignedWord S) w t) m'))) ]) h) ]

{` Reductions of words. `}
def fgauto_reduce_word (S : Type) (dec : DecidableEquality S) (u : SignedWord S) : ReducedWord S
  ≔ (word_reduction S dec u, word_reduction_reduced S dec u)

def fgauto_mem_map_preimage (A B : Type) (f : A → B) (b : B) (l : List A) (m : FgautoMem B b (fgauto_list_map A B f l))
  : Σ A (a ↦ Product (FgautoMem A a l) (Id B b (f a)))
  ≔ match l [
  | nil. ↦ match m []
  | cons. a t ↦ match m [
    | inl. e ↦ (a, (inl. (refl a), e))
    | inr. m' ↦ let z ≔ fgauto_mem_map_preimage A B f b t m' in (z .fst, (inr. (z .snd .fst), z .snd .snd)) ] ]

def FgautoLiftRel (S : Type) (dec : DecidableEquality S) (r : FgautoRatExpr (ReducedWord S)) (m : ReducedWord S) : Type
  ≔ Mere (Σ (SignedWord S) (w ↦ Product (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_lift_expr S r) w)
       (Id (SignedWord S) (word_reduction S dec w) (m .fst))))

def fgauto_lift_rel_prop (S : Type) (dec : DecidableEquality S) (r : FgautoRatExpr (ReducedWord S)) (m : ReducedWord S)
  : isProp (FgautoLiftRel S dec r m)
  ≔ mere_isprop (Σ (SignedWord S) (w ↦ Product (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_lift_expr S r) w)
       (Id (SignedWord S) (word_reduction S dec w) (m .fst))))

{` Products of reduced lists. `}
def fgauto_productF_map (S : Type) (dec : DecidableEquality S) (lw : List (SignedWord S))
  : Id (SignedWord S) (fgauto_list_product (fgauto_free_group_monoid S dec)
        (fgauto_list_map (SignedWord S) (ReducedWord S) (fgauto_reduce_word S dec) lw) .fst)
      (word_reduction S dec (fgauto_list_product (fgauto_free_monoid S) lw))
  ≔ let L ≔ SignedLetter S in
    match lw [
    | nil. ↦ refl (nil. : SignedWord S)
    | cons. u t ↦
      let P ≔ fgauto_list_product (fgauto_free_group_monoid S dec) (fgauto_list_map (SignedWord S) (ReducedWord S) (fgauto_reduce_word S dec) t) in
      let Pw ≔ fgauto_list_product (fgauto_free_monoid S) t in
      fgauto_wtrans S (word_reduction S dec (append L (word_reduction S dec u) (P .fst)))
        (word_reduction S dec (append L (word_reduction S dec u) (word_reduction S dec Pw)))
        (word_reduction S dec (append L u Pw))
        (refl ((z ↦ word_reduction S dec (append L (word_reduction S dec u) z)) : SignedWord S → SignedWord S) (fgauto_productF_map S dec t))
        (fgauto_wsym S (word_reduction S dec (append L u Pw)) (word_reduction S dec (append L (word_reduction S dec u) (word_reduction S dec Pw)))
          (word_reduction_append S dec u Pw)) ]

{` The main correspondence. `}
def fgauto_lift_star_out (S : Type) (dec : DecidableEquality S) (r1 : FgautoRatExpr (ReducedWord S))
  (ih : (a : ReducedWord S) → fgauto_rat_mem (fgauto_free_group_monoid S dec) r1 a → FgautoLiftRel S dec r1 a)
  (l : List (ReducedWord S)) (h : FgautoAllIn (ReducedWord S) (fgauto_rat_mem (fgauto_free_group_monoid S dec) r1) l)
  : Mere (Σ (List (SignedWord S)) (lw ↦ Product (FgautoAllIn (SignedWord S) (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_lift_expr S r1)) lw)
      (Id (SignedWord S) (fgauto_list_product (fgauto_free_group_monoid S dec) l .fst) (word_reduction S dec (fgauto_list_product (fgauto_free_monoid S) lw)))))
  ≔ let L ≔ SignedLetter S in
    let Mw ≔ fgauto_free_monoid S in
    let MF ≔ fgauto_free_group_monoid S dec in
    let T ≔ (l0 : List (ReducedWord S)) ↦ Σ (List (SignedWord S)) (lw ↦ Product (FgautoAllIn (SignedWord S) (fgauto_rat_mem Mw (fgauto_lift_expr S r1)) lw)
      (Id (SignedWord S) (fgauto_list_product MF l0 .fst) (word_reduction S dec (fgauto_list_product Mw lw)))) in
    match l [
    | nil. ↦ mere (T nil.) (nil., (star., refl (nil. : SignedWord S)))
    | cons. a t ↦
      mere_rec (Σ (SignedWord S) (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r1) w) (Id (SignedWord S) (word_reduction S dec w) (a .fst))))
        (Mere (T (cons. a t))) (mere_isprop (T (cons. a t)))
        (za ↦ mere_rec (T t) (Mere (T (cons. a t))) (mere_isprop (T (cons. a t)))
          (zt ↦ mere (T (cons. a t)) (cons. (za .fst) (zt .fst), ((za .snd .fst, zt .snd .fst),
            fgauto_wtrans S (word_reduction S dec (append L (a .fst) (fgauto_list_product MF t .fst)))
              (word_reduction S dec (append L (word_reduction S dec (za .fst)) (word_reduction S dec (fgauto_list_product Mw (zt .fst)))))
              (word_reduction S dec (append L (za .fst) (fgauto_list_product Mw (zt .fst))))
              (refl ((u v ↦ word_reduction S dec (append L u v)) : SignedWord S → SignedWord S → SignedWord S)
                (fgauto_wsym S (word_reduction S dec (za .fst)) (a .fst) (za .snd .snd)) (zt .snd .snd))
              (fgauto_wsym S (word_reduction S dec (append L (za .fst) (fgauto_list_product Mw (zt .fst))))
                (word_reduction S dec (append L (word_reduction S dec (za .fst)) (word_reduction S dec (fgauto_list_product Mw (zt .fst)))))
                (word_reduction_append S dec (za .fst) (fgauto_list_product Mw (zt .fst)))))))
          (fgauto_lift_star_out S dec r1 ih t (h .snd)))
        (ih a (h .fst)) ]

def fgauto_lift_star_in (S : Type) (dec : DecidableEquality S) (r1 : FgautoRatExpr (ReducedWord S))
  (ih : (a : ReducedWord S) → FgautoLiftRel S dec r1 a → fgauto_rat_mem (fgauto_free_group_monoid S dec) r1 a)
  (lw : List (SignedWord S)) (h : FgautoAllIn (SignedWord S) (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_lift_expr S r1)) lw)
  : FgautoAllIn (ReducedWord S) (fgauto_rat_mem (fgauto_free_group_monoid S dec) r1)
      (fgauto_list_map (SignedWord S) (ReducedWord S) (fgauto_reduce_word S dec) lw)
  ≔ match lw [
  | nil. ↦ star.
  | cons. u t ↦ (ih (fgauto_reduce_word S dec u)
        (mere (Σ (SignedWord S) (w ↦ Product (fgauto_rat_mem (fgauto_free_monoid S) (fgauto_lift_expr S r1) w)
           (Id (SignedWord S) (word_reduction S dec w) (word_reduction S dec u)))) (u, (h .fst, refl (word_reduction S dec u)))),
      fgauto_lift_star_in S dec r1 ih t (h .snd)) ]

def fgauto_lift_expr_correct (S : Type) (dec : DecidableEquality S) (r : FgautoRatExpr (ReducedWord S)) (m : ReducedWord S)
  : FgautoIff (fgauto_rat_mem (fgauto_free_group_monoid S dec) r m) (FgautoLiftRel S dec r m)
  ≔ let L ≔ SignedLetter S in
    let Mw ≔ fgauto_free_monoid S in
    let MF ≔ fgauto_free_group_monoid S dec in
    let RW ≔ ReducedWord S in
    let W ≔ SignedWord S in
    let red ≔ word_reduction S dec in
    let mk ≔ (r0 : FgautoRatExpr RW) (m0 : RW) (w : W) (hw : fgauto_rat_mem Mw (fgauto_lift_expr S r0) w) (e : Id W (red w) (m0 .fst)) ↦
      mere (Σ W (w0 ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r0) w0) (Id W (red w0) (m0 .fst)))) (w, (hw, e)) in
    match r [
    | rat_fin. l ↦
      (h ↦ mere_rec (FgautoMem RW m l) (FgautoLiftRel S dec (rat_fin. l) m) (fgauto_lift_rel_prop S dec (rat_fin. l) m)
         (k ↦ mk (rat_fin. l) m (m .fst)
           (fgauto_words_expr_mem S dec (fgauto_list_map RW W (g ↦ g .fst) l) (m .fst) .snd
             (mere (FgautoMem W (m .fst) (fgauto_list_map RW W (g ↦ g .fst) l)) (fgauto_mem_map RW W (g ↦ g .fst) m l k)))
           (word_reduction_of_reduced S dec (m .fst) (m .snd))) h,
       h ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S (rat_fin. l)) w) (Id W (red w) (m .fst))))
         (Mere (FgautoMem RW m l)) (mere_isprop (FgautoMem RW m l))
         (z ↦ mere_rec (FgautoMem W (z .fst) (fgauto_list_map RW W (g ↦ g .fst) l)) (Mere (FgautoMem RW m l)) (mere_isprop (FgautoMem RW m l))
           (k ↦
             let y ≔ fgauto_mem_map_preimage RW W (g ↦ g .fst) (z .fst) l k in
             mere (FgautoMem RW m l)
               (fgauto_mem_transport RW (y .fst) m l
                 (reduced_word_path S (y .fst) m
                   (concat W (y .fst .fst) (z .fst) (m .fst) (inverse W (z .fst) (y .fst .fst) (y .snd .snd))
                     (concat W (z .fst) (red (z .fst)) (m .fst)
                       (inverse W (red (z .fst)) (z .fst)
                         (transport W (u ↦ Id W (red u) u) (y .fst .fst) (z .fst) (inverse W (z .fst) (y .fst .fst) (y .snd .snd))
                           (word_reduction_of_reduced S dec (y .fst .fst) (y .fst .snd))))
                       (z .snd .snd))))
                 (y .snd .fst)))
           (fgauto_words_expr_mem S dec (fgauto_list_map RW W (g ↦ g .fst) l) (z .fst) .fst (z .snd .fst))) h)
    | rat_union. r1 r2 ↦
      (h ↦ mere_rec (Sum (fgauto_rat_mem MF r1 m) (fgauto_rat_mem MF r2 m)) (FgautoLiftRel S dec (rat_union. r1 r2) m)
         (fgauto_lift_rel_prop S dec (rat_union. r1 r2) m)
         (k ↦ match k [
           | inl. a ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r1) w) (Id W (red w) (m .fst))))
               (FgautoLiftRel S dec (rat_union. r1 r2) m) (fgauto_lift_rel_prop S dec (rat_union. r1 r2) m)
               (z ↦ mk (rat_union. r1 r2) m (z .fst)
                 (mere (Sum (fgauto_rat_mem Mw (fgauto_lift_expr S r1) (z .fst)) (fgauto_rat_mem Mw (fgauto_lift_expr S r2) (z .fst))) (inl. (z .snd .fst)))
                 (z .snd .snd)) (fgauto_lift_expr_correct S dec r1 m .fst a)
           | inr. b ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r2) w) (Id W (red w) (m .fst))))
               (FgautoLiftRel S dec (rat_union. r1 r2) m) (fgauto_lift_rel_prop S dec (rat_union. r1 r2) m)
               (z ↦ mk (rat_union. r1 r2) m (z .fst)
                 (mere (Sum (fgauto_rat_mem Mw (fgauto_lift_expr S r1) (z .fst)) (fgauto_rat_mem Mw (fgauto_lift_expr S r2) (z .fst))) (inr. (z .snd .fst)))
                 (z .snd .snd)) (fgauto_lift_expr_correct S dec r2 m .fst b) ]) h,
       h ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S (rat_union. r1 r2)) w) (Id W (red w) (m .fst))))
         (fgauto_rat_mem MF (rat_union. r1 r2) m) (fgauto_rat_mem_prop MF (rat_union. r1 r2) m)
         (z ↦ mere_rec (Sum (fgauto_rat_mem Mw (fgauto_lift_expr S r1) (z .fst)) (fgauto_rat_mem Mw (fgauto_lift_expr S r2) (z .fst)))
           (fgauto_rat_mem MF (rat_union. r1 r2) m) (fgauto_rat_mem_prop MF (rat_union. r1 r2) m)
           (k ↦ mere (Sum (fgauto_rat_mem MF r1 m) (fgauto_rat_mem MF r2 m)) (match k [
             | inl. a ↦ inl. (fgauto_lift_expr_correct S dec r1 m .snd (mk r1 m (z .fst) a (z .snd .snd)))
             | inr. b ↦ inr. (fgauto_lift_expr_correct S dec r2 m .snd (mk r2 m (z .fst) b (z .snd .snd))) ]))
           (z .snd .fst)) h)
    | rat_prod. r1 r2 ↦
      let TF ≔ Σ RW (a ↦ Σ RW (b ↦ Product (fgauto_rat_mem MF r1 a) (Product (fgauto_rat_mem MF r2 b) (Id RW m (fgauto_reduced_mul S dec a b))))) in
      let TW ≔ (w : W) ↦ Σ W (u ↦ Σ W (v ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r1) u)
          (Product (fgauto_rat_mem Mw (fgauto_lift_expr S r2) v) (Id W w (append L u v))))) in
      (h ↦ mere_rec TF (FgautoLiftRel S dec (rat_prod. r1 r2) m) (fgauto_lift_rel_prop S dec (rat_prod. r1 r2) m)
         (z ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r1) w) (Id W (red w) (z .fst .fst))))
           (FgautoLiftRel S dec (rat_prod. r1 r2) m) (fgauto_lift_rel_prop S dec (rat_prod. r1 r2) m)
           (za ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S r2) w) (Id W (red w) (z .snd .fst .fst))))
             (FgautoLiftRel S dec (rat_prod. r1 r2) m) (fgauto_lift_rel_prop S dec (rat_prod. r1 r2) m)
             (zb ↦ mk (rat_prod. r1 r2) m (append L (za .fst) (zb .fst))
               (mere (TW (append L (za .fst) (zb .fst))) (za .fst, (zb .fst, (za .snd .fst, (zb .snd .fst, refl (append L (za .fst) (zb .fst)))))))
               (calc
                 red (append L (za .fst) (zb .fst))
                 = red (append L (red (za .fst)) (red (zb .fst))) by word_reduction_append S dec (za .fst) (zb .fst)
                 = red (append L (z .fst .fst) (z .snd .fst .fst))
                   by refl ((u v ↦ red (append L u v)) : W → W → W) (za .snd .snd) (zb .snd .snd)
                 = m .fst by inverse W (m .fst) (red (append L (z .fst .fst) (z .snd .fst .fst)))
                      (refl ((g ↦ g .fst) : RW → W) (z .snd .snd .snd .snd)) ∎))
             (fgauto_lift_expr_correct S dec r2 (z .snd .fst) .fst (z .snd .snd .snd .fst)))
           (fgauto_lift_expr_correct S dec r1 (z .fst) .fst (z .snd .snd .fst))) h,
       h ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S (rat_prod. r1 r2)) w) (Id W (red w) (m .fst))))
         (fgauto_rat_mem MF (rat_prod. r1 r2) m) (fgauto_rat_mem_prop MF (rat_prod. r1 r2) m)
         (z ↦ mere_rec (TW (z .fst)) (fgauto_rat_mem MF (rat_prod. r1 r2) m) (fgauto_rat_mem_prop MF (rat_prod. r1 r2) m)
           (y ↦
             let u ≔ y .fst in
             let v ≔ y .snd .fst in
             mere TF (fgauto_reduce_word S dec u, (fgauto_reduce_word S dec v,
               (fgauto_lift_expr_correct S dec r1 (fgauto_reduce_word S dec u) .snd (mk r1 (fgauto_reduce_word S dec u) u (y .snd .snd .fst) (refl (red u))),
                (fgauto_lift_expr_correct S dec r2 (fgauto_reduce_word S dec v) .snd (mk r2 (fgauto_reduce_word S dec v) v (y .snd .snd .snd .fst) (refl (red v))),
                 reduced_word_path S m (fgauto_reduced_mul S dec (fgauto_reduce_word S dec u) (fgauto_reduce_word S dec v))
                   (calc
                     m .fst = red (z .fst) by inverse W (red (z .fst)) (m .fst) (z .snd .snd)
                     = red (append L u v) by refl red (y .snd .snd .snd .snd)
                     = red (append L (red u) (red v)) by word_reduction_append S dec u v ∎))))))
           (z .snd .fst)) h)
    | rat_star. r1 ↦
      let TF ≔ Σ (List RW) (l ↦ Product (FgautoAllIn RW (fgauto_rat_mem MF r1) l) (Id RW m (fgauto_list_product MF l))) in
      let TW ≔ (w : W) ↦ Σ (List W) (lw ↦ Product (FgautoAllIn W (fgauto_rat_mem Mw (fgauto_lift_expr S r1)) lw) (Id W w (fgauto_list_product Mw lw))) in
      (h ↦ mere_rec TF (FgautoLiftRel S dec (rat_star. r1) m) (fgauto_lift_rel_prop S dec (rat_star. r1) m)
         (z ↦ mere_rec (Σ (List W) (lw ↦ Product (FgautoAllIn W (fgauto_rat_mem Mw (fgauto_lift_expr S r1)) lw)
               (Id W (fgauto_list_product MF (z .fst) .fst) (red (fgauto_list_product Mw lw)))))
           (FgautoLiftRel S dec (rat_star. r1) m) (fgauto_lift_rel_prop S dec (rat_star. r1) m)
           (y ↦ mk (rat_star. r1) m (fgauto_list_product Mw (y .fst))
             (mere (TW (fgauto_list_product Mw (y .fst))) (y .fst, (y .snd .fst, refl (fgauto_list_product Mw (y .fst)))))
             (concat W (red (fgauto_list_product Mw (y .fst))) (fgauto_list_product MF (z .fst) .fst) (m .fst)
               (inverse W (fgauto_list_product MF (z .fst) .fst) (red (fgauto_list_product Mw (y .fst))) (y .snd .snd))
               (inverse W (m .fst) (fgauto_list_product MF (z .fst) .fst) (refl ((g ↦ g .fst) : RW → W) (z .snd .snd)))))
           (fgauto_lift_star_out S dec r1 (a ↦ fgauto_lift_expr_correct S dec r1 a .fst) (z .fst) (z .snd .fst))) h,
       h ↦ mere_rec (Σ W (w ↦ Product (fgauto_rat_mem Mw (fgauto_lift_expr S (rat_star. r1)) w) (Id W (red w) (m .fst))))
         (fgauto_rat_mem MF (rat_star. r1) m) (fgauto_rat_mem_prop MF (rat_star. r1) m)
         (z ↦ mere_rec (TW (z .fst)) (fgauto_rat_mem MF (rat_star. r1) m) (fgauto_rat_mem_prop MF (rat_star. r1) m)
           (y ↦ mere TF (fgauto_list_map W RW (fgauto_reduce_word S dec) (y .fst),
             (fgauto_lift_star_in S dec r1 (a ↦ fgauto_lift_expr_correct S dec r1 a .snd) (y .fst) (y .snd .fst),
              reduced_word_path S m (fgauto_list_product MF (fgauto_list_map W RW (fgauto_reduce_word S dec) (y .fst)))
                (calc
                  m .fst = red (z .fst) by inverse W (red (z .fst)) (m .fst) (z .snd .snd)
                  = red (fgauto_list_product Mw (y .fst)) by refl red (y .snd .snd)
                  = fgauto_list_product MF (fgauto_list_map W RW (fgauto_reduce_word S dec) (y .fst)) .fst
                    by inverse W (fgauto_list_product MF (fgauto_list_map W RW (fgauto_reduce_word S dec) (y .fst)) .fst)
                         (red (fgauto_list_product Mw (y .fst))) (fgauto_productF_map S dec (y .fst)) ∎))))
           (z .snd .fst)) h) ]
