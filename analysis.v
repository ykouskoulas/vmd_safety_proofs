Require Import Reals.
Require Import Rdefinitions.
Require Import Classical.
Require Import Fourier.
Require Import seot_util.
Require Import FunctionalExtensionality.
Require Import Classical_Prop.
Local Open Scope R_scope.


Lemma last_leg_drop_edge : forall f a b
                        (c : continuity f)
                        (altb : a < b)
                        (fagt0 : f a = 0)
                        (fblt0 : f b < 0),
    exists p, a <= p < b /\ f p = 0 /\ forall q, p < q < b -> f q < 0.
Proof.
  intros.

  set (z := a).
  assert (a <= z <= b) as zwithin.
  split. right. unfold z. reflexivity.
  left. assumption.
  assert (f z = 0) as zroot. assumption.
  
  assert (a <= z < b) as zwithin2.
  split; inversion_clear zwithin as [aleqz zleqb].
  assumption.
  inversion_clear aleqz as [altz | aeqz]. assumption.
  rewrite <- aeqz. assumption.

  set (E := (fun q => a <= q < b /\ f q = 0)).

  assert (bound E) as Ebnd. unfold E, bound, is_upper_bound.
  exists b. intros.
  inversion_clear H as [xbnd root].
  inversion_clear xbnd as [alex xleb].
  left. assumption.

  assert (E z) as Ez; [ unfold E; split; assumption | idtac].
  
  assert (exists x, E x) as Einhabited. exists z.
  unfold E. split; assumption.
  generalize (completeness E Ebnd Einhabited) as limsupE. intros.

  inversion_clear limsupE as [m mislub].
  exists m.

  assert (f m = 0) as fmeq0.
  generalize (Rtotal_order (f m) 0) as fm0. intros.
  inversion_clear fm0.
  apply False_ind.
  unfold continuity, continuity_pt, continue_in, D_x,
  no_cond, limit1_in, R_met, limit_in, dist, Base, R_dist in c.
  assert (- (f m / 2) > 0) as nfm2gt0. apply Rlt_gt.
  apply Ropp_0_gt_lt_contravar.
  apply Rlt_gt.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl (f m). setr 0. assumption.
  generalize (c m (- (f m / 2)) nfm2gt0). intros contfm.
  inversion_clear contfm as [alpha [agt0 contbox]].

  assert (forall x : R, m-(alpha/2) < x <= m -> f x < 0) as newub.
  intros x range.
  inversion_clear range as [xlb xub].
  inversion_clear xub as [xltm | xeqm].
  assert ((True /\ m <> x) /\ Rabs (x - m) < alpha) as precond.
  split. split. exact I.
  apply Rgt_not_eq.
  assumption.
  unfold Rabs.
  destruct (Rcase_abs (x - m)).
  fourier.
  fourier.
  generalize (contbox x precond) as nonzbnd. clear contbox precond.
  intros.
  unfold Rabs in nonzbnd.
  destruct (Rcase_abs (f x - f m)).
  fourier.
  fourier. clear contbox.
  subst. assumption.
  
  inversion_clear mislub as [misub nolowerub].
  assert (is_upper_bound E (m- (alpha/2))) as neub.
  unfold is_upper_bound.
  intros x Ex.
  apply Rnot_gt_le.
  intro xub.
  apply Rgt_lt in xub.
  generalize (Rtotal_order x m) as xandm3. intros.

  assert (x <= m \/ x > m) as xandm.
  inversion_clear xandm3. left. left. assumption.
  inversion_clear H0. left. right. assumption.
  right. assumption. clear xandm3.
  
  inversion_clear xandm as [xlem | xgtm].
  assert (m - alpha / 2 < x <= m).
  split. assumption.  assumption.
  generalize (newub x H0) as fxlt0. intros.
  unfold E in Ex.
  inversion_clear Ex as [altxltb fxeq0].
  rewrite fxeq0 in fxlt0.
  apply (Rlt_irrefl 0). assumption.
  unfold is_upper_bound in misub.
  generalize (misub _ Ex).
  apply Rgt_not_le. assumption.

  generalize (nolowerub (m - alpha/2) neub).
  apply Rlt_not_le .
  fourier.


  inversion_clear H as [fmeq0 | fmgt0].
  assumption.
  
  apply False_ind.
  inversion_clear mislub as [iub lub].
  unfold is_upper_bound in iub,lub.
  assert (forall x, E x -> x <= b). intros.
  unfold E in H. inversion_clear H. inversion_clear H0.
  left. assumption.
  generalize (lub b H) as mleqb. intros.
  assert (f m * f b <= 0) as prodneg. left.
  setr (f m * 0).
  apply Rmult_lt_compat_l; assumption.
  generalize (IVT_cor f m b c mleqb prodneg) as root. intros.
  inversion_clear root as [z0 [z0rng fz0eq0]].
  assert (E z0). unfold E.
  generalize (iub z Ez). intros.
  inversion_clear zwithin2.
  inversion_clear z0rng as [z0above z0below].
  split. split. fourier.

  inversion_clear z0below. assumption.
  subst. rewrite fz0eq0 in fblt0.
  apply False_ind.
  apply (Rlt_irrefl 0).
  assumption.
  assumption.

  generalize (iub z0 H0).
  intros z0lem.
  inversion_clear z0lem.
  inversion_clear z0rng.
  apply (Rlt_not_le m z0). assumption. assumption.
  rewrite H1 in fz0eq0. rewrite fz0eq0 in fmgt0.
  apply (Rgt_irrefl 0). assumption.

  inversion_clear mislub as [Emub Emlb].
  unfold is_upper_bound in Emlb , Emub.
  assert (forall x, E x -> x <= b).
  intros. unfold E in H.
  inversion_clear H. inversion_clear H0.
  left. assumption.
  generalize (Emlb b H). intros.
  inversion_clear H0.
  Focus 2. rewrite H1 in fmeq0.
  rewrite fmeq0 in fblt0.
  apply False_ind.
  apply (Rlt_irrefl 0). assumption.
  generalize (Emub z Ez). intros.
  inversion_clear zwithin2.
  
  split. split.
  fourier. fourier. split. assumption.

  intros q mqb.
  inversion_clear mqb as [mltq qltb].
  generalize (Rtotal_order (f q) 0) as fq0rel.
  intros.
  inversion_clear fq0rel as [fqlt0 | [fqeq0 | fqgt0]].
  assumption.

  apply False_ind.
  assert (E q) as Eq.
  unfold E.
  split. split.
  fourier.
  fourier.
  assumption.
  generalize (Emub q Eq) as qlem. intros.
  apply (Rlt_not_le q m mltq).
  assumption.

  assert (q <= b) as qleb. left. assumption.
  assert (f q * f b <= 0) as prodneg. left.
  setr (f q * 0).
  apply Rmult_lt_compat_l; assumption.
  generalize (IVT_cor f q b c qleb prodneg) as root. intros.
  inversion_clear root as [z0 [z0rng fz0eq0]].
  assert (E z0) as Ez0. unfold E.
  inversion_clear z0rng as [qlez0 z0leb].
  split.
  split.
  fourier.
  inversion z0leb as [z0ltb | z0eqb].
  assumption. rewrite z0eqb in fz0eq0.
  rewrite fz0eq0 in fblt0.
  apply False_ind.
  apply (Rlt_irrefl 0). assumption.
  assumption.
  apply False_ind.
  inversion_clear z0rng as [qlez0 z0leb].

  generalize (Emub z0 Ez0) as qlem. intros.
  fourier.
Qed.


Lemma last_leg_drop : forall f a b
                        (c : continuity f)
                        (altb : a < b)
                        (fage0 : f a >= 0)
                        (fblt0 : f b < 0),
    exists p, a <= p < b /\ f p = 0 /\ forall q, p < q < b -> f q < 0.
Proof.
  intros.
  inversion_clear fage0 as [fagt0 | faeq0].

  assert (a <= b) as aleqb. left. assumption.
  assert (f a * f b <= 0) as prodneg. left.
  setr (f a * 0).
  apply Rmult_lt_compat_l; assumption.
  generalize (IVT_cor f a b c aleqb prodneg) as root. intros.
  inversion_clear root as [z [zwithin zroot]]. clear prodneg aleqb.
  assert (a < z < b) as zwithin2.
  split; inversion_clear zwithin as [aleqz zleqb].
  inversion_clear aleqz as [altz | aeqz]. assumption.
  subst. rewrite zroot in fagt0.
  apply False_ind.
  apply (Rgt_irrefl 0). assumption.
  inversion_clear zleqb as [zltb | zeqb]. assumption.
  subst. rewrite zroot in fblt0.
  apply False_ind.
  apply (Rlt_irrefl 0). assumption.
  inversion_clear zwithin2 as [altz zltb].
  
  generalize (last_leg_drop_edge f z b c zltb zroot fblt0) as llde. intros.
  inversion_clear llde as [p [[zlep pltb] [fpeq0 fqlt0]]].
  exists p. split. split. fourier. assumption. split. assumption. assumption.
  
  apply (last_leg_drop_edge f a b c altb faeq0 fblt0).
Qed.


Lemma first_leg_rise : forall f a b
                        (c : continuity f)
                        (altb : a < b)
                        (fagt0 : f a < 0)
                        (fblt0 : f b >= 0),
    exists p, a < p <= b /\ f p = 0 /\ forall q, a < q < p -> f q < 0.
Proof.
  intros.
  set (g := (fun x => f (- x))).
  assert (continuity g) as cg.
  unfold g. reg.
  assert (g (-a) < 0) as gnalt0.
  unfold g. rewrite Ropp_involutive. assumption.
  assert (g (-b) >= 0) as gnbgt0.
  unfold g. rewrite Ropp_involutive. assumption.

  assert (-b < -a) as nbltna. fourier.
  generalize (last_leg_drop g (-b) (-a) cg nbltna gnbgt0 gnalt0) as root.
  intros.
  inversion_clear root as [p [[nbltp pltna] [gpeq0 rest]]].
  exists (-p).
  split.
  split.
  fourier.
  fourier.
  split.
  trivial.
  unfold g in rest.

  intros q altltnp.
  inversion_clear altltnp as [altq qltnp].
  assert (p < -q < -a) as pltnqltna.
  split; fourier.
  generalize (rest (-q) pltnqltna). intros.
  rewrite Ropp_involutive in H. assumption.
Qed.



Lemma last_leg_rise: forall f a b
                        (c : continuity f)
                        (altb : a < b)
                        (fagt0 : f a <= 0)
                        (fblt0 : f b > 0),
    exists p, a <= p < b /\ f p = 0 /\ forall q, p < q < b -> 0 < f q.
Proof.
  intros.
  set (g := (-f)%F).
  assert (continuity g).
  unfold g. reg.
  assert (0 <= g a). 
  unfold g, opp_fct.
  setl (- 0).
  apply Ropp_le_contravar. assumption.
  assert (g b < 0).
  unfold g, opp_fct.
  setr (- 0).
  apply Ropp_lt_contravar. assumption.
  unfold g, opp_fct.
  assert (forall x, f x = (fun x => - (g x)) x).
  intros.
  unfold g.
  unfold opp_fct.
  rewrite Ropp_involutive. reflexivity.
  generalize (functional_extensionality f (fun x0 : R => - g x0) H2). intros.
  rewrite H3.
  apply Rle_ge in H0.
  generalize (last_leg_drop g a b H altb H0 H1). intros.
  inversion_clear H4 as [p [q [r s]]].

  exists p. split. assumption. split.
  apply (Rmult_eq_reg_l (-1)).
  setr (0).
  setl (g p). assumption.
  discrR.
  intros.
  setl (- 0).
  apply Ropp_lt_contravar.
  apply s. assumption.
Qed.



Lemma first_leg_drop : forall f a b
                        (c : continuity f)
                        (altb : a < b)
                        (fagt0 : f a > 0)
                        (fblt0 : f b <= 0),
    exists p, a < p <= b /\ f p = 0 /\ forall q, a < q < p -> 0 < f q.
Proof.
  intros.
  set (g := (-f)%F).
  assert (continuity g).
  unfold g. reg.
  assert (g a < 0). 
  unfold g, opp_fct.
  setr (- 0).
  apply Ropp_lt_contravar. assumption.
  assert (0 <= g b).
  unfold g, opp_fct.
  setl (- 0).
  apply Ropp_le_contravar. assumption.
  unfold g, opp_fct.
  assert (forall x, f x = (fun x => - (g x)) x).
  intros.
  unfold g.
  unfold opp_fct.
  rewrite Ropp_involutive. reflexivity.
  generalize (functional_extensionality f (fun x0 : R => - g x0) H2). intros.
  rewrite H3.
  apply Rle_ge in H1.
  generalize (first_leg_rise g a b H altb H0 H1). intros.
  inversion_clear H4 as [p [q [r s]]].

  exists p. split. assumption. split.
  apply (Rmult_eq_reg_l (-1)).
  setr (0).
  setl (g p). assumption.
  discrR.
  intros.
  setl (- 0).
  apply Ropp_lt_contravar.
  apply s. assumption.
Qed.


Lemma limpoint : forall (f g : R -> R) y
                   (contf : continuity f)
                   (contg : continuity g)
                   (exgxltfx : exists w, w < y /\
                                         forall x, w < x < y -> g x <= f x),
    g y <= f y.
Proof.
  intros.
  inversion_clear exgxltfx as [w [wlty gxltfx]].
  apply Rnot_gt_le.
  intro gygtfy.
  apply Rgt_lt in gygtfy.
  assert (0 < g y - f y) as zltgymfy.
  Radd (f y). setl (f y). setr (g y). assumption.
  generalize (contf y) as contfy. intro.
  generalize (contg y) as contgy. intro.
  unfold continuity_pt, continue_in, limit1_in, limit_in, dist,
         R_met, D_x, no_cond, R_dist in contfy, contgy.
  simpl in contfy, contgy.
  set (eps := (g y - f y)/2).
  assert (eps > 0) as epsgt0.
  unfold eps.
  apply Rlt_gt.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl 0. setr (g y - f y). assumption.
  generalize (contgy eps epsgt0) as gyfacts.
  generalize (contfy eps epsgt0) as fyfacts.
  intros.
  clear contfy contgy.
  inversion_clear fyfacts as [alpf [alpfgt0 frest]].
  inversion_clear gyfacts as [alpg [alpggt0 grest]].
  set (alp := Rmax (y - (Rmin alpf alpg)/2) (y - (y - w)/2)).
  assert (0 < (Rmin alpf alpg)/2) as mingt0.
  unfold Rmin in *. destruct (Rle_dec alpf alpg).
  prove_sup. assumption. apply Rinv_0_lt_compat. prove_sup.
  prove_sup. assumption. apply Rinv_0_lt_compat. prove_sup.

  assert ((True /\ y <> alp) /\ Rabs (alp - y) < alpf) as fprec.
  split. split. trivial. intro. unfold alp in H.
  unfold Rmax in *.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w)/2)).
  assert (y = w) as yeqw. Radd (-y). setl 0. setr (- (y - w)).
  apply (Rmult_eq_reg_l (/2)).
  setl 0. setr (- (y - w)/2). setl (y - y).
  Radd y. setl y. setr (y - (y - w) / 2). assumption.
  apply Rinv_neq_0_compat. discrR.
  rewrite yeqw in wlty.
  apply (Rlt_irrefl w). assumption.
  assert (0 = (Rmin alpf alpg)/2) as zeromin.
  apply (Rmult_eq_reg_l (-1)).
  Radd y. setl y. setr (y - Rmin alpf alpg / 2). assumption.
  discrR.
  rewrite <- zeromin in mingt0.
  eapply Rlt_irrefl. apply mingt0.

  unfold alp.
  unfold Rmax in *.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w)/2)).
  fieldrewrite (y - (y - w)/2 - y) (- (y - w)/2).
  unfold Rabs. destruct (Rcase_abs (- (y - w)/2)).
  setl ((y - w)/2).
  assert ((y - w) <= Rmin alpf alpg).
  Radd (- (y - w) - Rmin alpf alpg).
  apply (Rmult_le_reg_l (/2)).
  apply Rinv_0_lt_compat. prove_sup.
  Radd y.
  setl (y - Rmin alpf alpg / 2).
  setr (y - (y - w) / 2). assumption.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl (y - w). unfold Rmin in H.
  destruct (Rle_dec alpf alpg). fourier.
  apply Rnot_le_lt in n. fourier.
  apply False_ind.
  apply (Rge_not_lt _ _ r0).
  setr (-0). setl (- ((y - w)/2)).
  apply Ropp_lt_contravar.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl 0. setr (y - w). fourier.
  
  fieldrewrite (y - (Rmin alpf alpg)/2 - y) (- Rmin alpf alpg / 2).
  unfold Rmin. destruct (Rle_dec alpf alpg).
  unfold Rabs. destruct (Rcase_abs (- alpf / 2)).
  setl (alpf / 2).
  apply (Rmult_lt_reg_l (2/alpf)). prove_sup.
  apply Rinv_0_lt_compat. assumption.
  setl 1. intro. rewrite H in r0. assert (0 < 0). fourier.
  eapply Rlt_irrefl. apply H0.
  setr 2. intro. rewrite H in r0. assert (0 < 0). fourier.
  eapply Rlt_irrefl. apply H0. prove_sup.

  apply (Rmult_lt_reg_l (2/alpf)). prove_sup.
  apply Rinv_0_lt_compat. assumption.
  setl (-1). intro. rewrite H in r0. assert (0 < 0). fourier.
  eapply Rlt_irrefl. apply H0.
  setr 2. intro. rewrite H in r0. assert (0 < 0). fourier.
  eapply Rlt_irrefl. apply H0. prove_sup.

  assert (alpg < alpf) as alpgltalpf. apply Rnot_le_lt. assumption.
  unfold Rabs. destruct (Rcase_abs (- alpg / 2)).
  
  setl (alpg / 2).
  apply (Rmult_lt_reg_l 2). prove_sup. setl (alpg + 0).
  setr (alpf + alpf).
  apply Rplus_lt_compat; try assumption.

  apply (Rmult_lt_reg_l 2). prove_sup. setl (0 + - alpg).
  setr (alpf + alpf).
  apply Rplus_lt_compat; try assumption.
  prove_sup; try assumption.

  generalize (frest alp fprec) as ffacts. clear fprec frest. intros.


  assert ((True /\ y <> alp) /\ Rabs (alp - y) < alpg) as gprec.
  split. split. trivial. intro. unfold alp in H.
  unfold Rmax in *.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w)/2)).
  assert (y = w) as yeqw. Radd (-y). setl 0. setr (- (y - w)).
  apply (Rmult_eq_reg_l (/2)).
  setl 0. setr (- (y - w)/2). setl (y - y).
  Radd y. setl y. setr (y - (y - w) / 2). assumption.
  apply Rinv_neq_0_compat. discrR.
  rewrite yeqw in wlty.
  apply (Rlt_irrefl w). assumption.

  assert (0 = (Rmin alpf alpg)/2) as zeromin.
  apply (Rmult_eq_reg_l (-1)).
  Radd y. setl y. setr (y - Rmin alpf alpg / 2). assumption.
  discrR.
  rewrite <- zeromin in mingt0.
  eapply Rlt_irrefl. apply mingt0.

  unfold alp.
  unfold Rmax in *.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w)/2)).
  fieldrewrite (y - (y - w)/2 - y) (- (y - w)/2).
  unfold Rabs. destruct (Rcase_abs (- (y - w)/2)).
  setl ((y - w)/2).
  assert ((y - w) <= Rmin alpf alpg).
  Radd (- (y - w) - Rmin alpf alpg).
  apply (Rmult_le_reg_l (/2)).
  apply Rinv_0_lt_compat. prove_sup.
  Radd y.
  setl (y - Rmin alpf alpg / 2).
  setr (y - (y - w) / 2). assumption.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl (y - w). unfold Rmin in H.
  destruct (Rle_dec alpf alpg). fourier.
  apply Rnot_le_lt in n. fourier.
  apply False_ind.
  apply (Rge_not_lt _ _ r0).
  setr (-0). setl (- ((y - w)/2)).
  apply Ropp_lt_contravar.
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl 0. setr (y - w). fourier.
  
  fieldrewrite (y - (Rmin alpf alpg)/2 - y) (- Rmin alpf alpg / 2).
  unfold Rmin. destruct (Rle_dec alpf alpg).
  unfold Rabs. destruct (Rcase_abs (- alpf / 2)).
  apply (Rmult_lt_reg_l 2). prove_sup.
  setl (0 + alpf). setr (alpg + alpg).
  apply Rplus_lt_le_compat; try assumption.

  apply (Rmult_lt_reg_l 2). prove_sup. setl (0 + - alpf).
  setr (alpg + alpg).
  apply Rplus_lt_compat; try assumption.
  prove_sup; try assumption.

  assert (alpg < alpf) as alpgltalpf. apply Rnot_le_lt. assumption.
  unfold Rabs. destruct (Rcase_abs (- alpg / 2)).
  
  setl (alpg / 2).
  apply (Rmult_lt_reg_l 2). prove_sup. setl (0 + alpg).
  setr (alpg + alpg).
  apply Rplus_lt_le_compat; try assumption. right. reflexivity.

  apply (Rmult_lt_reg_l 2). prove_sup. setl (0 + - alpg).
  setr (alpg + alpg).
  apply Rplus_lt_compat; try assumption.
  prove_sup; try assumption.

  generalize (grest alp gprec) as gfacts. clear gprec grest. intros.

  assert (f y < (f y + g y) / 2) as fybelow.
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd (- f y). setl (f y). setr (g y).
  assumption.

  assert ((f y + g y) / 2 < g y) as gyabove.
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd (- g y). setr (g y). setl (f y).
  assumption.

  unfold Rabs in ffacts, gfacts.
  assert (alp < y) as alplty.
  unfold alp.
  unfold Rmax.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w) / 2)).
  Radd (- y + (y - w)/2). setl 0.
  setr ((y - w)/2).
  apply (Rmult_lt_reg_l 2). prove_sup. setl 0. setr (y - w).
  fourier.
  
  Radd (-y + Rmin alpf alpg /2). setl 0.
  setr (Rmin alpf alpg / 2).
  unfold Rmin.
  destruct (Rle_dec alpf alpg).
  apply (Rmult_lt_reg_l 2). prove_sup. setl 0. setr alpf. assumption.
  apply (Rmult_lt_reg_l 2). prove_sup. setl 0. setr alpg. assumption.

  assert (w < alp) as wltalp. unfold alp, Rmax.
  destruct (Rle_dec (y - Rmin alpf alpg / 2) (y - (y - w) / 2)).
  setr ((y+w) / 2).
  apply (Rmult_lt_reg_l 2). prove_sup. setr (y + w).
  Radd (-w). setl w. setr y. fourier.
  apply Rnot_le_lt in n.
  assert (Rmin alpf alpg < (y - w)).
  apply (Rmult_lt_reg_l (/2)).
  apply Rinv_0_lt_compat. prove_sup.
  Radd (y - Rmin alpf alpg / 2 - (y - w)/2).
  setl ( y - (y - w) / 2). setr (y - Rmin alpf alpg / 2). assumption.
  fourier.

  assert (w < alp < y) as wltalplty. split; try assumption.
  generalize (gxltfx alp wltalplty) as galtfa. intros.
  destruct (Rcase_abs (f alp - f y)).
  destruct (Rcase_abs (g alp - g y)).

  unfold eps in gfacts, ffacts.
  clear ffacts r0.
  assert ((f y + g y) / 2 < g alp).
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd ((g y - f y) - 2 * g alp).
  setr ((g y - f y)).
  setl (- 2 * (g alp - g y)).
  apply (Rmult_lt_reg_l (/ 2)). prove_sup.
  apply Rinv_0_lt_compat. prove_sup.
  setl (- (g alp - g y)). setr ((g y - f y)/2). assumption.
  
  assert (f alp < f y) as faltfy. fourier.

  (*  falp < f y < (f y + g y)/2 < g alp *)
  assert (f alp < g alp) as falega.
  eapply Rlt_trans. apply faltfy.
  eapply Rlt_trans. apply fybelow.
  eapply Rlt_le_trans. apply H. right. reflexivity.
  eapply Rlt_not_ge. apply falega.
  fourier.

  assert (g y <= g alp) as gyltga. fourier.
  assert (f alp < f y) as faltfy. fourier.
  assert (f alp < g alp) as faltga. fourier.
  eapply Rlt_not_le. eapply faltga.
  assumption.


  destruct (Rcase_abs (g alp - g y)).

  unfold eps in gfacts, ffacts.
  clear r r0.
  assert ((f y + g y) / 2 < g alp).
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd ((g y - f y) - 2 * g alp).
  setr ((g y - f y)).
  setl (- 2 * (g alp - g y)).
  apply (Rmult_lt_reg_l (/ 2)). prove_sup.
  apply Rinv_0_lt_compat. prove_sup.
  setl (- (g alp - g y)). setr ((g y - f y)/2). assumption.

  assert (f alp < (f y + g y)/2) as faltfg2.
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd (- 2 * f y).
  setr (g y - f y).
  setl (2 * (f alp - f y)).
  apply (Rmult_lt_reg_l (/ 2)). prove_sup.
  apply Rinv_0_lt_compat. prove_sup.
  setl (f alp - f y). setr ((g y - f y)/2). assumption.

  (*  falp < (f y + g y)/2 < g alp *)
  assert (f alp < g alp) as falega.
  eapply Rlt_trans. apply faltfg2.
  apply H.
  eapply Rlt_not_ge. apply falega.
  fourier.

  unfold eps in gfacts, ffacts.
  assert (g y <= g alp) as gyltga. fourier.

  assert (f alp < (f y + g y)/2) as faltfg2.
  apply (Rmult_lt_reg_l 2). prove_sup.
  Radd (- 2 * f y).
  setr (g y - f y).
  setl (2 * (f alp - f y)).
  apply (Rmult_lt_reg_l (/ 2)). prove_sup.
  apply Rinv_0_lt_compat. prove_sup.
  setl (f alp - f y). setr ((g y - f y)/2). assumption.

  (*  falp < (f y + g y)/2 < g y <= g alp *)
  assert (f alp < g alp) as falega.
  eapply Rlt_trans. apply faltfg2.
  eapply Rlt_le_trans. apply gyabove.
  assumption.
  fourier.
Qed.
