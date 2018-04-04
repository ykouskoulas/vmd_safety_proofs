Require Import Classical.
Require Import Reals.
Require Import Fourier.
Require Import seot_util.
Require Import FunctionalExtensionality.
Require Import analysis.
Require Import List.
Import ListNotations.
Local Open Scope R_scope.


(* describes coefficents used in a second order polynomial *)
Record coeff : Type := mkcoeff { a : R;  b:R ; c:R }.

(* This construction describes conditions for polynomial with coefficients trj1 to be above and safely vertically separated from a polynomial path with coefficients trj2 by a distance of hp during the time period tb<=t<=te *)

(* Given coefficients a, b, and c, this function defines a trajectory
that describes the altitude of the aircraft for all t
J(t) = a*t^2 + b*t + c
*)
Definition J (z : coeff) (t : R) := (a z) *t^2 + (b z)*t + (c z).

Definition Poly A B C t := J (mkcoeff A B C) t.

                                        
Definition interv_vert_safe (trj1 trj2 : coeff) (tb te :R) : option R := 
let         A := (a trj1) - (a trj2) in
let         B := (b trj1) - (b trj2) in
let         C := (c trj1) - (c trj2) in
let         D := B^2 - 4*A*C in
let         S1 :=(-B - sqrt D)/(2*A) in
let         S2 :=(-B + sqrt D)/(2*A) in
let         x_extremal := -B/(2*A) in
match Rle_dec tb te with
| left tblete =>
  match total_order_T A 0 with
  | inleft (left alt0) => (* A < 0 *)
    match Rlt_dec x_extremal ((tb+te)/2%R) with
    | left xltave => Some (Poly A B C te)
    | right xgeave => Some (Poly A B C tb)
    end
  | inleft (right aeq0) => (* A = 0 *)
    match Rle_dec B 0 with
    | left Ble0 => Some (Poly A B C te)
    | right Bgt0 => Some (Poly A B C tb)
    end
  | inright agt0 => (* A > 0 *)
    match (Rle_dec tb x_extremal, Rle_dec x_extremal te) with
    | (left tblex, left xlete) => Some (Poly A B C x_extremal)
    | (right tbgtx, _) => Some (Poly A B C tb)
    | _ => Some (Poly A B C te)
    end
  end
| right tbnlete =>
  None
end.

Theorem ivs_empty_interval : forall trj1 trj2 tb te,
    tb>te ->
    interv_vert_safe trj1 trj2 tb te = None.
  intros.
  unfold interv_vert_safe.
  case_eq (Rle_dec tb te). intros.
  fourier. intros. reflexivity.
Qed.

Theorem ivs_interval_empty : forall trj1 trj2 tb te,
    interv_vert_safe trj1 trj2 tb te = None ->
    tb>te.
Proof.
  intros.
  unfold interv_vert_safe in H.
  case_eq (Rle_dec tb te).
  intros; rewrite H0 in H.
  exfalso.
  destruct (total_order_T (a trj1 - a trj2) 0).
  destruct s.
  destruct (Rlt_dec (- (b trj1 - b trj2) / (2 * (a trj1 - a trj2)))
                    ((tb + te) / 2)); discriminate.
  destruct (Rle_dec (b trj1 - b trj2) 0); discriminate.
  destruct (Rle_dec tb (- (b trj1 - b trj2) / (2 * (a trj1 - a trj2))));
  destruct (Rle_dec (- (b trj1 - b trj2) / (2 * (a trj1 - a trj2))) te);
  discriminate.
  intros.
  apply Rnot_le_gt. assumption.
Qed.

(* 
   This is the proof that shows that Γ does what
   we say it claims to do. Use this as a building block for the 
   rest of the vertical proof 
*)

Theorem safely_separated_second_order_polynomial_interval:
  forall coeffU coeffL t1 t2 t vmd,
               t1 <= t <= t2 ->
               (interv_vert_safe coeffU coeffL t1 t2) = Some vmd ->
               vmd <= (J coeffU t-J coeffL t).
Proof.
  intros.
  rename H0 into sfty.
  destruct coeffU as [au bu cu].
  destruct coeffL as [al bl cl].
  unfold J, a, b, c.
  apply (Rplus_le_reg_r (-vmd)).
  setl 0.
  setr ((au-al) * t ^ 2 + (bu-bl)* t + (cu-cl-vmd)).

  assert (t1 <= t2) as t1let2.
  inversion_clear H. fourier.
  
  unfold interv_vert_safe, Poly, J in sfty. simpl in sfty.
  destruct (Rle_dec t1 t2).
  Focus 2. apply False_ind. apply n. apply t1let2. clear r.
  set (A := (au - al)) in *.
  set (B := (bu - bl)) in *.
  set (C := (cu - cl - vmd)) in *.
  set (f := (fct_cte A * Rsqr + fct_cte B * id + fct_cte C)%F).
  establish_deriv2 f' (fct_cte 2 * fct_cte A * id + fct_cte B)%F f.
  establish_deriv2 f'' (fct_cte 2 * fct_cte A)%F f'.
  rename H0 into fderivable.
  rename H1 into f'derivable.
  
  destruct (total_order_T A 0); [destruct s | idtac]; try
  (assert (f' (-B/(2*A)) = 0); [
    unfold f', fct_cte, mult_fct, plus_fct, id; field;
    intro Aeq0; rewrite Aeq0 in r; generalize (Rlt_irrefl 0);
    intro not0lt0; apply not0lt0; assumption
   | idtac]).

  Focus 2.
  (* linear case A=0 *)
  (* A=0, B<=0 *)
  rewrite e in *.
  destruct (Rle_dec B 0); injection sfty; clear sfty; intro sfty.
  assert (f t >= f t2).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite e in *.
  Radd (-C).
 
  setl (B*t2). setr (B * t).
  apply Rmult_le_compat_neg_l. assumption.
  inversion H. assumption.

  assert (f t2 = 0) as ft2eq0.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C. rewrite <- sfty. rewrite e. field.
  rewrite ft2eq0 in H0. 
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr in H0.
  apply Rge_le.
  rewrite e in H0. 
  assert (t^2 = (t*t)). field.
  rewrite <- H1 in H0. assumption.

  (* A=0, B>0 *)
  assert (f t1 <= f t).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite e in *.
  Radd (-C).
 
  setr (B*t). setl (B * t1).
  apply Rmult_le_compat_l. left.
  generalize (Rnot_le_gt _ _ n). intro.
  fourier.
  inversion H. assumption.

  assert (f t1 = 0).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C. rewrite <- sfty. rewrite e. field.
  rewrite H1 in H0. 
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr in H0.
  rewrite e in H0. 
  assert (t^2 = (t*t)). field.
  rewrite <- H2 in H0. assumption.

  (* case A<0 *)

  assert (forall q, (f (- B / (2 * A) + q) = f (- B / (2 * A) - q))) as fsym. intros.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  Radd (- C - A*B*B/(2*2*A*A) - A*q*q).
  setl (B * (- B / (2 * A) + q) - 2*A*B*q/(2*A)).
  intro aeq0. rewrite aeq0 in r.  fourier.
  setr (B * (- B / (2 * A) - q) + 2*A*B*q/(2*A)).
  intro aeq0. rewrite aeq0 in r.  fourier.
  field.
  intro aeq0. rewrite aeq0 in r.  fourier.
  
  rename H0 into f'extr.

  generalize (fsym (B / (2 * A) + t1)). intros feq.
  assert ((- B / (2 * A) + (B / (2 * A) + t1)) = t1). field.
  intro aeq0. rewrite aeq0 in r.  fourier.
  rewrite H0 in feq. clear H0.

  assert ((- B / (2 * A) - (B / (2 * A) + t1)) =
          (- B / (2 * A) + (- B / (2 * A)) - t1)). field.
  intro aeq0. rewrite aeq0 in r. fourier.
  rewrite H0 in feq. clear H0.

  generalize (fsym (B / (2 * A) + t2)). intros feq2.
  assert ((- B / (2 * A) + (B / (2 * A) + t2)) = t2). field.
  intro aeq0. rewrite aeq0 in r.  fourier.
  rewrite H0 in feq2. clear H0.

  assert ((- B / (2 * A) - (B / (2 * A) + t2)) =
          (- B / (2 * A) - (t2 - - B / (2 * A)))). field.
  intro aeq0. rewrite aeq0 in r. fourier.
  rewrite H0 in feq2. clear H0.

  (* to the left of our [t1,t2] window *)
  destruct (Rlt_dec (- B / (2 * A)) ((t1 + t2) / 2)).
  injection sfty; clear sfty; intro sfty.
  assert (0 = f t2).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C.
  rewrite <- sfty.
  field.
  clear sfty. rename H0 into sfty.
  cut (0 <= f t). intro.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr in H0.
  setr (A * (t * t) + B * t + C). assumption.

  inversion_clear t1let2 as [t1ltt2 | l1eqt2].

  Focus 2. (* t1=t2 case*) inversion_clear H. subst. inversion_clear H1.
  inversion_clear H0. generalize (Rlt_asym _ _ H). intro.
  apply False_ind. apply H0. assumption.
  subst. apply False_ind. eapply Rlt_irrefl. apply H.
  subst. rewrite sfty. right. reflexivity.

  assert (- B / (2*A) < t2) as cpos.
  assert ((t1+t2)/2 < t2). apply (Rmult_lt_reg_l 2). fourier.
  setl (t1+t2). fourier.
  apply (Rlt_trans _  ((t1+t2)/2) _). assumption. assumption.

  assert (- B / (2 * A) + - B / (2 * A) - t1 < t2) as t1gap.
  Radd t1.
  setl (2 * - B / (2*A)).
  intro aeq0. rewrite aeq0 in r. fourier.
  apply (Rmult_lt_reg_l (1/2)). fourier.
  setl (-B/(2*A)).
  intro aeq0. rewrite aeq0 in r. fourier.
  setr ((t1+t2)/2). assumption.

  assert (- B / (2 * A) - (t2 - - B / (2 * A)) < t1) as t2gap.
  Radd (t2 - t1). setr t2. setl (- B / (2 * A) + - B / (2 * A) - t1).
  intro aeq0. rewrite aeq0 in r. fourier.
  assumption.

  generalize (Rle_dec t (- B / (2 * A))). intro tpos.
  inversion_clear tpos as [tposle | tposgt].

  Focus 2. (* - B/(2*A) < t case *)
  assert (- B / (2*A) < t) as midltt.
  apply Rnot_le_lt. assumption. clear tposgt.

(*  clear f''negR f'negR ffalling.*)
  assert (forall q, - B / (2 * A) < q < t2 -> f'' q < 0) as f''negR. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  (-B/(2*A)) < q < t2 -> f' q< 0) as f'negR.
  intros q interval.
  unfold f', fct_cte, mult_fct, plus_fct, id, Rsqr. 
  rewrite <- f'extr.
  rewrite <- fe0 in f''negR.
  inversion_clear interval.
  assert (- B / (2 * A) < t2) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_decreasing_interv (-B/(2*A)) (t2) f' f'derivable).
  assumption. assumption.
  split. right. reflexivity. left. assumption.
  split. left. assumption. left. assumption. assumption.

  assert (forall q r,  (-B/(2*A)) <= q <= t2 ->
                       (-B/(2*A)) <= r <= t2 -> q < r -> f r < f q) as ffalling.
  intros q s [qintlbnd qintrbnd] [sintlbnd sintrbnd] qlts.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'negR.
  assert (- B / (2 * A) < t2).
  apply (Rle_lt_trans _ q). assumption. apply (Rlt_le_trans _ s). assumption. assumption.
  apply (derive_decreasing_interv (-B/(2*A)) (t2) f fderivable).
  assumption. assumption.
  split; assumption. split; assumption. assumption.

  inversion_clear H. inversion_clear H1.
  rewrite sfty. left.
  apply (ffalling t t2).
  split. left. assumption. left. fourier.
  split. left. apply (Rlt_le_trans _ t). assumption.
  left. assumption. right. reflexivity. assumption.
  rewrite H. rewrite sfty. right. reflexivity.

  (* clear f''negL f'posL frising.*)
  assert (forall q, (- B / (2 * A) - (t2 - - B / (2 * A))) < q < - B / (2 * A) -> f'' q < 0)
    as f''negL. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  (- B / (2 * A) - (t2 - - B / (2 * A))) < q < (-B/(2*A)) -> 0 < f' q)
    as f'posL. intros q interval.
  rewrite <- f'extr.
  rewrite <- fe0 in f''negL.
  inversion_clear interval.
  assert (- B / (2 * A) - (t2 - - B / (2 * A)) < - B / (2 * A)) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_decreasing_interv (- B / (2 * A) - (t2 - - B / (2 * A)))
                                       (-B/(2*A)) f' f'derivable order f''negL).
  split. left. assumption. left. assumption.
  split. left. assumption. right. reflexivity. assumption.
  
  assert (forall q r,  (- B / (2 * A) - (t2 - - B / (2 * A))) <= q <= (-B/(2*A)) ->
                       (- B / (2 * A) - (t2 - - B / (2 * A))) <= r <= (-B/(2*A)) ->
                       q < r -> f q < f r) as frising. intros q s qinterval rinterval qltr.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'posL.
  inversion_clear qinterval. inversion_clear rinterval.
  apply (derive_increasing_interv (- B / (2 * A) - (t2 - - B / (2 * A)))
                                  (-B/(2*A)) f fderivable).
  apply (Rle_lt_trans _ q). assumption.
  apply (Rlt_le_trans _ s). assumption. assumption.
  assumption. split; assumption. split; assumption. assumption.

  rewrite <- sfty in feq2.
  rewrite feq2. left.
  apply frising.
  split. right. auto. left.
  inversion_clear H. apply (Rlt_le_trans _ t1). assumption.
  apply (Rle_trans _ t). assumption. assumption.
  split. left. inversion_clear H. apply (Rlt_le_trans _ t1).
  assumption. assumption. assumption.
  apply (Rlt_le_trans _ t1). assumption.
  inversion_clear H. assumption.

  generalize (Rnot_lt_le _ _ n); clear n; intro n.

  (* to the right of our [t1,t2] window *)
  injection sfty; clear sfty; intro sfty.
  assert (0 = f t1).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C.
  rewrite <- sfty.
  field.
  clear sfty. rename H0 into sfty.
  cut (0 <= f t). intro.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr in H0.
  setr (A * (t * t) + B * t + C). assumption.

  inversion_clear t1let2 as [t1ltt2 | l1eqt2].

  Focus 2. (* t1=t2 case*) inversion_clear H. subst. inversion_clear H1.
  inversion_clear H0. generalize (Rlt_asym _ _ H). intro.
  apply False_ind. apply H0. assumption.
  subst. apply False_ind. eapply Rlt_irrefl. apply H.
  subst. rewrite sfty. right. reflexivity.

  assert (t1 <= - B / (2*A)) as cpos.
  assert (t1 <= (t1+t2)/2). apply (Rmult_le_reg_l 2). fourier.
  setr (t1+t2). fourier.
  apply (Rle_trans _  ((t1+t2)/2) _). assumption. assumption.

  assert (t2 <= - B / (2 * A) + (- B / (2 * A) - t1)) as t1gap.
  Radd t1.
  setr (2 * - B / (2*A)).
  intro aeq0. rewrite aeq0 in r. fourier.
  apply (Rmult_le_reg_l (1/2)). fourier.
  setr (-B/(2*A)).
  intro aeq0. rewrite aeq0 in r. fourier.
  setl ((t1+t2)/2). assumption.

  assert (t1 <= - B / (2 * A) - (t2 - - B / (2 * A))) as t2gap.
  Radd (t2 - t1). setl t2. setr (- B / (2 * A) + (- B / (2 * A) - t1)).
  intro aeq0. rewrite aeq0 in r. fourier.
  assumption.

  generalize (Rle_dec t (- B / (2 * A))). intro tpos.
  inversion_clear tpos as [tposle | tposgt].

  Focus 2. (* - B/(2*A) < t case *)
  assert (- B / (2*A) < t) as midltt.
  apply Rnot_le_lt. assumption. clear tposgt.

(*  clear f''negR f'negR ffalling.*)
  assert (forall q, - B / (2 * A) < q < (- B / (2 * A) + (- B / (2 * A) - t1)) ->
                    f'' q < 0) as f''negR. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  (-B/(2*A)) < q < (- B / (2 * A) + (- B / (2 * A) - t1)) ->
                     f' q< 0) as f'negR. intros q interval.
  unfold f', fct_cte, mult_fct, plus_fct, id, Rsqr. 
  rewrite <- f'extr.
  rewrite <- fe0 in f''negR.
  inversion_clear interval.
  assert (- B / (2 * A) < (- B / (2 * A) + (- B / (2 * A) - t1))) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_decreasing_interv (-B/(2*A)) (- B / (2 * A) + (- B / (2 * A) - t1)) f' f'derivable).
  assumption. assumption.
  split. right. reflexivity. left. assumption.
  split. left. assumption. left. assumption. assumption.

  assert (forall q r,  (-B/(2*A)) <= q <= (- B / (2 * A) + (- B / (2 * A) - t1)) ->
                       (-B/(2*A)) <= r <= (- B / (2 * A) + (- B / (2 * A) - t1)) ->
                       q < r -> f r < f q) as ffalling.
  intros q s [qintlbnd qintrbnd] [sintlbnd sintrbnd] qlts.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'negR.
  assert (- B / (2 * A) < (- B / (2 * A) + (- B / (2 * A) - t1))).
  apply (Rle_lt_trans _ q). assumption. apply (Rlt_le_trans _ s). assumption. assumption.
  apply (derive_decreasing_interv (-B/(2*A)) (- B / (2 * A) + (- B / (2 * A) - t1)) f fderivable).
  assumption. assumption.
  split; assumption. split; assumption. assumption.

  inversion_clear H. inversion_clear H1.
  rewrite sfty. rewrite feq. left.
  assert (- B / (2 * A) + (- B / (2 * A) - t1) = - B / (2 * A) + - B / (2 * A) - t1). field.
  intro aeq0. rewrite aeq0 in r. fourier. rewrite <- H1.  clear H1.
  apply ffalling.
  split. left. assumption. apply (Rle_trans _ t2). left. assumption. assumption.
  split. apply (Rle_trans _ t). left. assumption.
  apply (Rle_trans _ t2). left. assumption. assumption. right. reflexivity.
  apply (Rlt_le_trans _ t2). assumption. assumption.
  rewrite H in *. clear H H0.
  rewrite sfty. rewrite feq.
  inversion t1gap. left.
  apply ffalling.
  split. left. assumption. assumption.
  split. left. apply (Rlt_le_trans _ t2). assumption. 
  assert (- B / (2 * A) + (- B / (2 * A) - t1) = - B / (2 * A) + - B / (2 * A) - t1). field.
  intro aeq0. rewrite aeq0 in r. fourier.
  rewrite <- H0.  assumption. right. field.
  intro aeq0. rewrite aeq0 in r. fourier.
  assert (- B / (2 * A) + (- B / (2 * A) - t1) = - B / (2 * A) + - B / (2 * A) - t1). field.
  intro aeq0. rewrite aeq0 in r. fourier.
  rewrite <- H0. assumption. rewrite H. right. 
  assert (- B / (2 * A) + (- B / (2 * A) - t1) = - B / (2 * A) + - B / (2 * A) - t1). field.
  intro aeq0. rewrite aeq0 in r. fourier. rewrite H0.
  reflexivity.

  (* clear f''negL f'posL frising.*)
  assert (forall q, t1 < q < - B / (2 * A) -> f'' q < 0)
    as f''negL. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  t1 < q < (-B/(2*A)) -> 0 < f' q)
    as f'posL. intros q interval.
  rewrite <- f'extr.
  rewrite <- fe0 in f''negL.
  inversion_clear interval.
  assert (t1 < - B / (2 * A)) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_decreasing_interv t1
                                       (-B/(2*A)) f' f'derivable order f''negL).
  split. left. assumption. left. assumption.
  split. left. assumption. right. reflexivity. assumption.
  
  assert (forall q r,  t1 <= q <= (-B/(2*A)) ->
                       t1 <= r <= (-B/(2*A)) ->
                       q < r -> f q < f r) as frising. intros q s qinterval rinterval qltr.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'posL.
  inversion_clear qinterval. inversion_clear rinterval.
  apply (derive_increasing_interv t1
                                  (-B/(2*A)) f fderivable).
  apply (Rle_lt_trans _ q). assumption.
  apply (Rlt_le_trans _ s). assumption. assumption.
  assumption. split; assumption. split; assumption. assumption.

  rewrite sfty.
  inversion_clear H. inversion_clear H0. left.
  apply frising.
  split. right. auto. assumption.
  split. left. assumption. assumption. assumption.
  rewrite H. right. reflexivity.

  (* case 0<A *)
  rename H0 into f'extr.
  
  assert (forall q, - B / (2 * A) < q < t2 -> 0 < f'' q ) as f''posR. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  (-B/(2*A)) < q < t2 -> 0 < f' q ) as f'posR.
  intros q interval.
  unfold f', fct_cte, mult_fct, plus_fct, id, Rsqr. 
  rewrite <- f'extr.
  rewrite <- fe0 in f''posR.
  inversion_clear interval.
  assert (- B / (2 * A) < t2) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_increasing_interv (-B/(2*A)) (t2) f' f'derivable).
  assumption. assumption.
  split. right. reflexivity. left. assumption.
  split. left. assumption. left. assumption. assumption.

  assert (forall q r,  (-B/(2*A)) <= q <= t2 ->
                       (-B/(2*A)) <= r <= t2 -> q < r -> f q < f r) as frising.
  intros q s [qintlbnd qintrbnd] [sintlbnd sintrbnd] qlts.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'posR.
  assert (- B / (2 * A) < t2).
  apply (Rle_lt_trans _ q). assumption. apply (Rlt_le_trans _ s). assumption. assumption.
  apply (derive_increasing_interv (-B/(2*A)) (t2) f fderivable).
  assumption. assumption.
  split; assumption. split; assumption. assumption.

  assert (forall q, t1 < q < - B / (2 * A) -> 0 < f'' q)
    as f''posL. intros.
  unfold f'', fct_cte, mult_fct, plus_fct, id, Rsqr.
  fourier.

  assert (forall q,  t1 < q < (-B/(2*A)) -> f' q < 0 )
    as f'negL. intros q interval.
  rewrite <- f'extr.
  rewrite <- fe0 in f''posL.
  inversion_clear interval.
  assert (t1 < - B / (2 * A)) as order.
  apply (Rlt_trans _ q); assumption.
  apply (derive_increasing_interv t1
                                       (-B/(2*A)) f' f'derivable order f''posL).
  split. left. assumption. left. assumption.
  split. left. assumption. right. reflexivity. assumption.
  
  assert (forall q r,  t1 <= q <= (-B/(2*A)) ->
                       t1 <= r <= (-B/(2*A)) ->
                       q < r -> f r < f q) as ffalling. intros q s qinterval rinterval qltr.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  rewrite <- fe in f'negL.
  inversion_clear qinterval. inversion_clear rinterval.
  apply (derive_decreasing_interv t1
                                  (-B/(2*A)) f fderivable).
  apply (Rle_lt_trans _ q). assumption.
  apply (Rlt_le_trans _ s). assumption. assumption.
  assumption. split; assumption. split; assumption. assumption.

  cut (0 <= f t). intros.
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr in H0.
  assert (t^2 = (t*t)). field. rewrite H1. assumption.

  destruct (Rle_dec t1 (- B / (2 * A))).
  destruct (Rle_dec (- B / (2 * A)) t2).
  
  injection sfty; clear sfty; intro sfty.
  assert (0 = f (-B/(2*A))).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C.
  rewrite <- sfty.
  field.
  intro aeq0. rewrite aeq0 in r. fourier.
  clear sfty. rename H0 into sfty.
  rewrite sfty.

  inversion_clear H.
  generalize (Rle_dec (- B / (2 * A)) t) as cpos; intro.
  inversion_clear cpos as [cposlet | cposgtt].
  inversion cposlet. left.
  apply frising.
  split. right. reflexivity. assumption.
  split. left. assumption. assumption. assumption.
  rewrite H. right. reflexivity.
  assert (t < - B / (2*A)) as midgtt.
  apply Rnot_le_lt. assumption. clear cposgtt.
  left.
  apply ffalling.
  split. assumption. left. assumption.
  split. left. apply (Rle_lt_trans _ t). assumption. assumption.
  right. reflexivity. assumption.

  assert (t2 < - B / (2 * A)) as midgtt2.
  apply Rnot_le_lt. assumption. clear n.
  injection sfty; clear sfty; intro sfty.
  assert (0 = f t2).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C.
  rewrite <- sfty.
  field.
  clear sfty. rename H0 into sfty.
  rewrite sfty. 
  inversion_clear H. inversion_clear H1. left.
  apply ffalling.
  split. assumption. apply (Rle_trans _ t2). left. assumption. left. assumption.
  split. left. apply (Rle_lt_trans _ t). assumption. assumption. left. assumption. assumption.
  rewrite H. right. reflexivity.

  assert (- B / (2 * A) < t1) as midltt1.
  apply Rnot_le_lt. assumption. clear n.
  injection sfty; clear sfty; intro sfty.
  assert (0 = f t1).
  unfold f, fct_cte, mult_fct, plus_fct, id, Rsqr.
  unfold C.
  rewrite <- sfty.
  field.
  clear sfty. rename H0 into sfty.
  rewrite sfty. 
  inversion_clear H. inversion_clear H0. left.
  apply frising.
  split. left. assumption. apply (Rle_trans _ t). left. assumption. assumption.
  split. left. apply (Rle_lt_trans _ t1). left. assumption. assumption. assumption. assumption.
  rewrite H. right. reflexivity.
Qed.

(* Recursive Extraction interv_vert_safe. *)


Theorem interv_safe_tight_bound : forall coeffU coeffL t1 t2 vmd,
    (interv_vert_safe coeffU coeffL t1 t2) = Some vmd ->
    exists t, t1 <= t <= t2 /\ J coeffU t - J coeffL t = vmd.
Proof.
  intros. rename H into H0.
  assert (0=0) as H. reflexivity.
  unfold interv_vert_safe in H0.
  destruct (Rle_dec t1 t2).
  destruct (total_order_T (a coeffU - a coeffL) 0).
  destruct s.
  
  destruct (Rlt_dec (- (b coeffU - b coeffL) / (2 * (a coeffU - a coeffL))) ((t1 + t2) / 2)).
  injection H0. intros. clear H0. exists t2. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. assumption. right. reflexivity. field.
  injection H0. intros. clear H0. exists t1. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. right. reflexivity. assumption. field.
  destruct (Rle_dec (b coeffU - b coeffL) 0).
  injection H0. intros. clear H0. exists t2. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. assumption. right. reflexivity. field.
  injection H0. intros. clear H0. exists t1. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. right. reflexivity. assumption. field.

  destruct (Rle_dec t1 (- (b coeffU - b coeffL) / (2 * (a coeffU - a coeffL))));
  destruct (Rle_dec (- (b coeffU - b coeffL) / (2 * (a coeffU - a coeffL))) t2).
  injection H0. intros. clear H0. exists (- (b coeffU - b coeffL) / (2 * (a coeffU - a coeffL))). intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. assumption. assumption. field.
  intro. rewrite H0 in r0. eapply Rgt_irrefl. apply r0.
  injection H0. intros. clear H0. exists t2. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. assumption. right. reflexivity. field.
  injection H0. intros. clear H0. exists t1. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. right. reflexivity. assumption. field.
  injection H0. intros. clear H0. exists t1. intros.
  rewrite <- H1. unfold Poly. unfold J. simpl.
  split. split. right. reflexivity. assumption. field.
  inversion H0.
Qed.


Theorem safe_subinterval : forall coeffU coeffL t1 t2 s1 s2 vmdt vmds,
    t1 <= t2 ->
    t1 <= s1 ->
    s1 <= s2 ->
    s2 <= t2 ->
    (interv_vert_safe coeffU coeffL t1 t2) = Some vmdt ->
    (interv_vert_safe coeffU coeffL s1 s2) = Some vmds ->
    vmdt <= vmds.
Proof.
  intros.
  assert (forall s, s1 <= s <= s2 ->
                    vmds <= J coeffU s - J coeffL s).
  intros. eapply safely_separated_second_order_polynomial_interval. apply H5. assumption.
  assert (forall t, t1 <= t <= t2 ->
                    vmdt <= J coeffU t - J coeffL t).
  intros. eapply safely_separated_second_order_polynomial_interval. apply H6. assumption.
  generalize (interv_safe_tight_bound _ _ _ _ _ H3). intros.
  generalize (interv_safe_tight_bound _ _ _ _ _ H4). intros.

  set (f := (fun x => J coeffU x - J coeffL x)).
  change (forall t : R, t1 <= t <= t2 -> vmdt <= f t) in H6.
  change (forall s : R, s1 <= s <= s2 -> vmds <= f s) in H5.
  change (exists t : R, t1 <= t <= t2 /\ f t = vmdt) in H7.
  change (exists t : R, s1 <= t <= s2 /\ f t = vmds) in H8.
  clear H3 H4.
  inversion_clear H7. inversion_clear H3.
  inversion_clear H8. inversion_clear H3.
  apply Rnot_lt_le. intro.
  assert (t1 <= x0 <= t2).
  split. eapply Rle_trans. apply H0. inversion H8. assumption.
  eapply Rle_trans. inversion H8. apply H11. assumption.
  generalize (H6 x0 H10).
  apply Rlt_not_le. rewrite H9.
  assumption.
Qed.



(*

The function 'K' defines a trajectory (altitude over time) that
represents the edge of an envelope of future possibilities.

'v' is our initial vertical velocity at t=0

'vt' is a minimum target vertical velocity, we want to bring our
vertical velocity to be above that value

'a' is the minimum acceleration necessary with which we approach the
target vertical velocity vt before we have reached it

Assume a>0 and v<vt. Before our velocity reaches vt, our acceleration
must be in the range [a,amax]. After it reaches vt, our acceleration
must be in the range [amin,amax] as long as v>vt.

The lowermost possible trajectory according to these rules is a
piecewise function that follows a parabolic path, accelerates at 'a'
until it reaches a target velocity 'vt', and then stays at that
velocity.

The initial altitude at t=0 is z, and v is the initial velocity (and
linear coefficient for the parabolic path). The beginning of our
trajectory is given by:

K(t) = a/2*t^2 + v*t + z when 0 <= t < tt,
where tt is the transition time between parabolic and linear behavior

When is the transition time? It happens when the velocity is vt. We
can take the derivative of the position, set it to vt, and solve for
tt:

K'(t) = a*t + v = vt at [tt = (vt-v)/a]

This means at t=tt, our vehicle reaches a vertical velocity of vt, and
an altitude given by:

K(tt) = a/2 tt^2 + v*tt + z
      = a/2*(vt-v)^2/a^2 + v (vt-v)/a + z
      = (vt^2+v^2 - 2vt*v)/(2a) + 2v(vt-v)/(2a) + z
      = (vt^2+v^2 - 2vt*v + 2v*vt - 2*v^2)/(2a) + z
      = (vt^2 - v^2)/(2a) + z

so the linear part of the equation is:

  vt (t-tt) + K(tt)
= vt (t-(vt-v)/a) + (vt^2 - v^2)/2a + z 
= vt t + 2*(- vt^2 + vt v)/2a + (vt^2 - v^2)/2a + z 
= vt t + (- vt^2 + 2 vt v - v^2)/2a + z
= vt t - ( vt^2 - 2 vt v + v^2)/2a + z 
= vt t - (vt - v)^2/2a + z 
= vt t - tt*(vt-v)/2 + z 

So now we can complete the function we started writing:

K(t) = a/2*t^2 + v*t + z when 0 <= t < tt,
       vt*t - (vt-v)/2*tt + z when tt <= t

If a>0 (as before) but instead v>=vt, we can find a lower envelope by
assuming at t=0, v=vt, and there is no acceleration in the lower edge
of the envelope. We can do this by using tt=max(0,(vt-v)/a) with the
equations above.

The equations are identical when a<0, except we will now accelerate
downwards towards vt only when we are above it (i.e. v>vt). When a<0
and v<=vt, we make the same modification to tt we did before, and 
everything still works.

*)

(*

This function takes two accelerations aa (acceleration above) and ab
(acceleration below), an initial velocity 'v', a target velocity 'vt',
and an initial altitude 'z' and produces the piecewise trajectory that
has the vehicle accelerating towards the target velocity from
whichever direction is appropriate, and then staying at that
velocity. It is in a sense the edge of an envelope describing the most
extreme possibility.

For example:

If the vt is a lower bound, and the vehicle must accelerate such that
it's vertical velocity is greater than vt. In this case, the
acceleration 'ab' represents the minimum upward (positive)
acceleration allowable when you are below vt, and 'aa' represents the
maximum downward (negative) acceleration when you are already above
vt, a.k.a. amin.

If the vt is an upper bound, and the vehicle must accelerate such that
it's vertical velocity is less than than vt. In this case, the
acceleration 'ab' represents the maximum upward (positive)
acceleration allowable when you are already below vt, a.k.a amax, and
'aa' represents the minimum downward (negative) acceleration when you
are above vt.

The function K has no information on whether vt is an upper or lower
bound, or whether the accelerations are minimums or maximums for which
situation. The equations work for creating the edge of an envelope in
both upper and lower cases, if given the proper accelerations.

*)

Definition K aa ab v vt z t :=
  let a := match Rle_dec vt v with
           | left _ => (* vt<=v *) aa
           | right _ => (* vt>v *) ab
           end in
  let Q := mkcoeff (a/2) v z in
  let tl := (vt-v)/a in
  let L := mkcoeff 0 vt (z - tl*(vt-v)/2) in
  match Rle_dec t tl with
  | left _ => (J Q t) (*le*)
  | right _ => (J L t) (*gt *)
  end.

Open Scope list_scope.

Fixpoint Rlistmin (lst : list (option R)) {struct lst} :=
  match lst with
  | List.nil => None
  | List.cons (Some head) rest =>
    match Rlistmin rest with
    | None => Some head
    | Some head2 => Some (Rmin head head2)
    end
  | List.cons None rest => Rlistmin rest
  end.

Theorem Rlistmin_nomin : forall i lst,
    Rlistmin lst = None -> nth i lst None = None.
Proof.
  induction i; induction lst. intros.
  simpl. reflexivity.
  intros. destruct a0. exfalso. simpl in H.
  destruct (Rlistmin lst); discriminate.
  simpl. reflexivity.
  intros.
  simpl. reflexivity.
  intros.
  simpl in H. destruct a0.
  case_eq (Rlistmin lst). intros. rewrite H0 in H. discriminate.
  intros. rewrite H0 in H. discriminate.
  generalize (IHi _ H). intros.
  simpl. assumption.
Qed.

Theorem Rlistmin_min_element : forall lst i v , 
    Rlistmin lst = Some v ->
    nth_ok i lst None = true ->
    (exists v', nth i lst None = Some v' /\ v <= v') \/ nth i lst None = None.
Proof.
  induction lst.
  intros. inversion H.
  intros.
  destruct i.
  destruct a0.
  Focus 2.
  right. simpl. reflexivity.
  left. exists r. split. simpl. reflexivity. clear H0.
  simpl in H.
  destruct (Rlistmin lst).
  unfold Rmin in H.
  destruct (Rle_dec r r0).
  injection H. intros. subst. right. reflexivity.
  injection H. intros. subst. left. apply Rnot_le_lt. assumption.
  injection H. intros. subst. right. reflexivity.

  assert (nth_ok i lst None = true). simpl in H0. assumption.
  case_eq (Rlistmin lst). intros.
  destruct a0. simpl in H. rewrite H2 in H.
  inversion H. clear H.
  generalize (IHlst i r H2 H1). intros.
  inversion_clear H. inversion_clear H3. inversion_clear H.
  left. exists x. split.
  simpl. assumption.
  unfold Rmin. destruct (Rle_dec r0 r). eapply Rle_trans. apply r1. assumption. assumption.
  right. simpl. assumption.
  simpl in H.
  rewrite H in H2.
  inversion H2. clear H2. subst.
  generalize (IHlst i r H H1). intros.
  inversion_clear H2. inversion_clear H3. inversion_clear H2.
  left. exists x. split.
  simpl. assumption. assumption.
  right. simpl. assumption.
  intros. right. simpl. clear IHlst H H0 a0 v.

  apply Rlistmin_nomin. assumption.
Qed.

Theorem Rlistmin_exists_min_element : forall lst v, 
    Rlistmin lst = Some v ->
    exists i, nth_ok i lst None = true /\ nth i lst None = Some v.
Proof.
  induction lst.
  intros. inversion H.
  intros.
  destruct a0.
  simpl in H.
  case_eq (Rlistmin lst).
  intros. rewrite H0 in *.
  injection H. intros. clear H.
  generalize (IHlst r0 (eq_refl (Some r0))).
  intros.
  inversion_clear H.
  inversion_clear H2.
  unfold Rmin in H1.
  destruct (Rle_dec r r0).
  subst.
  exists O. simpl. split; reflexivity.
  subst.
  exists (S x). split; assumption.

  intros. rewrite H0 in *.
  injection H. intros. clear H.
  subst.
  exists 0%nat.
  split; simpl; reflexivity.
  simpl in H.
  generalize (IHlst v H). intros.
  inversion_clear H0.
  inversion_clear H1.
  exists (S x).
  split. simpl. assumption. simpl. assumption.
Qed.

(*
Eval compute in  (Rlistmin [Some 1; Some 4; None; Some 5]).
 *)

Definition vert_safe_above
           aa1 ab1 v1 vt1 z1 (* 1 vehicle is above *)
           aa2 ab2 v2 vt2 z2 (* 2 vehicle is below *)
           tb te : option R := 
  (* assume: aa1 < 0 -> ab1 > 0 -> aa2 < 0 -> ab2 > 0 *)
  let a1 := (match Rle_dec vt1 v1 with
             | left _ => aa1
             | right _ => ab1
             end) in
  let a2 := (match Rle_dec vt2 v2 with
             | left _ => aa2
             | right _ => ab2
             end) in
  let Q1 := mkcoeff (a1/2) v1 z1 in
  let Q2 := mkcoeff (a2/2) v2 z2 in
  let t1 := (vt1-v1)/a1 in
  let t2 := (vt2-v2)/a2 in
  let L1 := mkcoeff 0 vt1 (z1 -t1*(vt1-v1)/2) in
  let L2 := mkcoeff 0 vt2 (z2 -t2*(vt2-v2)/2) in
  Rlistmin [(interv_vert_safe Q1 Q2 tb (Rmin te (Rmin t1 t2)));
              (interv_vert_safe L1 L2 (Rmax tb (Rmax t1 t2)) te);
              (match Rlt_dec t2 t1 with
               | left _ => (interv_vert_safe Q1 L2 (Rmax tb (Rmin t1 t2))
                                             (Rmin te (Rmax t1 t2)))
               | _ => None
               end);
              (match Rlt_dec t1 t2 with
               | left _ => (interv_vert_safe L1 Q2 (Rmax tb (Rmin t1 t2))
                                             (Rmin te (Rmax t1 t2)))
               | _ => None
               end)].


  Ltac rle_decide a b :=
    match goal with
    | [ineq : a <= b |- _ ] =>
      case_eq (Rle_dec a b);
      [intros p q; try rewrite q in *; clear p q |
       intros p q; exfalso; apply p; apply ineq]
    | [ineq : ~ a <= b |- _ ] => 
      case_eq (Rle_dec a b);
      [intros p q; exfalso; apply ineq; apply p |
       intros p q; try rewrite q in *; clear p q]
    end.


Theorem safely_separated_trajectory_interval_above:
  forall aa1 ab1 v1 vt1 z1 (* 1 above *)
         aa2 ab2 v2 vt2 z2 (* 2 below *)
         vmd tb te,
    vert_safe_above aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 tb te = Some vmd ->
    (forall t, tb <= t <= te ->
               vmd <= K aa1 ab1 v1 vt1 z1 t - K aa2 ab2 v2 vt2 z2 t).
Proof.
  intros aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 vmd tb te.
  intros vsa t tbletlete.

  generalize (Rle_dec vt1 v1) as vt1relv1.
  generalize (Rle_dec vt2 v2) as vt2relv2.
  intros.
  inversion_clear vt1relv1 as [vt1lev1 | vt1lev1];
    inversion_clear vt2relv2 as [vt2lev2 | vt2lev2];
    [
      set (t1 := (vt1 - v1)/aa1) in *; set (t2 := (vt2 - v2)/aa2) in * |
      set (t1 := (vt1 - v1)/aa1) in *; set (t2 := (vt2 - v2)/ab2) in * |
      set (t1 := (vt1 - v1)/ab1) in *; set (t2 := (vt2 - v2)/aa2) in * |
      set (t1 := (vt1 - v1)/ab1) in *; set (t2 := (vt2 - v2)/ab2) in *
    ]; 
  
  (generalize (Rle_dec t t1) as trelt1;
  generalize (Rle_dec t t2) as trelt2;
  intros;
  
  inversion_clear trelt1 as [tlet1 | tgtt1]; [


  inversion_clear trelt2 as [tlet2 | tgtt2]; [

  inversion tbletlete as [tblet tlete];
  assert (t <= (Rmin te (Rmin t1 t2))) as QQboundary;[
  unfold Rmin;
  destruct (Rle_dec t1 t2); [
    destruct (Rle_dec te t1); assumption |
    destruct (Rle_dec te t2); assumption] |idtac];
 
  generalize (Rlistmin_min_element _ 0 _ vsa (eq_refl true)) as cadist;
  intros; unfold nth in cadist; simpl;
  inversion_clear cadist as [[v' [ivs vmdlev']] | novmd]; [

  unfold K;
  rle_decide vt1 v1;
  rle_decide vt2 v2;
  (change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t))
  );

  rle_decide t t2;
  rle_decide t t1;
  (change (interv_vert_safe {| a := aa1 / 2; b := v1; c := z1 |}
          {| a := aa2 / 2; b := v2; c := z2 |} tb
          (Rmin te (Rmin t1 t2)) =  Some v') in ivs ||
   change (interv_vert_safe {| a := aa1 / 2; b := v1; c := z1 |}
          {| a := ab2 / 2; b := v2; c := z2 |} tb
          (Rmin te (Rmin t1 t2)) = Some v') in ivs ||
  change (interv_vert_safe {| a := ab1 / 2; b := v1; c := z1 |}
          {| a := aa2 / 2; b := v2; c := z2 |} tb
          (Rmin te (Rmin t1 t2)) =  Some v') in ivs ||
   change (interv_vert_safe {| a := ab1 / 2; b := v1; c := z1 |}
          {| a := ab2 / 2; b := v2; c := z2 |} tb
          (Rmin te (Rmin t1 t2)) = Some v') in ivs);

  eapply Rle_trans; [
  apply vmdlev'|
  eapply safely_separated_second_order_polynomial_interval; [
  split; [eapply tblet | eapply QQboundary] |
  assumption]]
  |
  generalize (ivs_interval_empty _ _ _ _ novmd) as tbgt; intros;
  rle_decide vt1 v1;
  rle_decide vt2 v2;
  exfalso;
  change (tb > Rmin te (Rmin t1 t2)) in tbgt;
  assert (tb <= Rmin te (Rmin t1 t2)); [
    fourier |
    eapply Rgt_not_le ; [ eapply tbgt | assumption]]]
  |

  (******************)
  generalize (Rlistmin_min_element _ 2 _ vsa (eq_refl true)) as cadist;
  intros; unfold nth in cadist; simpl;
  generalize (Rnot_le_lt _ _ tgtt2) as t2ltt; intros;

  inversion_clear cadist as [[v' [ivs vmdlev']] | novmd]; [

  unfold K;
  rle_decide vt2 v2;
  rle_decide vt1 v1;
  assert (t2 < t1) as t2ltt1; [
  eapply Rlt_le_trans; [ eapply t2ltt | assumption] | idtac];
  
  (change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)));

    (change ((if Rlt_dec t2 t1
         then
          interv_vert_safe {| a := aa1 / 2; b := v1; c := z1 |}
            {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |}
            (Rmax tb (Rmin t1 t2))
            (Rmin te (Rmax t1 t2))
           else None) = Some v') in ivs ||
    change ((if Rlt_dec t2 t1
         then
          interv_vert_safe {| a := ab1 / 2; b := v1; c := z1 |}
            {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |}
            (Rmax tb (Rmin t1 t2))
            (Rmin te (Rmax t1 t2))
         else None) = Some v') in ivs);
  rle_decide t t1;
  rle_decide t t2;
  case_eq (Rlt_dec t2 t1); intros; [

  rewrite H in *; clear r H;

  assert (~ t1 <= t2) as t1nget2; [
  apply Rlt_not_le; assumption | idtac];
  
  assert ((Rmax tb (Rmin t1 t2)) <= t <= (Rmin te (Rmax t1 t2))) as trange; [
  unfold Rmax, Rmin; inversion_clear tbletlete as [tblet tlete];
    rle_decide t1 t2;
  split; [destruct (Rle_dec tb t2); fourier|
  destruct (Rle_dec te t1); fourier] | idtac];

  generalize (safely_separated_second_order_polynomial_interval _ _ _ _ _ _ trange ivs);
  intros; eapply Rle_trans; [apply vmdlev' | assumption]
  |
  intros; exfalso; apply n; assumption]
  |

  rle_decide vt2 v2;
  rle_decide vt1 v1;
  (change ((if Rlt_dec t2 t1
            then
              interv_vert_safe {| a := aa1 / 2; b := v1; c := z1 |}
                               {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |}
                               (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))
            else None) = None) in novmd ||
   change ((if Rlt_dec t2 t1
            then
              interv_vert_safe {| a := ab1 / 2; b := v1; c := z1 |}
                               {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |}
                               (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))
            else None) = None) in novmd);

    assert (t2 < t1) as t2ltt1; [
      eapply Rlt_le_trans;
      [eapply t2ltt | assumption] | idtac];
    
    case_eq (Rlt_dec t2 t1); intros; [

  rewrite H in *;
  clear r H;

  generalize (ivs_interval_empty _ _ _ _ novmd) as tbgt;
  intros; exfalso;
  unfold Rmin,Rmax in tbgt;
  assert (~ t1 <= t2) as t1nlet2; [ apply Rlt_not_le; assumption| idtac];
  rle_decide t1 t2; clear t1nlet2; clear tgtt2 novmd;
  inversion_clear tbletlete as [tblet tlete];
  apply Rgt_lt in tbgt; (* swap assumption *)
  destruct (Rle_dec tb t2); destruct (Rle_dec te t1); fourier
  |
  exfalso; apply n; assumption]]]
  |
  (******************)

  inversion_clear trelt2 as [tlet2 | tnlet2]; [

  generalize (Rlistmin_min_element _ 3 _ vsa (eq_refl true)) as cadist;
  intros; unfold nth in cadist; simpl;

  inversion_clear cadist as [[v' [ivs vmdlev']] | novmd]; [


  unfold K;
  rle_decide vt2 v2;
  rle_decide vt1 v1;
  assert (t1 < t2) as t1ltt2; [
    eapply Rlt_le_trans;
    [apply Rnot_le_lt; apply tgtt1 | assumption] | idtac];
  
  (change (vmd <=
          (if Rle_dec t t1
           then J {| a := aa1 / 2; b := v1; c := z1 |} t
           else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
          (if Rle_dec t t2
           then J {| a := aa2 / 2; b := v2; c := z2 |} t
           else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
          (if Rle_dec t t1
           then J {| a := aa1 / 2; b := v1; c := z1 |} t
           else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
          (if Rle_dec t t2
           then J {| a := ab2 / 2; b := v2; c := z2 |} t
           else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
          (if Rle_dec t t1
           then J {| a := ab1 / 2; b := v1; c := z1 |} t
           else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
          (if Rle_dec t t2
           then J {| a := aa2 / 2; b := v2; c := z2 |} t
           else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
          (if Rle_dec t t1
           then J {| a := ab1 / 2; b := v1; c := z1 |} t
           else J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
          (if Rle_dec t t2
           then J {| a := ab2 / 2; b := v2; c := z2 |} t
           else J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)));

  (change ((if Rlt_dec t1 t2
         then
          interv_vert_safe {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |}
            {| a := aa2 / 2; b := v2; c := z2 |}
            (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2)) else None) = Some v') in ivs ||
   change ((if Rlt_dec t1 t2
         then
          interv_vert_safe {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |}
            {| a := ab2 / 2; b := v2; c := z2 |}
            (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2)) else None) = Some v') in ivs);
  rle_decide t t1;
  rle_decide t t2;

  case_eq (Rlt_dec t1 t2); intros; [
  rewrite H in *; clear r H;

(*  assert (~ t2 <= t1) as t2nget1. 
  apply Rlt_not_le. assumption. *)

  assert (t1 <= t2) as t1get2; [left; assumption | idtac];
  
  assert ((Rmax tb (Rmin t1 t2)) <= t <= (Rmin te (Rmax t1 t2))) as trange; [
  unfold Rmax, Rmin; split ; [
    rle_decide t1 t2;
    destruct (Rle_dec tb t1); [
      left; apply Rnot_le_lt in tgtt1; assumption |
      inversion_clear tbletlete as [tblet tlete]; assumption] |
    inversion_clear tbletlete as [tblet tlete];
    rle_decide t1 t2; destruct (Rle_dec te t2); assumption] |
  idtac];

  generalize (safely_separated_second_order_polynomial_interval _ _ _ _ _ _ trange ivs);
  intros; 
  eapply Rle_trans;
  try apply vmdlev'; assumption |

  exfalso; apply n; assumption] |

  rle_decide vt2 v2;
  rle_decide vt1 v1;
  (change ((if Rlt_dec t1 t2
           then
            interv_vert_safe {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |}
              {| a := aa2 / 2; b := v2; c := z2 |}
              (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))
            else None) = None) in novmd ||
   change ((if Rlt_dec t1 t2
           then
            interv_vert_safe {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |}
              {| a := ab2 / 2; b := v2; c := z2 |}
              (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))
            else None) = None) in novmd
  );
  assert (t1 < t2) as t1ltt2; [ apply Rnot_le_lt in tgtt1;
    eapply Rlt_le_trans; try eapply tgtt1; assumption | idtac];
  case_eq (Rlt_dec t1 t2); intros; [
    rewrite H in *; clear r H;
    generalize (ivs_interval_empty _ _ _ _ novmd) as tbgt;
    intros; exfalso;
    unfold Rmin,Rmax in tbgt;
    assert (t1 <= t2) as t1let2; try (left; assumption);
    rle_decide t1 t2; clear t1let2; clear novmd;
    inversion_clear tbletlete as [tblet tlete];
    apply Rnot_le_lt in tgtt1; (* swap assumption *)
    destruct (Rle_dec tb t1); destruct (Rle_dec te t2); fourier |
    exfalso; apply n; assumption]] |
  (******************)

  generalize (Rlistmin_min_element _ 1 _ vsa (eq_refl true)) as cadist;
  intros; unfold nth in cadist; simpl;
  inversion_clear cadist as [[v' [ivs vmdlev']] | novmd]; [

  unfold K;
  rle_decide vt1 v1;
  rle_decide vt2 v2;
  (change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := aa1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := aa2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)) ||
   change (vmd <=
           (if Rle_dec t t1
            then J {| a := ab1 / 2; b := v1; c := z1 |} t
            else
              J {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |} t) -
           (if Rle_dec t t2
            then J {| a := ab2 / 2; b := v2; c := z2 |} t
            else
              J {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |} t)))
  ;
  
  rle_decide t t2;
  rle_decide t t1;
   change (interv_vert_safe {| a := 0; b := vt1; c := z1 - t1 * (vt1 - v1) / 2 |}
          {| a := 0; b := vt2; c := z2 - t2 * (vt2 - v2) / 2 |}
          (Rmax tb (Rmax t1 t2)) te = Some v') in ivs;

  inversion_clear tbletlete as [tblet tlete];

  assert ((Rmax tb (Rmax t1 t2)) <= t) as LLboundary; [
  apply Rnot_le_lt in tgtt1;
  apply Rnot_le_lt in tnlet2;
  unfold Rmax;
  destruct (Rle_dec t1 t2);[ destruct (Rle_dec tb t2); fourier |
  destruct (Rle_dec tb t1); fourier] | idtac];

  eapply Rle_trans; [apply vmdlev' | 
  eapply safely_separated_second_order_polynomial_interval; [
  split; [apply LLboundary | apply tlete] | assumption]] |

  generalize (ivs_interval_empty _ _ _ _ novmd) as tbgt;
  intros;
  rle_decide vt1 v1;
  rle_decide vt2 v2;
  exfalso;
  change (te < Rmax tb (Rmax t1 t2)) in tbgt;
  apply Rnot_le_lt in tgtt1;
  apply Rnot_le_lt in tnlet2;

  assert (Rmax tb (Rmax t1 t2) <= te) as tegeRmax;
    [inversion_clear tbletlete as [tblet tlete];
  unfold Rmin, Rmax;

  destruct (Rle_dec t1 t2);
    [destruct (Rle_dec tb t2); fourier |
     destruct (Rle_dec tb t1); fourier] | idtac];

  eapply Rgt_not_le; [eapply tbgt | assumption]]]]).
Qed.


Ltac assume n := generalize n; intro.


(* Collects geometric and dynamic information about aircraft motion. *)

(* For this definition, we are continuous during the interior each
maneuver, but the point at the beginning of each maneuver is not
necessarily continuous on either side. We need to create a definition
for continuity "from the right" which shouldn't be to hard *)
(* todo : derivability -> continuity, we can remove this hypothesis *)
Inductive Path (z v a :R->R) :=
| pth_intro :
    forall (dvp : derivable z) (contz: continuity z)
           (dpeqv : derive z dvp = v)
           (dvv : derivable v) (contv: continuity v)
           (dveqa : derive v dvv = a)
           (conta: continuity a), Path z v a.

Record Objective  :=
  {
    vmax:R; vmin:R; aa:R; amax:R; amin:R; ab:R;
    vminlevmax : vmin<=vmax;
    aminleaa : amin <= aa;
    aalt0 : aa < 0;
    zltab : 0 < ab;
    ableamax : ab <= amax
  }.


(* The pilot follows the maneuver during the interval [t1,t2] *)
Inductive Maneuver {z v a} t1 t2 (P: Path z v a) (B:Objective) :=
| mnv_intro : forall 
           (interval : t1 <= t2)
           (vabove : forall t, t1<=t<t2 -> (vmax B) < v t -> (amin B) <= a t <= (aa B))
           (vatupper : forall t, t1<=t<t2 -> v t = (vmax B) -> (amin B) <= a t <= 0)
           (vwithin: forall t, t1<=t<t2 -> (vmin B) < v t < (vmax B)  -> (amin B) <= a t <= (amax B))
           (vatlower : forall t, t1<=t<t2 -> v t = (vmin B) -> 0 <= a t <= (amax B))
           (vbelow : forall t, t1<=t<t2 -> v t < (vmin B) -> (ab B) <= a t <= (amax B)),
                Maneuver t1 t2 P B.

Inductive TailManeuver {z v a} t1 (P: Path z v a) (B:Objective) :=
| tmnv_intro : forall
           (mnv : forall t2, Maneuver t1 t2 P B),
                TailManeuver t1 P B.

(*
The 'ua' ltac is short for "unpack assumptions."

Assumes type starts with the following:
forall t1 t2 z v a (P: Path z v a) B (M: Maneuver t1 t2 P B)...
*)
Ltac ua :=
  intros t1 t2 z v a P B M;
  inversion P;
  inversion M as [interval 
           vabove 
           vatupper 
           vwithin
           vatlower 
           vbelow];
  case_eq B;
  intros vmax vmin aa amax amin ab vminlevmax
         aminleaa aalt0 zltab ableamax Bdef;
  rewrite Bdef in vabove, vatupper, vwithin, vatlower, vbelow (*, M*);
  simpl in *(*; clear Bdef*).

Lemma pilot_model_maintains_lower_bound :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> (vmin B) <= v x ->
            forall y, t1 <= y < t2 -> x < y -> (vmin B) <= v y.
Proof.
  ua.
  intros x [t1lex xltt2] vminltvx y [t1ley yltt2] xlty.

  apply Rnot_lt_le.
  intro.

  set (C := (vmin + v y)/2).
  assert (C < vmin) as Cltvmin. unfold C;
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setl (vmin + v y); Radd (-vmin); setr vmin; setl (v y); assumption.

  assert (v y < C) as vyltC. unfold C.
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setr (vmin + v y); Radd (-v y); setr vmin; setl (v y); assumption.
  
  set (f := (fun x => v x - C)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (f y < 0) as fyltz. unfold f.
  Radd C.
  setl (v y).
  setr C. assumption.
  assert (0 < f x) as zltfx. unfold f. Radd C.
  setr (v x). setl C. fourier.
  assert (f x >= 0) as zlefx. left. assumption.
  generalize (last_leg_drop f x y contf xlty zlefx fyltz) as llr. intros.
  inversion_clear llr as [p [[xltp plty] [flhs below]]].
  assert (v p = C) as lhs.
  Radd (-C). setl (v p - C). setr 0. assumption.

  generalize (MVT_cor1 v p y dvv plty) as mvt. intros.
  inversion_clear mvt as [c [derivvc [pltc clty]]].
  assert (v y - v p < 0) as vymvplt0.
  rewrite lhs.
  Radd C.
  setr C.
  setl (v y).
  assumption.
  
  rewrite derivvc in vymvplt0.
  assert (0 < y-p).
  Radd p.
  setl p.
  setr y. assumption.
  assert (derive_pt v c (dvv c) < 0).
  apply (Rmult_lt_reg_r (y-p)); try assumption.
  setr 0. assumption.

  assert (p < c < y).
  split. assumption.
  assumption.
  generalize (below c H2). intros.

  assert (v c < vmin) as vcltvmin. 
  apply (Rlt_trans (v c) C vmin).
  Radd (-C). setr 0. setl (v c - C). assumption.
  assumption.

  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vbelow c cinterval vcltvmin) as accel. intros. clear below.
  inversion_clear accel as [ableac acleamax].
  rewrite <- dveqa in ableac.
  unfold derive in ableac.
  assert (0 < derive_pt v c (dvv c)).
  assume zltab. fourier.
  clear ableac acleamax.
  eapply Rlt_asym.
  apply H4. apply H1.
Qed.

Lemma pilot_model_maintains_upper_bound:
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x <= vmax B ->
            forall y, t1 <= y < t2 -> x < y -> v y <= vmax B.
Proof.
  ua.

  intros x [t1lex xltt2] vxlevmax y [t1ley yltt2] xlty.

  apply Rnot_lt_le.
  intro.

  set (C := (vmax + v y)/2).
  assert (vmax < C) as vmaxltC. unfold C;
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setr (vmax + v y); Radd (-vmax); setl vmax; setr (v y); assumption.

  assert (C < v y) as Cltvy. unfold C.
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setl (vmax + v y); Radd (-v y); setl vmax; setr (v y); assumption.
  
  set (f := (fun x => v x - C)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (0 < f y) as zltfy. unfold f.
  Radd C.
  setr (v y).
  setl C. assumption.
  assert (f x < 0) as fxltz. unfold f. Radd C.
  setl (v x). setr C. fourier.
  assert (f x <= 0 ) as fxle0. left. assumption.
  generalize (last_leg_rise f x y contf xlty fxle0 zltfy ) as llr. intros.
  inversion_clear llr as [p [[xltp plty] [flhs above]]].
  assert (v p = C) as lhs.
  Radd (-C). setl (v p - C). setr 0. assumption.

  generalize (MVT_cor1 v p y dvv plty) as mvt. intros.
  inversion_clear mvt as [c [derivvc [pltc clty]]].
  assert (0 < v y - v p ) as vymvygt0.
  rewrite lhs.
  Radd C.
  setl C.
  setr (v y).
  assumption.
  
  rewrite derivvc in vymvygt0.
  assert (0 < y-p).
  Radd p.
  setl p.
  setr y. assumption.
  assert (0 < derive_pt v c (dvv c)).
  apply (Rmult_lt_reg_r (y-p)); try assumption.
  setl 0. assumption.

  assert (p < c < y).
  split. assumption.
  assumption.
  generalize (above c H2). intros.

  assert (v c > vmax) as vcgtvmax. apply Rlt_gt.
  apply (Rlt_trans vmax C (v c)). assumption.
  Radd (-C). setl 0. setr (v c - C). assumption.

  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vabove c cinterval vcgtvmax) as accel. intros. clear above.
  inversion_clear accel as [aminleac acleaa].
  rewrite <- dveqa in acleaa.
  unfold derive in acleaa.
  assert (derive_pt v c (dvv c) < 0).
  assume aalt0.  fourier.
  clear acleaa aminleac.
  eapply Rlt_asym.
  apply H4. apply H1.
Qed.

Theorem pilot_model_maintains_vertical_compliance :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
    x, t1 <= x < t2 -> vmin B <= v x <= vmax B ->
       forall y, t1 <= y < t2 -> x < y -> vmin B <= v y <= vmax B.
Proof.
  ua.
  intros.
  inversion_clear H0.
  rewrite Bdef in M.
  split.
  apply (pilot_model_maintains_lower_bound P ({|
         vmax := vmax;
         vmin := vmin;
         aa := aa;
         amax := amax;
         amin := amin;
         ab := ab;
         vminlevmax := vminlevmax;
         aminleaa := aminleaa;
         aalt0 := aalt0;
         zltab := zltab;
         ableamax := ableamax |}) M x H H3 y H1 H2).
  apply (pilot_model_maintains_upper_bound P ({|
         vmax := vmax;
         vmin := vmin;
         aa := aa;
         amax := amax;
         amin := amin;
         ab := ab;
         vminlevmax := vminlevmax;
         aminleaa := aminleaa;
         aalt0 := aalt0;
         zltab := zltab;
         ableamax := ableamax |}) M x H H4 y H1 H2).
Qed.

Lemma pilot_model_accel_below :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> x < y -> v y < vmin B ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj. simpl in pilot_model_maintains_lower_bound_traj.
  intros x xinterval vxlevmin y yinterval xlty.
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].
  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (vl := (fct_cte ab * id)%F).
  assert (continuity vl) as contvl. unfold vl. reg.
  establish_deriv2 vl' (fct_cte ab)%F vl.
  rename H into derivvl.
  rename fe into dvleqvl'.
  assert (continuity vl') as contlv'. unfold vl'. reg.
  rewrite <- dvleqvl' in contlv'.

  set (afun := (mkC1 conta0)).
  set (alfun := (mkC1 contlv')).
  
  generalize (RiemannInt_P32 afun x y) as vintegr. intros.
  generalize (FTC_Riemann afun vintegr) as vintval. intros.

  generalize (RiemannInt_P32 alfun x y) as vlintegr. intros.
  generalize (FTC_Riemann alfun vlintegr) as vlintval. intros.

  simpl in *. unfold vl, fct_cte, id, mult_fct in vlintval.
  rewrite <- vintval.
  setl (ab* y - ab * x).
  rewrite <- vlintval.
  
  apply RiemannInt_P19.
  left. assumption.
  intros. unfold vl, fct_cte, mult_fct, id in dvleqvl'.
  rewrite dvleqvl'.
  rewrite dveqa.
  unfold vl', fct_cte.
  apply vbelow.
  inversion H0. split; fourier.

  assert (v x0 <= v y) as vx0levy.
  apply Rnot_lt_le. intro vyltvx0.
  inversion_clear H0 as [xltx0 x0lty].
  generalize (MVT_cor1 v x0 y dvv x0lty) as mvt. intro.
  inversion_clear mvt as [c [dpvc x0ltclty]].
  inversion_clear x0ltclty as [x0ltc clty].
  assert (v y - v x0 < 0) as vxmvx0lt0. fourier.
  rewrite dpvc in vxmvx0lt0.
  assert (derive_pt v c (dvv c) < 0) as vxmvx0lt00.
  apply (Rmult_lt_reg_r (y-x0)). fourier.
  setr 0. assumption. clear vxmvx0lt0 dpvc.
  generalize (Rtotal_order (v c) vmin) as vcto. intros.
  inversion_clear vcto as [vcltvmin | vcgeqvmin].
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vbelow c cinterval vcltvmin) as acrel. intros.
  inversion_clear acrel as [ableac acleamax].
  change ((derive v dvv) c < 0) in vxmvx0lt00.
  rewrite dveqa in vxmvx0lt00.
  assert (0 <= a c) as zleac. assume zltab. fourier.
  generalize zleac.
  apply Rlt_not_le. assumption.
  assert (vmin <= v c) as vminlevc.
  inversion_clear vcgeqvmin as [vceqvmin | vcgtvmin].
  right. symmetry. assumption. left. assumption. clear vcgeqvmin.
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (pilot_model_maintains_lower_bound_traj c cinterval vminlevc y yinterval clty) as vminlevy. intros.
  apply (Rlt_not_le vmin (v y)). assumption. assumption.
  fourier.
  
Qed.


Lemma pilot_model_accel_above :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
           x, t1 <= x < t2 -> vmax B < v x ->
              forall y, t1 <= y < t2 -> x < y -> vmax B < v y ->
                        v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj. simpl in pilot_model_maintains_upper_bound_traj.
  intros x xinterval vmaxltvx y yinterval xlty vmaxltvy.
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].
  
  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (vl := (fct_cte aa * id)%F).
  assert (continuity vl) as contvl. unfold vl. reg.
  establish_deriv2 vl' (fct_cte aa)%F vl.
  rename H into derivvl.
  rename fe into dvleqvl'.
  assert (continuity vl') as contlv'. unfold vl'. reg.
  rewrite <- dvleqvl' in contlv'.
  set (afun := (mkC1 conta0)).
  set (alfun := (mkC1 contlv')).
  
  generalize (RiemannInt_P32 afun x y) as vintegr. intros.
  generalize (FTC_Riemann afun vintegr) as vintval. intros.

  generalize (RiemannInt_P32 alfun x y) as vlintegr. intros.
  generalize (FTC_Riemann alfun vlintegr) as vlintval. intros.

  simpl in *. unfold vl, fct_cte, id, mult_fct in vlintval.
  rewrite <- vintval.
  setr (aa* y - aa * x).
  rewrite <- vlintval.
  
  apply RiemannInt_P19.
  left. assumption.
  intros. unfold vl, fct_cte, mult_fct, id in dvleqvl'.
  rewrite dvleqvl'.
  rewrite dveqa.
  unfold vl', fct_cte.
  apply vabove. inversion H. split ; fourier.

  assert (v y <= v x0) as vx0levy.
  apply Rnot_lt_le. intro vyltvx0.
  inversion_clear H as [xltx0 x0lty].
  generalize (MVT_cor1 v x0 y dvv x0lty) as mvt. intro.
  inversion_clear mvt as [c [dpvc x0ltclty]].
  inversion_clear x0ltclty as [x0ltc clty].
  assert (0 < v y - v x0) as vxmvx0lt0. fourier.
  rewrite dpvc in vxmvx0lt0.
  assert (0 < derive_pt v c (dvv c) ) as vxmvx0lt00.
  apply (Rmult_lt_reg_r (y-x0)). fourier.
  setl 0. assumption. clear vxmvx0lt0 dpvc.
  generalize (Rtotal_order vmax (v c)) as vcto. intros.
  inversion_clear vcto as [vcltvmin | vcgeqvmin].
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vabove c cinterval vcltvmin) as acrel. intros.
  inversion_clear acrel as [ableac acleamax].
  change (0 < (derive v dvv) c) in vxmvx0lt00.
  rewrite dveqa in vxmvx0lt00.
  assert (0 <= a c) as zleac. fourier. generalize zleac.
  apply Rlt_not_le. assume aalt0. fourier.
  assert (v c <= vmax) as vminlevc.
  inversion_clear vcgeqvmin as [vceqvmin | vcgtvmin].
  right. symmetry. assumption. left. assumption. clear vcgeqvmin.
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (pilot_model_maintains_upper_bound_traj c cinterval vminlevc y yinterval clty) as vminlevy. intros.
  apply (Rlt_not_le (v y) vmax). assumption. assumption.
  fourier.
  
Qed.

Lemma pilot_model_accel_below_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x < (vmin B - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below P B M) as pilot_model_accel_below_traj. intro.
  rewrite Bdef in pilot_model_accel_below_traj. simpl in pilot_model_accel_below_traj.
  intros x xinterval vxltvmxn y yinterval [zltymx ymxlttt].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  generalize (Rtotal_order (v y) vmin) as vyvminto. intros.
  assert (v y < vmin \/ v y >= vmin) as vyvminrel.
  inversion_clear vyvminto as [vyltvmin | [vyeqvmin | vygtvmin]].
  left. assumption. right. right. assumption. right. left. assumption.
  clear vyvminto.
  inversion_clear vyvminrel as [vyltvmin | vygevmin ].
  apply pilot_model_accel_below_traj. split; fourier.
  assumption. split; fourier. fourier. assumption.
  apply Rge_le in vygevmin.

  set (f := (fun q => v q - vmin)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (f x < 0) as fxlt0. unfold f. fourier.
  assert (x < y) as xlty. fourier.
  assert (f y >= 0) as fyge0. unfold f. fourier.
  generalize (first_leg_rise f x y contf xlty fxlt0 fyge0) as flr.
  intros. inversion_clear flr as [p [[xltp pley] [fpeq0 rst]]].
  unfold f in *.

  assume zltab. (*rename H0 into zltab0.*)
  apply (Rle_trans _ (vmin - v x) _).
  left. apply (Rmult_lt_reg_l (/ab)).
  apply Rinv_0_lt_compat. assume zltab. assumption.
  setl (y - x).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  setr ((vmin - v x) / ab).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  assumption.
  Radd (v x). setl vmin. setr (v y).
  assumption.
Qed.

Lemma pilot_model_accel_at_lower_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x /\ y - x = ((vmin B) - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below_limit P B M) as pilot_model_accel_below_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_below_limit_traj. simpl in pilot_model_accel_below_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx ymxlttt].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  intros.
  Radd (v x).
  setr (v y).
  set (fll := (fct_cte ab * (id - fct_cte x) + fct_cte (v x))%F).
  assert (continuity fll) as contfll. unfold fll. reg.
  change (fll y <= v y).
  assume contv.
  apply limpoint; try assumption. (* clear H1. *)
  exists x. split. fourier.
  intros x0 xltx0lty.
  unfold fll, fct_cte, mult_fct, id, minus_fct, plus_fct.
  Radd (- v x). setl (ab * (x0 - x)). setr (v x0 - v x).
  inversion_clear xltx0lty as [xltx0 x0lty]. 
  apply pilot_model_accel_below_limit_traj; try assumption.
  split; fourier.
  split. fourier.
  rewrite <- ymxlttt.
  Radd x. setl x0. setr y.
  assumption.
Qed.

Lemma pilot_model_accel_upto_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x <= (vmin B - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below_limit P B M) as pilot_model_accel_below_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_below_limit_traj. simpl in pilot_model_accel_below_limit_traj.
  generalize (pilot_model_accel_at_lower_limit P B M) as pilot_model_accel_at_lower_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_at_lower_limit_traj. simpl in pilot_model_accel_at_lower_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx [ymxltvm | ymxeqvm]].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  apply pilot_model_accel_below_limit_traj; try assumption.
  split; try assumption.
  apply pilot_model_accel_at_lower_limit_traj; try assumption.
  split. assumption. assumption.
Qed.

Lemma pilot_model_accel_above_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x ->
            forall y, t1 <= y < t2 -> 0 < y - x < (vmax B - v x) / (aa B) ->
                      v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above P B M) as pilot_model_accel_above_traj. intro.
  rewrite Bdef in pilot_model_accel_above_traj. simpl in pilot_model_accel_above_traj.
  intros x xinterval vmaxltvx y yinterval [zltymx ymxlttt].
  
  generalize (Rtotal_order vmax (v y)) as vyvminto. intros.
  assert (vmax < v y \/ vmax >= v y) as vyvminrel.
  inversion_clear vyvminto as [vyltvmin | [vyeqvmin | vygtvmin]].
  left. assumption. right. right. assumption. right. left. assumption.
  clear vyvminto.
  inversion_clear vyvminrel as [vyltvmin | vygevmin ].
  apply pilot_model_accel_above_traj. assumption. fourier. assumption. fourier. assumption.
  apply Rge_le in vygevmin.

  set (f := (fun q => v q - vmax)).
  assert (continuity f) as contf. unfold f. assume contv.
  reg.
  assert (0 < f x ) as fxlt0. unfold f. fourier.
  assert (x < y) as xlty. fourier.
  assert (f y <= 0) as fyge0. unfold f. fourier.
  generalize (first_leg_drop f x y contf xlty fxlt0 fyge0) as flr.
  intros. inversion_clear flr as [p [[xltp pley] [fpeq0 rst]]].
  unfold f in *.

  assume aalt0. rename aalt1 into aalt00. (* rename H0 into aalt00. *)
  apply (Rle_trans _ (vmax - v x) _).
  Radd (v x). setr vmax. setl (v y).
  assumption.
  left. apply (Rmult_lt_reg_l (/(-aa))).
  apply Rinv_0_lt_compat. setl (- 0).
  apply Ropp_lt_cancel. repeat rewrite Ropp_involutive.
  fourier.
  setr (- (y - x)).
  intro. rewrite H in aalt00. apply (Rlt_irrefl 0). assumption.
  setl (-((vmax - v x) / aa)).
  intro. rewrite H in aalt00. apply (Rlt_irrefl 0). assumption.
  apply Ropp_lt_cancel. repeat rewrite Ropp_involutive.
  assumption.
Qed.

Lemma pilot_model_accel_at_upper_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x  ->
            forall y, t1 <= y < t2 -> 0 < y - x /\ y - x = (vmax B - v x) / (aa B) ->
                                v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above_limit P B M) as pilot_model_accel_above_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_above_limit_traj. simpl in pilot_model_accel_above_limit_traj.
  intros x xinterval vmaxltvx y yinterval [zltymx ymeqvm].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  Radd (v x).
  setl (v y).
  set (fll := (fct_cte aa * (id - fct_cte x) + fct_cte (v x))%F).
  assert (continuity fll) as contfll. unfold fll. reg.
  change ( v y <= fll y).
  assume contv.
  apply limpoint; try assumption. (* clear H1. *)
  exists x. split.
  fourier.
  intros x0 xltx0lty.
  unfold fll, fct_cte, mult_fct, id, minus_fct, plus_fct.
  Radd (- v x). setr (aa * (x0 - x)). setl (v x0 - v x).
  inversion_clear xltx0lty.
  apply pilot_model_accel_above_limit_traj; try assumption.
  split; fourier. split. 
  Radd x. setl x. setr x0. assumption.
  rewrite <- ymeqvm.
  Radd x. setl x0. setr y.
  assumption.
Qed.

Lemma pilot_model_accel_downto_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x ->
            forall y, t1 <= y < t2 -> 0 < y - x <= (vmax B - v x) / (aa B) ->
                      v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above_limit P B M) as pilot_model_accel_above_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_above_limit_traj. simpl in pilot_model_accel_above_limit_traj.
  generalize (pilot_model_accel_at_upper_limit P B M) as pilot_model_accel_at_upper_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_at_upper_limit_traj. simpl in pilot_model_accel_at_upper_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx [ymxltvm | ymxeqvm]].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  apply pilot_model_accel_above_limit_traj; try assumption.
  split; try assumption.
  apply pilot_model_accel_at_upper_limit_traj; try assumption.
  split. assumption. assumption.
Qed.


Lemma above_vmin_lower_left_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : vmin B <= v t1)
         (s : (t-t1) <= (vmin B - v t1) / (amin B)),
    (amin B) / 2 * ((t-t1) * (t-t1)) + (v t1) * (t-t1) + (z t1) <= z t.
Proof.
  ua.
  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj. simpl in pilot_model_maintains_lower_bound_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
    apply (Rplus_le_reg_l (- (z t1)));
    setr (z t - z t1);
    rewrite <- vintval;
    try setl (amin / 2 * ((t-t1) * (t-t1)) + (v t1) * (t-t1)).
  set (f := (fct_cte (amin/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte amin * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  simpl in fintval;
  change ( f t <= RiemannInt vintegr);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, comp, minus_fct;
    field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19 ; [assumption | idtac].
  intros x t1ltxltt.
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct;
  apply (Rplus_le_reg_r (- v t1));
  setl (amin * (x-t1));
  setr (v x - v t1).
  set (vfun := (mkC1 conta0));
  generalize (RiemannInt_P32 vfun t1 x) as aintegr; intros;
  generalize (FTC_Riemann vfun aintegr) as aintval; intros;
  simpl in aintval, aintegr; clear vfun;
  rewrite <- aintval.
  set (g := (fct_cte amin * (id - fct_cte t1))%F);
    establish_deriv2 g' (fct_cte amin)%F g;
  rename H into gpf;
  assert (continuity (derive g gpf)) as contg;
    [rewrite fe0; unfold g'; reg | idtac];
  set (gfun := (mkC1 contg));
  generalize (RiemannInt_P32 gfun t1 x) as gintegr; intros;
  generalize (FTC_Riemann gfun gintegr) as gintval; intros;
  change (g x <= RiemannInt aintegr).
  assert (g x = g x - g t1); [unfold g;
  unfold fct_cte, mult_fct, id, minus_fct; setr (amin * (x-t1)); reflexivity | rewrite H ];
  simpl in gintval;
  rewrite <- gintval;
  apply RiemannInt_P19;
  [inversion t1ltxltt as [t1ltx xltt]; left; assumption | intros; rewrite fe0, dveqa];
  unfold g', fct_cte.
  clear H gintval gintegr gfun contg fe0 gpf g' g aintegr aintval.
  clear fintval fintegr ffun contf fe fpf f' f vintegr vintval.

  clear pfun.
  rewrite dpeqv in contv0.
  inversion_clear H0 as [zltx0 x0ltx].
  inversion t1ltxltt.
  assert (t1 <= t1 < t2) as t1interval. split; fourier.
  assert (t1 <= x0 < t2) as x0interval. split; fourier.
    generalize (pilot_model_maintains_lower_bound_traj t1 t1interval r x0 x0interval zltx0) as vminbnd. intros.

  inversion_clear vminbnd as [vminltvx0 | vmineqvx0].
  generalize (Rtotal_order (v x0) vmax) as vmaxorder; intros;
  inversion_clear vmaxorder as [vltvmax | [veqvmax | vgtvmax]].
  assert (vmin < v x0 < vmax) as vx0pos. split. assumption. assumption.

  generalize (vwithin _ x0interval vx0pos) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  generalize (vatupper _ x0interval veqvmax) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  generalize (vabove _ x0interval vgtvmax) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  symmetry in vmineqvx0.
  generalize (vatlower _ x0interval vmineqvx0) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax].
  assume aminleaa. assume aalt0. fourier.
Qed.



Lemma below_vmin_lower_left_limiting_trajectory_upto :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
         (s : (t-t1) < (vmin B - v t1) / (ab B)),
    (ab B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1 <= z t.
Proof.
  ua.
  generalize (pilot_model_accel_upto_limit P B M) as pilot_model_accel_upto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_upto_limit_traj. simpl in pilot_model_accel_upto_limit_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.


    apply (Rplus_le_reg_l (- (z t1)));
    setr (z t - z t1);
    rewrite <- vintval;
    try setl (ab / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
    set (f := (fct_cte (ab/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte ab * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( f t <= RiemannInt vintegr);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, minus_fct, comp, Rsqr, id;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19. assumption.
  intros x tgtxgtt1;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgtt1; split; left; assumption | idtac].
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct.

  clear pfun.
  rewrite dpeqv in contv0.
(*  inversion_clear H0 as [zltx0 x0ltx]. *)
  assert (0 < x - t1 <= (vmin - v t1) / ab) as x0pos.
  split. Radd t1. setl t1. setr x. inversion_clear tgtxgtt1 as [zltx xltt]. assumption.
  left. Radd t1. setl x. inversion_clear tgtxgtt1 as [zltx xltt].
  apply (Rlt_trans _ t _). assumption. Radd (-t1). setl (t - t1). setr ((vmin - v t1)/ab).
  intro. clear Bdef. rewrite H in zltab.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  assert (t1 <= t1 < t2) as t1interval. split; fourier.
  assert (t1 <= x < t2) as xinterval.
  inversion tgtxgtt1.
  split; fourier.
  generalize (pilot_model_accel_upto_limit_traj t1 t1interval r x xinterval x0pos) as vminbnd. intros.

  apply (Rplus_le_reg_r (- v t1)).
  setl (ab * (x - t1)).
  setr (v x - v t1). assumption.
Qed.

Lemma below_vmin_lower_left_limiting_trajectory :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
           t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
           (s : t-t1 <= (vmin B - v t1) / (ab B)),
      (ab B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1 <= z t.
Proof.
  ua.
  generalize (below_vmin_lower_left_limiting_trajectory_upto P B M) as
      below_vmin_lower_left_limiting_trajectory_upto_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_upto_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_upto_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  rename s into sold.
  inversion_clear sold as [s | s].
  apply below_vmin_lower_left_limiting_trajectory_upto_traj; try assumption.
  assert (0<=(t-t1)) as tmt1ge0. fourier.
  inversion_clear tmt1ge0 as [tmt1gt0 | tmt1eq0].
  set (fll := (fct_cte (ab/2) * comp Rsqr (id - fct_cte t1) +
               fct_cte (v t1) * (id-fct_cte t1) + fct_cte (z t1))%F).
  assert (continuity fll). unfold fll. reg.
  change (fll t <= z t).
  assume contz.
  apply limpoint; try assumption. (* clear H0. *)
  exists t1. split. fourier. 
  intros.
  inversion_clear H0 as [t1ltx xltt].
  apply below_vmin_lower_left_limiting_trajectory_upto_traj; try assumption.
  split. left. assumption. fourier. rewrite <- s. Radd t1. setl x. setr t. assumption.
  apply False_ind.
  rewrite s in tmt1eq0.
  assert (v t1 = vmin). Radd (- v t1).
  setl 0. setr (vmin - v t1).
  
  assume zltab. (* rename H into zltab0. *)
  apply (Rmult_eq_reg_l (/ ab )).
  setl 0.
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  setr ((vmin - v t1) / ab).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  assumption.
  apply Rinv_neq_0_compat. discrR.
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  rewrite H in r.
  apply (Rlt_irrefl vmin). assumption.
Qed.


Lemma above_vmin_lower_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : vmin B <= v t1)
         (s : (vmin B - v t1) / (amin B) <= t-t1),
    (vmin B) * (t-t1) - ((vmin B - v t1)/(amin B)) * (vmin B - v t1)/2 + z t1 <= z t.
Proof.
  ua.
  generalize (above_vmin_lower_left_limiting_trajectory P B M) as
      above_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_left_limiting_trajectory_traj.
  simpl in above_vmin_lower_left_limiting_trajectory_traj.

  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj.
  simpl in pilot_model_maintains_lower_bound_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  assume aminleaa. assume aalt0.
  rename aalt1 into aalt00. (*rename H into aminleaa0. rename H0 into aalt00.*)
  assert ((vmin*vmin - (v t1)*(v t1))/(2*amin) + z t1 <= z ((vmin - v t1)/amin + t1)).
  assert (0 <= (vmin - v t1) / amin). inversion_clear r.
  setr ((v t1 - vmin) / (- amin)).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  setr ((v t1 - vmin) * (/ -amin)).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1.
  left. apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier. 
  apply Rinv_0_lt_compat. fourier.
  rewrite H. setr 0.
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. right. reflexivity.
  assert ((vmin - v t1) / amin + t1 - t1 <= (vmin - v t1) / amin). right. setl ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  reflexivity.
  assert (t1 <= (vmin - v t1) / amin + t1 < t2) as vmininterval.
  split. Radd (-t1). setl 0. setr ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmin - v t1) / amin + t1 <= t). Radd (-t1). setl ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmin - v t1) / amin) in *. fourier.
  
  generalize (above_vmin_lower_left_limiting_trajectory_traj ((vmin - v t1) / amin + t1) vmininterval
             zlet1 r H0). intros.
  setl (amin / 2 * ((vmin - v t1) / amin * ((vmin - v t1) / amin)) +
        v t1 * ((vmin - v t1) / amin) + z t1).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  setl (amin / 2 *
       (((vmin - v t1) / amin + t1 - t1) *
        ((vmin - v t1) / amin + t1 - t1)) +
       v t1 * ((vmin - v t1) / amin + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assumption.

  setl (vmin * ( (t-t1) - ((vmin - v t1)/amin)) +
        (vmin * vmin - v t1 * v t1) / (2*amin) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmin - v t1) / amin + t1).
  change ((vmin * vmin - v t1 * v t1) / (2 * amin) + z t1 <= z tt) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmin - v t1) / amin).
  intro. rewrite H0 in *.
  assert (aa >= 0). fourier.
  apply (Rge_not_lt aa 0 H1 aalt00).
  assumption.
  apply (Rle_trans _ (vmin * (t - tt) + z tt) _).
  Radd (- vmin * (t - tt)). setr (z tt). unfold tt.
  setl ((vmin * vmin - v t1 * v t1) / (2 * amin) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt)));
    setl (vmin * (t - tt));
    setr (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmin * id)%F).
    establish_deriv2 f' (fct_cte vmin)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setl (vmin * t - vmin * tt).
  change ( f t - f tt <= RiemannInt vintegr).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (t1 <= t1 < t2) as t1interval. split. right. reflexivity. inversion tinterval.
  inversion H0. fourier. rewrite <- H2 in H1. assumption.
  eapply pilot_model_maintains_lower_bound_traj. apply t1interval. apply r.
  inversion ttltxltt as [ttltx xltt]. split.
  assert (t1 <= tt) as t1gett.
  unfold tt. Radd (-t1). setl 0. setr ((v t1 - vmin) * (/ -amin)).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  inversion_clear r. setl (0*0). left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier. 
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  right. reflexivity.

  fourier. fourier.
  assert (t1 <= tt) as zlett. unfold tt.
  setr (  ((v t1 - vmin) * / - amin) + t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  Radd (-t1). setl 0. setr ((v t1 - vmin) * / - amin).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  inversion_clear r.

  left.
  assert (0 = 0*0). field. rewrite H1 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  right. reflexivity. inversion_clear ttltxltt. fourier.
Qed.


Lemma below_vmin_lower_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
         (s : (vmin B - v t1) / (ab B) <= t-t1),
    (vmin B)* (t-t1) - ((vmin B - v t1)/(ab B)) * (vmin B - v t1)/2 + z t1 <= z t.
Proof.
  ua.
  generalize (below_vmin_lower_left_limiting_trajectory P B M) as
      below_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_traj.

  generalize (pilot_model_accel_upto_limit P B M) as
      pilot_model_accel_upto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_upto_limit_traj.
  simpl in pilot_model_accel_upto_limit_traj.

  generalize (pilot_model_maintains_lower_bound P B M) as
      pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj.
  simpl in pilot_model_maintains_lower_bound_traj.

  intros.

  assume zltab. (* rename H into zltab0. *)
  assert ((vmin*vmin - (v t1)*(v t1))/(2*ab) + z t1 <= z ((vmin - v t1)/ab + t1)).
  assert (0 <= (vmin - v t1) / ab).
  setr ((vmin - v t1) * / ab).
  intro. assume zltab. 
  subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H at 1. left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. apply zltab.
  assert ((vmin - v t1) / ab + t1 - t1 <= (vmin - v t1) / ab). right. setl ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  reflexivity.
  assert (t1 <= (vmin - v t1) / ab + t1 < t2) as vmininterval.
  split. Radd (-t1). setl 0. setr ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmin - v t1) / ab + t1 <= t). Radd (-t1). setl ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmin - v t1) / ab) in *. inversion tinterval. fourier.

  generalize (below_vmin_lower_left_limiting_trajectory_traj
                ((vmin - v t1)/ab+t1) vmininterval zlet1 r H0). intros.
  setl (ab / 2 *
       (((vmin - v t1) / ab + t1 - t1) * ((vmin - v t1) / ab + t1 - t1)) +
       v t1 * ((vmin - v t1) / ab + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setl (vmin * ( (t-t1) - ((vmin - v t1)/ab)) +
        (vmin * vmin - v t1 * v t1) / (2*ab) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmin - v t1) / ab + t1).
  change ((vmin * vmin - v t1 * v t1) / (2 * ab) + z t1 <=
          z tt) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmin - v t1) / ab).
  intro. rewrite H0 in *.  apply (Rlt_irrefl 0). assumption.
  assumption.
  
  apply (Rle_trans _ (vmin * (t - tt) + z tt) _).
  Radd (- vmin * (t - tt)). setr (z tt). unfold tt.
  setl ((vmin * vmin - v t1 * v t1) / (2 * ab) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt)));
    setl (vmin * (t - tt));
    setr (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmin * id)%F).
    establish_deriv2 f' (fct_cte vmin)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setl (vmin * t - vmin * tt).
  change ( f t - f tt <= RiemannInt vintegr).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 < tt - t1 <= (vmin - v t1) / ab) as ttpos.
  split.
  unfold tt.
  setr ((vmin - v t1) * / ab).
  intro. rewrite H0 in zltab0. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1. 
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  Radd t1.
  setl tt. unfold tt. right. reflexivity.
  assert (ab * (tt - t1) + v t1 <= v tt) as vttval.
  Radd (- v t1). setl (ab * (tt - t1)). setr (v tt - v t1).
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.
  apply (pilot_model_accel_upto_limit_traj t1 t1interval r tt ttinterval ttpos).
  unfold tt in vttval at 1.
  assert (ab * ((vmin - v t1) / ab + t1 - t1) + v t1 = vmin).
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite H0 in vttval.
  eapply pilot_model_maintains_lower_bound_traj.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.
  eapply ttinterval.
  apply vttval.
  inversion_clear ttltxltt. split.
  inversion ttpos. fourier.
  inversion ttlexlet. inversion tinterval. fourier.
  inversion ttltxltt.
  assumption.
Qed.

Lemma bounded_below :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1),
    K (amin B) (ab B) (v t1) (vmin B) (z t1) (t-t1) <= z t (*<= K aa amax (v 0) vmax (z 0) t *).
Proof.
  ua.
  generalize (above_vmin_lower_left_limiting_trajectory P B M) as 
    above_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_left_limiting_trajectory_traj.
  simpl in above_vmin_lower_left_limiting_trajectory_traj.
  generalize (above_vmin_lower_right_limiting_trajectory P B M) as 
    above_vmin_lower_right_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_right_limiting_trajectory_traj.
  simpl in above_vmin_lower_right_limiting_trajectory_traj.
  generalize (below_vmin_lower_left_limiting_trajectory P B M) as 
    below_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_traj.
  generalize (below_vmin_lower_right_limiting_trajectory P B M) as 
    below_vmin_lower_right_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_right_limiting_trajectory_traj.
  simpl in below_vmin_lower_right_limiting_trajectory_traj.

  
  intros.
  assume aalt0. rename aalt1 into aalt00.
  assume aminleaa. (* rename H into aminleaa0. *)
  assume zltab. (* rename H into zltab0. *)

  unfold K.
  
  destruct (total_order_T vmin (v t1)); [
      assert (vmin <= v t1) as r; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s; rle_decide vmin (v t1) |
      apply Rgt_not_le in r; rle_decide vmin (v t1); apply Rnot_le_gt in r]; [
  destruct (total_order_T (t-t1) ((vmin - v t1) / amin)); [
    assert ((t-t1) <= (vmin - v t1) / amin) as s0;
    [inversion s ;
     [ left; assumption | right ; assumption] |
     idtac]; clear s; rle_decide (t-t1) ((vmin- v t1)/amin) |
    apply Rgt_not_le in r0; rle_decide (t-t1) ((vmin- v t1)/amin);
    apply Rnot_le_gt in r0] |
  destruct (total_order_T (t-t1) ((vmin - v t1) / ab)); [
    assert ((t-t1) <= (vmin - v t1) / ab) as s0;
    [inversion s ;
     [ left; assumption | right ; assumption] |
     idtac]; clear s; rle_decide (t-t1) ((vmin- v t1)/ab) |
    apply Rgt_not_le in r0; rle_decide (t-t1) ((vmin- v t1)/ab);
    apply Rnot_le_gt in r0]]; unfold J; simpl.

  setl (amin / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply above_vmin_lower_left_limiting_trajectory_traj; try assumption.
  setl (vmin * (t-t1) - (vmin - v t1) / amin * (vmin - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply above_vmin_lower_right_limiting_trajectory_traj; try assumption.
  left. assumption.
  setl (ab / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply below_vmin_lower_left_limiting_trajectory_traj; try assumption.
  setl (vmin * (t-t1) - (vmin - v t1) / ab * (vmin - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply below_vmin_lower_right_limiting_trajectory_traj; try assumption.
  left. assumption.
Qed.

Lemma below_vmax_upper_left_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : v t1 <= vmax B) (s : t-t1 <= (vmax B - v t1) / (amax B)),
    z t <= (amax B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj.  intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.
  
  intros.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
    apply (Rplus_le_reg_l (- (z t1)));
    setl (z t - z t1);
    rewrite <- vintval;
    try setr (amax / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
  set (f := (fct_cte (amax/2) * comp Rsqr (id - fct_cte t1) + fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte amax * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( RiemannInt vintegr <= f t );
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, minus_fct, comp;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval];
  apply RiemannInt_P19 ; [inversion tinterval; assumption | idtac];
  intros x tgtxgt0;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgt0; split; left; assumption | idtac];
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct;
  apply (Rplus_le_reg_r (- v t1));
  setr (amax * (x-t1));
  setl (v x - v t1);
  set (vfun := (mkC1 conta0));
  generalize (RiemannInt_P32 vfun t1 x) as aintegr; intros;
  generalize (FTC_Riemann vfun aintegr) as aintval; intros;
  simpl in aintval, aintegr; clear vfun;
  rewrite <- aintval;
  set (g := (fct_cte amax * (id - fct_cte t1))%F);
    establish_deriv2 g' (fct_cte amax)%F g;
  rename H into gpf;
  assert (continuity (derive g gpf)) as contg;
    [rewrite fe0; unfold g'; reg | idtac];
  set (gfun := (mkC1 contg));
  generalize (RiemannInt_P32 gfun t1 x) as gintegr; intros;
  generalize (FTC_Riemann gfun gintegr) as gintval; intros;
  change (RiemannInt aintegr <= g x);
  assert (g x = g x - g t1); [ unfold g;
  unfold fct_cte, mult_fct, id, minus_fct; setr (amax *( x - t1)) ; reflexivity | rewrite H ];
  simpl in gintval;
  rewrite <- gintval;
  apply RiemannInt_P19;
  [left; inversion_clear tgtxgt0; assumption | intros; rewrite fe0, dveqa];
  unfold g', fct_cte;
  clear H gintval gintegr gfun contg fe0 gpf g' g aintegr aintval xge0let;
  clear fintval fintegr ffun contf fe fpf f' f vintegr vintval.

  clear pfun.
  rewrite dpeqv in contv0.
  inversion_clear H0 as [zltx0 x0ltx].
  
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x0 < t2) as x0interval. inversion tinterval. inversion tgtxgt0; split; fourier.
  generalize (pilot_model_maintains_upper_bound_traj t1 t1interval r x0 x0interval zltx0) as vmaxbnd. intros.

  inversion_clear vmaxbnd as [vmaxltvx0 | vmaxeqvx0].
  generalize (Rtotal_order (v x0) vmin) as vminorder; intros;
  inversion_clear vminorder as [vltvmin | [veqvmin | vgtvmin]].

  generalize (vbelow _ x0interval vltvmin) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  generalize (vatlower _ x0interval veqvmin) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  
  assert (vmin < v x0 < vmax) as vx0pos. split. assumption. assumption.
  generalize (vwithin _ x0interval vx0pos) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  generalize (vatupper _ x0interval vmaxeqvx0) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax].
  assume ableamax. assume zltab. fourier.
Qed.

Lemma above_vmax_upper_left_limiting_trajectory_upto :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : vmax B < v t1) (s : t-t1 < (vmax B - v t1) / (aa B)),
    z t <= (aa B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (pilot_model_accel_downto_limit P B M) as pilot_model_accel_downto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_downto_limit_traj.
  simpl in pilot_model_accel_downto_limit_traj.
  
  intros.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.


    apply (Rplus_le_reg_l (- (z t1)));
    setl (z t - z t1);
    rewrite <- vintval;
    try setr (aa / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
    set (f := (fct_cte (aa/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte aa * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( RiemannInt vintegr <= f t);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, comp, minus_fct;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19; [ inversion tinterval; assumption | idtac];
  intros x tgtxgt0;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgt0; split; left; assumption | idtac];
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct.

  clear pfun.
  rewrite dpeqv in contv0.
  assert (0 < x - t1 <= (vmax - v t1) / aa) as x0pos.
  split. inversion_clear tgtxgt0 as [zltx xltt]. fourier.
  left. inversion_clear tgtxgt0 as [zltx xltt].
  apply (Rlt_trans _ (t-t1) _). fourier. assumption.
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion tgtxgt0; split; fourier.
  generalize (pilot_model_accel_downto_limit_traj t1 t1interval r x xinterval x0pos) as vmaxbnd. intros.

  fourier.
Qed.

Lemma above_vmax_upper_left_limiting_trajectory :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
      (r : vmax B < v t1) (s : t-t1 <= (vmax B - v t1) / (aa B)),
     z t <= (aa B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory_upto P B M) as
    above_vmax_upper_left_limiting_trajectory_upto_traj. intro.
  rewrite Bdef in above_vmax_upper_left_limiting_trajectory_upto_traj.
  simpl in above_vmax_upper_left_limiting_trajectory_upto_traj.
  
  intros.
  rename s into sold.
  inversion tinterval as [t1let tltt2].
  inversion_clear sold as [s | s].
  apply above_vmax_upper_left_limiting_trajectory_upto_traj; try assumption.
  set (fll := (fct_cte (aa/2) * comp Rsqr (id - fct_cte t1) + fct_cte (v t1) * (id - fct_cte t1) + fct_cte (z t1))%F).
  assert (continuity fll). unfold fll. reg.
  change (z t <= fll t).
  assume contz.
  inversion t1let. 
  apply limpoint; try assumption. (* clear H0.*)
  exists t1. split. assumption.
  intros x xinterval.
  inversion xinterval as [t1ltx xltt].

  apply above_vmax_upper_left_limiting_trajectory_upto_traj; try assumption.
  split; fourier.
  Radd t1. setl x.
  assert (t = (vmax - v t1) / aa + t1) as tdef.
  Radd (-t1). setl (t - t1). setr ((vmax - v t1) / aa).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  rewrite <- tdef. assumption.

  apply False_ind.
  assert (0 = t - t1) as tmt1eq0. Radd t1. setl t1. setr t. assumption.
  rewrite s in tmt1eq0.
  assert (v t1 = vmax). Radd (- v t1).
  setl 0. setr (vmax - v t1).
  
  assume aalt0. rename aalt1 into aalt00.
  apply (Rmult_eq_reg_l (/ aa )).
  setl 0.
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  setr ((vmax - v t1) / aa).
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  assumption.
  apply Rinv_neq_0_compat.
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  rewrite H1 in r.
  apply (Rlt_irrefl vmax). assumption.
Qed.

Lemma below_vmax_upper_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : v t1 <= vmax B) (s : (vmax B - v t1) / (amax B) <= t-t1),
    z t <= (vmax B) * (t-t1) - ((vmax B - v t1)/(amax B)) * (vmax B - v t1)/2 + z t1.
Proof.
  ua.
  generalize (below_vmax_upper_left_limiting_trajectory P B M) as
      below_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmax_upper_left_limiting_trajectory_traj.
  simpl in below_vmax_upper_left_limiting_trajectory_traj.
  
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.

  intros.

  assume ableamax. (* rename H into ableamax0. *)
  assume zltab. (* rename H into zltab0. *)
  assert (z ((vmax - v t1)/amax + t1) <= (vmax*vmax - (v t1)*(v t1))/(2*amax) + z t1).
  assert (0 <= (vmax - v t1) / amax). inversion_clear r.
  left. setr ((vmax - v t1) * (/ amax)).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H. setr 0.
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. right. reflexivity.
  assert ((vmax - v t1) / amax + t1 - t1 <= (vmax - v t1) / amax).
  setl ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. 
  right. reflexivity.

  assert (t1 <= (vmax - v t1) / amax + t1 < t2) as vmaxinterval.
  split. Radd (-t1). setl 0. setr ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmax - v t1) / amax + t1 <= t). Radd (-t1). setl ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmax - v t1) / amax) in *. inversion tinterval. fourier.

  generalize (below_vmax_upper_left_limiting_trajectory_traj
                ((vmax - v t1)/amax + t1) vmaxinterval zlet1 r H0). intros.
  setr (amax / 2 * (((vmax - v t1) / amax + t1 - t1) * ((vmax - v t1) / amax + t1 - t1)) +
        v t1 * ((vmax - v t1) / amax + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setr (vmax * ( (t-t1) - ((vmax - v t1)/amax)) +
        (vmax * vmax - v t1 * v t1) / (2*amax) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmax - v t1) / amax + t1).
  change (z tt <=
          (vmax * vmax - v t1 * v t1) / (2 * amax) + z t1) in H.
  assert (tt <= t) as s1. unfold tt. Radd (-t1). setr (t-t1). setl ((vmax - v t1) / amax).
  intro. rewrite H0 in ableamax0. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  Radd (- vmax * (t - tt)).
  setl (z t - vmax * (t - tt)). unfold tt at 2.
  setr ((vmax * vmax - v t1 * v t1) / (2 * amax) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply (Rle_trans _ (z tt) _).

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.
  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt) + vmax * (t - tt)));
    setr (vmax * (t - tt));
    setl (z t - z tt);
  rewrite <- vintval.
  set (f := (fct_cte vmax * id)%F).
    establish_deriv2 f' (fct_cte vmax)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setr (vmax * t - vmax * tt).
  change ( RiemannInt vintegr <= f t - f tt ).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 <= tt - t1) as zlettmt1. unfold tt.
  inversion_clear r.

  left.
  setr ((vmax - v t1) / amax).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H1 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  right. reflexivity. 

  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion ttltxltt. split; fourier.
  inversion xinterval. inversion H0.
  eapply pilot_model_maintains_upper_bound_traj. apply t1interval. apply r. apply xinterval. assumption.
  rewrite <- H2. assumption.
  assumption.
Qed.

Lemma above_vmax_upper_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : vmax B < v t1) (s : (vmax B - v t1) / (aa B) <= t-t1),
     z t <= (vmax B) * (t-t1) - ((vmax B - v t1)/(aa B)) * (vmax B - v t1)/2 + z t1.
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory P B M) as
    above_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmax_upper_left_limiting_trajectory_traj.
  simpl in above_vmax_upper_left_limiting_trajectory_traj.
  generalize (pilot_model_maintains_upper_bound P B M) as
    pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.
  generalize (pilot_model_accel_downto_limit P B M) as
    pilot_model_accel_downto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_downto_limit_traj.
  simpl in pilot_model_accel_downto_limit_traj.
  
  intros.

  assume aalt0. rename aalt1 into aalt00.
  assert (z ((vmax - v t1)/aa + t1) <= (vmax*vmax - (v t1)*(v t1))/(2*aa) + z t1).
  assert (0 <= (vmax - v t1) / aa).
  setr ((v t1 - vmax) * / - aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H at 1. left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  assert ((vmax - v t1) / aa + t1 -t1 <= (vmax - v t1) / aa).
  setl ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  right. reflexivity.
  assert (t1 <= (vmax - v t1) / aa + t1 < t2) as vmaxinterval.
  split. Radd (-t1). setl 0. setr ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.
  inversion s as [vmaxlttmt1 | vmaxeqtmt1].
  inversion tinterval. apply (Rlt_trans _ t  _).
  Radd (-t1). setr (t-t1). setl ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption. assumption.
  rewrite vmaxeqtmt1. setl t. inversion tinterval. assumption.
  generalize (above_vmax_upper_left_limiting_trajectory_traj
                ((vmax - v t1)/aa + t1) vmaxinterval zlet1 r H0). intros.
  setr (aa / 2 * (((vmax - v t1) / aa + t1 - t1) * ((vmax - v t1) / aa + t1 - t1)) +
        v t1 * ((vmax - v t1) / aa + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setr (vmax * ( (t-t1) - ((vmax - v t1)/aa)) +
        (vmax * vmax - v t1 * v t1) / (2*aa) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmax - v t1) / aa + t1).
  change (z tt <= 
          (vmax * vmax - v t1 * v t1) / (2 * aa) + z t1) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmax - v t1) / aa).
  intro. rewrite H0 in aalt00. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.
  Radd (- vmax * (t - tt)). unfold tt at 2.
  setr ((vmax * vmax - v t1 * v t1) / (2 * aa) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  setl (z t - vmax * (t - tt)).
  apply (Rle_trans _ (z tt) _).

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.
  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt) + vmax * (t - tt)));
    setr (vmax * (t - tt));
    setl (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmax * id)%F).
    establish_deriv2 f' (fct_cte vmax)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setr (vmax * t - vmax * tt).
  change (RiemannInt vintegr <=  f t - f tt).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 < tt - t1 <= (vmax - v t1) / aa) as ttpos.

  split.
  unfold tt.
  setr ((v t1 - vmax ) * / - aa).
  intro. rewrite H0 in aalt00. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1. 
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  Radd t1.
  setl tt. unfold tt. right. reflexivity.

  assert ( v tt <= aa * (tt - t1) + v t1) as vttval.
  Radd (- v t1). setr (aa * (tt - t1)). setl (v tt - v t1).
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.

  apply (pilot_model_accel_downto_limit_traj t1 t1interval r tt ttinterval ttpos).
  
  assert (aa * ((vmax - v t1) / aa + t1 - t1) + v t1 = vmax).
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  change (aa * (tt - t1) + v t1 = vmax) in H0.
  rewrite H0 in vttval.

  assert (t1 <= tt < t2) as ttinterval. inversion ttpos. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion ttltxltt. inversion ttpos.
  split; fourier.
  inversion xinterval.
  eapply pilot_model_maintains_upper_bound_traj. apply ttinterval. assumption. apply xinterval.
  inversion_clear ttltxltt. assumption.
  assumption.

Qed.

Lemma bounded_above :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1),
    (* K amin ab (v 0) vmin (z 0) t <= *) z t <= K (aa B) (amax B) (v t1) (vmax B) (z t1) (t-t1).
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory P B M) as 
    above_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in     above_vmax_upper_left_limiting_trajectory_traj.
  simpl in     above_vmax_upper_left_limiting_trajectory_traj.
  generalize (above_vmax_upper_right_limiting_trajectory P B M) as 
    above_vmax_upper_right_limiting_trajectory_traj. intro.
  rewrite Bdef in     above_vmax_upper_right_limiting_trajectory_traj.
  simpl in     above_vmax_upper_right_limiting_trajectory_traj.
  generalize (below_vmax_upper_left_limiting_trajectory P B M) as 
    below_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in     below_vmax_upper_left_limiting_trajectory_traj.
  simpl in     below_vmax_upper_left_limiting_trajectory_traj.
  generalize (below_vmax_upper_right_limiting_trajectory P B M) as 
    below_vmax_upper_right_limiting_trajectory_traj. intro.
  rewrite Bdef in     below_vmax_upper_right_limiting_trajectory_traj.
  simpl in     below_vmax_upper_right_limiting_trajectory_traj.
  
  intros.
  assume aalt0. rename aalt1 into aalt00.
  assume ableamax. (* rename H into ableamax0. *)
  assume zltab. (* rename H into zltab0. *)


  unfold K.
  destruct (total_order_T vmax (v t1)); [
      assert (vmax <= v t1) as r; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s ; rle_decide vmax (v t1) |
      apply Rgt_not_le in r; rle_decide vmax (v t1);
      apply Rnot_le_gt in r]; [
  destruct (total_order_T (t-t1) ((vmax - v t1) / aa)); [
      assert (t-t1 <= (vmax - v t1) / aa) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s;  rle_decide (t-t1) ((vmax-v t1)/aa) |
      apply Rgt_not_le in r0; rle_decide (t-t1) ((vmax- v t1)/aa);
    apply Rnot_le_gt in r0] |
  destruct (total_order_T (t-t1) ((vmax - v t1) / amax)); [
      assert (t-t1 <= (vmax - v t1) / amax) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s; rle_decide (t-t1) ((vmax-v t1)/amax) |
      apply Rgt_not_le in r0; rle_decide (t-t1) ((vmax- v t1)/amax);
    apply Rnot_le_gt in r0]];
    unfold J;
    simpl.

  setr (aa / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  rename r into vmpos.
  inversion_clear vmpos as [r|r].
  apply above_vmax_upper_left_limiting_trajectory_traj; try assumption.
  assert (t-t1 <= 0) as tle0. rewrite r in s0.
  setr ((v t1 - v t1)/aa).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  assert (0 <= t-t1) as zletmt1. inversion tinterval. fourier.
  inversion tle0 as [tlt0 | teq0]. apply False_ind.
  eapply Rge_not_lt. apply Rle_ge. apply zletmt1. assumption.
  rewrite teq0. setr (z t1).
  assert (t=t1) as teqt1. Radd (-t1). setl (t-t1). setr 0. assumption.
  rewrite teqt1.
  right. reflexivity.

  setr (vmax * (t-t1) - (vmax - v t1) / aa * (vmax - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rename r into vmpos.
  inversion_clear vmpos as [r|r].
  apply above_vmax_upper_right_limiting_trajectory_traj; try assumption.
  left. assumption.

  assert (vmax - v t1 = 0) as zer.
  Radd (v t1). setl vmax. setr (v t1). assumption.

  assert (v t1 <= vmax) as v0levm. right. symmetry. assumption.
  assert ((vmax - v t1)/amax <= t-t1) as tgett. left. rewrite zer in *.
  setl 0.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 / aa = 0) as zltaa. field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite zltaa in r0. assumption.

  generalize (below_vmax_upper_right_limiting_trajectory_traj
                t tinterval zlet1 v0levm tgett) as bnd. intros.
  rewrite zer in *.
  fieldrewrite (vmax * (t-t1) - 0 / aa * 0 / 2 + z t1)
               (vmax * (t-t1) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.

  assert (vmax * (t-t1) - 0 / amax * 0 / 2 + z t1 = vmax * (t-t1) + z t1) as bndeq.
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite bndeq in bnd. assumption.

  setr (amax / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply below_vmax_upper_left_limiting_trajectory_traj; try assumption.
  left. assumption.
  setr (vmax * (t-t1) - (vmax - v t1) / amax * (vmax - v t1) / 2 + z t1).
  intro. rewrite H in ableamax0. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply below_vmax_upper_right_limiting_trajectory_traj; try assumption.
  left. assumption.
  left. assumption.
Qed.

(* End Trajectory. *)


(* When putting everything together, remember: K and Φ are
indexed from time zero in the polynomial, which we align with the
beginning of the maneuver. They have no absolute time reference, so
they need a -t1 adjustment (e.g. becomes t-t1) in their arguments. The
rest of our state such as z v a, all have an absolute time reference,
so they use t without adjustment. *)


(*
Two aircraft with paths Po and Pi, undergoing maneuvers Mo and Mi
respectively during time interval [t1,t2], which are in horizontal
conflict during time interval [tb,te] are safely separated during
[t1,t2] because the Po aircraft is above the Pi aircraft, separated by
at least distance hp.
*)
Lemma safely_above_for_1_maneuver :
  forall {t tb te vmd t1 t2 zo vo ao zi vi ai Bo Bi}
         (Po: Path zo vo ao) (Mo: Maneuver t1 t2 Po Bo)
         (Pi: Path zi vi ai) (Mi: Maneuver t1 t2 Pi Bi)
    (t1ge0 : 0 <= t1)
    (tmaneuver : t1 <= t < t2)
    (thconflict : tb <= t <= te),
    vert_safe_above (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
                    (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
                    (tb-t1) (te-t1) = Some vmd ->
    vmd <= zo t - zi t.
Proof.
  intros.
  rename H into vs.

  generalize (bounded_below Po Bo Mo t tmaneuver t1ge0) as ownbb. intros.
  generalize (bounded_above Pi Bi Mi t tmaneuver t1ge0) as intba. intros.
  
  apply (Rle_trans _
                      (K (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1) (t-t1) -
                       K (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1) (t-t1))
                      _).

  apply (safely_separated_trajectory_interval_above
                 (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
                 (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
                 vmd (tb-t1) (te-t1)); try assumption.
  inversion thconflict.
  split. Radd t1. setl tb. setr t. assumption.
  Radd t1. setl t. setr te. assumption.
  apply Rplus_le_compat; try assumption.
  apply Ropp_le_contravar; try assumption.
Qed.

(* The assertion that a pair of aircraft are vertically safe *)


(* This predicate describes a pair of aircraft following paths Po and
Pi, and an arbitrary sequence of maneuvers that satisfy our safety
predicates, where the Po aircraft is above the Pi aircraft.

Each vert_safe_above predicate computes vmd ensuring aircraft
separation during one maneuver (or the time the maneuver overlaps the
time of horizontal conflict, [tb,te])

*)

Inductive SafeFlt {zo vo ao zi vi ai} t1 tb te vmd
          (Po: Path zo vo ao) (Pi: Path zi vi ai) :Prop :=
| trj_intro : forall t2 Bo Bi,
    Maneuver t1 t2 Po Bo -> 
    Maneuver t1 t2 Pi Bi -> 
    vert_safe_above (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
                    (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
                    (Rmax (0-t1) (tb-t1)) (Rmin (t2-t1) (te-t1)) = Some vmd ->
    SafeFlt t2 tb te vmd Po Pi ->
    SafeFlt t1 tb te vmd Po Pi
| trj_null : forall Bo Bi,
    TailManeuver t1 Po Bo ->
    TailManeuver t1 Pi Bi ->
    vert_safe_above (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
                    (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
                    (Rmax (0-t1) (tb-t1)) (te-t1) = Some vmd->
    SafeFlt t1 tb te vmd Po Pi.

Definition P {zo vo ao zi vi ai} t1 tb te vmd (Po: Path zo vo ao) (Pi: Path zi vi ai) :=
  forall t : R, 0 <= t1 -> Rmax t1 tb <= t <= te -> vmd <= zo t - zi t.

(*
Two aircraft with paths Po and Pi, each of which follows an arbitrary sequence
of independent maneuvers, where the motion of each aircraft for each
maneuver separately satisfies our safety predicate, and whose
horizontal motion create a single horizontal conflict interval from
[tb,te] are safely separated for all time because the Po aircraft is
always above the Pi aircraft by at least a distance hp.
*)
Lemma safely_above_for_m_maneuvers : (* index o above i *)
  forall {zo vo ao zi vi ai}
             t1 tb te vmd
         (Po: Path zo vo ao) (Pi: Path zi vi ai)
         (F : SafeFlt t1 tb te vmd Po Pi),
  forall t
         (t1ge0 : 0 <= t1)
         (thconflict : (Rmax t1 tb) <= t <= te),
    vmd <= zo t - zi t.
Proof.
  intros zo vo ao zi vi ai.
  apply (SafeFlt_ind zo vo ao zi vi ai P).

  (* inductive step Pi->Pi+1 *)
  intros until 0. intros Mo Mi vs Ft2 Pt2. unfold P in *.
  inversion Mo. clear vabove vatupper vwithin vatlower vbelow.
  intros t zlet1 tinterval.
  unfold Rmax, Rmin in *.
  destruct (Rle_dec t1 tb).
  destruct (Rle_dec t2 tb).
  assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tinterval).
  generalize (Rnot_le_gt _ _ n) as tbltt2; intros; clear n.
  apply Rgt_lt in tbltt2.
  generalize (Rtotal_order t t2) as trelt2'. intros.
  inversion trelt2' as [trelt2 | trelt2]; clear trelt2'.
  (****** use Φ **********************)
  assert (tb <= t <= t2) as tsubinterval. inversion tinterval. split; fourier.
  assert (t1 <= t < t2) as tmaneuver. inversion tinterval. split; fourier.
  destruct (Rle_dec (0 - t1) (tb - t1)).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tinterval vs).
  apply False_ind.
  apply n. Radd t1. setl 0. setr tb. fourier.
  (****************************)
  assert (t2 <= t <= te) as tsubinterval. inversion tinterval.
  split. inversion trelt2. rewrite H1. right. reflexivity. left. fourier. assumption.
  clear trelt2. assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tsubinterval).

  destruct (Rle_dec t2 tb).
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  assert (t1>t2). fourier.
  generalize (Rgt_not_le _ _ H).
  intro. apply False_ind. apply H0. assumption.
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  generalize (Rnot_le_gt _ _ n0) as t2lttb; intros; clear n0.
  apply Rgt_lt in t2lttb.

  generalize (Rtotal_order t t2) as trelt2'. intros.
  inversion trelt2' as [trelt2 | trelt2]; clear trelt2'.
  (****** use Φ **********************)
  assert (tb <= t <= t2) as tsubinterval. inversion tinterval. split; fourier.
  assert (tb <= t <= te) as tsubinterval2. inversion tinterval. split; fourier.
  assert (t1 <= t < t2) as tmaneuver. inversion tinterval. split; fourier.
  assert (0 <= t <= t2) as tsubinterval3. inversion tinterval. split; fourier.
  assert (0 <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  destruct (Rle_dec (0 - t1) (tb - t1)).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval2 vs).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval3 vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval4 vs).
  (****************************)
  assert (t2 <= t <= te) as tsubinterval. inversion tinterval.
  split. inversion trelt2. rewrite H1. right. reflexivity. left. fourier. assumption.
  clear trelt2. assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tsubinterval).

  (* base case P0 *)
  intros until 0. intros Mo Mi vs.
  unfold Poly.
  intros t zlet1 tinterval.
  unfold Rmax in *.
  destruct (Rle_dec t1 tb).
  assert (t1 <= t < te+1) as tsubinterval. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  destruct (Rle_dec (0-t1) (tb-t1)). clear r0.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval tinterval vs).
  assert (0 <= t <= te) as tinterval2. inversion tinterval. split; fourier.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval tinterval2 vs).
  
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  destruct (Rle_dec (0-t1) (tb-t1)).

  assert (0 <= tb) as t1letb. fourier. clear r.
  assert (tb <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  assert (t1 <= t < (te+1)) as tsubinterval5. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval5 tsubinterval4 vs).

  assert (0 <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  assert (t1 <= t < (te+1)) as tsubinterval5. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval5 tsubinterval4 vs).
Qed.

(*
This predicate describes a pair of aircraft following paths Po and
Pi, and an arbitrary sequence of maneuvers that satisfy our safety
predicates.
*)

Definition SafeFltAB {zo vo ao zi vi ai} t1 tb te hp
           (Po: Path zo vo ao) (Pi: Path zi vi ai) :=
  SafeFlt t1 tb te hp Po Pi \/ SafeFlt t1 tb te hp Pi Po.


(*
Two aircraft with paths Po and Pi, each of which follows an
arbitrary sequence of independent maneuvers, where the motion of each
aircraft for each maneuver separately satisfies our safety predicate,
and whose horizontal motion create a single horizontal conflict
interval from [tb,te] are safely separated vertically for all time by
at least a distance hp.
*)

Lemma own_safe_for_m_maneuvers :
  forall {zo vo ao zi vi ai}
         t1 tb te vmd
         (hppos : 0 < vmd)
         (Po: Path zo vo ao) (Pi: Path zi vi ai)
         (F : SafeFltAB t1 tb te vmd Po Pi),
  forall t
         (t1ge0 : 0 <= t1)
         (thconflict : (Rmax t1 tb) <= t <= te),
    vmd <= Rabs (zo t - zi t).
Proof.
  intros.
  unfold SafeFltAB in F.
  inversion_clear F.
  generalize (safely_above_for_m_maneuvers t1 tb te vmd Po Pi
                                           H t t1ge0 thconflict).
  intros. assert (zo t > zi t) as order. fourier.
  unfold Rabs.
  destruct (Rcase_abs (zo t - zi t)).
  apply False_ind.
  assert (zo t <= zi t). fourier.
  eapply Rlt_not_le. apply order. assumption.
  assumption.

  generalize (safely_above_for_m_maneuvers t1 tb te vmd Pi Po
                                           H t t1ge0 thconflict).
  intros. assert (zo t < zi t) as order. fourier.
  unfold Rabs.
  destruct (Rcase_abs (zo t - zi t)).
  setr (zi t - zo t).
  assumption.
  apply False_ind.
  assert (zi t <= zo t). fourier.
  eapply Rlt_not_le. apply order. assumption.
Qed.

(*
This predicate says if our aircraft follows path Po, and there are a
sequence of other paths possibly belonging to multiple aircraft who
come into horizontal conflict with us at a sequence of different time
intervals, where the motion of each aircraft for each maneuver
separately satisfies the safety predicate for us, the Pi aircraft is
safely separated from all the others vertically by at least a distance
hp during the horizontal conflict intervals guaranteeing no collisions.
*)

Record CI  := { tb:R; te:R; zi:R->R; vi:R->R; ai:R->R; Pi:Path zi vi ai}.

Inductive Ψ {zo vo ao } t1 vmd
          (Po: Path zo vo ao) : list CI -> Prop :=
| mtrj_intro : forall (q:CI) (r:list CI),
    SafeFltAB t1 (tb q) (te q) vmd Po (Pi q) ->
    Ψ t1 vmd Po r ->
    Ψ t1 vmd Po (q::r)
| mtrj_null : Ψ t1 vmd Po List.nil.


Inductive SeparateMulti {zo vo ao} t1 vmd
          (Po: Path zo vo ao) : list CI -> Prop :=
| smtrj_intro : forall (q:CI) (r:list CI),
    (forall t, (Rmax t1 (tb q)) <= t <= (te q) ->
    vmd <= Rabs (zo t - (zi q) t)) ->
    SeparateMulti t1 vmd Po r ->
    SeparateMulti t1 vmd Po (q::r)
| smtrj_null : SeparateMulti t1 vmd Po List.nil.


(* equation 10 in vert-paper.pdf *)
Theorem safely_separated_vertical_trajectories:
  forall {zo vo ao} t1 vmd cilst
         (Po: Path zo vo ao) (hppos : 0 < vmd) (t1pos : 0 <= t1),
    Ψ t1 vmd Po cilst ->
    SeparateMulti t1 vmd Po cilst.
Proof.
  intros until 0. intros hppos t1pos sfm.
  induction cilst.
  apply smtrj_null.
  inversion_clear sfm. 
  destruct a0. apply smtrj_intro.
  simpl in *.
  (*************)
  clear H0 IHcilst cilst.
  intros.
  apply (own_safe_for_m_maneuvers
         t1 tb0 te0 vmd hppos Po Pi0 H t t1pos H0).
  (*************)
  apply IHcilst; try assumption.
Qed.

