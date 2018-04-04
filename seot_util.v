Require Import Reals.
Require Import Coq.Reals.Rdefinitions. 
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Fourier.
Local Open Scope R_scope.



Lemma derive_decreasing_interv :
  forall (a b:R) (f:R -> R) (pr:derivable f),
    a < b ->
    (forall t:R, a < t < b -> derive_pt f t (pr t) < 0) ->
    forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f y < f x.
  intros.
  set (g := ( - f)%F).
  assert (derivable g) as prg.
  unfold g. reg.
  assert (forall t : R, a < t < b -> 0 < derive_pt g t (prg t)).
  intros. unfold g.
  unfold derive_pt, proj1_sig.
  destruct (prg t).
  generalize (H0 t H4).
  intros.
  unfold derive_pt, proj1_sig in H5.
  destruct (pr t).
  unfold g in d.
  unfold derivable_pt_abs in d0, d.
  generalize (derivable_pt_lim_opp _ _ _ d0).
  intros.
  generalize (uniqueness_limite _ _ _ _ d H6).
  intros.
  rewrite H7.
  apply Ropp_0_gt_lt_contravar.
  trivial.
  apply Ropp_lt_cancel.
  change (g x < g y).
  apply (derive_increasing_interv a b g prg H H4 x y H1 H2 H3).
Qed.


Ltac fieldrewrite a b :=
  let name := fresh "ident" in
  assert (a = b) as name; [field | rewrite name; clear name].
 


Ltac establish_deriv2 f' f'expr f :=
  let fe := fresh "fe" in
  set (f' := f'expr);
  assert (derivable f) ;
  [unfold f; reg |
   match goal with
   | [ H : derivable f |- _ ] =>
     assert (forall x, derive f H x = f' x) ;
       [unfold f, f', fct_cte, plus_fct, mult_fct, pow_fct, pow, comp, minus_fct, id, opp_fct, derive; intros; reg;
        unfold f' (*, fct_cte, plus_fct, mult_fct, pow_fct, pow, comp, minus_fct, id, opp_fct*);
        field |
        match goal with
          | [H0 : forall x, derive f H x = f' x |- _ ] =>
            generalize (functional_extensionality (derive f H) f' H0);
              intro fe; clear H0
        end]
   end].

Create HintDb ltdb.
Hint Resolve Rle_trans : ltdb.

Ltac bnds := eauto with ltdb.

  Ltac Radd n :=
    match goal with
      | [|- ?a < ?b] => apply (Rplus_lt_reg_r n)
      | [|- ?a <= ?b] => apply (Rplus_le_reg_r n)
      | [|- ?a > ?b] => apply Rlt_gt; Radd n
      | [|- ?a >= ?b] => apply Rle_ge; Radd n
      | [|- ?a = ?b] => apply (Rplus_eq_reg_l n)
    end.

  Ltac setr e :=
    match goal with
      | [|- (?op ?a ?b) ] =>
        assert (b = e) as beq0; 
        [ try unfold Rsqr, pow; field | rewrite beq0; clear beq0]
    end.

  Ltac setl e :=
    match goal with
      | [|- (?op ?a ?b) ] =>
        assert (a = e) as beq0; 
        [ try unfold Rsqr, pow; field | rewrite beq0; clear beq0]
    end.
  

Local Close Scope R_scope.
