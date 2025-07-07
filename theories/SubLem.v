Require Export Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.










(* If we have substitutions sigma1,sigma2: nat ->chan
and if we want to do the substitution sigma1 and then substitution sigma2,
we might want to write:
     sigma1 >> sigma2  
but that's actually wrong, and the correct way to write it is:
     sigma1 >> (subst_chan sigma2)
*)





(*autosubst generates 2 notations for the "channel of index x": "var_chan x" and
"x __chan". I don't like these notations, so i use the notation "ch x" instead.
*)

Notation ch x := x __chan.






Lemma not_bdsend_sub: forall a sigma,
  not_bdsend a -> not_bdsend (a[sigma]). 
Proof.
intros. 
induction a; cbn; eauto with picalc.
firstorder; inversion H.
Qed.




(*--------- pure substitution lemmas -----------*)
Lemma up_beta_simpl: forall (sigma: nat->chan) y,
  y.. >> subst_chan sigma = up sigma >> subst_chan (y[sigma]..).
Proof.
intros.
unfold funcomp.
fe. intro.
cbv.
case x, y; auto.
case (sigma x). intro. auto.
Qed.


Lemma shift_permute: forall (sigma: nat->chan),
  sigma >> subst_chan shift_sb = shift_sb >> subst_chan (up sigma).
Proof.
intros.
unfold funcomp.
fe. intro.
unfold shift_sb, shiftn_sb.
auto.
Qed.
(*---------- substitution lemma with processes  --------------------*)

Lemma sub_comp_pr: forall (P:proc) (sigma1 sigma2: nat -> chan), 
  P[sigma1][sigma2] = P [sigma1 >> subst_chan sigma2].
Proof.  
asimpl. auto.
Qed.

Lemma up_beta_simpl_pr: forall (sigma: nat->chan) (P:proc) y ,  
  P[y..][sigma] = P [up sigma] [y[sigma]..].
Proof.
intros.
do 2 erewrite sub_comp_pr.
erewrite up_beta_simpl. 
auto.
Qed.


Lemma shift_permute_pr: forall (sigma: nat->chan) (P:proc),
  P[sigma][shift_sb] = P[shift_sb][up sigma].
Proof.
intros.
do 2 erewrite sub_comp_pr.
erewrite shift_permute.
auto.
Qed.


Lemma shift_permute_lab: forall (sigma: nat->chan) (a:lab),
  a[sigma][shift_sb] = a[shift_sb][up sigma].
Proof.
intros.
asimpl. auto.
Qed.


(*-----------------------------------------------------------*)


 
Lemma not_bdsend_ad_impl_a_too: forall ad a, ad = down a -> 
  not_bdsend ad -> not_bdsend a.  
Proof.
intros.
destruct a; eauto with picalc.
cbn in H. rewrite H in H0. 
firstorder; inversion H0.
Qed.



Lemma zero_notin_lab_sb: forall a sigma,
  notinlab a (ch 0) -> notinlab a[up sigma] (ch 0).
Proof.
intros.  
destruct a; cbn; auto; try (split; inversion H).
 -destruct c. destruct n. auto. cbv.
  destruct (sigma n). firstorder. inversion H2.
 -destruct c0. destruct n. auto. cbv.
  destruct (sigma n).  firstorder. inversion H2.

 -destruct c. destruct n. auto. cbv.
  destruct (sigma n). firstorder. inversion H2.
 -destruct c0. destruct n. auto. cbv.
  destruct (sigma n).  firstorder. inversion H2.

 -destruct c. destruct n. auto.
  cbv. destruct (sigma n). firstorder. inversion H0.
Qed.





Lemma lt_sub: forall P Q a sigma, lt P a Q -> 
  (not_bdsend a -> lt P[sigma] a[sigma] Q[sigma]) /\
  ( forall x0, a = LbdSend x0 -> lt P[sigma] a[sigma] Q[up sigma] ).
Proof.
intros.
generalize dependent sigma. 
induction H; intros; cbn in *; split; intros; eauto with picalc.
  
- inversion H.

- erewrite up_beta_simpl_pr.
  eauto with picalc.

- inversion H.
 
- eapply Lt_parL.
  destruct (IHlt sigma).
  auto. eauto using not_bdsend_sub.

- subst. firstorder; inversion H0.
  
- eapply Lt_parR.
  destruct (IHlt sigma).
  auto. eauto using not_bdsend_sub.

- subst. firstorder; inversion H0.
  
- subst. firstorder; inversion H0.
  
- destruct (IHlt sigma).  
  set (lem:= H3 x0 H1).
  eapply Lt_parL_bs. 
  eauto with picalc.
  rewrite H0.
  erewrite shift_permute_pr.
  auto.
 
- subst. firstorder; inversion H0.

- destruct (IHlt sigma).  
  set (lem:= H3 x0 H1).
  eapply Lt_parR_bs. 
  eauto with picalc.
  erewrite H0.
  erewrite shift_permute_pr. 
  auto.

 
- destruct (IHlt1 sigma), (IHlt2 sigma).
  eauto with picalc.

- inversion H1. 

   
- destruct (IHlt1 sigma), (IHlt2 sigma).
  eauto with picalc.

- inversion H1.
   
- firstorder; subst; inversion H2.

- destruct (IHlt (up sigma)). subst. inversion H2. subst.
  (*destruct (sb_ch_canon (up sigma) x). rewrite H3 in *.*)
  destruct x. cbn in *.  replace var_zero with 0 in *; auto.
  (*assert (up (sigma (x-1) = *)
  eapply Lt_open.
  apply H3. 
  eauto with picalc. destruct n. exfalso. apply H0. reflexivity.
  simpl. unfold_funcomp. cbv. case (sigma n). intros. inversion H1.
  destruct n. exfalso. apply H0; auto.
  replace (S n - 1) with n; auto; try lia.
  cbn. unfold_funcomp. case (sigma n). intros. cbn.
  replace (n0-0) with n0; auto; lia.
 

- destruct (IHlt (up sigma)).
  eapply Lt_res.     
  apply H4. auto. 
  eauto using zero_notin_lab_sb.
  eauto using not_bdsend_sub.
  
(*--------tentative pour le down------*)
rewrite H2. 
unfold down.
asimpl.  
replace (0-1) with 0; try lia.
assert (↑ >> (fun x : nat => ch (x - 1)) = fun x => ch x).
unfold funcomp. fe. intro. cbn. 
replace (x-0) with x; try lia; auto.
rewrite H6.
assert (sigma >> subst_chan (fun x : nat => ch x) = sigma).
asimpl.  
unfold funcomp. cbv. fe. intro. destruct (sigma x). auto.
rewrite H7.
assert(
(fun x : nat => ch (x - 1)) >> subst_chan sigma =
ch 0 .: sigma
).
unfold funcomp, scons. fe. intro. destruct x.
replace (0-1) with 0; try lia. simpl.
(*---------------------------------------*)


- destruct (IHlt1 sigma), (IHlt2 (up sigma)).
  eapply Lt_closeL.
  eapply H3. auto.
  cbn in *; replace var_zero with 0 in *; auto.
  erewrite shift_permute_pr.
  eauto with picalc.
  inversion H1.


- destruct (IHlt1 (up sigma)), (IHlt2 sigma).
  eapply Lt_closeR.
  erewrite shift_permute_pr.
  eapply H2.
  eauto with picalc.
  eauto with picalc.
  inversion H1.
Qed.









(*-----------  maybe useless lemmas --------*)
Lemma sub_com_ch: forall c:chan, forall y sigma,
  c[y..][sigma] = c[up sigma][y[sigma]..].
Proof.
intros. asimpl. auto.
Qed.



Lemma sub_comp_ch: forall (c:chan) (sigma1 sigma2: nat -> chan), 
  c[sigma1 >> subst_chan sigma2] = c[sigma1][sigma2]  .
Proof. 
asimpl. auto.
Qed.



Lemma sub_com_ch_2: forall c:chan, forall y sigma, 
  c[y..][sigma] = c[up sigma][(y[sigma])..].
Proof.
intros. asimpl. auto.
Qed.
(*-------------------------------------------*)






