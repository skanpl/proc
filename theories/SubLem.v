Require Import Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.




(* Si on a deux substitutions sigma1,sigma2: nat ->chan
pour faire la substi sigma1 puis la substi sigma2,
on aurait envie d'écrire :
  sigma1 >> sigma2  
mais en réalité il faut écrire:
  sigma1 >> (subst_chan sigma2)
*)







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
(*-----------------------------------------------------------*)



Lemma lt_sub: forall P Q a sigma, 
  lt P a Q -> lt P[sigma] a[sigma] Q[sigma].
Proof.
intros.
generalize dependent sigma.
induction H; intros; cbn in *; eauto with picalc.
- erewrite up_beta_simpl_pr.
  eauto with picalc.
 
- eapply Lt_parL.
  eauto with picalc.
  eauto using not_bdsend_sub.

- eapply Lt_parR.
  eauto with picalc.
  eauto using not_bdsend_sub.
  
- eapply Lt_parL_bs. 
  eauto with picalc. 
  rewrite H0.  
  erewrite shift_permute_pr.
(*TODO/TOFINISH*)














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




(*
Lemma lt_sub: forall P Q a sigma, 
  lt P a Q -> exists Q', lt P[sigma] a[sigma] Q'.
Proof.
intros. 
generalize dependent sigma.
induction H; intros; cbn in *.
eauto with picalc.
eauto with picalc.

destruct (IHlt sigma).
eexists.
eapply Lt_parL.
eauto with picalc. 
eauto using not_bdsend_sub.


destruct (IHlt sigma).
eexists.
eapply Lt_parR.
eauto with picalc.
eauto using not_bdsend_sub.


destruct (IHlt sigma). 
eauto with picalc.

destruct (IHlt sigma).
eauto with picalc.


destruct (IHlt1 sigma).
destruct (IHlt2 sigma).
eauto with picalc.

destruct (IHlt1 sigma).
destruct (IHlt2 sigma).
eauto with picalc.
 
(*!!!!!TODO/TOFINISH!!!!!!!*)  
destruct (IHlt (up sigma)).
destruct (sb_ch_canon (up sigma) x).
cbn in *.    
replace var_zero with 0 in *; auto.
(*!!!!!!!!!!!!!!!!!!!!!!!*)

*)



