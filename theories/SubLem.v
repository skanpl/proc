Require Import Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.



Lemma not_bdsend_sub: forall a sigma,
  not_bdsend a -> not_bdsend (a[sigma]). 
Proof.
intros. 
induction a; cbn; eauto with picalc.
firstorder; inversion H.
Qed.



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

Lemma sub_comp_pr: forall (P:proc) (sigma1 sigma2: nat -> chan), 
  P[sigma1][sigma2] = P [sigma1 >> subst_chan sigma2].
Proof. 
asimpl. auto.
Qed.



Lemma sub_com_ch_2: forall c:chan, forall y sigma, 
  c[y..][sigma] = c[up sigma][(y[sigma])..].
Proof.
intros. asimpl. auto.
Qed.
(*-----------------------------------------------------------*)







(* attemps at proving the renaming lemma
Lemma up_exch: forall y:chan, forall sigma, 
  (y[up sigma]).. = up (y[sigma] ..).
Proof.
intros.
asimpl.
unfold funcomp.
asimpl.
unfold scons.
fe. intro.
case x.
cbv.
case y. intro.
case n. auto.
intro. case (sigma n0).
intro.


Lemma sub_com_pr_2: forall P:proc, forall y sigma, 
  P[y..][sigma] = P[up sigma][(y[sigma])..].
Proof.
intros. 
generalize dependent sigma.
generalize dependent y.
induction P; intros; cbn.
auto. 
erewrite IHP1, IHP2; auto. 

   
erewrite sub_com_ch.
do 2 erewrite sub_comp_pr. 
set (lem:= IHP y (up sigma)).
do 2 erewrite sub_comp_pr in lem.
try erewrite
symmetry in lem.
unfold subst_chan.

case c. intro. case (up sigma n).
unfold funcomp in *.
intro.



Lemma lt_sub: forall P Q a sigma, 
  lt P a Q -> lt P[sigma] a[sigma] Q[sigma].
Proof.
intros.
generalize dependent sigma.
induction H; intros; cbn; eauto with picalc.
asimpl.
eauto with picalc.


*)
