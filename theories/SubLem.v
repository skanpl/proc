Require Import Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.


(*            The problems in this file:
 i tried to prove the renaming lemma for the LTS (lt_sub) but i'm
 stuck on the bounded send cases. 
 In Sangiorgi's book (lemma 1.4.8), there's a side condition for bounded sends actions
 in the renaming lemma which i don't really see how we can express it here in a
 way that would make the proof work.  

 Given those technicalities, i guess proving a weaker version (lt_sub_weak) would
 probabilly be sufficient for proving that congruence is a bismulation so i don't 
 think that the actual renaming lemma is necessary for now.
 But in that lt_sub_weak lemma i tried to prove, i'm stuck on the Lt_open rule because
 of the side condition of the Lt_open rule. 

*)











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
(*-----------------------------------------------------------*)






Lemma lt_sub_weak: forall P Q a sigma, 
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
 
(*------- stuck -------------------*)  
destruct (IHlt (up sigma)).
destruct (sb_ch_canon (up sigma) x).
cbn in *.    
replace var_zero with 0 in *; auto.
(*------------------------*)




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
  
(*------- stuck -------------------*)
- eapply Lt_parL_bs. 
  eauto with picalc. 
  rewrite H0.  
  erewrite shift_permute_pr.
(*-------------------------------*)
















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




(* failed attempt:
Lemma lt_sub_bdsend: forall P Q a x sigma, 
  lt P a Q -> a=LbdSend x -> lt P[sigma][shift_sb] a[sigma] Q[sigma].
Proof.
intros.
generalize dependent sigma. 
induction H; inversion H0; cbn in *; intros.
rewrite H0 in H1. firstorder; inversion H1.
rewrite H0 in H1. firstorder; inversion H1.

firstorder.
rewrite H3 in *.
eapply Lt_parL_bs.
auto.
rewrite H1.    
erewrite shift_permute_pr.
do 3 erewrite sub_comp_pr.
assert (shift_sb >> subst_chan sigma = 
  sigma >> subst_chan (shift_sb >> subst_chan (up shift_sb))
).
unfold shift_sb, shiftn_sb.
unfold funcomp. fe. intro.
asimpl. 
unfold funcomp.
cbv. 
case (sigma x1). intro.
*)
