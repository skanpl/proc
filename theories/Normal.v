Require Export Semantics.
Require Export SubLem.

Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.


Notation ch x := x __chan.



(*------------------ rule extensions ----------------------------------*)
Proposition sc_extr_n: forall n P Q,
  cong (Par (iter_nu n P) Q)   (iter_nu n (Par P (Q[shiftn_sb n ]) )).
Proof.
intro n. induction n; intros. 
asimpl. eauto with picalc.

unfold shiftn_sb. simpl.
assert(
(fun x : nat => ch (S (n + x)) )=
fun x : nat => ch ((n+1)+x)
). fe. intro. 
replace (S (n+x)) with ((n+1)+x); try lia; auto.
rewrite H. replace (n+1) with (S n); try lia; auto.
replace (fun x : nat => ch (S n + x)) with (shiftn_sb (S n)); auto.

eapply Cg_trans.
eapply Cg_nuPar.
eapply Cg_trans. 
eapply Cg_trans.
eapply Cg_ctxNu. 
eapply (IHn P (Q[shift_sb])). 
erewrite shift_succ_pr. eapply Cg_refl.
eauto with picalc.
Qed.

Proposition nuN_ctx: forall P Q n, 
  cong P Q -> cong (iter_nu n P) (iter_nu n Q).
Proof.
intros P Q n.
induction n; intros; eauto with picalc; simpl.
eauto with picalc.
Qed.

Proposition nuN_zero: forall n, 
  cong (iter_nu n Zero) Zero.
Proof.
intro. induction n; simpl; eauto with picalc.
Qed.

Hint Resolve nuN_zero sc_extr_n nuN_ctx: picalc.
(*----------------- misc  ------------------------------*)

(*repris du fichier CongLtLemmabla.v, donc a facctoriser *)
Lemma down_send_notzero: forall a x y ,      
  Lsend x y = down a -> notinlab a (ch 0) ->
  a = Lsend x[shift_sb] y[shift_sb].
Proof. 
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
inversion H0. destruct c; destruct c0.
destruct n; destruct n0; intuition. cbn.
replace (n-0) with n; auto with arith. replace (n0-0) with n0; auto with arith.
Qed.

Lemma down_bdsend: forall a x , down a = LbdSend x -> 
  exists x', a = LbdSend x'.
Proof. 
intros. intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.

Lemma shift_succ_ch: forall (c:chan) n, 
  c[shiftn_sb (S n)] = c [shift_sb][shiftn_sb n].  
Proof.
intros.
unfold shift_sb, shiftn_sb.
asimpl. unfold funcomp.  
destruct c. cbn. auto.
Qed.

Lemma sb_comp_ch: forall (c:chan) sigma1 sigma2,
  c[sigma1][sigma2] = c[sigma1 >> subst_chan sigma2].
Proof.
intros. asimpl. auto.
Qed.

Lemma sb_ch_shift_simpl: forall (x: chan) n sigma, 
 x[sigma >> subst_chan shift_sb][shiftn_sb n] = x [sigma][shiftn_sb (S n)].
Proof.
intros. replace (x[sigma >> subst_chan shift_sb]) with (x [sigma][shift_sb]).
erewrite shift_succ_ch. auto. asimpl. auto.
Qed.
(*------------------------------------------------------*)





Lemma red_normal: forall P Q ,
  red P Q -> exists n S x y R1 R2 , 
    cong P  (iter_nu n  (Par  (Par (Send x y R1) (Rcv x R2))    S) ) 
     /\
    cong Q  (iter_nu n  (Par (Par R1 (R2 [y..])  )   S)) .
Proof.
intros.
induction H; firstorder.
- (*how do you factor this out?*)
  exists x. repeat eexists.  
  eapply Cg_trans. 
  eapply Cg_trans. 
  eapply Cg_ctxParL. apply H0. 
  eapply sc_extr_n.
  eapply nuN_ctx.
  eapply Cg_parAssoc.

  eapply Cg_trans. 
  eapply Cg_trans. 
  eapply Cg_ctxParL. apply H1. 
  eapply sc_extr_n.
  eapply nuN_ctx. 
  eapply Cg_parAssoc.

- exists x. 
  repeat eexists; eauto with picalc.

- exists 0. 
  repeat eexists; simpl; eauto with picalc.

- exists (S x). 
  repeat eexists; simpl; eauto with picalc.
Qed.




Lemma ltsend_normal: forall Q Q' x y sigma, 
  lt Q (Lsend x[sigma] y[sigma])  Q' -> exists n R S,  
    cong Q (iter_nu n (Par (Send x[sigma][shiftn_sb n] y[sigma][shiftn_sb n] R) S) ) /\ 
    cong Q' (iter_nu n (Par R S) ).
Proof.
intros.
generalize dependent sigma.
generalize dependent Q'.
induction Q; intros.
- inversion H.
     
- inversion H; subst; eauto with picalc.     
  + destruct (IHQ1  P' sigma H2).  
    do 3 destruct H0.    
    do 3 eexists. split; eauto with picalc. 
    
  + firstorder; inversion H0.
    destruct (IHQ2 Q'0 sigma ). auto.
    do 3 destruct H1.
    repeat eexists. 
    eapply Cg_trans.  
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H1.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
    
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H5.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
        
- inversion H.
   
- inversion H. subst.   
  exists 0. repeat eexists; simpl. 
  unfold shiftn_sb. cbn.
  assert(forall z: chan, z[sigma][fun x0 : nat => x0 __chan] =
   z[sigma]
  ). asimpl. auto. do 2 erewrite H0.
   eauto with picalc. eauto with picalc.
  
- inversion H; subst.
  + symmetry in H3.  
    destruct (down_send (LbdSend x0) x[sigma] y[sigma] H3).
    destruct H0. inversion H0.
  + set (lem:= down_send_notzero a x[sigma] y[sigma] H4 H2).
    rewrite lem in H1. asimpl in H1.
    destruct (IHQ P' (sigma >> subst_chan shift_sb) H1).
    do 3 destruct H0.
    exists (S x0). repeat eexists. simpl in *.
	eapply Cg_ctxNu.
    do 2 erewrite sb_ch_shift_simpl in H0.
    do 2 erewrite sb_comp_ch in H0.
    eauto with picalc.
    eauto with picalc.
  + symmetry in H3. 
    destruct (down_send (LbdSend x0) x[sigma] y[sigma] H3).
    destruct H0. inversion H0.    
Qed.





















(* here is why not having a renaming on the labels would get us stuck:
Lemma ltsend_normal: forall Q Q' x y, 
  lt Q (Lsend x y)  Q' -> exists n R S,  
    cong Q (iter_nu n (Par (Send x[shiftn_sb n] y[shiftn_sb n] R) S) ) /\ 
    cong Q' (iter_nu n (Par R S) ).
Proof.
intros.
generalize dependent Q'.
induction Q; intros.
- inversion H.
     
- inversion H; subst; eauto with picalc.     
  + destruct (IHQ1  P' H2).  
    do 3 destruct H0.    
    do 3 eexists. split; eauto with picalc. 
    
  + firstorder; inversion H0. subst.
    destruct (IHQ2 Q'0 ). auto.
    do 3 destruct H1.
    repeat eexists. 
    eapply Cg_trans.  
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H1.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
    
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H3.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
        
- inversion H.
   
- inversion H. subst.   
  exists 0. repeat eexists; simpl. 
  unfold shiftn_sb. cbn.
  assert(forall z: chan, z[fun x0 : nat => x0 __chan] =
   z
  ). asimpl. auto. do 2 erewrite H0.
   eauto with picalc. eauto with picalc.
  
- inversion H; subst.
  + symmetry in H3.  
    destruct (down_send (LbdSend x0) x y H3).
    destruct H0. inversion H0.
  + set (lem:= down_send_notzero a x y H4 H2).
    rewrite lem in H1.
       (*the reason why we would be stuck if we didn't have the sigma*) 
    destruct (IHQ P' (sigma >> subst_chan shift_sb) H1).
    do 3 destruct H0.
    exists (S x0). repeat eexists. simpl in *.
	eapply Cg_ctxNu.
    do 2 erewrite sb_ch_shift_simpl in H0.
    do 2 erewrite sb_comp_ch in H0.
    eauto with picalc.
    eauto with picalc.
  + symmetry in H3. 
    destruct (down_send (LbdSend x0) x[sigma] y[sigma] H3).
    destruct H0. inversion H0.    
Qed.
*)

