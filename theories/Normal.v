Require Export Semantics.
Require Export SubLem.

Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.


Notation ch x := x __chan.


Lemma invert_sb_send: forall x y P Q sigma, 
  (Send x y P) = Q[sigma] -> exists x0 y0 P0,  Q = Send x0 y0 P0.
Proof.
intros.
induction Q; cbn in *; eauto with picalc; inversion H.
Qed.

Lemma invert_sb_rcv: forall x P Q sigma, 
  (Rcv x P) = Q[sigma] -> exists x0 P0,  Q = Rcv x0 P0.
Proof.
intros.
induction Q; cbn in *; eauto with picalc; inversion H.
Qed.

Lemma invert_sb_par: forall P Q R sigma, 
  (Par P Q) = R[sigma] -> exists P0 Q0,  R = Par P0 Q0.
Proof.
intros.
induction R; cbn in *; eauto with picalc; inversion H.
Qed.




Definition super_bij (sigma: nat -> chan) := 
 (forall c, exists x, c = x[sigma])    /\
 (forall x y, x[sigma] = y[sigma]  -> x = y).


Lemma not_bdsend_sub_rev: forall a sigma,  
  not_bdsend (a[sigma]) -> not_bdsend a.
Proof.
intros.
destruct a; cbn in *; eauto with picalc.
firstorder; inversion H.
Qed.

Lemma invert_sb_lt: forall P P0 a Q sigma, lt P a Q -> 
  P = P0[sigma] -> super_bij sigma ->  
  exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P'. 
Proof.
intros. 
generalize dependent sigma.
generalize dependent P0.
induction H; intros.   
- set (lem:= invert_sb_send).
  specialize (lem _ _ _ _ _ H0).
  destruct lem. do 2 destruct H. subst. cbn in *.
  inversion H0. 
  eexists. exists (Lsend x0 x1). 
  split; eauto with picalc. 

-set (lem:= invert_sb_rcv).
  specialize (lem _ _ _ _ H0).
  destruct lem. destruct H as [p H]. subst. cbn in *.
  inversion H0.
  unfold super_bij in H1. destruct H1.
  assert (exists y0, y = y0[sigma]). eapply H.
  destruct H4 as [y0 H4].
  exists (p[y0 ..]). exists (Lrcv x0 y0). 
  split; cbn; try erewrite up_beta_simpl_pr; rewrite H4; eauto with picalc.

- set (lem:= invert_sb_par).
  specialize (lem _ _ _ _ H1).
  destruct lem as [P1 [Q1 lem]].  subst.
  cbn in H1. inversion H1. rewrite H4 in IHlt.
  specialize (IHlt P1 sigma eq_refl H2).
  destruct IHlt as [P'0 [a0 IHlt]].  destruct IHlt.
  destruct H6.  rewrite H3. 
  exists (Par P'0 Q1). eexists. split; eauto with picalc.
  split. apply H6. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in H6. rewrite H6. auto.

- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2).
  destruct IHlt as [P' [a0 IHlt]].
  destruct IHlt as [IHlt1 [IHlt2 IHlt3]].
  rewrite IHlt1.
  exists (Par p P'). repeat eexists. 
  eauto with picalc. 
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in IHlt2. rewrite IHlt2. auto.

 
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2).
  destruct IHlt as [p' [a0 IHlt]].
  destruct IHlt as [IHlt1 [IHlt2 IHlt3]].
  rewrite IHlt1. Print super_bij.

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

(*repris du fichier CongLtLemmabla.v, donc a facctoriser *)
Lemma down_rcv_notzero: forall a x y , 
  Lrcv x y = down a -> notinlab a (ch 0) ->
  a = Lrcv x[shift_sb] y[shift_sb].
Proof. 
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
inversion H0. destruct c; destruct c0.
destruct n; destruct n0; intuition. cbn.
replace (n-0) with n; auto with arith. replace (n0-0) with n0; auto with arith.
Qed.


(*repris du fichier CongLtLemmabla.v, donc a facctoriser *)
Lemma down_bs_notzero: forall x x0 , 
  LbdSend x = down (LbdSend x0) -> x0 <> (ch 0) ->
  x0 = x[shift_sb].
Proof. 
intros. unfold down in *.
cbn in H; inversion H; eauto with picalc.
destruct x0; destruct x. cbn.
destruct n; destruct n0; intuition. cbn.
replace (n-0) with n; auto with arith. replace (S n-1) with n; auto with arith.
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

 


Lemma ltsend_normal: forall Q Q' x y, 
  lt Q (Lsend x y)  Q' -> exists n R P,  
    cong Q (iter_nu n (Par (Send x[shiftn_sb n] y[shiftn_sb n] R) P) ) /\ 
    cong Q' (iter_nu n (Par R P) ).
Proof.
intros.
generalize dependent y.
generalize dependent x.
generalize dependent Q'.
induction Q; intros.
- inversion H.
     
- inversion H; subst; eauto with picalc.     
  + destruct (IHQ1  P' x y H2).  
    do 3 destruct H0.    
    do 3 eexists. split; eauto with picalc. 
    
  + firstorder; inversion H0; subst.
    destruct (IHQ2 Q'0 x0 x1 ). auto.
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
    rewrite lem in H1. asimpl in H1. rewrite lem in *.
    destruct (IHQ P' x[shift_sb] y[shift_sb]  H1).
    do 3 destruct H0.
    exists (S x0). repeat eexists. simpl in *.
	eapply Cg_ctxNu.
    do 2 erewrite shift_succ_ch.
    eauto with picalc.
    eauto with picalc.
  + symmetry in H3. 
    destruct (down_send (LbdSend x0) x y H3).
    destruct H0. inversion H0.    
Qed.


Lemma ltrcv_normal: forall Q Q' x y,
  lt Q (Lrcv x y) Q' ->  exists n R P,
    cong Q (iter_nu n (Par (Rcv x[shiftn_sb n] R) P) ) /\  
    cong Q' (iter_nu n (Par (R[y[shiftn_sb n]..]) P) ).
Proof.
intros.
generalize dependent y.
generalize dependent x.
generalize dependent Q'.
induction Q; intros.

- inversion H.

- inversion H; subst; eauto with picalc.     
  + destruct (IHQ1  P' x y H2).  
    do 3 destruct H0.    
    do 3 eexists. split; eauto with picalc. 
    
  + firstorder; inversion H0; subst.
    destruct (IHQ2 Q'0 x0 x1 ). auto.
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

- inversion H. subst. exists 0. 
  repeat eexists; unfold shiftn_sb; simpl. 
  replace (x[fun x0 : nat => ch x0]) with x; try asimpl; eauto with picalc.
  replace (y[fun x0 : nat => ch x0]) with y; try asimpl; eauto with picalc.
   
- inversion H.

- inversion H; subst; simpl in *; try symmetry in H3.
  + destruct (down_rcv (LbdSend x0) x y H3).
    destruct H0. inversion H0.
  + set (lem:= down_rcv_notzero a x y H4 H2).
    rewrite lem in H1. rewrite lem in *.
    destruct (IHQ P' x[shift_sb] y[shift_sb]  H1).
    do 3 destruct H0.
    exists (S x0). 
    repeat eexists; eapply Cg_ctxNu; erewrite shift_succ_ch; eauto with picalc.
  + destruct (down_rcv (LbdSend x0) x y H3).
    destruct H0. inversion H0.
Qed.


  



















(* /!\  DONT DELETE THIS  /!\
Lemma ltbdsend_normal: forall Q Q' x, 
  lt Q (LbdSend x)  Q' -> exists n R P,  
  cong Q ( iter_nu (S n) (Par (Send x[shiftn_sb (S n)] (ch 0)[shiftn_sb  n] R) P) ) 
    /\ 
  cong Q' (iter_nu n (Par R P) ).
Proof.
intros.
generalize dependent x.
generalize dependent Q'.
induction Q; intros.
- inversion H.
     
- inversion H; subst. 
 + firstorder; inversion H0.
 + firstorder; inversion H0.
 + 
    destruct (IHQ1 P' x). auto. simpl in *.
    do 3 destruct H0.
    repeat eexists. 
    eapply Cg_trans.  
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_ctxParL. apply H0.
    (*eapply Cg_parCom.*)
    eapply Cg_nuPar. 
    eauto with picalc.
    eauto with picalc. 
    eauto with picalc.  
+   destruct (IHQ2 Q'0 x). auto.
    do 3 destruct H0. 
    repeat eexists. 
    eapply Cg_trans.  
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H0.
    eapply Cg_parCom.
	eapply sc_extr_n.
    eapply nuN_ctx.    
    eapply Cg_parAssoc.
 
    eapply Cg_trans.  
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H1.
    eapply Cg_parCom.
	eapply sc_extr_n.
    erewrite shift_succ_pr. eapply Cg_refl.
 	eapply nuN_ctx.    
    eapply Cg_parAssoc.      

- inversion H.
- inversion H.
    
- inversion H; subst.
  + set (lem:= ltsend_normal Q Q' x0 (ch 0)).
	set (lemd:= down_bs_notzero x x0 H3 H2).
    rewrite lemd in *.
    specialize (lem H1).
    destruct lem as [n lem]. destruct lem as [R lem]. 
    destruct lem as [P lem]. destruct lem.
    set (lemm:= shift_succ_ch). symmetry in lemm.
    erewrite lemm in H0.
    repeat eexists; simpl; eauto with picalc. 
  + symmetry in H4. 
    destruct (down_bdsend a x H4). subst.
    firstorder; inversion H0. 
  + set (lem:= down_bs_notzero x x0 H3 H2). rewrite lem in *.  
    destruct (IHQ P' x[shift_sb] H1) as [n IH]. 
    destruct IH as [R IH]. destruct IH as [P IH]. destruct IH. 
    set (lemm:= shift_succ_ch x (S n)). symmetry in lemm.
    erewrite lemm in H0. 
    exists (S n). exists R. exists P. split. cbn in *.
    eapply Cg_ctxNu.
 
	admit.
     
    simpl. eapply Cg_ctxNu.
    eauto with picalc.
*)    
   

(*
Definition not_nu P := 
P = Zero \/
(exists Q R, P = Par Q R) \/
(exists x Q, P = Rcv x Q) \/
(exists x y Q, P = Send x y Q). 
*) 










(*
Theorem lttau_impl_red: forall P Q,
  lt P Ltau Q -> red P Q.
Proof.
intros. 
generalize dependent Q.
induction P; intros.

- inversion H.
- inversion H; subst; eauto with picalc.
+
set (rnlem := ltrcv_normal P2 Q' x y H3).
set (snlem := ltsend_normal P1 P' x y H2).
firstorder.
(*the derivation tree*)
eapply Red_struc.
*)







(*--------  reduction implies tau-tansition --------------------*)



Lemma cong_resp_lt: forall P Q P' Q' a, 
  cong P Q -> 
     (lt P a P'  -> exists Q0, lt Q a Q0 /\ cong P' Q0)  /\
      (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof. Admitted.


Lemma lt_res_tau_nuN: forall P P' n, lt P Ltau P' -> 
  lt (iter_nu n P) Ltau (iter_nu n P').
Proof.
intros. 
induction n; simpl; auto.
eapply Lt_res. apply IHn.
unfold notinlab. auto.
eauto with picalc.
eauto with picalc.
Qed.


Theorem red_impl_lt: forall P Q, red P Q -> 
  exists Q', lt P Ltau Q' /\ cong Q Q'.
Proof.
intros.
set (lem:= red_normal P Q). 
 
firstorder. 
assert(
lt
 (iter_nu x (Par (Par (Send x1 x2 x3) (Rcv x1 x4)) x0))
Ltau
 (iter_nu x (Par (Par x3 x4[x2..]) x0))
).
eapply lt_res_tau_nuN.
eapply Lt_parL.
eapply Lt_commL.
eapply Lt_send. 
eapply Lt_rcv.
eauto with picalc.
set (lem:= 
cong_resp_lt (iter_nu x (Par (Par (Send x1 x2 x3) (Rcv x1 x4)) x0)) P (iter_nu x (Par (Par x3 x4[x2..]) x0))  P Ltau 
). 
eapply Cg_sym in H0.
firstorder.
eexists; split; 
eauto with picalc.
Qed.
