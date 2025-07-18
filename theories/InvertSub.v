Require Export Semantics.
Require Export SubLem.

Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.


Notation ch x := x __chan.




(*---------  injection/surjection   ----------------------------*)
Definition super_bij (sigma: nat -> chan) := 
 (forall c, exists x, c = x[sigma])    /\
 (forall x y, x[sigma] = y[sigma]  -> x = y).


Definition injective (sigma: nat -> chan) := 
 forall x y, x[sigma] = y[sigma]  -> x = y.

Definition surjective (sigma: nat -> chan) := 
 forall c, exists x, c = x[sigma].


Lemma lift_preserve_inj: forall sigma, 
  injective sigma -> injective (up sigma).
Proof.
unfold injective in *. intros.
destruct x, y. destruct n, n0; auto.

-cbv in H0.
 destruct (sigma n0).
 inversion H0.

-cbv in H0.
 destruct (sigma n).
 inversion H0.

-cbv in H0.
 specialize (H (ch n) (ch n0)).
 cbn in H.
 destruct (sigma n), (sigma n0).
 inversion H0. rewrite H2 in H.
 specialize (H eq_refl).
 inversion H. auto.
Qed.
(*----  inversion of the substituted process  ------------------*)
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

Lemma invert_sb_nu: forall P Q sigma, 
  (Nu P) = Q[sigma] -> exists P0,  Q = Nu P0.
Proof.
intros.
induction Q; cbn in *; eauto with picalc; inversion H.
Qed.
(*------  inversion of the substituted label  ---------------*)
Lemma sb_bdsend: forall a x sigma,  LbdSend x = a[sigma] -> 
  exists x', a = LbdSend x'.
Proof. 
intros. intros.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.

Lemma sb_send: forall a x y sigma,  Lsend x y = a[sigma] -> 
  exists x' y', a = Lsend x' y'.
Proof. 
intros. intros.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.

Lemma sb_rcv: forall a x y sigma,  Lrcv x y = a[sigma] -> 
  exists x' y', a = Lrcv x' y'.
Proof. 
intros. intros.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.
(*----------  maybe useless lemmas  ---------------------*)
Lemma not_bdsend_sub_rev: forall a sigma,  
  not_bdsend (a[sigma]) -> not_bdsend a.
Proof.
intros.
destruct a; cbn in *; eauto with picalc.
firstorder; inversion H.
Qed.

Lemma subst_constr: forall sigma k, sigma k = (ch k)[sigma].
Proof.
auto.
Qed.

Lemma shift_equiv: subst_chan (S >> Semantics.ch) = subst_chan shift_sb.
Proof.
auto.
Qed.

Lemma shift_inj: forall x y, 
  (subst_chan shift_sb) x = (subst_chan shift_sb) y -> x = y. 
Proof.
intros.
destruct x,y. destruct n,n0; cbn in *; auto; unfold shift_sb, shiftn_sb in *; simpl in H; inversion H.
auto.
Qed.

Lemma shift_nonzero: forall x, (subst_chan shift_sb) x <> ch 0.
Proof.
intros. intro.
destruct x. cbn in H.
unfold shift_sb, shiftn_sb in H.
inversion H.
Qed.
(*--------------- down stuff   -----------------------------------*)
Definition down_sb := fun x => ch (x-1).

Lemma down_permute_ch: forall x sigma, x<>ch 0 -> 
  x[down_sb][sigma] = x[up sigma][down_sb].
Proof.
intros.
destruct x,n. exfalso. apply H. auto.
cbn.  replace (n-0) with n; try lia; auto.
asimpl. unfold funcomp.  destruct (sigma n).
unfold down_sb. 
assert(
(fun x : nat => ch (↑ x - 1))
= fun x:nat => ch x
). fe. intro. 
replace ↑ with S; auto.
replace (S x - 1) with x; try lia; auto.
rewrite H0. auto.
Qed.

Lemma down_permute_lab: forall a sigma, notinlab a (ch 0)-> 
  a[down_sb][sigma] = a[up sigma][down_sb].
Proof.
intros. 
destruct a; cbn in *; auto.

destruct H.
erewrite down_permute_ch. erewrite down_permute_ch. auto.
intro. symmetry in H1. apply (H0 H1).
intro. symmetry in H1. apply (H H1).
  
destruct H.
erewrite down_permute_ch. erewrite down_permute_ch. auto.
intro. symmetry in H1. apply (H0 H1).
intro. symmetry in H1. apply (H H1).

erewrite down_permute_ch. auto.
intro. symmetry in H0. apply (H H0).
Qed.

(* repris de CongLtLemmabla.v donc a factoriser *)
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

(*-----a converse to an obvious lemma  -------------------*)
Lemma notinlabup: forall a sigma, 
  notinlab a[up sigma] (ch 0) ->  notinlab a (ch 0). 
Proof.
intros.
destruct a; cbn in *; auto.
- destruct H. split. 
  * intro. clear H0.
    unfold up in *.
    unfold funcomp, scons in *.
    cbv in *.
    destruct c, n. auto.
    destruct (sigma n). inversion H1.
  * intro. clear H.
    unfold up in *.
    unfold funcomp, scons in *.
    cbv in *.
    destruct c0, n. auto.
    destruct (sigma n). inversion H1.
- destruct H. split.
  * intro. clear H0.
    unfold up in *.
    unfold funcomp, scons in *.
    cbv in *.
    destruct c, n. auto.
    destruct (sigma n). inversion H1.
  * intro. clear H.
    unfold up in *.
    unfold funcomp, scons in *.
    cbv in *.
    destruct c0, n. auto.
    destruct (sigma n). inversion H1.
- intro. 
  unfold up in *.
  unfold funcomp, scons in *.
  cbv in *.
  destruct c, n. auto.
  destruct (sigma n). inversion H0.
Qed.
(*----------------------------------------------------------*)
 
 (*  Here are all the attemps so far for proving "mapN_lts_rev" *)     


















(* DNW bcs the necessary premises are also a pain 

Lemma invert_sb_lt: forall P P0 a Q sigma, lt P a Q -> P = P0[sigma] -> 
 (forall x y, a = Lrcv x y -> surjective sigma -> 
    exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P') 
         /\
  ( forall x y, (a = Lsend x y \/a= Ltau) -> injective sigma  ->
    exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P') 
         /\
  (forall x0, a = LbdSend x0 -> injective sigma  -> 
     exists P' a0, Q = P'[up sigma] /\  a = a0[sigma] /\  lt P0 a0 P') . 
*)








(*==========   this is the "by individual actions" attempt    ===============*)

(* it seems like for tau-actions, we need to have the inversion for
   both senders and receptors in order to proceed in the proof and the IH cannot be used   as it's protected by the condition that the action must be a tau-action.
  so i decided to prove first the inversion for send and receive actions.
  It appears that for the send version, no conditions on sigma is necessary. 
  While for the receive version, we need to require surjectivity on sigma but
  that requirement also makes us stuck since lifting doesn't seem to preserve
  surjectivity.
*)


Lemma invert_sblt_send: forall P P0 a Q sigma x y, a = Lsend x y -> lt P a Q  -> 
  P = P0[sigma] -> 
  exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P'. 
Proof.
intros P P0 a Q sigma x y Hlsend Hlt Hsb.
generalize dependent x.
generalize dependent y.
generalize dependent sigma.
generalize dependent P0.
induction Hlt; intros; inversion Hlsend.   
- set (lem:= invert_sb_send).
  specialize (lem _ _ _ _ _ Hsb).  
  destruct lem as [xp [yp [p lem]]].  subst. cbn in *.
  inversion Hsb. 
  repeat eexists; eauto with picalc; cbn; auto. 


- set (lem:= invert_sb_par _ _ _ _ Hsb).
  destruct lem as [p [q lem]].  subst.
  cbn in Hsb. inversion Hsb. subst. 
  specialize (IHHlt p sigma eq_refl _ _ eq_refl). 
  destruct IHHlt as [p' [a0 IHHlt]].  
  destruct IHHlt as [G1 [G2 G3]].
  rewrite G1. 
  exists (Par p' q). eexists. split; eauto with picalc.
  split. apply G2. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in G2. rewrite G2. auto.

- set (lem:= invert_sb_par _ _ _ _ Hsb).  
  destruct lem as [p [q lem]]. subst. cbn in Hsb.
  inversion Hsb. subst.
  specialize (IHHlt q sigma eq_refl _ _ eq_refl). 
  destruct IHHlt as [q' [a0 IHHlt]].
  destruct IHHlt as [G1 [G2 G3]]. 
  rewrite G1.
  exists (Par p q'). repeat eexists. 
  eauto with picalc.  
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma). 
  symmetry in G2. rewrite G2. auto.
 
- subst. destruct (down_send (LbdSend x) x0 y). 
  auto. destruct H0. inversion H0.

- set (lem := invert_sb_nu  _ _ _ Hsb).
  destruct lem as [p lem]. subst. 
  cbn in Hsb. inversion Hsb. subst.
  specialize (IHHlt p _ eq_refl). 
  set (lem := down_send a x y Hlsend). 
  destruct lem as [x0 [y0 lem]]. specialize (IHHlt _ _ lem).
  destruct IHHlt as [p' [a0 IHHlt]].  
  destruct IHHlt as [G1 [G2 G3]]. rewrite G2 in Hlsend.


  unfold down in Hlsend. 
  replace (fun x : nat => ch (x - 1)) with down_sb in Hlsend; auto.
  symmetry in Hlsend.
  rewrite Hlsend. rewrite G1.
  rewrite G2 in H.
  exists (Nu p'). exists (a0[down_sb]).  
  repeat eexists; cbn; eauto with picalc.
  erewrite down_permute_lab. auto. 
  eapply notinlabup. apply H.
  eapply Lt_res. apply G3. 
  eapply notinlabup. apply H.
  rewrite G2 in H0.
  eapply not_bdsend_sub_rev. apply H0.
  auto.

- subst. destruct (down_send (LbdSend x) x0 y). 
  auto. destruct H0. inversion H0.
Qed.


Lemma invert_sblt_rcv: forall P P0 a Q sigma x y, a = Lrcv x y -> lt P a Q  -> 
  P = P0[sigma] -> surjective sigma  -> 
  exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P'. 
Proof.
intros P P0 a Q sigma x y Hlrcv Hlt Hsb Hsurj.
generalize dependent x.
generalize dependent y.
generalize dependent sigma.
generalize dependent P0.
induction Hlt; intros; inversion Hlrcv.   
-set (lem:= invert_sb_rcv).
  specialize (lem _ _ _ _ Hsb).
  destruct lem as [xp [p lem]]. subst. cbn in *.
  inversion Hsb.
  (*note that we used surjectivity here*)
  unfold surjective in Hsurj. 
  assert (exists yp, y0 = yp[sigma]). eapply Hsurj. 
  destruct H as [yp H].
  exists (p[yp ..]). exists (Lrcv xp yp). 
  split; cbn; try erewrite up_beta_simpl_pr; rewrite H; eauto with picalc.
- set (lem:= invert_sb_par _ _ _ _ Hsb).
  destruct lem as [p [q lem]].  subst.
  cbn in Hsb. inversion Hsb. subst. 
  specialize (IHHlt p sigma eq_refl Hsurj _ _ eq_refl). 
  destruct IHHlt as [p' [a0 IHHlt]].  
  destruct IHHlt as [G1 [G2 G3]].
  rewrite G1. 
  exists (Par p' q). eexists. split; eauto with picalc.
  split. apply G2. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in G2. rewrite G2. auto.

- set (lem:= invert_sb_par _ _ _ _ Hsb).  
  destruct lem as [p [q lem]]. subst. cbn in Hsb.
  inversion Hsb. subst.
  specialize (IHHlt q sigma eq_refl Hsurj _ _ eq_refl). 
  destruct IHHlt as [q' [a0 IHHlt]].
  destruct IHHlt as [G1 [G2 G3]]. 
  rewrite G1.
  exists (Par p q'). repeat eexists. 
  eauto with picalc.  
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma). 
  symmetry in G2. rewrite G2. auto.

- subst. destruct (down_rcv (LbdSend x) x0 y). 
  auto. destruct H0. inversion H0.

- set (lem := invert_sb_nu  _ _ _ Hsb).
  destruct lem as [p lem]. subst. 
  cbn in Hsb. inversion Hsb. subst . admit.
  (*
  specialize (IHHlt p _ eq_refl Hsurj). 
  set (lem := down_rcv a x y Hlsend). 
  destruct lem as [x0 [y0 lem]]. specialize (IHHlt _ _ lem).
  destruct IHHlt as [p' [a0 IHHlt]].  
  destruct IHHlt as [G1 [G2 G3]]. rewrite G2 in Hlsend.
  unfold down in Hlsend. 
  replace (fun x : nat => ch (x - 1)) with down_sb in Hlsend; auto.
  symmetry in Hlsend.
  rewrite Hlsend. rewrite G1.
  rewrite G2 in H.
  exists (Nu p'). exists (a0[down_sb]).  
  repeat eexists; cbn; eauto with picalc.
  erewrite down_permute_lab. auto. 
  eapply notinlabup. apply H.
  eapply Lt_res. apply G3. 
  eapply notinlabup. apply H.
  rewrite G2 in H0.
  eapply not_bdsend_sub_rev. apply H0.
  auto.

- subst. destruct (down_rcv (LbdSend x) x0 y). 
  auto. destruct H0. inversion H0. *)
Admitted.


(* /!\ for tau*)   
Lemma invert_sblt_tau: forall P P0 a Q sigma, a = Ltau -> lt P a Q  -> 
  P = P0[sigma] -> injective sigma  -> 
  exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P'. 
Proof.
intros P P0 a Q sigma Hltau Hlt Hsb Hinj.
generalize dependent sigma.
generalize dependent P0.
induction Hlt; intros; inversion Hltau.   

- set (lem:= invert_sb_par _ _ _ _ Hsb).
  destruct lem as [p [q lem]].  subst.
  cbn in Hsb. inversion Hsb. subst. 
  specialize (IHHlt eq_refl p sigma eq_refl Hinj). 
  destruct IHHlt as [p' [a0 IHHlt]].  
  destruct IHHlt as [G1 [G2 G3]].
  rewrite G1. 
  exists (Par p' q). eexists. split; eauto with picalc.
  split. apply G2. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in G2. rewrite G2. auto.

- set (lem:= invert_sb_par _ _ _ _ Hsb).  
  destruct lem as [p [q lem]]. subst. cbn in Hsb.
  inversion Hsb. subst.
  specialize (IHHlt eq_refl q sigma eq_refl Hinj). 
  destruct IHHlt as [q' [a0 IHHlt]].
  destruct IHHlt as [G1 [G2 G3]]. 
  rewrite G1.
  exists (Par p q'). repeat eexists. 
  eauto with picalc.  
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma). 
  symmetry in G2. rewrite G2. auto.

 
- set (lem:= invert_sb_par _ _ _ _ Hsb).  
  destruct lem as [p [q lem]]. subst. cbn in Hsb.
  inversion Hsb. subst. admit.
  (*
  specialize (IHHlt1 _ _ eq_refl Hsb). destruct IHlt1.
  specialize (IHHlt2 _ _ eq_refl Hsb). destruct IHlt2.
  *)
Admitted.



(*========== attempt requiring sigma to be a bijection   ===============*)

Lemma invert_sb_lt: forall P P0 a Q sigma, lt P a Q -> 
  P = P0[sigma] -> super_bij sigma ->  
  (not_bdsend a -> exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P') /\
  (forall x0, a = LbdSend x0 ->  exists P' a0, Q = P'[up sigma] /\  a = a0[sigma] /\  lt P0 a0 P') . 
Proof.
intros. 
generalize dependent sigma.
generalize dependent P0.
induction H; split; intros.   
- set (lem:= invert_sb_send).
  specialize (lem _ _ _ _ _ H0).
  destruct lem. do 2 destruct H2. subst. cbn in *.
  inversion H0. 
  eexists. exists (Lsend x0 x1). 
  split; eauto with picalc. 
- inversion H.


-set (lem:= invert_sb_rcv).
  specialize (lem _ _ _ _ H0).
  destruct lem. destruct H2 as [p H2]. subst. cbn in *.
  inversion H0.
  (*note that we used surjectivity here*)
  unfold super_bij in H1. destruct H1.
  assert (exists y0, y = y0[sigma]). eapply H1. 
  destruct H5 as [y0 H5].
  exists (p[y0 ..]). exists (Lrcv x0 y0). 
  split; cbn; try erewrite up_beta_simpl_pr; rewrite H5; eauto with picalc.
- inversion H. 

- set (lem:= invert_sb_par _ _ _ _ H1).
  destruct lem as [P1 [Q1 lem]].  subst.
  cbn in H1. inversion H1. rewrite H5 in IHlt.
  specialize (IHlt P1 sigma eq_refl H2). 
  destruct IHlt.  specialize (H4 H3).
  destruct H4 as [P'0 [a0 H4]].  
  destruct H4 as [G1 [G2 G3]].
  rewrite G1. 
  exists (Par P'0 Q1). eexists. split; eauto with picalc.
  split. apply G2. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in G2. rewrite G2. auto.
- subst; firstorder; inversion H0.

- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 H3). destruct H4 as [P'[a0 H4]]. 
  destruct H4 as [G1 [G2 G3]]. 
  rewrite G1.
  exists (Par p P'). repeat eexists. 
  eauto with picalc.  
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma). 
  symmetry in G2. rewrite G2. auto.
- subst; firstorder; inversion H0.

- firstorder; inversion H3. 
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 _ eq_refl).
  destruct H4 as [p' [a0 H4]].
  destruct H4 as [G1 [G2 G3]].
  rewrite G1.
  exists (Par p' q[shift_sb]). repeat eexists.
  cbn. erewrite shift_permute_pr. auto.
  apply G2. 
  destruct (sb_bdsend _ _ _ G2). rewrite H4 in *.
  eauto with picalc.

- firstorder; inversion H3.
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 _ eq_refl).
  destruct H4 as [q' [a0 H4]].
  destruct H4 as [G1 [G2 G3]].
  rewrite G1.
  exists (Par p[shift_sb] q'). repeat eexists.
  cbn. erewrite shift_permute_pr. auto.
  apply G2. 
  destruct (sb_bdsend _ _ _ G2). rewrite H4 in *.
  eauto with picalc.
    
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt1 _ _ eq_refl H2). destruct IHlt1.
  specialize (IHlt2 _ _ eq_refl H2). destruct IHlt2.
  clear H7 H5 H3.
  assert (not_bdsend (Lsend x y)); eauto with picalc.
  assert (not_bdsend (Lrcv x y)); eauto with picalc.
  specialize (H6 H5). specialize (H4 H3). clear H3 H5.
  destruct H4 as [p' [a0 H4]]. destruct H6 as [q' [b0 H6]].
  destruct H4 as [F1 [F2 F3]]. destruct H6 as [G1 [G2 G3]].   
  subst. 
  exists (Par p' q'). exists Ltau. cbn. split; eauto with picalc. 
  split. auto. 
  destruct (sb_send _ _ _ _ F2). destruct (sb_rcv _ _ _ _ G2). 
  destruct H3. destruct H4. subst. cbn in *.
  inversion F2. inversion G2. subst.
  (*note that we used injectivity here*)
  unfold super_bij in H2. destruct H2.
  assert (x0 = x1).  apply H3. auto.
  assert (x2 = x3).  apply H3. auto. 
  subst. eauto with picalc.
- inversion H3.


- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt1 _ _ eq_refl H2). destruct IHlt1.
  specialize (IHlt2 _ _ eq_refl H2). destruct IHlt2.
  clear H7 H5 H3.
  assert (not_bdsend (Lsend x y)); eauto with picalc.
  assert (not_bdsend (Lrcv x y)); eauto with picalc.
  specialize (H4 H5). specialize (H6 H3). clear H3 H5.
  destruct H4 as [p' [a0 H4]]. destruct H6 as [q' [b0 H6]].
  destruct H4 as [F1 [F2 F3]]. destruct H6 as [G1 [G2 G3]].   
  subst. 
  exists (Par p' q'). exists Ltau. cbn. split; eauto with picalc. 
  split. auto. 
  destruct (sb_send _ _ _ _ G2). destruct (sb_rcv _ _ _ _ F2). 
  destruct H3. destruct H4. subst. cbn in *.
  inversion F2. inversion G2. subst.
  (*note that we used injectivity here*)
  unfold super_bij in H2. destruct H2.
  assert (x0 = x1).  apply H3. auto.
  assert (x2 = x3).  apply H3. auto. 
  subst. eauto with picalc.
- inversion H3.

- subst.  set (lem:= not_bdsend_down _ H4).
  firstorder; inversion H5.
- set (lem:= invert_sb_nu  _ _ _ H2). 
  destruct lem as [p lem]. 
  subst. cbn in  *.
  inversion H2. subst.  
  specialize (IHlt _ _ eq_refl).
  (*
  (*-----   experimental   -----------*)
  assert (super_bij (up sigma)). admit.
  specialize (IHlt H1).
  destruct IHlt as [IHlt _].
  destruct IHlt as [p' [a0 IHlt]]; eauto with picalc.
  destruct IHlt as [G1 [G2 G3]]. subst.
 (*-----------------------------------*)
  *)
  Admitted.



Lemma invert_sb_lt2: forall P P0 a Q sigma, lt P a Q -> 
  P = P0[sigma] -> super_bij sigma ->  
  (not_bdsend a -> exists P' a0, Q = P'[sigma] /\  a = a0[sigma] /\  lt P0 a0 P') /\
  (forall x0, a = LbdSend x0 ->  exists P' a0, Q = P'[up sigma] /\  a = a0[sigma] /\  lt P0 a0 P') . 
Proof.
intros. 
generalize dependent sigma.
generalize dependent P0.
induction H; split; intros.   
- set (lem:= invert_sb_send).
  specialize (lem _ _ _ _ _ H0).
  destruct lem. do 2 destruct H2. subst. cbn in *.
  inversion H0. 
  eexists. exists (Lsend x0 x1). 
  split; eauto with picalc. 
- inversion H.


-set (lem:= invert_sb_rcv).
  specialize (lem _ _ _ _ H0).
  destruct lem. destruct H2 as [p H2]. subst. cbn in *.
  inversion H0.
  (*note that we used surjectivity here*)
  unfold super_bij in H1. destruct H1.
  assert (exists y0, y = y0[sigma]). eapply H1. 
  destruct H5 as [y0 H5].
  exists (p[y0 ..]). exists (Lrcv x0 y0). 
  split; cbn; try erewrite up_beta_simpl_pr; rewrite H5; eauto with picalc.
- inversion H. 

- set (lem:= invert_sb_par _ _ _ _ H1).
  destruct lem as [P1 [Q1 lem]].  subst.
  cbn in H1. inversion H1. rewrite H5 in IHlt.
  specialize (IHlt P1 sigma eq_refl H2). 
  destruct IHlt.  specialize (H4 H3).
  destruct H4 as [P'0 [a0 H4]].  
  destruct H4 as [G1 [G2 G3]].
  rewrite G1. 
  exists (Par P'0 Q1). eexists. split; eauto with picalc.
  split. apply G2. eapply Lt_parL. auto.
  eapply (not_bdsend_sub_rev _ sigma).
  symmetry in G2. rewrite G2. auto.
- subst; firstorder; inversion H0.

- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 H3). destruct H4 as [P'[a0 H4]]. 
  destruct H4 as [G1 [G2 G3]]. 
  rewrite G1.
  exists (Par p P'). repeat eexists. 
  eauto with picalc.  
  eapply Lt_parR. auto.
  eapply (not_bdsend_sub_rev _ sigma). 
  symmetry in G2. rewrite G2. auto.
- subst; firstorder; inversion H0.

- firstorder; inversion H3. 
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 _ eq_refl).
  destruct H4 as [p' [a0 H4]].
  destruct H4 as [G1 [G2 G3]].
  rewrite G1.
  exists (Par p' q[shift_sb]). repeat eexists.
  cbn. erewrite shift_permute_pr. auto.
  apply G2. 
  destruct (sb_bdsend _ _ _ G2). rewrite H4 in *.
  eauto with picalc.

- firstorder; inversion H3.
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt _ _ eq_refl H2). destruct IHlt.
  specialize (H4 _ eq_refl).
  destruct H4 as [q' [a0 H4]].
  destruct H4 as [G1 [G2 G3]].
  rewrite G1.
  exists (Par p[shift_sb] q'). repeat eexists.
  cbn. erewrite shift_permute_pr. auto.
  apply G2. 
  destruct (sb_bdsend _ _ _ G2). rewrite H4 in *.
  eauto with picalc.
    
- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt1 _ _ eq_refl H2). destruct IHlt1.
  specialize (IHlt2 _ _ eq_refl H2). destruct IHlt2.
  clear H7 H5 H3.
  assert (not_bdsend (Lsend x y)); eauto with picalc.
  assert (not_bdsend (Lrcv x y)); eauto with picalc.
  specialize (H6 H5). specialize (H4 H3). clear H3 H5.
  destruct H4 as [p' [a0 H4]]. destruct H6 as [q' [b0 H6]].
  destruct H4 as [F1 [F2 F3]]. destruct H6 as [G1 [G2 G3]].   
  subst. 
  exists (Par p' q'). exists Ltau. cbn. split; eauto with picalc. 
  split. auto. 
  destruct (sb_send _ _ _ _ F2). destruct (sb_rcv _ _ _ _ G2). 
  destruct H3. destruct H4. subst. cbn in *.
  inversion F2. inversion G2. subst.
  (*note that we used injectivity here*)
  unfold super_bij in H2. destruct H2.
  assert (x0 = x1).  apply H3. auto.
  assert (x2 = x3).  apply H3. auto. 
  subst. eauto with picalc.
- inversion H3.


- set (lem:= invert_sb_par _ _ _ _ H1).  
  destruct lem as [p [q lem]]. subst. cbn in H1.
  inversion H1. subst.
  specialize (IHlt1 _ _ eq_refl H2). destruct IHlt1.
  specialize (IHlt2 _ _ eq_refl H2). destruct IHlt2.
  clear H7 H5 H3.
  assert (not_bdsend (Lsend x y)); eauto with picalc.
  assert (not_bdsend (Lrcv x y)); eauto with picalc.
  specialize (H4 H5). specialize (H6 H3). clear H3 H5.
  destruct H4 as [p' [a0 H4]]. destruct H6 as [q' [b0 H6]].
  destruct H4 as [F1 [F2 F3]]. destruct H6 as [G1 [G2 G3]].   
  subst. 
  exists (Par p' q'). exists Ltau. cbn. split; eauto with picalc. 
  split. auto. 
  destruct (sb_send _ _ _ _ G2). destruct (sb_rcv _ _ _ _ F2). 
  destruct H3. destruct H4. subst. cbn in *.
  inversion F2. inversion G2. subst.
  (*note that we used injectivity here*)
  unfold super_bij in H2. destruct H2.
  assert (x0 = x1).  apply H3. auto.
  assert (x2 = x3).  apply H3. auto. 
  subst. eauto with picalc.
- inversion H3.

- subst.  set (lem:= not_bdsend_down _ H4).
  firstorder; inversion H5.
- destruct (invert_sb_nu  _ _ _ H2). subst. cbn in  *.
  inversion H2. subst.  
  specialize (IHlt _ _ eq_refl H3). destruct IHlt.

(**)








































(* -------------------------------------------------------------
   This attempt obviously doesn't work since the lt-renaming lemma
   for free and bounded actions work differently.
   ------------------------------------------------------------
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
  rewrite IHlt1. 
 *)
