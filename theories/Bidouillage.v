Require Import Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import SubLem.


(* TODO : *)
(* rendre cong symétrique sans Cg_sym, ca fera moins de boulot dans le résultat principal *)
(* définir down comme une substiution (pour écrire P[down]), pour être cohérent avec le reste *)
(* prouver: P[shift][down] = P *)
(* prouver mapN_lts_rev dans la formalisation HOpi *)


 (*
Lemma lt_assocR: forall P Q R P0 a, 
  lt (Par P Q) a P0 -> 
  exists Q0, lt (Par P (Par Q R)) a Q0.
Proof.
intros.  
inversion H; eauto with picalc.
subst. 
eexists.
eapply Lt_closeL.
eauto with picalc.
cbn. 
eauto with picalc.
Qed.*)




Lemma extr_rl_assoc: forall P Q R, 
  cong (Nu (Par (Par P[shift_sb] Q)  R) )  (Par P (Nu (Par Q R))).
Proof.
intros.
eapply Cg_sym.
eapply Cg_trans.

eapply Cg_trans.
eapply Cg_parCom.
eapply Cg_nuPar.

eapply Cg_ctxNu.
eapply Cg_trans.
eapply Cg_parCom.
eapply Cg_sym.
eapply Cg_parAssoc.
Qed.

Definition shift_sb2 x := (subst_chan (S >> var_chan)) (ch x).
Lemma equiv_shift: shift_sb2 = shift_sb.
Proof.
fe. auto.
Qed.

Lemma notzero_shift: forall x, x[shift_sb] <> (ch 0).
Proof.
  intros. destruct x; cbn. destruct n; intuition; inversion H.
Qed.

Lemma notinlab_shift: forall a, notinlab a[shift_sb] (ch 0).
Proof.
  intros. 
  destruct a; simpl;
  try (destruct c); try (destruct c0); try (destruct n); try (destruct n0); cbv; intuition; inversion H.
Qed.


Lemma not_bdsend_subs : forall a sigma, not_bdsend a -> not_bdsend a[sigma].
Proof.
  intros.
  inversion H; subst.
  cbv; intuition.
  intuition; destruct H1; destruct H0; subst; cbn; auto with picalc.
Qed.

Lemma down_shift_lab : forall a, a = down a[shift_sb].
Proof.
  intros.
  destruct a; subst; simpl;
  try (destruct c); try (destruct c0); cbn; try (replace (n-0) with n; auto with arith); 
  try (replace (n0-0) with n0; auto with arith).
  auto.
Qed.

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

Lemma down_bs: forall a x , LbdSend x = down a -> 
  exists x',  a = LbdSend x'.
Proof. 
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.


Lemma cong_resp_lt: forall P Q P' Q' a, 
  cong P Q -> 
     (lt P a P'  -> exists Q0, lt Q a Q0 /\ cong P' Q0)  /\
      (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof.
intros. 
generalize dependent P'.
generalize dependent Q'.
generalize dependent a. 
induction H.      
   
(*=========case commutative par ===================*)
- firstorder.
inversion H; eauto with picalc.
inversion H; eauto with picalc.
(*========== case  assoc par  ==============================*)
(* LHS *)
- firstorder.    
inversion H; try eauto with picalc. (*caseAn on (P|Q)|R-->a ...*)
subst.
   
(**)  
inversion H2; subst; eauto with picalc. (*caseAn on P|Q -->a ...*)
 
firstorder; inversion H0.

eexists. split. 
eapply Lt_closeL.
eauto with picalc.
cbn. 
eauto with picalc.
eauto with picalc.
 
eexists. split.
eauto with picalc.
eauto with picalc.
(**)
        
(**)  
inversion H2; subst. (*caseAn P|Q -->a ...*)
firstorder; inversion H0.
firstorder; inversion H0.
 
eauto with picalc.
eauto with picalc.
(**)
 
cbn in *. rewrite H5 in *. 
eexists; split; eauto with picalc.
  
inversion H2; eauto with picalc.
 
inversion H2; eauto with picalc.

(*******) 
inversion H2; eauto with picalc. (*casAn P|Q -->a ...*)
subst; firstorder; inversion H0.
subst; firstorder; inversion H0.

subst.
eexists. split.
eapply Lt_closeL.
eauto with picalc. 
cbn. eauto with picalc.
eauto with picalc.

subst. 
eexists. split.
eauto with picalc.
eauto with picalc.
eapply extr_rl_assoc.
(******)
   
subst.
cbn in *.
inversion H2; subst.
eexists. split. 
eapply Lt_closeR.
eauto with picalc.
eauto with picalc.
eauto with picalc.

eexists. split. 
eauto with picalc. 
eapply extr_rl_assoc.  
(* assoc RHS *)   
inversion H; eauto with picalc. (*caseAn P|(Q|R) --->a ...*)
subst.
  
     
(*___*)
inversion H2; eauto with picalc. (*caseAn Q|R --->a ...*) (*gen 4 new goals *)

subst; eauto with picalc.
  
subst; firstorder; inversion H0.

subst.
eexists. split. 
eapply Lt_closeL.
eauto with picalc.  
eauto with picalc. 
eapply extr_rl_assoc.

subst.
eexists. split.
eapply Lt_closeR.
cbn. 
eauto with picalc. 
eauto with picalc.
eapply extr_rl_assoc. 
(*__________*)
 
subst. eauto with picalc.

(*___*)  
inversion H2; eauto with picalc.  (*caseAn Q|R  -->a ...*)
subst.      
firstorder; inversion H0.
subst.
  
eexists. split.
eauto with picalc. 
cbn.
eauto with picalc.
(*___*)

     
inversion H5; eauto with picalc.

inversion H5; eauto with picalc.
 
(*__*)
subst. cbn in *.     
inversion H5; eauto with picalc. (*caseAn Q[shift]|R[shift] -->? ...*) 
subst; eexists; split; eauto with picalc. 
subst; eexists; split; eauto with picalc.
(*__*)


(*__*)
subst. 
inversion H5; eauto with picalc. (*caseAn Q|R -->b! ...*)
firstorder; inversion H7.
firstorder; inversion H7.

subst; eexists; split; eauto with picalc. 

subst. eexists. split. 
eapply Lt_closeR.
cbn.
eauto with picalc.
eauto with picalc. 
eauto with picalc.
(*==============  case neut    ======================================*)
(*LHS*)   
- firstorder.  
inversion H; eauto with picalc.
inversion H2. 
subst. eauto with picalc.
inversion H2. inversion H5.
inversion H5.   
cbn in *. inversion H5. 
inversion H5.          

(*RHS*)  
destruct a; cbn in *; try destruct c, c0; eauto with picalc.
(*destruct c. eauto with picalc.*) 
(*==============  case NuZero    ======================================*)  
- firstorder; inversion H; inversion H1.
(*==============  case NuPar    ======================================*) 
- firstorder.     
 + inversion H;  eauto with picalc; subst. (*caseAn (Nu P)|Q -->a ... *)
    
   * (*____ freeParL____*) 
    inversion H2. (*caseAn Nu P -->a ... *)
    
    subst. (*case Lt_open*)
    firstorder inversion H0. 
    subst. (*case Lt_res*)
    eexists. split; eauto with picalc.
    subst. simpl in H5. inversion H5. inversion H0. firstorder; inversion H4.
    
   * (*_____freeParR____*) 
    destruct (lt_sub Q Q'0 a shift_sb H2).
    eexists; split.
    eapply Lt_res.
    eapply Lt_parR.  apply H0; auto.
    eapply not_bdsend_sub; auto.
    apply notinlab_shift.
    apply not_bdsend_subs; auto.
    apply down_shift_lab. 
    auto with picalc.
    

  * (*_____bdParL____*)
    inversion H2; subst.
    eauto with picalc.
    inversion H4. subst. inversion H5. 
    intuition; destruct H6; destruct H0; subst; inversion H5.
    eexists; split; eauto with picalc.
    cbn. replace (Q[shift_sb][shift_sb][swap_sb]) with (Q[shift_sb][shift_sb]); auto with picalc. 
    asimpl. auto. (* pourquoi c'est si facile ?*)
 
  * (*_____bdParR____*)
   eexists. 
   destruct (lt_sub Q Q'0 _ shift_sb H2).
   specialize (H1 x).
   split.
   eapply Lt_res_bd. 
   eapply Lt_parR_bs. apply H1; auto. 
   reflexivity.
   apply notzero_shift.
   apply down_shift_lab.
   cbn. replace (P[shift_sb][swap_sb]) with P[up shift_sb].
   replace (Q'0[up shift_sb][swap_sb]) with Q'0[shift_sb]; auto with picalc.
   asimpl; auto. replace (swap_sb 0 .: shift_sb >> subst_chan (↑ >> swap_sb)) with (shift_sb) ; auto.
   fe. auto_case.
   asimpl; auto. (* pourquoi c'est si facile ?*)

  * (*______commL_____*)
    destruct (lt_sub Q Q'0 _ shift_sb H5).
    inversion H2; subst; try (simpl in H7; inversion H7). 
    subst. inversion H8. do 3 (destruct H3). subst.
    apply down_send_notzero in H8; auto. inversion H8; subst.
    eexists; split. 
    eapply Lt_res with (a:=Ltau); cbn; eauto with picalc.
    eauto with picalc.
    subst. simpl in H8. inversion H8.

  * (*______commR_____*)
    inversion H2; subst; try (simpl in H4; inversion H4). 
    subst. simpl in H6; inversion H6.
    do 3 (destruct H0). subst. simpl in H6; inversion H6.
    subst. apply down_rcv_notzero in H6; auto. inversion H6; subst.
    destruct (lt_sub Q Q'0 _ shift_sb H5).
    eexists; split. 
    eapply Lt_res with (a:=Ltau); cbn; eauto with picalc.
    eauto with picalc.
   
  * (*_____closeL_______*)
    inversion H2; subst. 
    apply down_bs_notzero in H4; auto; subst.
    eexists; split; eauto with picalc. 
    eapply Lt_res with (a:=Ltau); cbn; eauto with picalc.
    apply down_bs in H6. destruct H6. subst. cbv in H4.
    intuition; try inversion H0; try (destruct H4; destruct H0; inversion H0).
    apply down_bs_notzero in H4; auto. subst.
    eexists; split. 
    eapply Lt_res with (a:=Ltau); cbn; eauto with picalc.
    eapply Lt_closeL; eauto with picalc.
    destruct (lt_sub _ _ _ shift_sb H5). clear H4.
    assert (lt Q[shift_sb][shift_sb] (Lrcv x[shift_sb] (ch 0))[shift_sb] Q'0[shift_sb]).
    apply H0. apply not_bdsend_rcv. clear H0.
    destruct (lt_sub _ _ _ swap_sb H4). clear H6. cbn in H0.
    assert (lt Q[shift_sb][shift_sb][swap_sb] 
      (Lrcv x[shift_sb][shift_sb][swap_sb] (ch 0)) Q'0[shift_sb][swap_sb]).
    apply H0. apply not_bdsend_rcv. clear H0.
    replace (Q[shift_sb][shift_sb][swap_sb]) with (Q[shift_sb][shift_sb]) in H6.
    replace (Lrcv x[shift_sb][shift_sb][swap_sb] (ch 0)) with (Lrcv x[shift_sb][shift_sb] (ch 0)) in H6.
    apply H6.
    asimpl. auto. (*facile*)
    asimpl. auto. (*facile*)
    eapply Cg_trans. apply Cg_ctxNu. apply Cg_nuPar.
    apply Cg_sym. 
    replace (Nu (Nu (Par P'[swap_sb] Q'0[shift_sb]))) 
      with (Nu (Nu (Par P' (Q'0[shift_sb][swap_sb]))[swap_sb] )).
    apply Cg_nuSwap. 
    cbn. replace (Q'0[shift_sb][swap_sb][swap_sb]) with (Q'0[shift_sb]); auto.
    asimpl. replace (shift_sb >> subst_chan (swap_sb >> subst_chan swap_sb)) with shift_sb; auto.
    fe. auto_case. (*facile*)

  * (*_____closeR_______*)
    inversion H2; subst. 
    simpl in H4. inversion H4.
    apply down_rcv_notzero in H6; auto; subst.
    destruct (lt_sub _ _ _ swap_sb H1).
    clear H6. apply H0 in H4 as H12. clear H0.
    assert (Lrcv x[shift_sb][shift_sb][swap_sb] (ch 0) = Lrcv x[shift_sb][shift_sb] (ch 0)).
    asimpl. auto. (*facile*)
    cbn in H12. replace (subst_chan swap_sb (subst1 shift_sb (subst1 shift_sb x)))
    with (subst1 swap_sb (subst1 shift_sb (subst1 shift_sb x))) in H12 by auto. (*WTF???*)
    rewrite H0 in H12. clear H0.
    replace (subst1 swap_sb (Subst_proc (up_chan_chan shift_sb) P)) with (Subst_proc shift_sb P) in H12.
    destruct (lt_sub _ _ _ shift_sb H5).
    clear H0. specialize (H6 x). assert (lt Q[shift_sb] (LbdSend x)[shift_sb] Q'0[up shift_sb]) by auto.
    clear H6.
    eexists; split.
    eapply Lt_res with (a:= Ltau); simpl; eauto with picalc.
    eapply Cg_trans. apply Cg_ctxNu. apply Cg_nuPar.
    eapply Cg_trans. apply Cg_nuSwap. cbn.
    replace (Q'0[up shift_sb]) with (Q'0[shift_sb][swap_sb]); eauto with picalc.
    asimpl. auto. (*facile*)
    asimpl. assert (shift_sb = swap_sb 0 .: shift_sb >> subst_chan (↑ >> swap_sb)).
    fe. auto_case. (*facile *) rewrite <- H0; auto.
    simpl in H4. inversion H4.
 + (* clause inverse*)
    inversion H; subst.
    * (*Lt_open *)
      inversion H1; subst.
      -- (* parL*)
          eexists; split.
          eapply Lt_parL_bs; eauto with picalc. 
          eauto with picalc.
      -- (* parR *)
           
         (* cas impossible, H4 est absurde, un processus shifté ne peut pas envoyer 0*)
          admit.
   * (*Lt_res*)
      inversion H1; subst.
      -- (*parL *)
          eexists; split.
          eapply Lt_parL; eauto with picalc. unfold down. apply not_bdsend_sub; auto.
          eauto with picalc.
      -- (* parR *)
          eexists; split.
          eapply Lt_parR; eauto with picalc.
          destruct (lt_sub _ _ _ (fun x => ch (x-1)) H5).
          clear H4. apply H0 in H8 as H12. clear H0.
          replace (Q[shift_sb][fun x : nat => ch (x - 1)]) with Q in H12. exact H12.
          asimpl. assert (shift_sb >> subst_chan (fun x : nat => ch (x - 1)) = fun x => ch x).
          fe. auto_case. rewrite H0. asimpl. auto.
          apply not_bdsend_sub; auto.
          eapply Cg_trans. apply Cg_nuPar. eapply Cg_ctxNu.
          (* si Q' ne contient pas 0, alors Q'[fun x : nat => ch (x - 1)][shift_sb] = Q' *)
          (* montrer que lt Q[shift_sb] a0 Q'implique Q' = Q''[shift_sb] pour un certain Q''*)
          (* plus généralement, on a besoin de mapN_lts_rev dans la formalisation HOpi *)
          admit.
      -- inversion H3. inversion H0. do 3 destruct H0. inversion H0. inversion H0.
      -- inversion H3. inversion H0. do 3 destruct H0. inversion H0. inversion H0.
      -- (* comL *)
          eexists; split.
          eapply (Lt_commL _ _ _ _ (x[fun x => ch (x-1)]) (y[fun y => ch (y-1)])); eauto with picalc.
          eapply Lt_res; eauto with picalc.
          (* on a Q[shift] --x<y> --> ... donc x<> 0 et y <> 0 *)
          admit.
          destruct (lt_sub _ _ _ (fun x => ch (x-1)) H8).
          clear H4. 
          assert (lt Q[shift_sb][fun x : nat => ch (x - 1)] (Lrcv x y)[fun x : nat => ch (x - 1)] Q'
              [fun x : nat => ch (x - 1)]).
          apply H0; auto with picalc. clear H0.
          replace (Q[shift_sb][fun x : nat => ch (x - 1)]) with Q in H4. exact H4.
          asimpl. assert (shift_sb >> subst_chan (fun x : nat => ch (x - 1)) = fun x => ch x).
          fe. auto_case. rewrite H0. asimpl. auto.
          eapply Cg_trans. apply Cg_nuPar.
          (* montrer que lt Q[shift_sb] a0 Q'implique Q' = Q''[shift_sb] pour un certain Q''*)
          admit.
      -- (*comR *)          
          eexists; split.
          eapply (Lt_commR _ _ _ _ (x[fun x => ch (x-1)]) (y[fun y => ch (y-1)])); eauto with picalc.
          eapply Lt_res; eauto with picalc.
          (* on a Q[shift] --x<y> --> ... donc x<> 0 et y <> 0 *)
          admit.
          destruct (lt_sub _ _ _ (fun x => ch (x-1)) H8).
          clear H4. 
          assert ( lt Q[shift_sb][fun x : nat => ch (x - 1)] (Lsend x y)[fun x : nat => ch (x - 1)] Q'
            [fun x : nat => ch (x - 1)]).
          apply H0; auto with picalc. clear H0.
          replace (Q[shift_sb][fun x : nat => ch (x - 1)]) with Q in H4. exact H4.
          asimpl. assert (shift_sb >> subst_chan (fun x : nat => ch (x - 1)) = fun x => ch x).
          fe. auto_case. rewrite H0. asimpl. auto.
          eapply Cg_trans. apply Cg_nuPar.
          (* montrer que lt Q[shift_sb] a0 Q'implique Q' = Q''[shift_sb] pour un certain Q''*)
          admit.
       -- (* closeL *)
          eexists; split.
          eapply (Lt_closeL _ _ _ _ (x[fun x => ch (x-1)])); eauto with picalc.
          eapply Lt_res_bd; eauto with picalc.
          admit. (* parce que Q[S][S] ---x[S]--> implique x>=1 *)
          destruct (lt_sub _ _ _ (fun x => ch (x-1)) H8).
          clear H4. 
          assert (lt Q[shift_sb][shift_sb][fun x : nat => ch (x - 1)] (Lrcv x[shift_sb] (ch 0))
            [fun x : nat => ch (x - 1)] Q'[fun x : nat => ch (x - 1)]).
          apply H0; auto with picalc. clear H0.
          replace (Q[shift_sb][shift_sb][fun x : nat => ch (x - 1)]) with Q[shift_sb] in H4.
          cbn in H4. replace 
            (subst_chan (fun x : nat => var_chan (Nat.sub x 1)) (subst1 shift_sb x)) with x in H4.
          replace ( x[fun x0 : nat => ch (x0 - 1)][shift_sb]) with x. exact H4.
          admit. (* parce que x >=1 *)
          asimpl. assert (shift_sb >> subst_chan (fun x : nat => ch (x - 1)) = fun x => ch x).
          fe. auto_case. rewrite H0. asimpl. auto.
          asimpl. assert (shift_sb >> subst_chan (fun x : nat => ch (x - 1)) = fun x => ch x).
          fe. auto_case. rewrite H0. asimpl. auto.
          (* Q' = Q''[shift_sb] pour un certain Q'' *)
          admit.
       -- (* closeR *)
          eexists; split.
          eapply (Lt_closeR _ _ _ _ (x[fun x => ch (x-1)])); eauto with picalc.
          cbn. eapply (Lt_res _ _ (Lrcv (x[shift_sb]) (ch 1))); eauto with picalc.
          destruct (lt_sub _ _ _ swap_sb H5). clear H4.
          assert (lt P[shift_sb][swap_sb] (Lrcv x[shift_sb] (ch 0))[swap_sb] P'1[swap_sb]).
          apply H0; auto with picalc. clear H0. cbn in H4.
          replace (subst_chan swap_sb (subst1 shift_sb x)) with (x[shift_sb]) in H4.
          replace (P[shift_sb][swap_sb]) with (P[up shift_sb]) in H4.
          exact H4.
          asimpl. auto.
          admit. (*parce que x >=1 *)
          cbn. destruct x. asimpl. destruct n. cbv. intuition; inversion H0.
          cbv. intuition; inversion H0.
          admit. (*parce que x >=1 *)
          admit. (*lts_mapN_rev *)
          admit.
   * (* Lt_res_bound *)
      inversion H1; subst.
      -- inversion H7. inversion H0. do 3 destruct H0;  inversion H0.
      -- inversion H7. inversion H0. do 3 destruct H0;  inversion H0.
      -- (* parL *)
         eexists; split. 
         eapply Lt_parL_bs; eauto with picalc. 
         cbn. replace (Q[shift_sb][shift_sb][swap_sb]) with (Q[shift_sb][shift_sb]); eauto with picalc.
         asimpl. auto.
      -- (* parR *)
         eexists; split. 
         eapply Lt_parR_bs; eauto with picalc. 
         admit. (*lts_mapN_rev *)
         admit.
  - firstorder. inversion H; subst. (* nu nu P -> *)
    * (* Lt_open *)
      inversion H1; subst.
      cbn in H5. inversion H5.
      destruct a; inversion H6; subst.
      cbn in H6. cbn in H4. destruct c0. destruct n. intuition.
      cbn in H8. replace (n-0) with n in H8 by auto with arith. inversion H8; subst.
      destruct c. destruct n. intuition. destruct n. intuition.
      cbn. replace (n-0) with n by auto with arith.
      destruct (lt_sub _ _ _ swap_sb H3). clear H7.
      assert (lt P[swap_sb] (Lsend (ch (S (S n))) (ch 1))[swap_sb] P'0[swap_sb]).
      apply H0; auto with picalc. clear H0. cbn in H7.
      eexists; split.
      eapply Lt_res_bd; eauto with picalc.
      eapply Lt_open; eauto with picalc.
      cbv. intuition. 
      cbn. replace (n-0) with n by auto with arith. auto.
      replace (P'0[swap_sb][swap_sb]) with (P'0); auto with picalc.
      asimpl. replace (swap_sb >> subst_chan swap_sb) with (fun x => ch x).
      asimpl. auto. fe. destruct x; cbn; auto. destruct x; cbn; auto.
      cbn in H5; inversion H5.
                  
           
        
          
         
      





(* 
Lemma cong_resp_lt: forall P Q P' Q' a, 
  cong P Q -> 
     (lt P a P'  -> exists Q0, lt Q a Q0 /\ cong P' Q0)  /\
      (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof.
intros. 
generalize dependent P'.
generalize dependent Q'.
generalize dependent a. 
induction H.      
   
(*=========case commutative par ===================*)
- firstorder.
inversion H; eauto with picalc.
inversion H; eauto with picalc.
(*========== case  assoc par  ==============================*)
(* LHS *)
- firstorder.    
inversion H; try eauto with picalc. (*caseAn on (P|Q)|R-->a ...*)
subst.
   
(**)  
inversion H2; subst; eauto with picalc. (*caseAn on P|Q -->a ...*)
 
firstorder; inversion H0.

eexists. split. 
eapply Lt_closeL.
eauto with picalc.
cbn. 
eauto with picalc.
eauto with picalc.
 
eexists. split.
eauto with picalc.
eauto with picalc.
(**)
        
(**)  
inversion H2; subst. (*caseAn P|Q -->a ...*)
firstorder; inversion H0.
firstorder; inversion H0.
 
eauto with picalc.
eauto with picalc.
(**)
 
cbn in *. rewrite H5 in *. 
eexists; split; eauto with picalc.
  
inversion H2; eauto with picalc.
 
inversion H2; eauto with picalc.

(*******) 
inversion H2; eauto with picalc. (*casAn P|Q -->a ...*)
subst; firstorder; inversion H0.
subst; firstorder; inversion H0.

subst.
eexists. split.
eapply Lt_closeL.
eauto with picalc. 
cbn. eauto with picalc.
eauto with picalc.

subst. 
eexists. split.
eauto with picalc.
eauto with picalc.
eapply extr_rl_assoc.
(******)
   
subst.
cbn in *.
inversion H2; subst.
eexists. split. 
eapply Lt_closeR.
eauto with picalc.
eauto with picalc.
eauto with picalc.

eexists. split. 
eauto with picalc. 
eapply extr_rl_assoc.  
(* assoc RHS *)   
inversion H; eauto with picalc. (*caseAn P|(Q|R) --->a ...*)
subst.
  
     
(*___*)
inversion H2; eauto with picalc. (*caseAn Q|R --->a ...*) (*gen 4 new goals *)

subst; eauto with picalc.
  
subst; firstorder; inversion H0.

subst.
eexists. split. 
eapply Lt_closeL.
eauto with picalc.  
eauto with picalc. 
eapply extr_rl_assoc.

subst.
eexists. split.
eapply Lt_closeR.
cbn. 
eauto with picalc. 
eauto with picalc.
eapply extr_rl_assoc. 
(*__________*)
 
subst. eauto with picalc.

(*___*)  
inversion H2; eauto with picalc.  (*caseAn Q|R  -->a ...*)
subst.      
firstorder; inversion H0.
subst.
  
eexists. split.
eauto with picalc. 
cbn.
eauto with picalc.
(*___*)

     
inversion H5; eauto with picalc.

inversion H5; eauto with picalc.
 
(*__*)
subst. cbn in *.     
inversion H5; eauto with picalc. (*caseAn Q[shift]|R[shift] -->? ...*) 
subst; eexists; split; eauto with picalc. 
subst; eexists; split; eauto with picalc.
(*__*)


(*__*)
subst. 
inversion H5; eauto with picalc. (*caseAn Q|R -->b! ...*)
firstorder; inversion H7.
firstorder; inversion H7.

subst; eexists; split; eauto with picalc. 

subst. eexists. split. 
eapply Lt_closeR.
cbn.
eauto with picalc.
eauto with picalc. 
eauto with picalc.
(*==============  case neut    ======================================*)
(*LHS*)   
- firstorder.  
inversion H; eauto with picalc.
inversion H2. 
subst. eauto with picalc.
inversion H2. inversion H5.
inversion H5.   
cbn in *. inversion H5. 
inversion H5.          

(*RHS*)  
destruct a; cbn in *; try destruct c, c0; eauto with picalc.
(*destruct c. eauto with picalc.*) 
(*==============  case NuZero    ======================================*)  
- firstorder; inversion H; inversion H1.
(*==============  case NuPar    ======================================*) 
- firstorder.    
 + inversion H;  eauto with picalc; subst. (*caseAn (Nu P)|Q -->a ... *)
  *  
(*____ freeParL____*) 
inversion H2. (*caseAn Nu P -->a ... *)
    
subst. (*case Lt_open*)
firstorder; inversion H0. 
  
subst. (*case Lt_res*)
eexists. split.
eapply Lt_res.
eapply Lt_parL.
eauto with picalc.   

eauto using not_bdsend_down. 
eauto with picalc.
eauto with picalc.
auto with picalc.
(*_____freeParR____*)
 
 * 
eexists. split. 
eapply Lt_res. 
eapply Lt_parR.

*)



