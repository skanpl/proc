Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive chan : Type :=
    var_chan : nat -> chan.

Definition subst_chan (sigma_chan : nat -> chan) (s : chan) : chan :=
  match s with
  | var_chan s0 => sigma_chan s0
  end.

Lemma up_chan_chan (sigma : nat -> chan) : nat -> chan.
Proof.
exact (scons (var_chan var_zero)
         (funcomp (subst_chan (funcomp (var_chan) shift)) sigma)).
Defined.

Lemma upId_chan_chan (sigma : nat -> chan)
  (Eq : forall x, sigma x = var_chan x) :
  forall x, up_chan_chan sigma x = var_chan x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (subst_chan (funcomp (var_chan) shift)) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition idSubst_chan (sigma_chan : nat -> chan)
  (Eq_chan : forall x, sigma_chan x = var_chan x) (s : chan) :
  subst_chan sigma_chan s = s := match s with
                                 | var_chan s0 => Eq_chan s0
                                 end.

Lemma upExt_chan_chan (sigma : nat -> chan) (tau : nat -> chan)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_chan_chan sigma x = up_chan_chan tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (subst_chan (funcomp (var_chan) shift)) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition ext_chan (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
  (Eq_chan : forall x, sigma_chan x = tau_chan x) (s : chan) :
  subst_chan sigma_chan s = subst_chan tau_chan s :=
  match s with
  | var_chan s0 => Eq_chan s0
  end.

Definition compSubstSubst_chan (sigma_chan : nat -> chan)
  (tau_chan : nat -> chan) (theta_chan : nat -> chan)
  (Eq_chan : forall x,
             funcomp (subst_chan tau_chan) sigma_chan x = theta_chan x)
  (s : chan) :
  subst_chan tau_chan (subst_chan sigma_chan s) = subst_chan theta_chan s :=
  match s with
  | var_chan s0 => Eq_chan s0
  end.

Lemma up_subst_subst_chan_chan (sigma : nat -> chan) (tau_chan : nat -> chan)
  (theta : nat -> chan)
  (Eq : forall x, funcomp (subst_chan tau_chan) sigma x = theta x) :
  forall x,
  funcomp (subst_chan (up_chan_chan tau_chan)) (up_chan_chan sigma) x =
  up_chan_chan theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compSubstSubst_chan (funcomp (var_chan) shift)
                (up_chan_chan tau_chan)
                (funcomp (up_chan_chan tau_chan) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstSubst_chan tau_chan (funcomp (var_chan) shift)
                      (funcomp (subst_chan (funcomp (var_chan) shift))
                         tau_chan)
                      (fun x => eq_refl) (sigma n')))
                (ap (subst_chan (funcomp (var_chan) shift)) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma substSubst_chan (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
  (s : chan) :
  subst_chan tau_chan (subst_chan sigma_chan s) =
  subst_chan (funcomp (subst_chan tau_chan) sigma_chan) s.
Proof.
exact (compSubstSubst_chan sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_chan_pointwise (sigma_chan : nat -> chan)
  (tau_chan : nat -> chan) :
  pointwise_relation _ eq
    (funcomp (subst_chan tau_chan) (subst_chan sigma_chan))
    (subst_chan (funcomp (subst_chan tau_chan) sigma_chan)).
Proof.
exact (fun s =>
       compSubstSubst_chan sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma instId'_chan (s : chan) : subst_chan (var_chan) s = s.
Proof.
exact (idSubst_chan (var_chan) (fun n => eq_refl) s).
Qed.

Lemma instId'_chan_pointwise :
  pointwise_relation _ eq (subst_chan (var_chan)) id.
Proof.
exact (fun s => idSubst_chan (var_chan) (fun n => eq_refl) s).
Qed.

Lemma varL'_chan (sigma_chan : nat -> chan) (x : nat) :
  subst_chan sigma_chan (var_chan x) = sigma_chan x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_chan_pointwise (sigma_chan : nat -> chan) :
  pointwise_relation _ eq (funcomp (subst_chan sigma_chan) (var_chan))
    sigma_chan.
Proof.
exact (fun x => eq_refl).
Qed.

Inductive lab : Type :=
  | Lsend : chan -> chan -> lab
  | Lrcv : chan -> chan -> lab
  | LbdSend : chan -> lab
  | Ltau : lab.

Lemma congr_Lsend {s0 : chan} {s1 : chan} {t0 : chan} {t1 : chan}
  (H0 : s0 = t0) (H1 : s1 = t1) : Lsend s0 s1 = Lsend t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Lsend x s1) H0))
         (ap (fun x => Lsend t0 x) H1)).
Qed.

Lemma congr_Lrcv {s0 : chan} {s1 : chan} {t0 : chan} {t1 : chan}
  (H0 : s0 = t0) (H1 : s1 = t1) : Lrcv s0 s1 = Lrcv t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Lrcv x s1) H0))
         (ap (fun x => Lrcv t0 x) H1)).
Qed.

Lemma congr_LbdSend {s0 : chan} {t0 : chan} (H0 : s0 = t0) :
  LbdSend s0 = LbdSend t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => LbdSend x) H0)).
Qed.

Lemma congr_Ltau : Ltau = Ltau.
Proof.
exact (eq_refl).
Qed.

Definition subst_lab (sigma_chan : nat -> chan) (s : lab) : lab :=
  match s with
  | Lsend s0 s1 =>
      Lsend (subst_chan sigma_chan s0) (subst_chan sigma_chan s1)
  | Lrcv s0 s1 => Lrcv (subst_chan sigma_chan s0) (subst_chan sigma_chan s1)
  | LbdSend s0 => LbdSend (subst_chan sigma_chan s0)
  | Ltau => Ltau
  end.

Definition idSubst_lab (sigma_chan : nat -> chan)
  (Eq_chan : forall x, sigma_chan x = var_chan x) (s : lab) :
  subst_lab sigma_chan s = s :=
  match s with
  | Lsend s0 s1 =>
      congr_Lsend (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_chan sigma_chan Eq_chan s1)
  | Lrcv s0 s1 =>
      congr_Lrcv (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_chan sigma_chan Eq_chan s1)
  | LbdSend s0 => congr_LbdSend (idSubst_chan sigma_chan Eq_chan s0)
  | Ltau => congr_Ltau
  end.

Definition ext_lab (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
  (Eq_chan : forall x, sigma_chan x = tau_chan x) (s : lab) :
  subst_lab sigma_chan s = subst_lab tau_chan s :=
  match s with
  | Lsend s0 s1 =>
      congr_Lsend (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_chan sigma_chan tau_chan Eq_chan s1)
  | Lrcv s0 s1 =>
      congr_Lrcv (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_chan sigma_chan tau_chan Eq_chan s1)
  | LbdSend s0 => congr_LbdSend (ext_chan sigma_chan tau_chan Eq_chan s0)
  | Ltau => congr_Ltau
  end.

Definition compSubstSubst_lab (sigma_chan : nat -> chan)
  (tau_chan : nat -> chan) (theta_chan : nat -> chan)
  (Eq_chan : forall x,
             funcomp (subst_chan tau_chan) sigma_chan x = theta_chan x)
  (s : lab) :
  subst_lab tau_chan (subst_lab sigma_chan s) = subst_lab theta_chan s :=
  match s with
  | Lsend s0 s1 =>
      congr_Lsend
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s1)
  | Lrcv s0 s1 =>
      congr_Lrcv
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s1)
  | LbdSend s0 =>
      congr_LbdSend
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
  | Ltau => congr_Ltau
  end.

Lemma substSubst_lab (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
  (s : lab) :
  subst_lab tau_chan (subst_lab sigma_chan s) =
  subst_lab (funcomp (subst_chan tau_chan) sigma_chan) s.
Proof.
exact (compSubstSubst_lab sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_lab_pointwise (sigma_chan : nat -> chan)
  (tau_chan : nat -> chan) :
  pointwise_relation _ eq
    (funcomp (subst_lab tau_chan) (subst_lab sigma_chan))
    (subst_lab (funcomp (subst_chan tau_chan) sigma_chan)).
Proof.
exact (fun s => compSubstSubst_lab sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma instId'_lab (s : lab) : subst_lab (var_chan) s = s.
Proof.
exact (idSubst_lab (var_chan) (fun n => eq_refl) s).
Qed.

Lemma instId'_lab_pointwise :
  pointwise_relation _ eq (subst_lab (var_chan)) id.
Proof.
exact (fun s => idSubst_lab (var_chan) (fun n => eq_refl) s).
Qed.

Inductive proc : Type :=
  | Zero : proc
  | Par : proc -> proc -> proc
  | Rcv : chan -> proc -> proc
  | Send : chan -> chan -> proc -> proc
  | Nu : proc -> proc.

Lemma congr_Zero : Zero = Zero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Par {s0 : proc} {s1 : proc} {t0 : proc} {t1 : proc}
  (H0 : s0 = t0) (H1 : s1 = t1) : Par s0 s1 = Par t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Par x s1) H0))
         (ap (fun x => Par t0 x) H1)).
Qed.

Lemma congr_Rcv {s0 : chan} {s1 : proc} {t0 : chan} {t1 : proc}
  (H0 : s0 = t0) (H1 : s1 = t1) : Rcv s0 s1 = Rcv t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Rcv x s1) H0))
         (ap (fun x => Rcv t0 x) H1)).
Qed.

Lemma congr_Send {s0 : chan} {s1 : chan} {s2 : proc} {t0 : chan} {t1 : chan}
  {t2 : proc} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  Send s0 s1 s2 = Send t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => Send x s1 s2) H0))
            (ap (fun x => Send t0 x s2) H1))
         (ap (fun x => Send t0 t1 x) H2)).
Qed.

Lemma congr_Nu {s0 : proc} {t0 : proc} (H0 : s0 = t0) : Nu s0 = Nu t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Nu x) H0)).
Qed.

Fixpoint subst_proc (sigma_chan : nat -> chan) (s : proc) {struct s} : 
proc :=
  match s with
  | Zero => Zero
  | Par s0 s1 => Par (subst_proc sigma_chan s0) (subst_proc sigma_chan s1)
  | Rcv s0 s1 =>
      Rcv (subst_chan sigma_chan s0)
        (subst_proc (up_chan_chan sigma_chan) s1)
  | Send s0 s1 s2 =>
      Send (subst_chan sigma_chan s0) (subst_chan sigma_chan s1)
        (subst_proc sigma_chan s2)
  | Nu s0 => Nu (subst_proc (up_chan_chan sigma_chan) s0)
  end.

Fixpoint idSubst_proc (sigma_chan : nat -> chan)
(Eq_chan : forall x, sigma_chan x = var_chan x) (s : proc) {struct s} :
subst_proc sigma_chan s = s :=
  match s with
  | Zero => congr_Zero
  | Par s0 s1 =>
      congr_Par (idSubst_proc sigma_chan Eq_chan s0)
        (idSubst_proc sigma_chan Eq_chan s1)
  | Rcv s0 s1 =>
      congr_Rcv (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s1)
  | Send s0 s1 s2 =>
      congr_Send (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_chan sigma_chan Eq_chan s1)
        (idSubst_proc sigma_chan Eq_chan s2)
  | Nu s0 =>
      congr_Nu
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s0)
  end.

Fixpoint ext_proc (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
(Eq_chan : forall x, sigma_chan x = tau_chan x) (s : proc) {struct s} :
subst_proc sigma_chan s = subst_proc tau_chan s :=
  match s with
  | Zero => congr_Zero
  | Par s0 s1 =>
      congr_Par (ext_proc sigma_chan tau_chan Eq_chan s0)
        (ext_proc sigma_chan tau_chan Eq_chan s1)
  | Rcv s0 s1 =>
      congr_Rcv (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s1)
  | Send s0 s1 s2 =>
      congr_Send (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_chan sigma_chan tau_chan Eq_chan s1)
        (ext_proc sigma_chan tau_chan Eq_chan s2)
  | Nu s0 =>
      congr_Nu
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s0)
  end.

Fixpoint compSubstSubst_proc (sigma_chan : nat -> chan)
(tau_chan : nat -> chan) (theta_chan : nat -> chan)
(Eq_chan : forall x,
           funcomp (subst_chan tau_chan) sigma_chan x = theta_chan x)
(s : proc) {struct s} :
subst_proc tau_chan (subst_proc sigma_chan s) = subst_proc theta_chan s :=
  match s with
  | Zero => congr_Zero
  | Par s0 s1 =>
      congr_Par
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s1)
  | Rcv s0 s1 =>
      congr_Rcv
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s1)
  | Send s0 s1 s2 =>
      congr_Send
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s1)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s2)
  | Nu s0 =>
      congr_Nu
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s0)
  end.

Lemma substSubst_proc (sigma_chan : nat -> chan) (tau_chan : nat -> chan)
  (s : proc) :
  subst_proc tau_chan (subst_proc sigma_chan s) =
  subst_proc (funcomp (subst_chan tau_chan) sigma_chan) s.
Proof.
exact (compSubstSubst_proc sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc_pointwise (sigma_chan : nat -> chan)
  (tau_chan : nat -> chan) :
  pointwise_relation _ eq
    (funcomp (subst_proc tau_chan) (subst_proc sigma_chan))
    (subst_proc (funcomp (subst_chan tau_chan) sigma_chan)).
Proof.
exact (fun s =>
       compSubstSubst_proc sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma instId'_proc (s : proc) : subst_proc (var_chan) s = s.
Proof.
exact (idSubst_proc (var_chan) (fun n => eq_refl) s).
Qed.

Lemma instId'_proc_pointwise :
  pointwise_relation _ eq (subst_proc (var_chan)) id.
Proof.
exact (fun s => idSubst_proc (var_chan) (fun n => eq_refl) s).
Qed.

Class Up_proc X Y :=
    up_proc : X -> Y.

Class Up_lab X Y :=
    up_lab : X -> Y.

Class Up_chan X Y :=
    up_chan : X -> Y.

#[global] Instance Subst_proc : (Subst1 _ _ _) := @subst_proc.

#[global] Instance Subst_lab : (Subst1 _ _ _) := @subst_lab.

#[global] Instance Up_chan_chan : (Up_chan _ _) := @up_chan_chan.

#[global] Instance Subst_chan : (Subst1 _ _ _) := @subst_chan.

#[global]
Instance VarInstance_chan : (Var _ _) := @var_chan.

Notation "s [ sigma_chan ]" := (subst_proc sigma_chan s)
( at level 7, left associativity, only printing)  : subst_scope.
(*
Notation "↑__proc" := up_proc (only printing)  : subst_scope.
*)
Notation "s [ sigma_chan ]" := (subst_lab sigma_chan s)
( at level 7, left associativity, only printing)  : subst_scope.
(*
Notation "↑__lab" := up_lab (only printing)  : subst_scope.

Notation "↑__chan" := up_chan_chan (only printing)  : subst_scope.
*)
Notation "s [ sigma_chan ]" := (subst_chan sigma_chan s)
( at level 7, left associativity, only printing)  : subst_scope.
(*
Notation "↑__chan" := up_chan (only printing)  : subst_scope.
*)
Notation "'var'" := var_chan ( at level 1, only printing)  : subst_scope.

Notation "x '__chan'" := (@ids _ _ VarInstance_chan x)
( at level 5, format "x __chan", only printing)  : subst_scope.

Notation "x '__chan'" := (var_chan x) ( at level 5, format "x __chan")  :
subst_scope.

#[global]
Instance subst_proc_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_proc)).
Proof.
exact (fun f_chan g_chan Eq_chan s t Eq_st =>
       eq_ind s (fun t' => subst_proc f_chan s = subst_proc g_chan t')
         (ext_proc f_chan g_chan Eq_chan s) t Eq_st).
Qed.

#[global]
Instance subst_proc_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_proc)).
Proof.
exact (fun f_chan g_chan Eq_chan s => ext_proc f_chan g_chan Eq_chan s).
Qed.

#[global]
Instance subst_lab_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_lab)).
Proof.
exact (fun f_chan g_chan Eq_chan s t Eq_st =>
       eq_ind s (fun t' => subst_lab f_chan s = subst_lab g_chan t')
         (ext_lab f_chan g_chan Eq_chan s) t Eq_st).
Qed.

#[global]
Instance subst_lab_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_lab)).
Proof.
exact (fun f_chan g_chan Eq_chan s => ext_lab f_chan g_chan Eq_chan s).
Qed.

#[global]
Instance subst_chan_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s t Eq_st =>
       eq_ind s (fun t' => subst_chan f_chan s = subst_chan g_chan t')
         (ext_chan f_chan g_chan Eq_chan s) t Eq_st).
Qed.

#[global]
Instance subst_chan_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s => ext_chan f_chan g_chan Eq_chan s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_chan, Var, ids, Subst_chan, Subst1,
                      subst1, Up_chan_chan, Up_chan, up_chan, Subst_lab,
                      Subst1, subst1, Subst_proc, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_chan, Var, ids,
                                            Subst_chan, Subst1, subst1,
                                            Up_chan_chan, Up_chan, up_chan,
                                            Subst_lab, Subst1, subst1,
                                            Subst_proc, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_proc_pointwise
                 | progress setoid_rewrite substSubst_proc
                 | progress setoid_rewrite substSubst_lab_pointwise
                 | progress setoid_rewrite substSubst_lab
                 | progress setoid_rewrite substSubst_chan_pointwise
                 | progress setoid_rewrite substSubst_chan
                 | progress setoid_rewrite instId'_proc_pointwise
                 | progress setoid_rewrite instId'_proc
                 | progress setoid_rewrite instId'_lab_pointwise
                 | progress setoid_rewrite instId'_lab
                 | progress setoid_rewrite varL'_chan_pointwise
                 | progress setoid_rewrite varL'_chan
                 | progress setoid_rewrite instId'_chan_pointwise
                 | progress setoid_rewrite instId'_chan
                 | progress unfold up_chan_chan, up_ren
                 | progress cbn[subst_proc subst_lab subst_chan]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_chan, Var, ids, Subst_chan, Subst1,
                  subst1, Up_chan_chan, Up_chan, up_chan, Subst_lab, Subst1,
                  subst1, Subst_proc, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_proc: rewrite.

#[global] Hint Opaque subst_lab: rewrite.

#[global] Hint Opaque subst_chan: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

