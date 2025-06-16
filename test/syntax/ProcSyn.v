Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive chan (n_chan : nat) : Type :=
    var_chan : fin n_chan -> chan n_chan.

Definition subst_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : fin m_chan -> chan n_chan) (s : chan m_chan) : chan n_chan :=
  match s with
  | var_chan _ s0 => sigma_chan s0
  end.

Lemma up_chan_chan {m : nat} {n_chan : nat} (sigma : fin m -> chan n_chan) :
  fin (S m) -> chan (S n_chan).
Proof.
exact (scons (var_chan (S n_chan) var_zero)
         (funcomp (subst_chan (funcomp (var_chan _) shift)) sigma)).
Defined.

Lemma up_list_chan_chan (p : nat) {m : nat} {n_chan : nat}
  (sigma : fin m -> chan n_chan) : fin (plus p m) -> chan (plus p n_chan).
Proof.
exact (scons_p p (funcomp (var_chan (plus p n_chan)) (zero_p p))
         (funcomp (subst_chan (funcomp (var_chan _) (shift_p p))) sigma)).
Defined.

Lemma upId_chan_chan {m_chan : nat} (sigma : fin m_chan -> chan m_chan)
  (Eq : forall x, sigma x = var_chan m_chan x) :
  forall x, up_chan_chan sigma x = var_chan (S m_chan) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_chan_chan {p : nat} {m_chan : nat}
  (sigma : fin m_chan -> chan m_chan)
  (Eq : forall x, sigma x = var_chan m_chan x) :
  forall x, up_list_chan_chan p sigma x = var_chan (plus p m_chan) x.
Proof.
exact (fun n =>
       scons_p_eta (var_chan (plus p m_chan))
         (fun n => ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n))
         (fun n => eq_refl)).
Qed.

Definition idSubst_chan {m_chan : nat}
  (sigma_chan : fin m_chan -> chan m_chan)
  (Eq_chan : forall x, sigma_chan x = var_chan m_chan x) (s : chan m_chan) :
  subst_chan sigma_chan s = s :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.

Lemma upExt_chan_chan {m : nat} {n_chan : nat} (sigma : fin m -> chan n_chan)
  (tau : fin m -> chan n_chan) (Eq : forall x, sigma x = tau x) :
  forall x, up_chan_chan sigma x = up_chan_chan tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_chan_chan {p : nat} {m : nat} {n_chan : nat}
  (sigma : fin m -> chan n_chan) (tau : fin m -> chan n_chan)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_chan_chan p sigma x = up_list_chan_chan p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n))).
Qed.

Definition ext_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : fin m_chan -> chan n_chan)
  (tau_chan : fin m_chan -> chan n_chan)
  (Eq_chan : forall x, sigma_chan x = tau_chan x) (s : chan m_chan) :
  subst_chan sigma_chan s = subst_chan tau_chan s :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.

Definition compSubstSubst_chan {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : fin m_chan -> chan k_chan)
  (tau_chan : fin k_chan -> chan l_chan)
  (theta_chan : fin m_chan -> chan l_chan)
  (Eq_chan : forall x,
             funcomp (subst_chan tau_chan) sigma_chan x = theta_chan x)
  (s : chan m_chan) :
  subst_chan tau_chan (subst_chan sigma_chan s) = subst_chan theta_chan s :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.

Lemma up_subst_subst_chan_chan {k : nat} {l_chan : nat} {m_chan : nat}
  (sigma : fin k -> chan l_chan) (tau_chan : fin l_chan -> chan m_chan)
  (theta : fin k -> chan m_chan)
  (Eq : forall x, funcomp (subst_chan tau_chan) sigma x = theta x) :
  forall x,
  funcomp (subst_chan (up_chan_chan tau_chan)) (up_chan_chan sigma) x =
  up_chan_chan theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compSubstSubst_chan (funcomp (var_chan _) shift)
                (up_chan_chan tau_chan)
                (funcomp (up_chan_chan tau_chan) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstSubst_chan tau_chan (funcomp (var_chan _) shift)
                      (funcomp (subst_chan (funcomp (var_chan _) shift))
                         tau_chan)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_chan_chan {p : nat} {k : nat} {l_chan : nat}
  {m_chan : nat} (sigma : fin k -> chan l_chan)
  (tau_chan : fin l_chan -> chan m_chan) (theta : fin k -> chan m_chan)
  (Eq : forall x, funcomp (subst_chan tau_chan) sigma x = theta x) :
  forall x,
  funcomp (subst_chan (up_list_chan_chan p tau_chan))
    (up_list_chan_chan p sigma) x =
  up_list_chan_chan p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_chan (plus p l_chan)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x =>
             scons_p_head' _
               (fun z => subst_chan (funcomp (var_chan _) (shift_p p)) _) x)
            (fun n =>
             eq_trans
               (compSubstSubst_chan (funcomp (var_chan _) (shift_p p))
                  (up_list_chan_chan p tau_chan)
                  (funcomp (up_list_chan_chan p tau_chan) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstSubst_chan tau_chan
                        (funcomp (var_chan _) (shift_p p)) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n)))))).
Qed.

Lemma substSubst_chan {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : fin m_chan -> chan k_chan)
  (tau_chan : fin k_chan -> chan l_chan) (s : chan m_chan) :
  subst_chan tau_chan (subst_chan sigma_chan s) =
  subst_chan (funcomp (subst_chan tau_chan) sigma_chan) s.
Proof.
exact (compSubstSubst_chan sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_chan_pointwise {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : fin m_chan -> chan k_chan)
  (tau_chan : fin k_chan -> chan l_chan) :
  pointwise_relation _ eq
    (funcomp (subst_chan tau_chan) (subst_chan sigma_chan))
    (subst_chan (funcomp (subst_chan tau_chan) sigma_chan)).
Proof.
exact (fun s =>
       compSubstSubst_chan sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma instId'_chan {m_chan : nat} (s : chan m_chan) :
  subst_chan (var_chan m_chan) s = s.
Proof.
exact (idSubst_chan (var_chan m_chan) (fun n => eq_refl) s).
Qed.

Lemma instId'_chan_pointwise {m_chan : nat} :
  pointwise_relation _ eq (subst_chan (var_chan m_chan)) id.
Proof.
exact (fun s => idSubst_chan (var_chan m_chan) (fun n => eq_refl) s).
Qed.

Lemma varL'_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : fin m_chan -> chan n_chan) (x : fin m_chan) :
  subst_chan sigma_chan (var_chan m_chan x) = sigma_chan x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_chan_pointwise {m_chan : nat} {n_chan : nat}
  (sigma_chan : fin m_chan -> chan n_chan) :
  pointwise_relation _ eq (funcomp (subst_chan sigma_chan) (var_chan m_chan))
    sigma_chan.
Proof.
exact (fun x => eq_refl).
Qed.

Inductive proc (n_chan : nat) : Type :=
  | Zero : proc n_chan
  | Par : proc n_chan -> proc n_chan -> proc n_chan
  | Rcv : chan n_chan -> proc (S n_chan) -> proc n_chan
  | Send : chan n_chan -> chan n_chan -> proc n_chan -> proc n_chan
  | Nu : proc (S n_chan) -> proc n_chan.

Lemma congr_Zero {m_chan : nat} : Zero m_chan = Zero m_chan.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Par {m_chan : nat} {s0 : proc m_chan} {s1 : proc m_chan}
  {t0 : proc m_chan} {t1 : proc m_chan} (H0 : s0 = t0) (H1 : s1 = t1) :
  Par m_chan s0 s1 = Par m_chan t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Par m_chan x s1) H0))
         (ap (fun x => Par m_chan t0 x) H1)).
Qed.

Lemma congr_Rcv {m_chan : nat} {s0 : chan m_chan} {s1 : proc (S m_chan)}
  {t0 : chan m_chan} {t1 : proc (S m_chan)} (H0 : s0 = t0) (H1 : s1 = t1) :
  Rcv m_chan s0 s1 = Rcv m_chan t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Rcv m_chan x s1) H0))
         (ap (fun x => Rcv m_chan t0 x) H1)).
Qed.

Lemma congr_Send {m_chan : nat} {s0 : chan m_chan} {s1 : chan m_chan}
  {s2 : proc m_chan} {t0 : chan m_chan} {t1 : chan m_chan} {t2 : proc m_chan}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  Send m_chan s0 s1 s2 = Send m_chan t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => Send m_chan x s1 s2) H0))
            (ap (fun x => Send m_chan t0 x s2) H1))
         (ap (fun x => Send m_chan t0 t1 x) H2)).
Qed.

Lemma congr_Nu {m_chan : nat} {s0 : proc (S m_chan)} {t0 : proc (S m_chan)}
  (H0 : s0 = t0) : Nu m_chan s0 = Nu m_chan t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Nu m_chan x) H0)).
Qed.

Fixpoint subst_proc {m_chan : nat} {n_chan : nat}
(sigma_chan : fin m_chan -> chan n_chan) (s : proc m_chan) {struct s} :
proc n_chan :=
  match s with
  | Zero _ => Zero n_chan
  | Par _ s0 s1 =>
      Par n_chan (subst_proc sigma_chan s0) (subst_proc sigma_chan s1)
  | Rcv _ s0 s1 =>
      Rcv n_chan (subst_chan sigma_chan s0)
        (subst_proc (up_chan_chan sigma_chan) s1)
  | Send _ s0 s1 s2 =>
      Send n_chan (subst_chan sigma_chan s0) (subst_chan sigma_chan s1)
        (subst_proc sigma_chan s2)
  | Nu _ s0 => Nu n_chan (subst_proc (up_chan_chan sigma_chan) s0)
  end.

Fixpoint idSubst_proc {m_chan : nat} (sigma_chan : fin m_chan -> chan m_chan)
(Eq_chan : forall x, sigma_chan x = var_chan m_chan x) (s : proc m_chan)
{struct s} : subst_proc sigma_chan s = s :=
  match s with
  | Zero _ => congr_Zero
  | Par _ s0 s1 =>
      congr_Par (idSubst_proc sigma_chan Eq_chan s0)
        (idSubst_proc sigma_chan Eq_chan s1)
  | Rcv _ s0 s1 =>
      congr_Rcv (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s1)
  | Send _ s0 s1 s2 =>
      congr_Send (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_chan sigma_chan Eq_chan s1)
        (idSubst_proc sigma_chan Eq_chan s2)
  | Nu _ s0 =>
      congr_Nu
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s0)
  end.

Fixpoint ext_proc {m_chan : nat} {n_chan : nat}
(sigma_chan : fin m_chan -> chan n_chan)
(tau_chan : fin m_chan -> chan n_chan)
(Eq_chan : forall x, sigma_chan x = tau_chan x) (s : proc m_chan) {struct s}
   :
subst_proc sigma_chan s = subst_proc tau_chan s :=
  match s with
  | Zero _ => congr_Zero
  | Par _ s0 s1 =>
      congr_Par (ext_proc sigma_chan tau_chan Eq_chan s0)
        (ext_proc sigma_chan tau_chan Eq_chan s1)
  | Rcv _ s0 s1 =>
      congr_Rcv (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s1)
  | Send _ s0 s1 s2 =>
      congr_Send (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_chan sigma_chan tau_chan Eq_chan s1)
        (ext_proc sigma_chan tau_chan Eq_chan s2)
  | Nu _ s0 =>
      congr_Nu
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s0)
  end.

Fixpoint compSubstSubst_proc {k_chan : nat} {l_chan : nat} {m_chan : nat}
(sigma_chan : fin m_chan -> chan k_chan)
(tau_chan : fin k_chan -> chan l_chan)
(theta_chan : fin m_chan -> chan l_chan)
(Eq_chan : forall x,
           funcomp (subst_chan tau_chan) sigma_chan x = theta_chan x)
(s : proc m_chan) {struct s} :
subst_proc tau_chan (subst_proc sigma_chan s) = subst_proc theta_chan s :=
  match s with
  | Zero _ => congr_Zero
  | Par _ s0 s1 =>
      congr_Par
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s1)
  | Rcv _ s0 s1 =>
      congr_Rcv
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s1)
  | Send _ s0 s1 s2 =>
      congr_Send
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s1)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s2)
  | Nu _ s0 =>
      congr_Nu
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s0)
  end.

Lemma substSubst_proc {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : fin m_chan -> chan k_chan)
  (tau_chan : fin k_chan -> chan l_chan) (s : proc m_chan) :
  subst_proc tau_chan (subst_proc sigma_chan s) =
  subst_proc (funcomp (subst_chan tau_chan) sigma_chan) s.
Proof.
exact (compSubstSubst_proc sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc_pointwise {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : fin m_chan -> chan k_chan)
  (tau_chan : fin k_chan -> chan l_chan) :
  pointwise_relation _ eq
    (funcomp (subst_proc tau_chan) (subst_proc sigma_chan))
    (subst_proc (funcomp (subst_chan tau_chan) sigma_chan)).
Proof.
exact (fun s =>
       compSubstSubst_proc sigma_chan tau_chan _ (fun n => eq_refl) s).
Qed.

Lemma instId'_proc {m_chan : nat} (s : proc m_chan) :
  subst_proc (var_chan m_chan) s = s.
Proof.
exact (idSubst_proc (var_chan m_chan) (fun n => eq_refl) s).
Qed.

Lemma instId'_proc_pointwise {m_chan : nat} :
  pointwise_relation _ eq (subst_proc (var_chan m_chan)) id.
Proof.
exact (fun s => idSubst_proc (var_chan m_chan) (fun n => eq_refl) s).
Qed.

Class Up_proc X Y :=
    up_proc : X -> Y.

Class Up_chan X Y :=
    up_chan : X -> Y.

#[global]
Instance Subst_proc  {m_chan n_chan : nat}: (Subst1 _ _ _) :=
 (@subst_proc m_chan n_chan).

#[global]
Instance Up_chan_chan  {m n_chan : nat}: (Up_chan _ _) :=
 (@up_chan_chan m n_chan).

#[global]
Instance Subst_chan  {m_chan n_chan : nat}: (Subst1 _ _ _) :=
 (@subst_chan m_chan n_chan).

#[global]
Instance VarInstance_chan  {n_chan : nat}: (Var _ _) := (@var_chan n_chan).

Notation "s [ sigma_chan ]" := (subst_proc sigma_chan s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__proc" := up_proc (only printing)  : subst_scope.

Notation "↑__chan" := up_chan_chan (only printing)  : subst_scope.

Notation "s [ sigma_chan ]" := (subst_chan sigma_chan s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__chan" := up_chan (only printing)  : subst_scope.

Notation "'var'" := var_chan ( at level 1, only printing)  : subst_scope.

Notation "x '__chan'" := (@ids _ _ VarInstance_chan x)
( at level 5, format "x __chan", only printing)  : subst_scope.

Notation "x '__chan'" := (var_chan x) ( at level 5, format "x __chan")  :
subst_scope.

#[global]
Instance subst_proc_morphism  {m_chan : nat} {n_chan : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_proc m_chan n_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s t Eq_st =>
       eq_ind s (fun t' => subst_proc f_chan s = subst_proc g_chan t')
         (ext_proc f_chan g_chan Eq_chan s) t Eq_st).
Qed.

#[global]
Instance subst_proc_morphism2  {m_chan : nat} {n_chan : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_proc m_chan n_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s => ext_proc f_chan g_chan Eq_chan s).
Qed.

#[global]
Instance subst_chan_morphism  {m_chan : nat} {n_chan : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_chan m_chan n_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s t Eq_st =>
       eq_ind s (fun t' => subst_chan f_chan s = subst_chan g_chan t')
         (ext_chan f_chan g_chan Eq_chan s) t Eq_st).
Qed.

#[global]
Instance subst_chan_morphism2  {m_chan : nat} {n_chan : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_chan m_chan n_chan)).
Proof.
exact (fun f_chan g_chan Eq_chan s => ext_chan f_chan g_chan Eq_chan s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_chan, Var, ids, Subst_chan, Subst1,
                      subst1, Up_chan_chan, Up_chan, up_chan, Subst_proc,
                      Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_chan, Var, ids,
                                            Subst_chan, Subst1, subst1,
                                            Up_chan_chan, Up_chan, up_chan,
                                            Subst_proc, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_proc_pointwise
                 | progress setoid_rewrite substSubst_proc
                 | progress setoid_rewrite substSubst_chan_pointwise
                 | progress setoid_rewrite substSubst_chan
                 | progress setoid_rewrite instId'_proc_pointwise
                 | progress setoid_rewrite instId'_proc
                 | progress setoid_rewrite varL'_chan_pointwise
                 | progress setoid_rewrite varL'_chan
                 | progress setoid_rewrite instId'_chan_pointwise
                 | progress setoid_rewrite instId'_chan
                 | progress unfold up_list_chan_chan, up_chan_chan, up_ren
                 | progress cbn[subst_proc subst_chan]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_chan, Var, ids, Subst_chan, Subst1,
                  subst1, Up_chan_chan, Up_chan, up_chan, Subst_proc, Subst1,
                  subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.

End Core.

Module Extra.

Import
Core.

Arguments Nu {n_chan}.

Arguments Send {n_chan}.

Arguments Rcv {n_chan}.

Arguments Par {n_chan}.

Arguments Zero {n_chan}.

Arguments var_chan {n_chan}.

#[global] Hint Opaque subst_proc: rewrite.

#[global] Hint Opaque subst_chan: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

