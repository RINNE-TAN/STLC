From Coq Require Import Strings.String.

Module STLC.
  Inductive Ty : Type :=
    | Ty_Bool : Ty
    | Ty_Arrow : Ty -> Ty -> Ty.

  Inductive Term : Type :=
    | tm_false : Term
    | tm_true : Term
    | tm_var : string -> Term
    | tm_lam : string -> Ty -> Term -> Term
    | tm_app : Term -> Term -> Term
    | tm_if : Term -> Term -> Term -> Term.

  Inductive value : Term -> Prop :=
    | v_lam : forall x T t, value (tm_lam x T t)
    | v_false : value tm_false
    | v_true : value tm_true.

  Fixpoint subst (x : string) (s : Term) (t : Term) : Term :=
    match t with
    | tm_false => tm_false
    | tm_true => tm_true
    | tm_var y =>
      if String.eqb x y
        then s
        else t
    | tm_lam y T t1 =>
      if String.eqb x y
        then t
        else tm_lam y T (subst x s t1)
    | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
    | tm_if t t1 t2 => tm_if (subst x s t) (subst x s t1) (subst x s t2)
    end.

  Inductive substi (x : string) (s : Term) : Term -> Term -> Prop :=
    | s_false : substi x s tm_false tm_false
    | s_true : substi x s tm_true tm_true
    | s_var1 : forall y, x = y -> substi x s (tm_var y) s
    | s_var2 : forall y, x <> y -> substi x s (tm_var y) (tm_var y)
    | s_lam1 : forall y T t, x = y -> substi x s (tm_lam y T t) (tm_lam y T t)
    | s_lam2 :
        forall y T t t',
          x <> y -> substi x s t t' -> substi x s (tm_lam y T t) (tm_lam y T t')
    | s_app :
        forall t1 t1' t2 t2',
          substi x s t1 t1' ->
          substi x s t2 t2' -> substi x s (tm_app t1 t2) (tm_app t1' t2')
    | s_if :
        forall t t1 t2 t' t1' t2',
          substi x s t t' ->
          substi x s t1 t1' ->
          substi x s t2 t2' -> substi x s (tm_if t t1 t2) (tm_if t' t1' t2').

  Theorem substi_correct :
    forall x s t t', subst x s t = t' <-> substi x s t t'.
  Proof.
    split.
      - revert x s t'; induction t; intros; unfold subst in *.
          + rewrite <- H.
            constructor.
          + rewrite <- H.
            constructor.
          + case_eq (String.eqb x s); intro; rewrite -> H0 in H.
              * rewrite -> H.
                apply s_var1.
                apply String.eqb_eq.
                auto.
              * rewrite <- H.
                apply s_var2.
                apply String.eqb_neq.
                auto.
          + fold subst in *.
            case_eq (String.eqb x s); intro; rewrite -> H0 in H; rewrite <- H.
              * apply s_lam1.
                apply String.eqb_eq.
                auto.
              * apply s_lam2.
                  ** apply String.eqb_neq.
                     auto.
                  ** apply IHt.
                     reflexivity.
          + fold subst in *.
            rewrite <- H.
            constructor.
              * apply IHt1.
                reflexivity.
              * apply IHt2.
                reflexivity.
          + fold subst in *.
            rewrite <- H.
            constructor.
              * apply IHt1.
                reflexivity.
              * apply IHt2.
                reflexivity.
              * apply IHt3.
                reflexivity.
      - intro.
        induction H; unfold subst.
          + auto.
          + auto.
          + apply String.eqb_eq in H.
            rewrite -> H.
            reflexivity.
          + apply String.eqb_neq in H.
            rewrite -> H.
            reflexivity.
          + apply String.eqb_eq in H.
            rewrite -> H.
            reflexivity.
          + apply String.eqb_neq in H.
            rewrite -> H.
            fold subst.
            rewrite -> IHsubsti.
            reflexivity.
          + fold subst.
            rewrite -> IHsubsti1.
            rewrite -> IHsubsti2.
            reflexivity.
          + fold subst.
            rewrite -> IHsubsti1.
            rewrite -> IHsubsti2.
            rewrite -> IHsubsti3.
            reflexivity.
  Qed.

  Inductive step : Term -> Term -> Prop :=
    | ST_AppAbs :
        forall x T t v, value v -> step (tm_app (tm_lam x T t) v) (subst x v t)
    | ST_AppL :
        forall t1 t2 t1', step t1 t1' -> step (tm_app t1 t2) (tm_app t1' t2)
    | ST_AppR :
        forall t1 t2 t2', step t2 t2' -> step (tm_app t1 t2) (tm_app t1 t2')
    | ST_IfTrue : forall t1 t2, step (tm_if tm_true t1 t2) t1
    | ST_IfFalse : forall t1 t2, step (tm_if tm_false t1 t2) t2
    | ST_If :
        forall t t' t1 t2, step t t' -> step (tm_if t t1 t2) (tm_if t' t1 t2).

  Definition Env := string -> option Ty.

  Definition empty : Env := fun _ => None.

  Definition update (env : Env) (x : string) (T : Ty) : Env :=
    fun y =>
      if String.eqb x y
        then Some T
        else env y.

  Definition eq_Env (Gamma1 : Env) (Gamma2 : Env) : Prop :=
    forall x, Gamma1 x = Gamma2 x.

  Definition father_Env (Gamma1 : Env) (Gamma2 : Env) : Prop :=
    forall x, Gamma1 x = None \/ Gamma1 x = Gamma2 x.

  Lemma eq2father :
    forall Gamma1 Gamma2, eq_Env Gamma1 Gamma2 -> father_Env Gamma1 Gamma2.
  Proof.
    unfold eq_Env.
    unfold father_Env.
    intros.
    right.
    auto.
  Qed.

  Lemma eq_Env_refl :
    forall Gamma1 Gamma2, eq_Env Gamma1 Gamma2 -> eq_Env Gamma2 Gamma1.
  Proof.
    unfold eq_Env.
    intros.
    specialize (H x).
    auto.
  Qed.

  Lemma update_same :
    forall t T Gamma1 Gamma2,
      eq_Env Gamma1 Gamma2 -> eq_Env (update Gamma1 t T) (update Gamma2 t T).
  Proof.
    unfold eq_Env.
    intros.
    unfold update.
    case_eq (String.eqb t x); auto.
  Qed.

  Lemma father_update_same :
    forall t T Gamma1 Gamma2,
      father_Env Gamma1 Gamma2 ->
      father_Env (update Gamma1 t T) (update Gamma2 t T).
  Proof.
    unfold father_Env.
    intros.
    unfold update.
    case_eq (String.eqb t x); intros.
      - right.
        auto.
      - apply H.
  Qed.

  Lemma update_eq :
    forall x T1 T2 Gamma Gamma1 Gamma2,
      Gamma1 = update (update Gamma x T1) x T2 ->
      Gamma2 = update Gamma x T2 -> eq_Env Gamma1 Gamma2.
  Proof.
    unfold eq_Env.
    intros.
    rewrite -> H in *.
    rewrite -> H0 in *.
    unfold update.
    case_eq (String.eqb x x0); reflexivity.
  Qed.

  Lemma update_ne :
    forall x1 T1 x2 T2 Gamma Gamma1 Gamma2,
      x1 <> x2 ->
      Gamma1 = update (update Gamma x1 T1) x2 T2 ->
      Gamma2 = update (update Gamma x2 T2) x1 T1 -> eq_Env Gamma1 Gamma2.
  Proof.
    unfold eq_Env.
    intros.
    rewrite -> H0 in *.
    rewrite -> H1 in *.
    unfold update.
    case_eq (String.eqb x2 x); case_eq (String.eqb x1 x); try reflexivity.
    intros.
    apply String.eqb_eq in H2.
    apply String.eqb_eq in H3.
    rewrite -> H2 in H.
    rewrite -> H3 in H.
    exfalso.
    auto.
  Qed.

  Inductive has_Ty : Env -> Term -> Ty -> Prop :=
    | T_Var : forall Gamma x T, Gamma x = Some T -> has_Ty Gamma (tm_var x) T
    | T_Lam :
        forall Gamma x T1 t T2,
          has_Ty (update Gamma x T1) t T2 ->
          has_Ty Gamma (tm_lam x T1 t) (Ty_Arrow T1 T2)
    | T_App :
        forall Gamma t1 t2 T1 T2,
          has_Ty Gamma t1 (Ty_Arrow T2 T1) ->
          has_Ty Gamma t2 T2 -> has_Ty Gamma (tm_app t1 t2) T1
    | T_True : forall Gamma, has_Ty Gamma tm_true Ty_Bool
    | T_False : forall Gamma, has_Ty Gamma tm_false Ty_Bool
    | T_If :
        forall Gamma t t1 t2 T,
          has_Ty Gamma t Ty_Bool ->
          has_Ty Gamma t1 T ->
          has_Ty Gamma t2 T -> has_Ty Gamma (tm_if t t1 t2) T.

  Lemma type_father_env :
    forall t T Gamma1 Gamma2,
      has_Ty Gamma1 t T -> father_Env Gamma1 Gamma2 -> has_Ty Gamma2 t T.
  Proof.
    intro.
    induction t; intros; inversion H; econstructor.
      - specialize (H0 s).
        destruct H0.
          + rewrite -> H0 in *.
            discriminate.
          + rewrite -> H0 in *.
            auto.
      - eapply IHt; intros.
        apply H6.
        apply father_update_same.
        auto.
      - eapply IHt1.
        apply H4.
        auto.
      - eapply IHt2.
        apply H6.
        auto.
      - eapply IHt1.
        apply H5.
        auto.
      - eapply IHt2.
        apply H7.
        auto.
      - eapply IHt3.
        apply H8.
        auto.
  Qed.

  Lemma type_eq_env :
    forall Gamma1 Gamma2 t T,
      eq_Env Gamma1 Gamma2 -> has_Ty Gamma2 t T -> has_Ty Gamma1 t T.
  Proof.
    intros.
    eapply type_father_env.
      - apply H0.
      - apply eq2father.
        apply eq_Env_refl.
        auto.
  Qed.

  Inductive free : string -> Term -> Prop :=
    | F_Var : forall x, free x (tm_var x)
    | F_Lam : forall x y t T, x <> y -> free y t -> free y (tm_lam x T t)
    | F_App : forall x t1 t2, free x t1 \/ free x t2 -> free x (tm_app t1 t2)
    | F_If :
        forall x t t1 t2,
          free x t \/ free x t1 \/ free x t2 -> free x (tm_if t t1 t2).

  Definition closed (t : Term) : Prop := forall x, ~ free x t.

  Definition closed_in_gamma (Gamma : Env) (t : Term) : Prop :=
    forall x, Gamma x = None -> ~ free x t.

  Lemma well_typed_closed_in_gamma :
    forall t T Gamma, has_Ty Gamma t T -> closed_in_gamma Gamma t.
  Proof.
    unfold closed_in_gamma.
    unfold not.
    intro.
    induction t; intros.
      - inversion H1.
      - inversion H1.
      - inversion H1.
        inversion H.
        rewrite -> H4 in *.
        rewrite -> H6 in H0.
        discriminate.
      - inversion H1.
        inversion H.
        eapply IHt.
          + apply H13.
          + unfold update.
            apply String.eqb_neq in H5.
            rewrite -> H5.
            auto.
          + apply H7.
      - inversion H1.
        inversion H.
        destruct H4.
          + eapply IHt1.
            apply H9.
            apply H0.
            auto.
          + eapply IHt2.
            apply H11.
            apply H0.
            auto.
      - inversion H1.
        inversion H.
        destruct H4.
          + eapply IHt1.
            apply H11.
            apply H0.
            apply H4.
          + destruct H4.
              * eapply IHt2.
                apply H13.
                apply H0.
                apply H4.
              * eapply IHt3.
                apply H14.
                apply H0.
                apply H4.
  Qed.

  Lemma well_typed_closed : forall t T, has_Ty empty t T -> closed t.
  Proof.
    unfold closed.
    intros.
    apply well_typed_closed_in_gamma in H.
    unfold closed_in_gamma in H.
    specialize (H x).
    apply H.
    auto.
  Qed.

  Lemma subst_has_Ty :
    forall x t s T1 T2 Gamma,
      has_Ty empty s T2 ->
      has_Ty (update Gamma x T2) t T1 -> has_Ty Gamma (subst x s t) T1.
  Proof.
    intros.
    remember (subst x s t) as t'.
    remember empty as Empty.
    symmetry in Heqt'.
    apply substi_correct in Heqt'.
    revert T1 T2 H H0.
    generalize dependent Gamma.
    induction Heqt'; intros.
      - inversion H0.
        constructor.
      - inversion H0.
        constructor.
      - inversion H1.
        unfold update in H4.
        apply String.eqb_eq in H.
        rewrite -> H in H4.
        inversion H4.
        rewrite <- H7.
        eapply type_father_env.
          + unfold father_Env.
            intros.
            apply H0.
          + rewrite -> HeqEmpty.
            unfold father_Env.
            left.
            auto.
      - inversion H1.
        unfold update in H4.
        apply String.eqb_neq in H.
        rewrite -> H in H4.
        constructor.
        auto.
      - inversion H1.
        constructor.
        rewrite -> H in *.
        eapply type_eq_env.
          + apply eq_Env_refl.
            eapply update_eq.
            auto.
            auto.
          + apply H7.
      - inversion H1.
        constructor.
        eapply IHHeqt'.
        apply H0.
        eapply type_eq_env.
          + apply eq_Env_refl.
            eapply update_ne.
            apply H.
            auto.
            auto.
          + auto.
      - inversion H0.
        econstructor.
          + eapply IHHeqt'1.
            apply H.
            apply H4.
          + eapply IHHeqt'2.
            apply H.
            apply H6.
      - inversion H0.
        constructor.
          + eapply IHHeqt'1.
            apply H.
            auto.
          + eapply IHHeqt'2.
            apply H.
            auto.
          + eapply IHHeqt'3.
            apply H.
            auto.
  Qed.

  Theorem progress :
    forall t T, has_Ty empty t T -> value t \/ (exists t', step t t').
  Proof.
    intros.
    remember empty as Gamma.
    induction H.
      - rewrite -> HeqGamma in H.
        unfold empty in H.
        discriminate H.
      - left.
        constructor.
      - specialize (IHhas_Ty1 HeqGamma).
        specialize (IHhas_Ty2 HeqGamma).
        destruct IHhas_Ty1; destruct IHhas_Ty2; right.
          + destruct H1.
              * exists (subst x t2 t).
                constructor.
                auto.
              * inversion H.
              * inversion H.
          + destruct H2.
            exists (tm_app t1 x).
            constructor.
            auto.
          + destruct H1.
            exists (tm_app x t2).
            constructor.
            auto.
          + destruct H2.
            exists (tm_app t1 x).
            constructor.
            auto.
      - left.
        constructor.
      - left.
        constructor.
      - specialize (IHhas_Ty1 HeqGamma).
        specialize (IHhas_Ty2 HeqGamma).
        specialize (IHhas_Ty3 HeqGamma).
        destruct IHhas_Ty1; right.
          + destruct H2.
              * inversion H.
              * exists t2.
                constructor.
              * exists t1.
                constructor.
          + destruct H2.
            exists (tm_if x t1 t2).
            constructor.
            auto.
  Qed.

  Theorem preservation :
    forall t t' T, has_Ty empty t T -> step t t' -> has_Ty empty t' T.
  Proof.
    intros.
    revert t' H0.
    remember empty as Gamma.
    induction H; intros.
      - rewrite -> HeqGamma in H.
        discriminate H.
      - inversion H0.
      - inversion H1.
          + rewrite -> HeqGamma in *.
            eapply subst_has_Ty.
              * apply H0.
              * rewrite <- H2 in H.
                inversion H.
                auto.
          + specialize (IHhas_Ty1 HeqGamma t1' H5).
            apply (T_App Gamma t1' t2 T1 T2 IHhas_Ty1 H0).
          + specialize (IHhas_Ty2 HeqGamma t2' H5).
            apply (T_App Gamma t1 t2' T1 T2 H IHhas_Ty2).
      - inversion H0.
      - inversion H0.
      - inversion H2.
          + rewrite <- H3.
            auto.
          + rewrite <- H3.
            auto.
          + constructor; try apply (IHhas_Ty1 HeqGamma); auto.
  Qed.

  Inductive multi : Term -> Term -> Prop :=
    | multi_refl : forall x, multi x x
    | multi_step : forall x y z, step x y -> multi y z -> multi x z.

  Theorem multi_R : forall x y, step x y -> multi x y.
  Proof.
    intros.
    apply (multi_step x y y); try constructor; auto.
  Qed.

  Theorem multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros.
    induction H.
      - auto.
      - apply (multi_step x y z); auto.
  Qed.

  Theorem multi_progress :
    forall t T, has_Ty empty t T -> value t \/ (exists t', multi t t').
  Proof.
    intros.
    apply progress in H.
    destruct H.
      - auto.
      - right.
        destruct H.
        exists x.
        apply multi_R.
        auto.
  Qed.

  Theorem multi_preservation :
    forall t t' T, has_Ty empty t T -> multi t t' -> has_Ty empty t' T.
  Proof.
    intros.
    generalize dependent T.
    induction H0; intros.
      - auto.
      - eapply IHmulti.
        eapply preservation.
        apply H1.
        auto.
  Qed.

  Definition stuck (t : Term) : Prop := ~ (exists t', step t t') /\ ~ value t.

  Theorem soundness :
    forall t t' T, has_Ty empty t T -> multi t t' -> ~ stuck t'.
  Proof.
    unfold not.
    unfold stuck.
    intros.
    destruct H1.
    eapply multi_preservation in H0.
      - eapply progress in H0.
        destruct H0; auto.
      - apply H.
  Qed.
