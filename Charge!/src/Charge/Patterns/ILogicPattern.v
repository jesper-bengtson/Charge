Section MakeILogic.
  Context {typ func : Set} {FV : PartialView func (ilfunc typ)}.

  Definition fTrue t := f_insert (ilf_true t).
  Definition fFalse t := f_insert (ilf_false t).
  Definition fAnd t := f_insert (ilf_and t).
  Definition fOr t := f_insert (ilf_or t).
  Definition fImpl t := f_insert (ilf_impl t).
  Definition fEntails t := f_insert (ilf_entails t).
  Definition fExists t u := f_insert (ilf_exists t u).
  Definition fForall t u := f_insert (ilf_forall t u).

  Definition mkEntails (t : typ) (P Q : expr typ func) := App (App (Inj (fEntails t)) P) Q.
  Definition mkTrue t : expr typ func := Inj (fTrue t).
  Definition mkFalse t : expr typ func := Inj (fFalse t).
  Definition mkAnd (t : typ) (P Q : expr typ func) := App (App (Inj (fAnd t)) P) Q.
  Definition mkOr (t : typ) (P Q : expr typ func) := App (App (Inj (fOr t)) P) Q.
  Definition mkImpl (t : typ) (P Q : expr typ func) := App (App (Inj (fImpl t)) P) Q.
  Definition mkExists (t l : typ) (f : expr typ func) := App (Inj (fExists t l)) (Abs t f).
  Definition mkForall (t l : typ) (f : expr typ func) := App (Inj (fForall t l)) (Abs t f).

  Definition fptrnTrue {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => p t U good (fun x => bad (ilf_true t))
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnFalse {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => p t U good (fun x => bad (ilf_false t))
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnAnd {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => p t U good (fun x => bad (ilf_and t))
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnOr {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => p t U good (fun x => bad (ilf_or t))
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnImpl {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => p t U good (fun x => bad (ilf_impl t))
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnEntails {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => p t U good (fun x => bad (ilf_entails t))
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnExists {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => p (t, u) U good (fun x => bad (ilf_exists t u))
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnForall {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => p (t, u) U good (fun x => bad (ilf_forall t u))
      end.

  Global Instance fptrnEntails_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEntails p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok logic) | | | | | | |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnTrue_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnTrue p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok logic) | | | | | |].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnFalse_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnFalse p).
  Proof.
    red; intros.
    destruct x; simpl; [| |destruct (Hok logic) | | | | |].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnAnd_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnAnd p).
  Proof.
    red; intros.
    destruct x; simpl; [| | | destruct (Hok logic) | | | |].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnOr_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnOr p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnImpl_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnImpl p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnExists_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnExists p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok (arg, logic)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnForall_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnExists p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok (arg, logic)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

 
  Lemma Succeeds_fptrnTrue {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnTrue p) res) :
    exists t, Succeeds t p res /\ f = ilf_true t.
  Proof.
    unfold Succeeds, fptrnTrue in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnFalse {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnFalse p) res) :
    exists t, Succeeds t p res /\ f = ilf_false t.
  Proof.
    unfold Succeeds, fptrnFalse in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnEntails {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEntails p) res) :
    exists t, Succeeds t p res /\ f = ilf_entails t.
  Proof.
    unfold Succeeds, fptrnEntails in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnAnd {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnAnd p) res) :
    exists t, Succeeds t p res /\ f = ilf_and t.
  Proof.
    unfold Succeeds, fptrnAnd in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnOr {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnOr p) res) :
    exists t, Succeeds t p res /\ f = ilf_or t.
  Proof.
    unfold Succeeds, fptrnOr in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnImpl {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnImpl p) res) :
    exists t, Succeeds t p res /\ f = ilf_impl t.
  Proof.
    unfold Succeeds, fptrnImpl in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnExists {T : Type} (f : ilfunc typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnExists p) res) :
    exists t u, Succeeds (t, u) p res /\ f = ilf_exists t u.
  Proof.
    unfold Succeeds, fptrnExists in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (arg, logic)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists arg, logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnForall {T : Type} (f : ilfunc typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnForall p) res) :
    exists t u, Succeeds (t, u) p res /\ f = ilf_forall t u.
  Proof.
    unfold Succeeds, fptrnForall in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (arg, logic)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists arg, logic; split; [assumption | reflexivity].
  Qed.
  
  Global Instance fptrnTrue_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnTrue p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_true t;
      s_elim := @Succeeds_fptrnTrue T f p res pok
    }.

  Global Instance fptrnFalse_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnFalse p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_false t;
      s_elim := @Succeeds_fptrnFalse T f p res pok
    }.

  Global Instance fptrnEntails_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEntails p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_entails t;
      s_elim := @Succeeds_fptrnEntails T f p res pok
    }.

  Global Instance fptrnAnd_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnAnd p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_and t;
      s_elim := @Succeeds_fptrnAnd T f p res pok
    }.

  Global Instance fptrnOr_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnOr p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_or t;
      s_elim := @Succeeds_fptrnOr T f p res pok
    }.

  Global Instance fptrnImpl_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnImpl p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_impl t;
      s_elim := @Succeeds_fptrnImpl T f p res pok
    }.

  Global Instance fptrnExists_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnExists p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = ilf_exists t u;
      s_elim := @Succeeds_fptrnExists T f p res pok
    }.

  Global Instance fptrnForall_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnForall p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = ilf_forall t u;
      s_elim := @Succeeds_fptrnForall T f p res pok
    }.

End MakeILogic.

Section ILogicPtrn.
  Context {typ func : Set} {FV : PartialView func (ilfunc typ)}.

 Definition ptrnTrue {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnTrue p)).

  Definition ptrnFalse {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnFalse p)).

  Definition ptrnEntails {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnEntails p))) a) b.

  Definition ptrnAnd {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnAnd p))) a) b.

  Definition ptrnOr {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnOr p))) a) b.

  Definition ptrnImpl {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnImpl p))) a) b.

  Definition ptrnExists {A T : Type}
             (p : ptrn (typ * typ) T)
             (f : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnExists p))) f.

  Definition ptrnForall {A T : Type}
             (p : ptrn (typ * typ) T)
             (f : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnForall p))) f.

Definition ilogic_ptrn_cases {T : Type}
           (do_true : typ -> T)
           (do_false : typ -> T)
           (do_and : typ -> expr typ func -> expr typ func -> T)
           (do_or : typ -> expr typ func -> expr typ func -> T)
           (do_impl : typ -> expr typ func -> expr typ func -> T)
           (do_exists : typ -> typ -> expr typ func -> T)
           (do_forall : typ -> typ -> expr typ func -> T) : ptrn (expr typ func) T :=
  por (inj (ptrn_view _ (por (fptrnTrue (pmap do_true get))
                             (fptrnFalse (pmap do_false get)))))
      (appr (por (appr (inj (ptrn_view _ 
                                       (por (fptrnAnd (pmap do_and get)) 
                                            (por (fptrnOr (pmap do_or get))
                                                 (fptrnImpl (pmap do_impl get)))))) get)
                 (inj (ptrn_view _ (por (fptrnExists (pmap 
                                                        (fun x f => do_exists (fst x) 
                                                                              (snd x) f) get))
                                        (fptrnForall (pmap 
                                                        (fun x f => do_forall (fst x) 
                                                                              (snd x) f) get))))))
            get).

Definition ilogic_cases {T : Type}
           (do_true : typ -> T)
           (do_false : typ -> T)
           (do_and : typ -> expr typ func -> expr typ func -> T)
           (do_or : typ -> expr typ func -> expr typ func -> T)
           (do_impl : typ -> expr typ func -> expr typ func -> T)
           (do_exists : typ -> typ -> expr typ func -> T)
           (do_forall : typ -> typ -> expr typ func -> T)
           (do_default : T) :=
  run_ptrn (ilogic_ptrn_cases
              do_true do_false do_and do_or do_impl do_exists do_forall)
           do_default.
           
End ILogicPtrn.
