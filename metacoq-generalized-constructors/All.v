Require Export MetaCoq.Template.All.
Require Export MetaCoq.PCUIC.PCUICAst MetaCoq.PCUIC.PCUICLiftSubst MetaCoq.Checker.All.
Require Export List String.
Export ListNotations MonadNotation.

From MetaCoq.PCUIC Require Export PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require PCUICToTemplate TemplateToPCUIC.

Existing Instance config.default_checker_flags.

Existing Instance default_fuel.
Open Scope string_scope.

Definition make_plugin {X} (f : global_env_ext -> context -> term -> term) (x : X) {Y} : TemplateMonad Y :=
  tmBind (tmQuoteRec x) (fun '(Sigma, q_x) =>
                           tmUnquoteTyped Y (PCUICToTemplate.trans (f (TemplateToPCUIC.trans_global (Sigma, Monomorphic_ctx ContextSet.empty)) [] (TemplateToPCUIC.trans q_x)))).

Definition make_lemma {X} name (f : global_env_ext -> context -> term -> term) (x : X) : TemplateMonad unit :=
  tmBind (tmQuoteRec x) (fun '(Sigma, q_x) =>
                           tmBind (tmUnquoteTyped Type (PCUICToTemplate.trans (f (TemplateToPCUIC.trans_global (Sigma, Monomorphic_ctx ContextSet.empty)) [] (TemplateToPCUIC.trans q_x)))) (fun t => tmBind (tmLemma name t) (fun _ => tmReturn tt))).

Definition try_infer `{config.checker_flags} `{Fuel} (Σ : global_env_ext) Γ t :=
  match infer' (PCUICToTemplate.trans_global Σ) (PCUICToTemplate.trans_local Γ) (PCUICToTemplate.trans t) with Checked res => TemplateToPCUIC.trans res | TypeError _ => tApp (tVar "error") t end.

Definition tEq := TemplateToPCUIC.trans <% @eq %>.

Definition abstract_eqns (Σ : global_env_ext) (Γ : context) (t : term) : term :=
  let fix abstract_eqns (Γ : context) (ty : term) n :=
      match ty with
      | tProd na A B =>
        tProd na A (abstract_eqns (Γ ,, vass na A) B 0)
      | tApp L A =>
        let type_of_x := try_infer Σ Γ (lift (2 * n) 0 A) in
        let eqn := mkApps tEq [type_of_x; tRel 0; lift (1 + 2 * n) 0 A] in
        tProd (nNamed "x") type_of_x
              (tProd (nAnon) eqn (abstract_eqns (Γ,, vass (nNamed "x") type_of_x ,, vass nAnon eqn) L (S n)))
      | B => mkApps B (map (fun m => tRel (1 + 2 * m)) (seq 0 n))
      end
  in let ty := try_infer Σ Γ t in abstract_eqns Γ ty 0.

Coercion Nanon := vass nAnon.
Local Notation "a '↦' b" := (vass a b) (at level 10).

(* Fixpoint abstract_eqns (Σ : global_env_ext) (Γ : context) (ty : term) (n : nat) : term := *)
(*   match ty with *)
(*   | tProd na A B => *)
(*     tProd na A (abstract_eqns Σ (Γ ,, na ↦ A) B 0) *)
(*   | tApp L A => *)
(*     let type_of_x := try_infer Σ Γ (lift (2 * n) 0 A) in *)
(*     let eqn := mkApps tEq [type_of_x; tRel 0; lift (1 + 2 * n) 0 A] in *)
(*     tProd (nNamed "x") type_of_x *)
(*           (tProd (nAnon) eqn (abstract_eqns Σ (Γ,, nNamed "x" ↦ type_of_x ,, eqn) L (S n))) *)
(*   | B => mkApps B (map (fun m => tRel (1 + 2 * m)) (seq 0 n)) *)
(*   end. *)
(*   in let ty := try_infer Σ Γ t in abstract_eqns Γ ty 0. *)

Ltac eqn_apply C := run_template_program (make_plugin (Y := Prop) abstract_eqns C)
                       (fun lem =>
                          let H := fresh "H" in
                          assert lem as H by (cbn;intros;subst;now eapply C); cbn [my_projT2] in H
                          ;eapply H; clear H ).

MetaCoq Run (make_plugin abstract_eqns le_S >>= tmPrint).

Goal forall n m, le n m -> forall x1, x1 = n -> forall x2, x2 = S m -> le x1 x2.
Proof.
  intros. eqn_apply le_S; eauto.
Qed.

Module test.

Variable A B C:Type.
Variable c0:C.
Variable a0:A.
Variable f: C -> B.
Variable f': C -> B.

Inductive foo : A -> B -> Prop :=
| Foo : forall c, foo a0 (f c).

MetaCoq Run (make_plugin abstract_eqns Foo >>= tmPrint).

Lemma foobar: foo a0 (f' c0). 
Proof.
  eqn_apply Foo.
Abort.

End test.

Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x;;
  match t with 
  | Ast.tLambda (nNamed na) _ _ => tmReturn na
  | _ => tmReturn "" 
  end.

Notation name_of n := (ltac:(let k x := exact x in run_template_program (getName (fun n : nat => 0)) k)).

Notation "'Derive' 'Generalized' 'Constructor' 'for' N 'as' n" := (name <- getName (fun n : nat => n);; make_lemma name abstract_eqns N) (at level 0).

Global Obligation Tactic := cbn; intros; subst; econstructor; eauto.

(* Fixpoint make_generalize_constructors name n {f : Fuel} : TemplateMonad unit := *)
(*   match f with 0 => ret tt | S f =>  *)
(*   ctr <- tmUnquote (Ast.tConstruct (mkInd name 0) n []) ;; *)
(*   make_lemma (String.append name (string_of_nat n)) abstract_eqns (my_projT2 ctr);; *)
(*   @make_generalize_constructors name (S n) f end. *)

(* MetaCoq Run Derive Generalized Constructor le_S as bla. *)
(* Compute bla. *)

(* MetaCoq Run (make_generalize_constructors "brtree" 0). *)
(* Next Obligation. *)
(* Unshelve. *)


(* Fixpoint make_generalized_constructors (name : string) (inst : Instance.t) (ctors : list ((ident × Ast.term) × nat)) : TemplateMonad unit := *)
(*   match ctors with *)
(*   | nil => ret tt *)
(*   | ((ctr_name, ctr_type), idx) :: ctors => *)
(*     constr <- tmUnquote (Ast.tConstruct (mkInd name 0) idx []) ;; *)
(*     make_lemma (String.append ctr_name "_eqs") abstract_eqns (my_projT2 constr) ;; *)
(*     make_generalized_constructors name inst ctors *)
(*   end. *)

(* Definition generalized_constructors {X} (type : X) : TemplateMonad unit := *)
(*   ty <- tmQuote type;; *)
(*   match ty with *)
(*   | Ast.tInd (mkInd name i) inst => *)
(*     i <- tmQuoteInductive name ;; *)
(*     match i.(Ast.ind_bodies) with *)
(*     | b :: _ =>  *)
(*       make_generalized_constructors name inst (b.(Ast.ind_ctors)) *)
(*     | _ => tmFail" empty inductive" *)
(*     end *)
(*   | _ => tmFail "not an inductive" *)
(*   end. *)

(* MetaCoq Run (generalized_constructors brtree). *)


(* MetaCoq Run (make_plugin abstract_eqns Node' >>= tmPrint). *)

(* Ltac abstract_eqns' T := *)
(*   match constr:(T) with *)
(*   | forall x : ?X, ?T => *)
(*     let res := abstract_eqns' T in *)
(*      constr:(forall x : X, res) *)
(*    | ?L ?A => let type_of_x := type of A in *)
(*              let x := fresh "x" in *)
(*              let res := abstract_eqns' L in *)
(*              constr:(forall x : type_of x, x = A -> res) *)
(*   end. *)
(* Ltac abstract_eqns C := let T := type of C in abstract_eqns' T. *)

(* Ltac eqn_apply C := let lem := abstract_eqns C in  *)
(*                     assert lem as H by (cbn;intros;subst;now eapply C); cbn [my_projT2] in H *)
(*                     ;eapply H; clear H. *)

(* Goal forall n m, le n m -> forall x1, x1 = n -> forall x2, x2 = S m -> le x1 x2. *)
(* Proof. *)
(*   intros. *)
(*   Set Ltac Debug. *)
(*   eqn_apply le_S. *)
(* Qed. *)
