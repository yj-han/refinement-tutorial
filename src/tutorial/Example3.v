From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.
From Tutorial Require Import Imp Simulation.

Set Implicit Arguments.

Section EX.
  (** Let us revisit examples in Example2.v, and prove them with correct simulation. *)

  (* DIV2. Prove by coinduction. *)
  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com :=
    <{ "x" := 100;
       while ("x")
do ("x" := AAny)
       end;
       ret "x"
    }>.

(* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub :=
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

(* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (guclo @sim_indC_spec; econs 4;
         [ss
    |ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  (* Makes a src silent step. *)
  Ltac step_src_silent :=
    try (guclo @sim_indC_spec; econs 3;
         [ss
         | ss; exists (inr LInternal); eexists; splits; ss; [repeat econs | ]
    ]).

  Goal refines (Imp_Program_Ext src6) (Imp_Program_Ext tgt6).
  Proof.
apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Ext, src6, tgt6, Imp_init.
    ss. intros.
    (* *gpaco* is more convenient here: we will do up-to reasoning with the inductive closure (sim_indC). *)
    ginit.
    guclo @sim_indC_spec. econs 4. ss.
    i. inv H. 2: solve_tgt_ub. inv STEP. split; auto.
    (* Combining above into a tactic and take steps until the while loop. *)
    step_tgt_silent. step_tgt_silent. step_tgt_silent.
    inv H6.
    (* The target reached a while loop. We take the source side to the loop too. *)
    do 4 step_src_silent.

    (** Now we start a coinductive proof. We first set up a coinductive hypothesis. *)
    clear ps pt.
    remember Reg.init as reg. clear Heqreg.
    remember 100 as n. clear Heqn.
    (* Generalize the progress flags. *)
    pose proof true as ps. pose proof true as pt.
    guclo @sim_progressC_spec. econs. instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
    revert reg n ps pt. gcofix CIH. i.
    (* Then make progress. *)
    step_tgt_silent.
    - (* False case; loop terminates. *)
      clear CIH.
      inv H6. inv H1.
      do 2 step_src_silent.
      do 2 step_tgt_silent.
      inv H5. inv H1.
      do 1 step_src_silent.
      gstep. econs; ss.
    - (* True case; loops. *)
      rename H7 into TRUE. inv H6. inv H1.
      step_tgt_silent.
      inv H6.
      step_tgt_silent.
      (* Tactic 'step_src_silent' picks wrong constructor, so we prove manually. *)
      guclo @sim_indC_spec. econs 3; ss. do 2 eexists. splits.
      { econs 1. eapply E_WhileTrue. repeat econs. auto. }
      { ss. }
      (* AAny introduces nondeterminism. We picks what we need when AAny is in the src. *)
      guclo @sim_indC_spec. econs 3; ss. do 2 eexists. splits.
      { econs 1. eapply E_Asgn. eapply (E_AAny _ n). }
      { ss. }
      step_src_silent.
      (* Now we came back to the start of the while loop. We can end the proof by coinduction. *)
      gstep. eapply sim_progress. 2,3: auto.
      gfinal. left. eapply CIH.
      Unshelve. exact 0.
    - (* Leftover undef case. *)
      exfalso. destruct (Nat.eqb n 0) eqn:CASES.
      + eapply UNDEF. eapply E_WhileFalse. repeat econs. apply PeanoNat.Nat.eqb_eq. auto.
      + eapply UNDEF. eapply E_WhileTrue. repeat econs. apply PeanoNat.Nat.eqb_neq; auto.
  Qed.


  (** This simulation is sound, as proven by the adequacy theorem, and the following examples cannot be proven as expected.
      You can check that you cannot *unguard* the coinductive hypothesis, because either the source or the target side progress flag is not set to true.
   *)

  (* EX1. The src terminates, but the tgt diverges. *)
  Definition src1 : com :=
    <{ ret 0 }>.

  Definition tgt1 : com :=
    <{ while (1)
       do skip
       end;
       ret 1
    }>.

  Goal refines (Imp_Program_Ext src1) (Imp_Program_Ext tgt1).
  Proof.
  Abort.

End EX.

Section EXOPT.
  (* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub :=
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  Ltac step_tgt_silent1 :=
    try (econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (guclo @sim_indC_spec; step_tgt_silent1).

  (* Makes a src silent step. *)
  Ltac step_src_silent1 :=
    try (econs 3;
         [ss
         | ss; exists (inr LInternal); eexists; splits; ss; [repeat econs | ]
      ]).

  Ltac step_src_silent :=
    try (guclo @sim_indC_spec; step_src_silent1).

  (** Code optimizations are insteresting examples to verify with our simulation.
      Note that you will need to find a loop invariant.
   *)

  (* OPT1. Store-to-load forwarding. *)
  Definition src_opt1 : com :=
    <{ "c" :=@ "scan" <[]>;
       &<1> := "c";
       "x" := &<1>;
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := &<1>)
       end;
       ret 0
    }>.

  Definition tgt_opt1 : com :=
    <{ "c" :=@ "scan" <[]>;
       &<1> := "c";
       "x" := "c";
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := "c")
       end;
       ret 0
    }>.

  Goal refines (Imp_Program_Ext src_opt1) (Imp_Program_Ext tgt_opt1).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Ext, src_opt1, tgt_opt1, Imp_init.
    ss. intros.
    ginit.
    step_tgt_silent. step_src_silent.

    guclo @sim_indC_spec. econs 2; ss.
    i. inv H. inv STEP. inv H7. ss; split; auto.
    eexists. split. repeat econs.
    2: { solve_tgt_ub. Unshelve. exact O. }
    econs 6; ss.
    step_tgt_silent. step_src_silent.
 
    step_tgt_silent. step_src_silent.
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.
    step_tgt_silent. step_src_silent.
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.
    inv H6. inv H7. inv H1. inv H2.
    
    step_tgt_silent. step_src_silent.
    clear ps pt.
    remember (Reg.write Reg.init "c" n) as reg.
    assert (H: Reg.read reg "c" = Some n). { inv Heqreg. ss. }
    clear Heqreg.
    remember Mem.init as mem. clear Heqmem.
    pose proof true as ps. pose proof true as pt.
    guclo @sim_progressC_spec. econs. instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
    revert H. revert reg n ps pt. gcofix CIH. i.

    step_tgt_silent.
    - step_src_silent.
      + inv H7. inv H2. ss.
      + step_tgt_silent. step_src_silent.
        step_tgt_silent. step_src_silent.
        inv H7. inv H6.
        guclo @sim_indC_spec. econs 1; ss.
    - rename H8 into TRUE. inv H7. inv H2.
      guclo @sim_indC_spec. econs 3; ss. do 2 eexists. splits.
      + econs 1. eapply E_WhileTrue. repeat econs. auto.
      + ss.
      + step_tgt_silent. step_src_silent.
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H8. ss; split; auto.
        eexists. split. repeat econs.
        2: { solve_tgt_ub. Unshelve. exact O. }
        econs 6; ss.
        step_tgt_silent. step_src_silent.
        
        step_tgt_silent. step_src_silent.
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H8. ss; split; auto.
        eexists. split. repeat econs.
        4: { solve_tgt_ub. Unshelve. exact O. }
        { inv H2. inv H3. ss. }
        { inv H4. ss. }
        econs 6; ss.
        step_tgt_silent. step_src_silent.

        step_tgt_silent. 
        guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
        step_tgt_silent. step_src_silent.
        2: { solve_tgt_ub. unfold Reg.write. unfold Reg.read in H0. ss. eauto.
          Unshelve. exact O. }

        inv H9. unfold Reg.write in H3. inv H3. unfold Reg.read in H0. rewrite H0 in H1. inv H1.
        gstep. eapply sim_progress. 2,3: auto.
        gfinal. left. eapply CIH.
        ss.
    - exfalso. destruct (Nat.eqb n 0) eqn:CASES.
      + eapply UNDEF. eapply E_WhileFalse. repeat econs. apply PeanoNat.Nat.eqb_eq. auto.
      + eapply UNDEF. eapply E_WhileTrue. repeat econs. apply PeanoNat.Nat.eqb_neq; auto.
  Qed.

  (* OPT2. Load-to-load forwarding. *)
  Definition src_opt2 : com :=
    <{ "a" :=@ "scan" <[]>;
       &<1> := "a";
       "c" := &<1>;
       "x" := &<1>;
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := &<1>)
       end;
       ret 0
    }>.

  Definition tgt_opt2 : com :=
    <{ "a" :=@ "scan" <[]>;
       &<1> := "a";
       "c" := &<1>;
       "x" := "c";
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := "c")
       end;
       ret 0
    }>.

  Goal refines (Imp_Program_Ext src_opt2) (Imp_Program_Ext tgt_opt2).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Ext, src_opt1, tgt_opt1, Imp_init.
    ss. intros.
    ginit.
    step_tgt_silent. step_src_silent.

    guclo @sim_indC_spec. econs 2; ss.
    i. inv H. inv STEP. inv H7. ss; split; auto.
    eexists. split. repeat econs.
    2: { solve_tgt_ub. Unshelve. exact O. }
    econs 6; ss.
    step_tgt_silent. step_src_silent.
    
    step_tgt_silent. step_src_silent.
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.
    step_tgt_silent. step_src_silent.
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.
    step_tgt_silent. step_src_silent.
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.
   
    step_tgt_silent. step_src_silent.
    inv H6. inv H7. inv H8. inv H1. inv H2.
    clear ps pt.
    remember (Reg.write (Reg.write Reg.init "a" n) "c" n) as reg.
    assert (H: reg "c" = Some n). { inv Heqreg. ss. }
    clear Heqreg.
    remember Mem.init as mem. clear Heqmem.
    pose proof true as ps. pose proof true as pt.
    guclo @sim_progressC_spec. econs. instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
    revert H. revert reg n ps pt. gcofix CIH. i.

    step_tgt_silent.
    - step_src_silent.
      + inv H7. inv H2. ss.
      + step_tgt_silent. step_src_silent.
        step_tgt_silent. step_src_silent.
        inv H7. inv H6.
        guclo @sim_indC_spec. econs 1; ss.
    - rename H8 into TRUE. inv H7. inv H2.
      guclo @sim_indC_spec. econs 3; ss. do 2 eexists. splits.
      + econs 1. eapply E_WhileTrue. repeat econs. auto.
      + ss.
      + step_tgt_silent. step_src_silent.
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H8. ss; split; auto.
        eexists. split. repeat econs.
        2: { solve_tgt_ub. Unshelve. exact O. }
        econs 6; ss.
        step_tgt_silent. step_src_silent.

        step_tgt_silent. step_src_silent.
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H8. ss; split; auto.
        eexists. split. repeat econs.
        4: { solve_tgt_ub. Unshelve. exact O. }
        { inv H2. inv H3. ss. }
        { inv H4. ss. }
        econs 6; ss.
        step_tgt_silent. step_src_silent.

        step_tgt_silent. 
        guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
        step_tgt_silent. step_src_silent.
        2: { solve_tgt_ub. unfold Reg.write. unfold Reg.read in H0. ss. eauto.
          Unshelve. exact O. }

        inv H9. unfold Reg.write in H3. inv H3. unfold Reg.read in H0. rewrite H0 in H1. inv H1.
        gstep. eapply sim_progress. 2,3: auto.
        gfinal. left. eapply CIH.
        ss.
    - exfalso. destruct (Nat.eqb n 0) eqn:CASES.
      + eapply UNDEF. eapply E_WhileFalse. repeat econs. apply PeanoNat.Nat.eqb_eq. auto.
      + eapply UNDEF. eapply E_WhileTrue. repeat econs. apply PeanoNat.Nat.eqb_neq; auto.
  Qed.

  (* OPT3. Loop invariant code motion. *)
  Definition src_opt3 : com :=
    <{ &<1> := 1;
       while (1)
       do ("x" :=@ "scan" <[]>;
           "a" := &<1>;
           "x" := "x" + "a";
           "a" :=@ "print" <["x" : aexp]>)
       end;
       ret 0
    }>.

  Definition tgt_opt3 : com :=
    <{ &<1> := 1;
       "c" := &<1>;
       while (1)
       do ("x" :=@ "scan" <[]>;
           "a" := "c";
           "x" := "x" + "a";
           "a" :=@ "print" <["x" : aexp]>)
       end;
       ret 0
    }>.

  Goal refines (Imp_Program_Ext src_opt3) (Imp_Program_Ext tgt_opt3).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Ext, src_opt1, tgt_opt1, Imp_init.
    ss. intros.
    ginit.
    step_tgt_silent. step_src_silent.
  
    step_tgt_silent.
    guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. ss.
    step_tgt_silent. step_src_silent.

    do 3 step_tgt_silent.
    step_tgt_silent. step_src_silent.

    inv H6. inv H7.
    clear ps pt.
    remember 1 as n. clear Heqn.
    remember Reg.init as reg1. clear Heqreg1.
    remember (Reg.write reg1 "c" n) as reg2.
    assert (HR: reg2 "c" = Some n). { inv Heqreg2. ss. }
    clear Heqreg2.
    remember (Mem.store Mem.init n n) as mem.
    assert (HM: Mem.load mem n = Some n).
    { inv Heqmem. unfold Mem.load, Mem.store.
      case_eq (Nat.eqb n n). ss.
      i. apply EqNat.beq_nat_false in H. exfalso. auto. }
    clear Heqmem.
    pose proof true as ps. pose proof true as pt.
    guclo @sim_progressC_spec. econs. instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
    revert HR HM. revert reg1 reg2 mem n ps pt. gcofix CIH. i.
    
    step_tgt_silent.
    - step_src_silent.
      + inv H6. ss.
      + step_tgt_silent. step_src_silent.
        inv H6.
        step_tgt_silent. step_src_silent.
        inv H5.
        guclo @sim_indC_spec. econs 1; ss.
    - rename H7 into TRUE. inv H6.
      guclo @sim_indC_spec. econs 3; ss. do 2 eexists. splits.
      + econs 1. eapply E_WhileTrue. repeat econs. auto.
      + ss.
      + step_tgt_silent. step_src_silent.
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H7. ss; split; auto.
        eexists. split. repeat econs.
        2: { solve_tgt_ub. Unshelve. exact O. }
        econs 6; ss. 
        step_tgt_silent. step_src_silent.

        step_tgt_silent. step_src_silent.
        step_tgt_silent.
        guclo @sim_indC_spec. econs 3; ss. do 2 eexists; splits. repeat econs. apply HM. ss.
        step_tgt_silent. step_src_silent.

        do 3 step_tgt_silent. do 3 step_src_silent.
        
        inv H6. inv H7. inv H5. inv H2. inv H1. inv H6.
        inv HR. unfold Reg.write in H0. simpl in H0. rewrite H0 in H1. inv H1. inv H2.
        2: { eauto. }
        guclo @sim_indC_spec. econs 2; ss.
        i. inv H. inv STEP. inv H8. ss; split; auto.
        eexists. split. repeat econs.
        4: { solve_tgt_ub. Unshelve. exact O. }
        { inv H2. inv H3. ss. }
        { inv H4. ss. }
        econs 6; ss.
        step_tgt_silent. step_src_silent.

        gstep. eapply sim_progress. 2,3: auto.
        gfinal. left. eapply CIH; ss.
    - exfalso. destruct (Nat.eqb n 0) eqn:CASES.
      + eapply UNDEF. eapply E_WhileFalse. repeat econs. apply PeanoNat.Nat.eqb_eq. auto.
      + eapply UNDEF. eapply E_WhileTrue. repeat econs. apply PeanoNat.Nat.eqb_neq; auto.
  Qed.

End EXOPT.
