Require Import List Lia.
Import ListNotations.

Require Import Undecidability.CFG.CFG.
Require Import Undecidability.CFG.CFP.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Import PCPListNotation.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Undecidability.CFG.Reductions.CFPP_to_CFP.

Require Import Undecidability.Synthetic.Definitions.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section PCP_CFA.

    Variable P : stack nat.

    Definition Sigma := sym P.
    Notation "#" := (fresh Sigma).

    Definition gamma1 (A : stack nat) := 
        map (fun '(x, y) => (x, ([#] ++ x ++  [#] ++ y))) A.

    Definition gamma2 (A: stack nat) := 
        map (fun '(x, y) => (y, ([#] ++ x ++  [#] ++ y))) A.

    Definition create_cfg :=
        let startsym1 := (fresh (sym P ++ [#])) in
        let Post_CFG1 := CFPP_to_CFP.G (gamma1 P) # startsym1 in
        let startsym2 := fresh (sym P ++ [#] ++ [startsym1]) in
        let Post_CFG2 := CFPP_to_CFP.G (gamma2 P) # startsym2 in
        let new_start_sym := fresh (sym P ++ [#] ++ [startsym1] ++ [startsym2]) in
        (new_start_sym, [(new_start_sym, [startsym Post_CFG1])] ++ [(new_start_sym, [startsym Post_CFG2])] ++ rules Post_CFG1 ++ rules Post_CFG2).

    Fixpoint gamma (A: stack nat) :=
    match A with
        | [] => []
        | (x, y) :: A => gamma A ++ [#] ++ x ++ [#] ++ y   
    end.

    Lemma sigma_gamma1 A :
        sigma # (gamma1 A) = tau1 A ++ [#] ++ gamma A.
    Proof.
        induction A as [ | (x, y)]; cbn.
        - reflexivity.
        - unfold gamma1 in IHA. cbn in *.
          rewrite IHA. now simpl_list.
    Qed. 

    Lemma sigma_gamma2 A:
        sigma # (gamma2 A) = tau2 A ++ [#] ++ gamma A.
        Proof.
            induction A as [ | (x, y)]; cbn.
            - reflexivity.
            - unfold gamma2 in IHA. cbn in *.
              rewrite IHA. now simpl_list.
        Qed.

End PCP_CFA.


Theorem gamma1_incl (P R: stack sig): (P <<= R) -> (gamma1 R P <<= gamma1 R R).
Proof.
    intros.
    unfold gamma1.
    apply (incl_map (fun '(x0, y) => (x0, [fresh (Sigma R)] ++ x0 ++ [fresh (Sigma R)] ++ y)) H).
Qed.

Theorem gamma2_incl (P R: stack sig): (P <<= R) -> (gamma2 R P <<= gamma2 R R).
Proof.
    intros.
    unfold gamma2.
    apply (incl_map (fun '(x, y0) => (y0, [fresh (Sigma R)] ++ x ++ [fresh (Sigma R)] ++ y0)) H).
Qed.

Theorem reduction: 
    PCP ⪯ CFA.
Proof.
    unfold "⪯".
    exists create_cfg.
    intros R.
    remember (create_cfg R) as ambig_CFG.
    remember (fresh (sym R)) as delimiter.
    split.
    - intros (P & Hi & He & H). unfold CFA.
    remember (sigma delimiter (gamma1 P R)) as x.
    exists x.
            * remember (CFPP_to_CFP.Post_CFG_1_left (gamma1 R R) delimiter (gamma1 R P) H1) as H2.
            destruct H2 as [| H4].
             --  exfalso. remember (map_eq_nil (fun '(x, y) => (x, [fresh (Sigma R)] ++ x ++ [fresh (Sigma R)] ++ y)) P e) as H3. firstorder.
             -- 
             assert ((forall s : sig, s el map fst (rules (startsym ambig_CFG, [(startsym ambig_CFG, [CFPP_to_CFP.S (gamma1 R R) delimiter]); (startsym ambig_CFG, [CFPP_to_CFP.S (gamma2 R R) delimiter])])) -> ~
             s el flat_map snd (rules (CFPP_to_CFP.G (gamma1 R R) delimiter)) ++ [CFPP_to_CFP.S (gamma1 R R) delimiter])).
                ++ admit.
    

Admitted.
