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
        let Post_CFG1 := CFPP_to_CFP.G (gamma1 P) # in
        let delim2 := fresh (sym P ++ [#] ++ [startsym Post_CFG1]) in
        let Post_CFG2 := CFPP_to_CFP.G (gamma2 P) delim2 in
        let new_start_sym := fresh (sym P ++ [#] ++ [delim2] ++ [startsym Post_CFG1] ++ [startsym Post_CFG2]) in
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

    Lemma sigma_gamma2 A delim:
        sigma delim (gamma2 A) = tau2 A ++ [delim] ++ gamma A.
        Proof.
            induction A as [ | (x, y)]; cbn.
            - reflexivity.
            - unfold gamma2 in IHA. cbn in *.
              rewrite IHA. now simpl_list.
        Qed.

End PCP_CFA.

(* Definition R : stack nat := [([1],[2]);  ([3], [4]); ([5], [6])].

Notation "#" := (fresh (sym R)).

Definition PostG1 := CFPP_to_CFP.G (gamma1 R R) #.
Definition PostG2 := CFPP_to_CFP.G (gamma2 R R) #.

Compute PostG1.
Compute PostG2.

Compute (create_cfg R). *)

Lemma boo: forall a b c, (not b) -> (a -> (b \/ c)) -> a -> c.
Proof. intros. apply H0 in X. case X.
- intros. exfalso. apply H. trivial.
- trivial.
Qed.

(* PostG1 and PostG2 have different start symbols. So just create a new CFG with a new start symbol and rules (new, startsym PostG1) and (new, startsym PostG2) alongwith all the existing rules.s *)

Lemma or_neg : forall P Q, (P \/ Q) -> (~P) -> Q.
Proof.
    intros. firstorder.  
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
    remember (sigma delimiter P) as x.
    exists x.
    Check CFPP_to_CFP.reduction_full R delimiter x.
    assert (exists P0 : list (card sig),
    P0 <<= R /\ P0 <> [] /\ sigma delimiter P = x).
        + exists P; firstorder.
        + assert (gamma1 R P <<= gamma1 R R) as H1.
            * unfold gamma1. apply (incl_map (fun '(x0, y) => (x0, [fresh (Sigma R)] ++ x0 ++ [fresh (Sigma R)] ++ y)) Hi).
            * remember (CFPP_to_CFP.Post_CFG_1_left (gamma1 R R) delimiter (gamma1 R P) H1) as H2.
            destruct H2 as [| H4].
             --  exfalso. remember (map_eq_nil (fun '(x, y) => (x, [fresh (Sigma R)] ++ x ++ [fresh (Sigma R)] ++ y)) P e) as H3. firstorder.
             -- 
             assert ((forall s : sig, s el map fst (rules (startsym ambig_CFG, [(startsym ambig_CFG, [CFPP_to_CFP.S (gamma1 R R) delimiter]); (startsym ambig_CFG, [CFPP_to_CFP.S (gamma2 R R) delimiter])])) -> ~
             s el flat_map snd (rules (CFPP_to_CFP.G (gamma1 R R) delimiter)) ++ [CFPP_to_CFP.S (gamma1 R R) delimiter])).
                ++ admit.
                ++ remember (CFPP_to_CFP.cfg_subset (CFPP_to_CFP.G (gamma1 R R) delimiter) (startsym ambig_CFG, [(startsym ambig_CFG, [CFPP_to_CFP.S (gamma1 R R) delimiter]); (startsym ambig_CFG, [CFPP_to_CFP.S (gamma2 R R) delimiter])]) [CFPP_to_CFP.S (gamma1 R R) delimiter] (sigma delimiter (gamma1 R P)) H4 H2) as Ho.
                rewrite  
    - unfold CFA. intros. destruct H. destruct H.
    destruct H. destruct H.
    unfold PCP. unfold PCPX.

Admitted.

rewt_left (startsym (CFPP_to_CFP.G (gamma1 R R) delimiter,     rules
      (startsym ambig_CFG,
      [(startsym ambig_CFG, [CFPP_to_CFP.S (gamma1 R R) delimiter]);
      (startsym ambig_CFG, [CFPP_to_CFP.S (gamma2 R R) delimiter])]) ++
    rules (CFPP_to_CFP.G (gamma1 R R) delimiter))
    [CFPP_to_CFP.S (gamma1 R R) delimiter] (sigma delimiter (gamma1 R P))

rewt_left ambig_CFG [startsym ambig_CFG] x


(* - intros (A & Hi & He & H). unfold CFA.
exists (sigma # A).
remember (CFPP_to_CFP.G (gamma1 A A) (fresh (sym A))) as PostG1.
remember (CFPP_to_CFP.G (gamma2 A A) (fresh (sym A))) as
PostG2.
remember (CFPP_to_CFP.G P #) as finalPostG.
exists ([(startsym finalPostG, [startsym PostG1])] ++ rules_to_derivation (gamma1 A A)).
exists ([(startsym finalPostG, [startsym PostG2])] ++ rules_to_derivation (gamma2 A A)).
repeat split.
    + apply (boo (A <<= P) (A = []) (rewt (CFPP_to_CFP.G P #) [CFPP_to_CFP.S P #] (sigma # A)) (He) (CFPP_to_CFP.Post_CFG_1' P # A)).
 *)
