Require Import Undecidability.CFG.CFG.

From Undecidability.CFG.Reductions Require 
  CFPP_to_CFP CFPI_to_CFI PCP_to_CFA.

Require Import Undecidability.Synthetic.Undecidability.

Require Undecidability.CFG.CFP_undec.
Require Undecidability.PCP.PCP_undec.

(* The Context-free Palindrome Problem is undecidable. *)
Lemma CFP_undec : undecidable CFP.
Proof.
  eapply undecidability_from_reducibility.
  exact CFP_undec.CFPP_undec.
  exact CFPP_to_CFP.reduction.
Qed.

Check CFP_undec.

(* The Context-free Intersection Problem is undecidable. *)
Lemma CFI_undec : undecidable CFI.
Proof.
  eapply undecidability_from_reducibility.
  exact CFP_undec.CFPI_undec.
  exact CFPI_to_CFI.reduction.
Qed.

Check CFI_undec.

(* The Context-free Ambiguity Problem is undecidable. *)
Lemma CFA_undec: undecidable CFA.
Proof.
Admitted.