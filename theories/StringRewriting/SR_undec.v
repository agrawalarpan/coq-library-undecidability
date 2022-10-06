
Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.TM.SBTM_undec.

Require Undecidability.StringRewriting.Reductions.SBTM_HALT_to_SR.
Require Undecidability.StringRewriting.Reductions.SBTM_HALT_to_TSR.

(* String rewriting is undecidable. *)
Lemma SR_undec : undecidable SR.
Proof.
  apply (undecidability_from_reducibility SBTM_HALT_undec).
  exact SBTM_HALT_to_SR.reduction.
Qed.

Check SR_undec.

(* Thue system reachability is undecidable. *)
Lemma TSR_undec : undecidable TSR.
Proof.
  apply (undecidability_from_reducibility SBTM_HALT_undec).
  exact SBTM_HALT_to_TSR.reduction.
Qed.

Check TSR_undec.
