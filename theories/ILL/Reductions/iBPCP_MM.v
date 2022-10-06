(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Import ListNotations.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.Shared.Libs.DLW
  Require Import utils.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.StackMachines
  Require Import BSM iPCPb_to_BSM_HALTING.

From Undecidability.MinskyMachines
  Require Import MM BSM_MM MM_sss.

Import ReductionChainNotations UndecidabilityNotations.

Lemma iBPCP_chain_MM : 
  iPCPb ⪯ Halt_BSM /\
  Halt_BSM ⪯ MM_HALTS_ON_ZERO.
Proof.
  msplit 1.
  + apply iPCPb_to_BSM_HALTING.
  + apply BSM_MM_HALTS_ON_ZERO.
Qed.

Lemma iBPCP_to_MM : iPCPb ⪯ MM_HALTS_ON_ZERO.
Proof.
  reduce with chain iBPCP_chain_MM.
Qed.
