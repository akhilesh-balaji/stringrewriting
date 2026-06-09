import Halt
import SRS

import Cslib.Computability.Machines.SingleTapeTuring.Basic

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM
open Halt

/-
Proof Sketch (Akhilesh Balaji).

HALT_TM ≤_M SR. Let M := (Q, Γ, ⊔, Σ, δ, q_0, F) be a Turing machine with input W = w_1 ··· w_k ∈ Σ*.

We construct an instance of String Rewriting from M. Recall that the initial
instantaneous description (ID) of M is q_0 w_1 ··· w_k.

A general ID has the form w_1 ··· w_{i-1} q w_i w_{i+1} ··· w_k, where the state symbol q marks the position of the head.

We establish a correspondence between transitions of M and derivations in the string-rewriting system. Suppose
    w_1 ··· w_{i-1} q w_i ··· w_{i+ℓ} ··· w_k ⊢ w_1 ··· w_{i-1} w̃'_i ··· w̃'_{i+ℓ'} p ··· w_k.

If ℓ' < ℓ, we erase the excess symbols and rewrite the remainder, padding with blank symbols ⊔ as necessary. If ℓ < ℓ', we first erase the subsequent portion of the tape and then rewrite it farther to the right, inserting the required number of blanks.

This transition is represented by the production
    w_i ··· w_{i+ℓ} → w̃'_i ··· w̃'_{i+ℓ'}.

Applying this construction to every transition of M yields a set of productions P.

The goal is for the rewriting system to transform W into W'. Equivalently,
there should be a derivation W = w_1 ··· w_k ⇒* w̃'_1 ··· w̃'_m q_h, where q_h ∈ F is a halting state. Thus, W ⇒* W̃' corresponds exactly to a halting computation of M.

Therefore, if the string-rewriting instance has a solution, then M halts.
Conversely, a halting computation of M yields a solution to the string-rewriting instance.

Since the Halting Problem is undecidable, and we have constructed a many-one
reduction HALT_TM ≤_M SR, it follows that String Rewriting is also undecidable.
-/

theorem sr_if_halt (s : SRS) (u v : List s.alphabet)
    [Inhabited s.alphabet] [Fintype s.alphabet]
    (tm : SingleTapeTM s.alphabet) :
    Halts tm u → s.HasSolution u v := by
  sorry

