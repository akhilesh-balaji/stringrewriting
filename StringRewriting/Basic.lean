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

/-- The type of the TM's instantaneous description -/
def TMID (tm : SingleTapeTM Bool) : Type := Sum (Option tm.State) Bool

/-- The TM's instanteneous description -/
def TMCfgID (tm : SingleTapeTM Bool) (c : tm.Cfg) : List (TMID tm) :=
  c.BiTape.left.toList.filterMap  (·.map Sum.inr) ++
  [Sum.inl c.state] ++
  c.BiTape.head.toList.map Sum.inr ++
  c.BiTape.right.toList.filterMap (·.map Sum.inr)

def isHaltID (tm : SingleTapeTM Bool) (v : List (TMID tm)) : Prop :=
  Sum.inl none ∈ v

def encodeInitID (tm : SingleTapeTM Bool) (w : List Bool) : List (TMID tm) :=
  Sum.inl (some tm.q₀) :: w.map Sum.inr

-- each δ(q, a) = (b, d, q') becomes one or more productions over State ⊕ Bool
inductive TMProductions (tm : SingleTapeTM Bool) :
    List (TMID tm) → List (TMID tm) → Prop where
  | right (q : tm.State) (a : Bool) (b : Bool) (q' : tm.State)
      (h : tm.tr q (some a) = (⟨some b, some Dir.right⟩, some q'))
      : TMProductions tm
          [Sum.inl (some q), Sum.inr a]
          [Sum.inr b, Sum.inl (some q')]
  | left (q : tm.State) (a : Bool) (b : Bool) (q' : tm.State) (c : Bool)
      (h : tm.tr q (some a) = (⟨some b, some Dir.left⟩, some q'))
      : TMProductions tm
          [Sum.inr c, Sum.inl (some q), Sum.inr a]
          [Sum.inl (some q'), Sum.inr c, Sum.inr b]

noncomputable def Turing.SingleTapeTM.toSRS (tm : SingleTapeTM Bool) : SRS where
  alphabet := TMID tm
  productions :=
    do
      let q ← (Finset.univ.toList : List tm.State)
      let a ← (Finset.univ.toList : List Bool)
      let (stmt, q'opt) := tm.tr q (some a)
      match stmt.movement, q'opt with
      | some Dir.right, some q' =>
          [ ( [Sum.inl (some q), Sum.inr a],
              [Sum.inr (stmt.symbol.getD default), Sum.inl (some q')] ) ]
      | some Dir.right, none =>                                          -- halt, moving right
          [ ( [Sum.inl (some q), Sum.inr a],
              [Sum.inr (stmt.symbol.getD default), Sum.inl none] ) ]
      | some Dir.left, some q' =>
          do
            let c ← (Finset.univ.toList : List Bool)
            [ ( [Sum.inr c, Sum.inl (some q), Sum.inr a],
                [Sum.inl (some q'), Sum.inr c, Sum.inr (stmt.symbol.getD default)] ) ]
      | some Dir.left, none =>                                           -- halt, moving left
          do
            let c ← (Finset.univ.toList : List Bool)
            [ ( [Sum.inr c, Sum.inl (some q), Sum.inr a],
                [Sum.inl none, Sum.inr c, Sum.inr (stmt.symbol.getD default)] ) ]
      | _, _ => []

lemma encodeInitID_eq_TMCfgID (tm : SingleTapeTM Bool) (u : List Bool) :
    encodeInitID tm u = TMCfgID tm (tm.initCfg u) := by
  simp only [initCfg]
  simp [encodeInitID, TMCfgID, Option.toList, BiTape.mk₁]
  cases u with
  | nil =>
      simp [BiTape.nil]
      exact Eq.symm List.singleton_append
  | cons b rest =>
      simp [StackTape.mapSome]
      exact List.toList_toArray

lemma srs_simulates_step (tm : SingleTapeTM Bool) (c c' : tm.Cfg) :
    tm.TransitionRelation c c' →
    (tm.toSRS).step (TMCfgID tm c) (TMCfgID tm c') := by
  /- simp [ TransitionRelation] -/
  intro h
  simp [SRS.step]
  rw [SingleTapeTM.TransitionRelation] at h
  cases hc : c with
  | mk q tape =>
    simp [SingleTapeTM.step] at h
    subst hc
    cases q with
    | none =>
      simp at h
    | some q =>
      injection h with hcfg
      subst hcfg
      set tr := tm.tr q tape.head
      sorry
        


  /- sorry -- case analysis on direction and q'opt, matches toSRS productions -/

lemma srs_simulates (tm : SingleTapeTM Bool) (c c' : tm.Cfg) :
    Relation.ReflTransGen tm.TransitionRelation c c' →
    (tm.toSRS).HasSolution (TMCfgID tm c) (TMCfgID tm c') := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (srs_simulates_step tm _ _ h_step)

lemma isHaltID_haltCfg (tm : SingleTapeTM Bool) (v : List Bool) :
    isHaltID tm (TMCfgID tm (tm.haltCfg v)) := by
  simp [isHaltID, TMCfgID, haltCfg]
  sorry
  
lemma haltid_if_halts (tm : SingleTapeTM Bool) (u : List Bool) :
    Halts tm u → ∃ tape, isHaltID tm (TMCfgID tm ⟨none, tape⟩) := by
  intro ⟨tape, _⟩
  /- exact ⟨tape, by simp [isHaltID, TMCfgID, List.mem_append, List.mem_cons]⟩ -/
  simp [isHaltID, TMCfgID]
  sorry

lemma isHaltID_none (tm : SingleTapeTM Bool) (tape : BiTape Bool) :
    isHaltID tm (TMCfgID tm ⟨none, tape⟩) := by sorry
  /- List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self) -/

theorem sr_if_halt (tm : SingleTapeTM Bool) (u : List Bool) :
    Halts tm u →
    ∃ v, (tm.toSRS).HasSolution (encodeInitID tm u) v ∧ isHaltID tm v := by
  intro ⟨tape, h_halts⟩
  exact ⟨TMCfgID tm ⟨none, tape⟩,
    encodeInitID_eq_TMCfgID tm u ▸ srs_simulates tm _ _ h_halts,
    isHaltID_none tm tape⟩

/- optional -/
theorem halts_if_sr (s : SRS) (u v : List s.alphabet)
    [Inhabited s.alphabet] [Fintype s.alphabet]
    [DecidableEq s.alphabet] :
  s.HasSolution u v → Halts (s.toTM u v) u := by sorry

theorem halts_iff_sr (tm : SingleTapeTM Bool) (u : List Bool) :
    Halts tm u ↔
    ∃ v, (tm.toSRS).HasSolution (encodeInitID tm u) v ∧ isHaltID tm v := by
  constructor
  · exact sr_if_halt tm u
  · intro ⟨v, h_sol, h_halt⟩
    -- unfold along encodeInitID = CfgID of initCfg, then
    -- lift tm_simulates_step through ReflTransGen to get a halting run
    rw [encodeInitID_eq_TMCfgID] at h_sol
    sorry

