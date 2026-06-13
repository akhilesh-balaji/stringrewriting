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

def optEnc (tm : SingleTapeTM Bool) (o : Option Bool) : List (TMID tm) := o.toList.map Sum.inr

def srMap (tm : SingleTapeTM Bool) (s : StackTape Bool) : List (TMID tm) :=
  s.toList.filterMap (fun x => x.map Sum.inr)

/-- The TM's instanteneous description -/
def TMCfgID (tm : SingleTapeTM Bool) (c : tm.Cfg) : List (TMID tm) :=
  (srMap tm c.BiTape.left).reverse ++
  ([Sum.inl c.state] : List (TMID tm)) ++
  optEnc tm c.BiTape.head ++
  srMap tm c.BiTape.right

def isHaltID (tm : SingleTapeTM Bool) (v : List (TMID tm)) : Prop :=
  Sum.inl none ∈ v

def encodeInitID (tm : SingleTapeTM Bool) (w : List Bool) : List (TMID tm) :=
  Sum.inl (some tm.q₀) :: w.map Sum.inr

noncomputable def Turing.SingleTapeTM.toSRS (tm : SingleTapeTM Bool) : SRS where
  alphabet := TMID tm
  productions :=
   (Finset.univ.toList : List tm.State).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun r =>
        match (tm.tr q r).1.movement with
        | none =>
            [ (Sum.inl (some q) :: optEnc tm r,
               Sum.inl (tm.tr q r).2 :: optEnc tm (tm.tr q r).1.symbol) ]
        | some Dir.right =>
            [ (Sum.inl (some q) :: optEnc tm r,
               optEnc tm (tm.tr q r).1.symbol ++ ([Sum.inl (tm.tr q r).2] : List (TMID tm))) ]
        | some Dir.left =>
            (Sum.inl (some q) :: optEnc tm r,
             Sum.inl (tm.tr q r).2 :: optEnc tm (tm.tr q r).1.symbol) ::
            ([false, true] : List Bool).flatMap fun c =>
              [ (Sum.inr c :: Sum.inl (some q) :: optEnc tm r,
                 Sum.inl (tm.tr q r).2 :: Sum.inr c :: optEnc tm (tm.tr q r).1.symbol) ]

lemma optEnc_append_srMap_tail (tm : SingleTapeTM Bool) (s : StackTape Bool) :
    optEnc tm s.head ++ srMap tm s.tail = srMap tm s := by
  unfold optEnc srMap StackTape.head StackTape.tail
  rcases s with ⟨l, hl⟩
  cases l with
  | nil => simp
  | cons hd tl => cases hd <;> simp

lemma srMap_cons (tm : SingleTapeTM Bool) (o : Option Bool) (s : StackTape Bool) :
    srMap tm (StackTape.cons o s) = optEnc tm o ++ srMap tm s := by
  unfold optEnc srMap
  cases o with
  | none =>
    rcases s with ⟨l, hl⟩
    cases l <;> simp [StackTape.cons]
  | some b => simp [StackTape.cons]

/-- All toSRS_mem_... lemmas proved by Aristotle -/
lemma toSRS_mem_none (tm : SingleTapeTM Bool) (q : tm.State) (r : Option Bool)
    (h : (tm.tr q r).1.movement = none) :
    (Sum.inl (some q) :: optEnc tm r,
     Sum.inl (tm.tr q r).2 :: optEnc tm (tm.tr q r).1.symbol) ∈ (tm.toSRS).productions := by
  simp only [SingleTapeTM.toSRS]
  apply List.mem_flatMap.mpr
  refine ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, ?_⟩
  · cases r with
    | none => simp
    | some b => cases b <;> simp
  · simp [h]
    exact List.mem_singleton.mpr rfl

lemma toSRS_mem_right (tm : SingleTapeTM Bool) (q : tm.State) (r : Option Bool)
    (h : (tm.tr q r).1.movement = some Dir.right) :
    (Sum.inl (some q) :: optEnc tm r,
     optEnc tm (tm.tr q r).1.symbol ++ ([Sum.inl (tm.tr q r).2] : List (TMID tm)))
      ∈ (tm.toSRS).productions := by
  simp only [SingleTapeTM.toSRS]
  apply List.mem_flatMap.mpr
  refine ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, ?_⟩
  · cases r with
    | none => simp
    | some b => cases b <;> simp
  · simp [h]; exact List.mem_singleton.mpr rfl

lemma toSRS_mem_left_edge (tm : SingleTapeTM Bool) (q : tm.State) (r : Option Bool)
    (h : (tm.tr q r).1.movement = some Dir.left) :
    (Sum.inl (some q) :: optEnc tm r,
     Sum.inl (tm.tr q r).2 :: optEnc tm (tm.tr q r).1.symbol) ∈ (tm.toSRS).productions := by
  simp only [SingleTapeTM.toSRS]
  apply List.mem_flatMap.mpr
  refine ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, ?_⟩
  · cases r with
    | none => simp
    | some b => cases b <;> simp
  · simp [h]; exact List.mem_cons_self

lemma toSRS_mem_left (tm : SingleTapeTM Bool) (q : tm.State) (r : Option Bool) (c : Bool)
    (h : (tm.tr q r).1.movement = some Dir.left) :
    (Sum.inr c :: Sum.inl (some q) :: optEnc tm r,
     Sum.inl (tm.tr q r).2 :: Sum.inr c :: optEnc tm (tm.tr q r).1.symbol)
      ∈ (tm.toSRS).productions := by
  simp only [SingleTapeTM.toSRS]
  apply List.mem_flatMap.mpr
  refine ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r, ?_, ?_⟩
  · cases r with
    | none => simp
    | some b => cases b <;> simp
  · rw [h]
    apply List.mem_cons.mpr
    right
    apply List.mem_flatMap.mpr
    exact ⟨c, by cases c <;> simp, List.mem_singleton.mpr rfl⟩

lemma encodeInitID_eq_TMCfgID (tm : SingleTapeTM Bool) (u : List Bool) :
    encodeInitID tm u = TMCfgID tm (tm.initCfg u) := by
  simp only [encodeInitID, TMCfgID, initCfg, BiTape.mk₁, srMap, optEnc]
  cases u with
  | nil =>
      simp [BiTape.nil]
  | cons hd tl =>
      simp [StackTape.mapSome, List.filterMap_map]

theorem turing_tape_step
    (a b b' d e f : List α) (c : α)
    (h_sym : b = b') (h_right : d ++ e = f) 
    : a ++ (b ++ c :: (d ++ e)) = a ++ (b' ++ [c]) ++ f := by
  simp [h_sym, h_right, List.append_assoc]

theorem List.assoc_cons (a : List α) (b : α) (c d : List α) : 
    a ++ b :: (c ++ d) = a ++ b :: c ++ d := by simp

theorem List.assoc_match (A : List α) (c b : α) (C D : List α) :
  A ++ c :: b :: (C ++ D) = A ++ c :: b :: C ++ D := by
  simp [List.append_assoc]

/-- Proved by aristotle, corrected by me to work in 4.31 -/
lemma srs_simulates_step (tm : SingleTapeTM Bool) (c c' : tm.Cfg) :
    tm.TransitionRelation c c' →
    (tm.toSRS).step (TMCfgID tm c) (TMCfgID tm c') := by
  intro h
  rw [SingleTapeTM.TransitionRelation] at h
  obtain ⟨st, tape⟩ := c
  cases st with
  | none => simp [SingleTapeTM.step] at h
  | some q =>
    have hrev : ∀ o : Option Bool, (optEnc tm o).reverse = optEnc tm o := fun o => by
      cases o <;> simp [optEnc]
    have hstep : tm.step ⟨some q, tape⟩ = some ⟨(tm.tr q tape.head).2,
        (tape.write (tm.tr q tape.head).1.symbol).optionMove (tm.tr q tape.head).1.movement⟩ := by
      simp [SingleTapeTM.step]
    rw [hstep] at h
    obtain rfl := Option.some.inj h
    simp only [SRS.step, TMCfgID]
    cases hmov : (tm.tr q tape.head).1.movement with
    | none =>
      refine ⟨(srMap tm tape.left).reverse, srMap tm tape.right,
        Sum.inl (some q) :: optEnc tm tape.head,
        Sum.inl (tm.tr q tape.head).2 :: optEnc tm (tm.tr q tape.head).1.symbol, ?_, ?_, ?_⟩
      · exact toSRS_mem_none tm q tape.head hmov
      · simp [List.append_assoc, List.cons_append, List.nil_append]
        exact List.assoc_cons (srMap tm tape.left).reverse (Sum.inl (some q)) (optEnc tm tape.head) (srMap tm tape.right)
      · simp [BiTape.write, BiTape.optionMove, List.append_assoc]
        exact List.assoc_cons (srMap tm tape.left).reverse (Sum.inl (tm.tr q tape.head).2)
          (optEnc tm (tm.tr q tape.head).1.symbol) (srMap tm tape.right)
    | some dir =>
      cases dir with
      | right =>
            refine ⟨(srMap tm tape.left).reverse, srMap tm tape.right, Sum.inl (some q) :: optEnc tm tape.head, optEnc tm (tm.tr q tape.head).1.symbol ++ ([Sum.inl (tm.tr q tape.head).2] : List (TMID tm)), ?_, ?_, ?_⟩
            · exact toSRS_mem_right tm q tape.head hmov
            · simp [List.append_assoc]
              exact List.assoc_cons (srMap tm tape.left).reverse (Sum.inl (some q)) (optEnc tm tape.head) (srMap tm tape.right)
            · simp only [BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight]
              simp [srMap_cons, List.reverse_append, List.append_assoc, optEnc]
              refine turing_tape_step (srMap tm tape.left).reverse (List.map Sum.inr (tm.tr q tape.head).1.symbol.toList).reverse
                (List.map Sum.inr (tm.tr q tape.head).1.symbol.toList) (List.map Sum.inr tape.right.head.toList)
                (srMap tm tape.right.tail) (srMap tm tape.right) (Sum.inl (tm.tr q tape.head).2) (hrev (tm.tr q tape.head).1.symbol)
                ?_
              · have h := optEnc_append_srMap_tail tm tape.right
                rwa [show optEnc tm tape.right.head = List.map Sum.inr tape.right.head.toList from by cases tape.right.head <;> simp [optEnc]; exact Array.toList_empty; exact List.singleton_inj.mpr rfl] at h
      | left =>
        have hleft : (srMap tm tape.left).reverse
            = (srMap tm tape.left.tail).reverse ++ optEnc tm tape.left.head := by
          conv_lhs => rw [← optEnc_append_srMap_tail tm tape.left]
          rw [List.reverse_append, hrev]
        cases htl : tape.left.head with
        | some cc =>
          refine ⟨(srMap tm tape.left.tail).reverse, srMap tm tape.right,
            Sum.inr cc :: Sum.inl (some q) :: optEnc tm tape.head,
            Sum.inl (tm.tr q tape.head).2 :: Sum.inr cc :: optEnc tm (tm.tr q tape.head).1.symbol,
            ?_, ?_, ?_⟩
          · exact toSRS_mem_left tm q tape.head cc hmov
          · rw [hleft, htl]; simp [List.append_assoc, optEnc]
            exact List.assoc_match (srMap tm tape.left.tail).reverse (Sum.inr cc) (Sum.inl (some q)) (List.map Sum.inr tape.head.toList) (srMap tm tape.right)
          · simp only [BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft]
            rw [htl]; simp [optEnc, srMap_cons, List.append_assoc]
            exact List.assoc_match (srMap tm tape.left.tail).reverse (Sum.inl (tm.tr q tape.head).2) (Sum.inr cc) (List.map Sum.inr (tm.tr q tape.head).1.symbol.toList) (srMap tm tape.right)
        | none =>
          refine ⟨(srMap tm tape.left.tail).reverse, srMap tm tape.right,
            Sum.inl (some q) :: optEnc tm tape.head,
            Sum.inl (tm.tr q tape.head).2 :: optEnc tm (tm.tr q tape.head).1.symbol,
            ?_, ?_, ?_⟩
          · exact toSRS_mem_left_edge tm q tape.head hmov
          · rw [hleft, htl]; simp [optEnc, List.append_assoc]
            exact List.assoc_cons (srMap tm tape.left.tail).reverse (Sum.inl (some q)) (List.map Sum.inr tape.head.toList) (srMap tm tape.right)
          · simp only [BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft]
            rw [htl]; simp [optEnc, srMap_cons, List.append_assoc]
            exact List.assoc_cons (srMap tm tape.left.tail).reverse (Sum.inl (tm.tr q tape.head).2) (List.map Sum.inr (tm.tr q tape.head).1.symbol.toList) (srMap tm tape.right)

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
  exact List.mem_append_cons_self
  
lemma haltid_if_halts (tm : SingleTapeTM Bool) (u : List Bool) :
    Halts tm u → ∃ tape, isHaltID tm (TMCfgID tm ⟨none, tape⟩) := by
  intro ⟨tape, _⟩
  exact ⟨tape, by simp [isHaltID, TMCfgID]; exact List.mem_append_cons_self⟩

lemma isHaltID_none (tm : SingleTapeTM Bool) (tape : BiTape Bool) :
    isHaltID tm (TMCfgID tm ⟨none, tape⟩) := by
  simp [isHaltID, TMCfgID]
  exact List.mem_append_cons_self

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
    rw [encodeInitID_eq_TMCfgID] at h_sol
    sorry

