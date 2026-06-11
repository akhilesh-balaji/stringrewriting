import Mathlib.Logic.Relation

import Cslib.Computability.Machines.SingleTapeTuring.Basic

open Turing SingleTapeTM

structure SRS where
  alphabet : Type
  productions : List (List alphabet × List alphabet)

namespace SRS

/-- Stepping `u=l++lhs++r` to `v=l++rhs++r` using the rule `lhs ↦ rhs`. -/
def step (s : SRS) (u v : List s.alphabet) : Prop :=
  ∃ (l r lhs rhs : List s.alphabet),
    (lhs, rhs) ∈ s.productions ∧
    u = l ++ lhs ++ r ∧
    v = l ++ rhs ++ r

def reduces (s : SRS) : List s.alphabet → List s.alphabet → Prop :=
  Relation.ReflTransGen s.step

syntax "⸨" str "⸩" : term
macro_rules
  | `(⸨$s⸩) => `(String.toList $s)

syntax term " ↦ " term : term
macro_rules
  | `($lhs ↦ $rhs) => `(($lhs, $rhs))

/- syntax term " ↦{" term "}" term : term -/
syntax term  "{" term "}↦ " term : term
macro_rules
  | `($u {$s}↦ $v) => `(SRS.reduces $s $u $v)

private def catToDog : SRS where
  alphabet := Char
  productions := [
    ⸨"c"⸩ ↦ ⸨"d"⸩,
    ⸨"a"⸩ ↦ ⸨"o"⸩,
    ⸨"t"⸩ ↦ ⸨"g"⸩,
  ]
private example : ⸨"cat"⸩ {catToDog}↦ ⸨"dog"⸩ := by
  -- cat ↦ dat ↦ dot ↦ dog
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    exact ⟨⸨""⸩, ⸨"at"⸩, ⸨"c"⸩, ⸨"d"⸩, List.mem_of_mem_head? rfl, rfl, rfl⟩
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    exact ⟨⸨"d"⸩, ⸨"t"⸩, ⸨"a"⸩, ⸨"o"⸩, List.mem_cons.mpr (Or.inr List.mem_cons_self), rfl, rfl⟩
  apply Relation.ReflTransGen.single
  exact ⟨⸨"do"⸩, ⸨""⸩, ⸨"t"⸩, ⸨"g"⸩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))), rfl, rfl⟩

def HasSolution (s : SRS) (u v : List s.alphabet) : Prop := u {s}↦ v

private inductive SRSTMState (n : ℕ) (m : ℕ) : Type
  | scan  : SRSTMState n m
  | write : Fin n → Fin m → SRSTMState n m
  | check : SRSTMState n m

/-- Claude-generated. I have replaced most proofs it generated with `grind`. -/
instance : Inhabited (SRSTMState n m) := ⟨.scan⟩

instance : DecidableEq (SRSTMState n m)
  | .scan,      .scan       => isTrue rfl
  | .scan,      .check      => isFalse (by grind)
  | .scan,      .write _ _  => isFalse (by grind)
  | .check,     .scan       => isFalse (by grind)
  | .check,     .check      => isTrue rfl
  | .check,     .write _ _  => isFalse (by grind)
  | .write _ _, .scan       => isFalse (by grind)
  | .write _ _, .check      => isFalse (by grind)
  | .write i j, .write i' j' =>
      if hi : i = i' then (if hj : j = j' then isTrue (by grind) else isFalse (by grind))
      else isFalse (by grind)

instance : Fintype (SRSTMState n m) where
  elems := insert .scan (insert .check
    ((Finset.univ : Finset (Fin n × Fin m)).image (fun p => .write p.1 p.2)))
  complete := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    cases x with
    | scan      => grind
    | check     => grind
    | write i j => exact Or.inr (Or.inr ⟨⟨i, j⟩, rfl⟩)
/- end of Claude generated -/

def toTM (s : SRS) (u v : List s.alphabet)
    [Inhabited s.alphabet] [Fintype s.alphabet] : SingleTapeTM s.alphabet where
  State        := SRSTMState s.productions.length (v.length + 1)
  stateFintype := inferInstance 
  q₀           := .scan
  tr           := sorry

end SRS

