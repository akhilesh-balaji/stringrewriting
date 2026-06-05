import Mathlib.Logic.Relation

structure SRS where
  alphabet : Type
  productions : List (List alphabet × List alphabet)

namespace SRS

def step (s : SRS) (u v : List s.alphabet) : Prop :=
  ∃ (l r lhs rhs : List s.alphabet),
    (lhs, rhs) ∈ s.productions ∧
    u = l ++ lhs ++ r ∧
    v = l ++ rhs ++ r

def reduces (s : SRS) : List s.alphabet → List s.alphabet → Prop :=
  Relation.ReflTransGen s.step

syntax "⟪" str "⟫" : term
macro_rules
  | `(⟪$s⟫) => `(String.toList $s)

syntax term " ↦ " term : term
macro_rules
  | `($lhs ↦ $rhs) => `(($lhs, $rhs))

syntax term " ↦{" term "}" term : term
macro_rules
  | `($u {$s}↦ $v) => `(SRS.reduces $s $u $v)

def catToDog : SRS where
  alphabet := Char
  productions := [
    ⟪"c"⟫ ↦ ⟪"d"⟫,
    ⟪"a"⟫ ↦ ⟪"o"⟫,
    ⟪"t"⟫ ↦ ⟪"g"⟫,
  ]

example : ⟪"cat"⟫ {catToDog}↦ ⟪"dog"⟫ := by
  -- cat → dat → dot → dog
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    exact ⟨[], ⟪"at"⟫, ⟪"c"⟫, ⟪"d"⟫, List.mem_of_mem_head? rfl, rfl, rfl⟩
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    exact ⟨⟪"d"⟫, ⟪"t"⟫, ⟪"a"⟫, ⟪"o"⟫, List.mem_cons.mpr (Or.inr List.mem_cons_self), rfl, rfl⟩
  apply Relation.ReflTransGen.single
  exact ⟨⟪"do"⟫, [], ⟪"t"⟫, ⟪"g"⟫, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))), rfl, rfl⟩

end SRS

