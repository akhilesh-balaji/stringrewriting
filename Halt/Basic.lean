import Cslib.Computability.Machines.SingleTapeTuring.Basic

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM

namespace Halt

/-- Halts at `state=none`. -/
def Halts (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩

/-- Halts within `n` steps. -/
def HaltsWithinTime (tm : SingleTapeTM Symbol) (w : List Symbol) (n : ℕ) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.RelatesWithinSteps tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩ n

/-- Halts within `n` steps iff halts. -/
theorem halts_iff_exists_n_haltsWithinTime (tm : SingleTapeTM Symbol)
    (w : List Symbol) :
    Halts tm w ↔ ∃ n, HaltsWithinTime tm w n := by
  constructor
  · rintro ⟨tape, h⟩
    obtain ⟨n, hn⟩ := h.relatesInSteps
    exact ⟨n, tape, .of_relatesInSteps hn⟩
  · rintro ⟨n, tape, m, _, hm⟩
    exact ⟨tape, hm.reflTransGen⟩

/- Define encodings first -/

/-- **`IsHaltDecider D`** (pair form, "HALT_TM"): the single-tape TM
`D` over `Bool`, when run on the encoded pair `(c, w)`, halts with
output `[true]` if `c.toTM` halts on `w`, and `[false]` otherwise. -/
def IsHaltDecider (D : SingleTapeTM Bool) : Prop := sorry

end Halt

