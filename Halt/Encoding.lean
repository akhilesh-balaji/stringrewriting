import Cslib.Computability.Machines.SingleTapeTuring.Basic

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM

namespace Halt.Encoding

/- encodeTr transitions is of the form δ(qi, Xj ) = (qk, Xl, Dm), for some integers i, j , k, l, and
m. We shall code this rule by the string 0i 10j 10k 10l 10m. Notice that, since all of i, j , k, l,
and m are at least one, there are no occurrences of two or more consecutive 1's within the code for
a single transition. A code for the entire TM M consists of all the codes for the transitions, in
some order, separated by pairs of 1's: C1 11 C2 11 ... 11 Cn-1 11Cn. We shall assume the states are
q1,...,  qr for some r. The start state will always be q1, and q2 will be the only accepting state.
Note that, since we may assume the TM halts whenever it enters an accepting state, there is never
any need for more than one accepting state. We shall assume the tape symbols are X1,... , Xs for
some s. X1 always will be the symbol 0, X2 will be 1, and X3 will be ⊔, the blank. However, other
tape symbols can be assigned to the remaining integers arbitrarily. We shall refer to direction L as
D1 and direction R as D2. -/

structure ConventionalTM (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] 
    [DecidableEq Symbol] extends SingleTapeTM Symbol where
  /-- The accepting state -/
  qAccept : State
  /-- X1: the '0' symbol -/
  sym0 : Symbol
  /-- X2: the '1' symbol -/
  sym1 : Symbol

def encodeNat (n : ℕ) : List Bool := List.replicate n false
#eval encodeNat 3

@[simp]
lemma encodeNat_zero : encodeNat 0 = [] := rfl

@[simp]
lemma encodeNat_succ (n : ℕ) :
    encodeNat (n + 1) = false :: encodeNat n := by
  simp [encodeNat, List.replicate_succ]

/-- The binary string `w` is the binary number `[1w]_2 ∈ ℕ`. -/
def enumeratedBinaryString (w : List Bool) : ℕ :=
  w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 1
#eval enumeratedBinaryString []

noncomputable def symbolIdx [DecidableEq Symbol] (s : Option Symbol) : ℕ :=
  match s with
  | none   => 1
  | some s => (Fintype.equivFin Symbol s).val + 2

def dirIdx (d : Option Dir) : ℕ :=
  match d with
  | some Dir.left => 1
  | some Dir.right => 2
  | none       => 3

def boolSymbolIdx (s : Option Bool) : ℕ :=
  match s with
  | some false => 1  -- X1 = 0
  | some true  => 2  -- X2 = 1
  | none       => 3  -- X3 = blank

noncomputable def boolStateIdx (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) : ℕ :=
  if q == tm.q₀ then 1
  else Finset.univ.toList.findIdx (· == q) + 2

noncomputable def encodeBoolTransition (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool)
    (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) : List Bool :=
  let i := boolStateIdx tm q
  let j := boolSymbolIdx x
  let k := boolStateIdx tm q'
  let l := boolSymbolIdx stmt.symbol
  let m := dirIdx stmt.movement
  encodeNat i ++ [true] ++
  encodeNat j ++ [true] ++
  encodeNat k ++ [true] ++
  encodeNat l ++ [true] ++
  encodeNat m

noncomputable def encodeBoolTr (tm : SingleTapeTM Bool) [DecidableEq tm.State] : List Bool :=
  let states := (@Finset.univ tm.State tm.stateFintype).toList
  let pairs := states ×ˢ [none, some false, some true]
  let encoded := pairs.filterMap (fun ⟨q, x⟩ =>
    match tm.tr q x with
    | (stmt, some q') => some (encodeBoolTransition tm q x stmt q')
    | (_, none)       => none
  )
  List.intercalate [true, true] encoded

noncomputable def encodeTM (tm : SingleTapeTM Bool) [DecidableEq tm.State] : List Bool :=
  encodeNat (Fintype.card tm.State) ++ List.replicate 3 true ++ encodeBoolTr tm

end Halt.Encoding
