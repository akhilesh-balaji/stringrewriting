import Cslib.Computability.Machines.SingleTapeTuring.Basic
import Halt
import SRS

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM
open Halt

theorem srs_if_halt (s : SRS) (u v : List s.alphabet) [Inhabited s.alphabet] [Fintype s.alphabet] (tm : SingleTapeTM s.alphabet) :
    Halts tm u → s.HasSolution u v := by sorry

