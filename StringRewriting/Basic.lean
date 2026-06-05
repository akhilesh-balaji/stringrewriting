import Cslib.Computability.Machines.SingleTapeTuring.Basic

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM

variable {M : SingleTapeTM Symbol}
variable {N : SingleTapeTM Symbol}

