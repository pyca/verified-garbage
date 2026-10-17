module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs

/-! # Products modulo a number, on ARMv7

On the arrays of the key working space (`Impl/Rsa/Arm/KeyWs.lean`):

* `addMod o a b m z t`: `[o] := ([a] + [b]) mod [m]` for `[a], [b] < [m]`
  and `2 [m] ≤ 2^(32 w)`, through the temporaries `t`, `t + 1` and `t + 2`
  (`[z]` is zero): `[b]` negated, `[a] - (-[b])`, and its difference with
  `[m]`, of which the borrow selects one.
* `mulMod z y x a m t`: `r6` steps of binary multiplication from the least
  significant bit of `[y]`, which each step shifts out: the bit selects `[x]`
  or zero (into `[t]`), which is added to `[a]` modulo `[m]`, and `[x]` is
  doubled modulo `[m]`. From `[a] = 0` and `[x] < [m]`, `[a]` ends as
  `([y] mod 2^r6) [x] mod [m]`.

The bits only select (`sel`): the addresses and branches depend only on `w`
and the count.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Keys
open VG VG.Arm

/-- `[o] := ([a] + [b]) mod [m]`, through `t`–`t + 2`. -/
def addMod (o a b m z t : Nat) : List (Prog isa) :=
  [sub3 t z b, sub3 (t + 1) a t, sub3 (t + 2) (t + 1) m, .block [.str .r11 .r8 sC],
   sel o (t + 2) (t + 1) sC]

/-- The low bit of `[y]` selects `[x]` into `[t]`. -/
def mulHead (z y x t : Nat) : Prog isa := .seq (.block (bitOf sB y)) (sel t z x sB)

/-- `[y]` halved, and the count decremented. -/
def mulTail (y : Nat) : Prog isa := seqs [.block [.mov .r11 (.imm 0)], half y, .block [.subs .r6 .r6 (.imm 1)]]

/-- One step: the low bit of `[y]` selects `[x]` into `[t]`, which is added
to `[a]`; `[x]` is doubled, and `[y]` halved. -/
def mulModStep (z y x a m t : Nat) : Prog isa :=
  seqs [mulHead z y x t, seqs (addMod a a t m z (t + 1)), seqs (addMod x x x m z (t + 1)), mulTail y]

/-- `r6` steps (at least one). -/
def mulMod (z y x a m t : Nat) : Prog isa := .loop (mulModStep z y x a m t) .ne

end VG.Impl.Rsa.Arm.Keys
