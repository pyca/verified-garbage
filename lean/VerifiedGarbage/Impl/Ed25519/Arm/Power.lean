module

public import VerifiedGarbage.Impl.Ed25519.Arm.Point16

/-! A fixed addition chain shared by inversion and square-root recovery. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def mulP (umaal : Bool) (o a b : Slot) : Prog isa := mulIn umaal (offset o) (offset a) (offset b)

def sqn (umaal : Bool) (o a : Slot) (n : Nat) : Prog isa :=
  .seq (mulP umaal o a a) <|
  .seq (.block [.movw .r10 (BitVec.ofNat 16 (n - 1))]) <|
    .loop (.seq (mulP umaal o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne

/-- From z in slot 2, leave z^(2^250 - 1) in slot 15 and z^11 in slot 14,
using slots 16 and 17. -/
def chain250 (umaal : Bool) : Prog isa :=
  .seq (mulP umaal 14 2 2) <|
  .seq (mulP umaal 15 14 14) <| .seq (mulP umaal 15 15 15) <|
  .seq (mulP umaal 15 2 15) <| .seq (mulP umaal 14 14 15) <|
  .seq (mulP umaal 16 14 14) <| .seq (mulP umaal 15 15 16) <|
  .seq (sqn umaal 16 15 5) <| .seq (mulP umaal 15 16 15) <|
  .seq (sqn umaal 16 15 10) <| .seq (mulP umaal 16 16 15) <|
  .seq (sqn umaal 17 16 20) <| .seq (mulP umaal 16 17 16) <|
  .seq (sqn umaal 16 16 10) <| .seq (mulP umaal 15 16 15) <|
  .seq (sqn umaal 16 15 50) <| .seq (mulP umaal 16 16 15) <|
  .seq (sqn umaal 17 16 100) <| .seq (mulP umaal 16 17 16) <|
  .seq (sqn umaal 16 16 50) (mulP umaal 15 16 15)

/-- `vg_gf25519_r16_pow250` (`Proof/X25519/Field16Contract.lean`): the chain, saving
and restoring the registers it changes, `r10` (its squarings' counter)
among them. -/
def pow250Fn (umaal : Bool) : Prog isa := asFn true (chain250 umaal)

/-- A call of `vg_gf25519_r16_pow250`. -/
def power250 (umaal : Bool) : Prog isa := .call ("vg_gf25519_r16_pow250" ++ suffix umaal) (pow250Fn umaal)

/-- `[o] = [a] · [b]`, by a call of `vg_gf25519_r16_mul`. -/
def mulPc (umaal : Bool) (o a b : Slot) : Prog isa := mulCall umaal (offset o) (offset a) (offset b)

/-- Slot `o` squared `n` times in place, in a loop counted by `r10`. -/
def sqnLoop (umaal : Bool) (o : Slot) (n : Nat) : Prog isa :=
  .seq (.block [.movw .r10 (BitVec.ofNat 16 n)]) <|
    .loop (.seq (mulP umaal o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne

def invert (umaal : Bool) : Prog isa := .seq (power250 umaal) (.seq (sqnLoop umaal 15 5) (mulPc umaal 15 15 14))

def rootPower (umaal : Bool) : Prog isa := .seq (power250 umaal) (.seq (sqnLoop umaal 15 2) (mulPc umaal 15 15 2))

end VG.Impl.Ed25519.Arm
