module

public import VerifiedGarbage.Impl.Ed25519.Arm.Point16

/-! A fixed addition chain shared by inversion and square-root recovery,
inlined where it is used. Each product outside a loop is a call of
`vg_gf25519_r16_mul` (`mulPc`), and each run of squarings a call of
`vg_gf25519_r16_sqr{o}` (`sqrCall`), a function of the inlined squaring
of slot `o` in a loop counted by `r10`, which its caller sets: the counter
never crosses a call within the loop. The chain runs once per inversion or
square root, where a call costs little next to a product. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG.Arm

def mulP (umaal : Bool) (o a b : Slot) : Prog isa := mulIn umaal (offset o) (offset a) (offset b)

/-- `[o] = [a] · [b]`, by a call of `vg_gf25519_r16_mul`. -/
def mulPc (umaal : Bool) (o a b : Slot) : Prog isa := mulCall umaal (offset o) (offset a) (offset b)

/-- Slot `o` squared in place `r10` times (`r10 ≥ 1`). -/
def sqLoop (umaal : Bool) (o : Slot) : Prog isa :=
  .loop (.seq (mulP umaal o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne

/-- `vg_gf25519_r16_sqr{o}`: `sqLoop`, saving and restoring the registers it
changes, `r10` among them. -/
def sqrFn (umaal : Bool) (o : Slot) : Prog isa := asFn true (sqLoop umaal o)

/-- Each slot's number, as text: literals, which the kernel compares as they
are where it checks the code's literals (`materialize_code`). -/
def slotTags : List String :=
  ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17", "18",
    "19", "20", "21"]

def sqrName (umaal : Bool) (o : Slot) : String := "vg_gf25519_r16_sqr" ++ slotTags.getD o.val "" ++ suffix umaal

/-- Slot `o` squared in place `n` times (`1 ≤ n < 2¹⁶`), by a call of
`vg_gf25519_r16_sqr{o}`. -/
def sqrCall (umaal : Bool) (o : Slot) (n : Nat) : Prog isa :=
  .seq (.block [.movw .r10 (BitVec.ofNat 16 n)]) (.call (sqrName umaal o) (sqrFn umaal o))

/-- Slot `o` = slot `a` squared `n` times, `n ≥ 2`. -/
def sqn (umaal : Bool) (o a : Slot) (n : Nat) : Prog isa :=
  .seq (mulPc umaal o a a) (sqrCall umaal o (n - 1))

/-- From z in slot 2, leave z^(2^250 - 1) in slot 15 and z^11 in slot 14,
using slots 16 and 17. -/
def chain250 (umaal : Bool) : Prog isa :=
  .seq (mulPc umaal 14 2 2) <|
  .seq (mulPc umaal 15 14 14) <| .seq (mulPc umaal 15 15 15) <|
  .seq (mulPc umaal 15 2 15) <| .seq (mulPc umaal 14 14 15) <|
  .seq (mulPc umaal 16 14 14) <| .seq (mulPc umaal 15 15 16) <|
  .seq (sqn umaal 16 15 5) <| .seq (mulPc umaal 15 16 15) <|
  .seq (sqn umaal 16 15 10) <| .seq (mulPc umaal 16 16 15) <|
  .seq (sqn umaal 17 16 20) <| .seq (mulPc umaal 16 17 16) <|
  .seq (sqn umaal 16 16 10) <| .seq (mulPc umaal 15 16 15) <|
  .seq (sqn umaal 16 15 50) <| .seq (mulPc umaal 16 16 15) <|
  .seq (sqn umaal 17 16 100) <| .seq (mulPc umaal 16 17 16) <|
  .seq (sqn umaal 16 16 50) (mulPc umaal 15 16 15)

/-- Slot `o` squared `n` times in place. -/
def sqnLoop (umaal : Bool) (o : Slot) (n : Nat) : Prog isa := sqrCall umaal o n

def invert (umaal : Bool) : Prog isa := .seq (chain250 umaal) (.seq (sqnLoop umaal 15 5) (mulPc umaal 15 15 14))

def rootPower (umaal : Bool) : Prog isa := .seq (chain250 umaal) (.seq (sqnLoop umaal 15 2) (mulPc umaal 15 15 2))

end VG.Impl.Ed25519.Arm
