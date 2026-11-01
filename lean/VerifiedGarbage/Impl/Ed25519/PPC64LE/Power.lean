module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Point

/-! A fixed addition chain shared by inversion and square-root recovery. -/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

def mulP (o a b : Slot) : Prog isa := mul (offset o) (offset a) (offset b)

/-- `a` squared `n` times into `o`, the squarings after the first in a loop
counted by `r12`, which the inlined products do not write. -/
def sqn (o a : Slot) (n : Nat) : Prog isa :=
  .seq (mulP o a a) <|
  .seq (.block [.li .r12 (n - 1)]) <|
    .loop (.seq (mulP o o o) (.block [.subi .r12 .r12 1])) (.nonzero .d .r12)

/-- From z in slot 2, leave z^(2^250 - 1) in slot 15 and z^11 in slot 14,
using slots 16 and 17. -/
def chain250 : Prog isa :=
  .seq (mulP 14 2 2) <|
  .seq (mulP 15 14 14) <| .seq (mulP 15 15 15) <|
  .seq (mulP 15 2 15) <| .seq (mulP 14 14 15) <|
  .seq (mulP 16 14 14) <| .seq (mulP 15 15 16) <|
  .seq (sqn 16 15 5) <| .seq (mulP 15 16 15) <|
  .seq (sqn 16 15 10) <| .seq (mulP 16 16 15) <|
  .seq (sqn 17 16 20) <| .seq (mulP 16 17 16) <|
  .seq (sqn 16 16 10) <| .seq (mulP 15 16 15) <|
  .seq (sqn 16 15 50) <| .seq (mulP 16 16 15) <|
  .seq (sqn 17 16 100) <| .seq (mulP 16 17 16) <|
  .seq (sqn 16 16 50) (mulP 15 16 15)

/-- `vg_gf25519_r32_pow250` (`Proof/X25519/Field32Contract.lean`): `ws` moved to
`r6`, and the chain. It uses only volatile registers. -/
def pow250Fn : Prog isa := .seq (.block [.addi .r6 .r3 0]) chain250

/-- A call of `vg_gf25519_r32_pow250`. -/
def power250 : Prog isa :=
  .seq (.block [.addi .r3 .r6 0])
    (.seq (.call "vg_gf25519_r32_pow250" pow250Fn) (.block [.addi .r6 .r3 0]))

/-- `[o] = [a] · [b]`, by a call of `vg_gf25519_r32_mul`. -/
def mulPc (o a b : Slot) : Prog isa := mulCall (offset o) (offset a) (offset b)

/-- Slot `o` squared `n` times in place, in a loop counted by `r12`. -/
def sqnLoop (o : Slot) (n : Nat) : Prog isa :=
  .seq (.block [.li .r12 n]) <|
    .loop (.seq (mulP o o o) (.block [.subi .r12 .r12 1])) (.nonzero .d .r12)

def invert : Prog isa := .seq power250 (.seq (sqnLoop 15 5) (mulPc 15 15 14))

def rootPower : Prog isa := .seq power250 (.seq (sqnLoop 15 2) (mulPc 15 15 2))

end VG.Impl.Ed25519.PPC64LE
