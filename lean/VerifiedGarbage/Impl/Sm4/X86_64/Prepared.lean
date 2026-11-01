module

public import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's batches under prepared round keys, on x86-64

`vg_sm4_crypt_prepared` (`Proof/Sm4/Prepared.lean`): ECB's sixteen blocks
(`Ecb.lean`) as a function of the working space, for the modes, which call
it (`Ctr.lean`).

`cryptPrepared(ws = rdi, ws_len = rsi)` moves `ws` to `sb`, saves the
callee-saved registers in their slots (384–389), transforms the sixteen
blocks of the tail buffer (`crypt16`) under the table and the masks, and
restores the registers.

The working space is ECB's 392 slots (`slots`). The masks and the table are
what `vg_sm4_crypt_prepared` reads (`layout`): each plane of a round key is
a 64-bit word whose bit `16 i + b` is bit `j` of the key's byte `i`
(`planeOf`), for every block `b`.

The modes build the table themselves, ECB's key setup inline in their
core's `prepare`: its loop stores through a pointer that the analysis of
constant time cannot place, which would leave it nothing known of the
working space after a call, and the core keeps the modes' data pointer
and count (`rdx`, `r8`) in registers that `vg_sm4_crypt_prepared` does not
write.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- `vg_sm4_crypt_prepared`: the sixteen blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .rdi] ++ saveRegs ++ slotAddr .rdi tableEnd)) (.seq crypt16 (.block restoreRegs))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Sm4.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The round key of the table's entry `e`, for the round keys `k` in the
order of the direction. -/
def keyEntry (k : Spec.Sm4.Schedule) : Dir → Nat → Spec.Sm4.Word
  | .encrypt, e => k.getD e 0
  | .decrypt, e => k.getD (31 - e) 0

/-- The word of slot `w` of the working space that the key setup writes: a
mask of the round keys' planes, or plane `w % 8` of the table's entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 64 :=
  if w < tableSlot then (keyMasks.find? (·.1 = w)).elim 0 (·.2)
  else Impl.Sm4.planeOf (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

/-! ## The call -/

/-- A call of `vg_sm4_crypt_prepared` on the working space at `sb`, of
`slots` words, which leaves `sb` as it was: the function moves `ws` there. -/
def cryptCall : Prog isa :=
  .seq (.block [movR .rdi sb, .movImm64 .rsi (BitVec.ofNat 64 slots)])
    (.call "vg_sm4_crypt_prepared" cryptPrepared)

end VG.Impl.Sm4.X86_64
