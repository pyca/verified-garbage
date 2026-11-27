module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on PPC64LE

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions of
the working space, for the modes. As on AArch64
(`Impl/Sm4/AArch64/Prepared.lean`):

* `prepareKeys(schedule = r3, decrypt = r4, ws = r5, ws_len = r6)` saves
  the callee-saved registers in their slots (384–401), sets the masks of
  the round keys' planes, builds the table of bitsliced round keys in the
  order `decrypt` selects (public) and restores the registers.
* `cryptPrepared(ws = r3, ws_len = r4)` saves the registers the same way and
  transforms the sixteen blocks of the tail buffer (`crypt16`) under the
  table and the masks.

The working space is ECB's 402 slots (`slots`). The table and the masks
are what `vg_sm4_crypt_prepared` reads of the preparation (`layout`): each
plane of a round key is a 64-bit word whose bit `16 i + b` is bit `j` of the
key's byte `i` (`planeOf`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- `vg_sm4_prepare_keys`: the table of the direction `r4` selects. Each
direction's table is the code a branch skips (its `ite`'s first branch), not
the code a conditional branch jumps over (the second branch, here empty):
the unrolled tables are longer than a conditional branch reaches. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .r5] ++ saveRegs ++ setSlots keyMasks))
    (.seq (.seq (.ite (.nonzero .d .r4) (keys .decrypt) (.block [])) (.ite (.zero .d .r4) (keys .encrypt) (.block [])))
      (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the sixteen blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .r3] ++ saveRegs ++ slotAddr .r11 tableEnd)) (.seq crypt16 (.block restoreRegs))

/-! ## ECB

`ecb d(schedule = r3, data = r4, n = r5, scratch = r6)`: `vg_sm4_ecb_encrypt`
and `vg_sm4_ecb_decrypt` with their working space in the scratch buffer,
`ecbSlots` slots: the functions' 402 (`slots`), then the caller's `r30` and
`r31` and the return address, which the function saves there (`ecbEntry`)
and restores (`ecbExit`).

* `vg_sm4_prepare_keys` builds the table of the direction `d` (`ecbPrepare`).
* Each group of up to sixteen blocks is copied to the tail buffer
  (`copyIn`), transformed by `vg_sm4_crypt_prepared` (`ecbCrypt`), and
  copied back (`copyOut`).

Neither function writes `r5` or `r7`, and both keep the callee-saved
registers: `r7` keeps the scratch buffer's address throughout (in `r8` too
between the calls), `r5` the blocks left, `r31` the data pointer, and `r30`
`n` across `vg_sm4_prepare_keys`, which takes the scratch buffer in `r5`.
Only these and the copies' pointers and counts (`r3`, `r6`, `r10`, `r12`,
and the test in `r9`) are addressed or counted, all public. The scratch
buffer's address stays in a register that no call writes, so the analysis of
constant time (`VG.PPC64LE.slotTaint`) knows it, and the slots the functions
save the registers in, on every call.
-/

/-- The bit `vg_sm4_prepare_keys` takes for the direction. -/
def dirBit : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- ECB's slots for the caller's `r30` and `r31` and the return address. -/
def ecbR30 : Nat := slots
def ecbR31 : Nat := slots + 1
def ecbLr : Nat := slots + 2

/-- ECB's working space, in 8-byte slots: a 16-byte multiple. -/
def ecbSlots : Nat := slots + 4

/-- The return address and the caller's `r30` and `r31` to their slots (of
the scratch buffer, at `r6`); the scratch buffer's address to `r7`, the data
pointer to `r31` and `n` to `r30`. -/
def ecbEntry : List Instr :=
  [.mflr .r0, .store .d .r0 .r6 (8 * ecbLr), .store .d .r30 .r6 (8 * ecbR30),
   .store .d .r31 .r6 (8 * ecbR31), movR .r7 .r6, movR .r31 .r4, movR .r30 .r5]

/-- `vg_sm4_prepare_keys(r3, d, r7, slots)`, then `n` back to `r5` and the
scratch buffer's address to `r8`. -/
def ecbPrepare (d : Dir) : Prog isa :=
  .seq (.block [.li .r4 (dirBit d), movR .r5 .r7, .li .r6 slots])
    (.seq (.call "vg_sm4_prepare_keys" prepareKeys) (.block [movR .r5 .r30, movR sb .r7]))

/-- `vg_sm4_crypt_prepared(r7, slots)`, then the scratch buffer's address
back to `r8`. -/
def ecbCrypt : Prog isa :=
  .seq (.block [movR .r3 .r7, .li .r4 slots])
    (.seq (.call "vg_sm4_crypt_prepared" cryptPrepared) (.block [movR sb .r7]))

/-- Sixteen blocks, or the last one to fifteen, and on to the next. -/
def ecbGroup : Prog isa :=
  .seq copyIn (.seq ecbCrypt (.seq copyOut (.block [.sub .r5 .r5 .r12, .addi .r31 .r31 256])))

/-- The caller's `r30`, the return address and the caller's `r31` restored. -/
def ecbExit : List Instr :=
  [.load .d .r30 .r7 (8 * ecbR30), .load .d .r0 .r7 (8 * ecbLr), .mtlr .r0,
   .load .d .r31 .r7 (8 * ecbR31)]

/-- ECB in the direction `d`. -/
def ecb (d : Dir) : Prog isa :=
  .seq (.block ecbEntry) (.seq (ecbPrepare d)
    (.seq (.ite (.zero .d .r5) (.block []) (.loop ecbGroup (.nonzero .d .r5))) (.block ecbExit)))

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

/-- The word of slot `w` of the working space that the preparation writes:
a mask of the round keys' planes, or plane `w % 8` of the table's entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 64 :=
  if w < tableSlot then (keyMasks.find? (·.1 = w)).elim 0 (·.2)
  else Impl.Sm4.planeOf (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

end VG.Impl.Sm4.PPC64LE
