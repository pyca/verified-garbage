module

public import VerifiedGarbage.Impl.Camellia.X86.AesNi
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# The Camellia key schedule on x86 (32-bit), its rounds by `aesenclast`

The key schedule (`ExpandKey.lean`) whose `KA` and `KB` take the three pairs
of rounds by AES-NI: each the last pair of a group of the one-block code's
(`AesNi.lean`) on the 128-bit value in `xmm0` (`pairX`): the value to the
rounds' form (`headX`), the two rounds, and back to bytes (`layerIn`, and the
byte shuffle that `headX` starts with). The keys they read, in that code's
form, are constants of its table, copied (`keysIn`) to the scratch buffer's
first 48 slots, where `kr` reads them, 32 bytes further on for each pair.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86.AesNiKey

open VG.X86
open VG.Impl.Aes.X86 (sb)
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 x ld stx tb tableName headX layerIn oBSW oSIG)

/-- The keys of pair `p`, from the table to where its code reads them. -/
def keysOne (p : Nat) : List Instr :=
  [tb .xmm0 (oSIG p), stx sb (32 * p) .xmm0, tb .xmm0 (oSIG p + 16), stx sb (32 * p + 48) .xmm0]

/-- The keys of the three pairs of rounds. -/
def keysIn : List Instr := keysOne 0 ++ (keysOne 1 ++ keysOne 2)

/-- The halves in the rounds' form, back to the value in `xmm4`. -/
def backX : List Instr := layerIn ++ [tb .xmm5 oBSW, x .pshufb .xmm4 .xmm5]

/-- Two rounds on the value in `xmm0`, to `xmm4`. -/
def pairX : List Instr := headX ++ ((AesNi.round .xmm0 .xmm1 4 ++ AesNi.round .xmm1 .xmm0 5) ++ backX)

/-- The value at slot `v`, to `d`. -/
def ldV (d : XReg) (v : Nat) : Instr := ld d sb (4 * v)

/-- On to the next pair's keys. -/
def nextKeys : Instr := .alu .add kr (.imm 32)

/-- `KA` and `KB`, from `KL` and `KR`. -/
def kaKb : List Instr :=
  ldV .xmm0 klSlot :: ldV .xmm1 krSlot :: x .pxor .xmm0 .xmm1 :: (pairX ++
  ldV .xmm0 klSlot :: x .pxor .xmm0 .xmm4 :: nextKeys :: (pairX ++
  stx sb (4 * kaSlot) .xmm4 :: ldV .xmm0 krSlot :: x .pxor .xmm0 .xmm4 :: nextKeys :: (pairX ++
  [stx sb (4 * kbSlot) .xmm4])))

/-- The block of the key schedule's code for `KA` and `KB`. -/
def mid : List Instr := .mov tbr (.reg .edx) :: .mov kr (.reg sb) :: (keysIn ++ kaKb)

/-- `vg_camellia_expand_key`, with its scratch buffer as the fourth argument. -/
def expandKey : Prog isa := X86.expandKey tableName mid

namespace Fn

/-- The doublewords of the 420 bytes of stack below `esp` that the residue
analysis finds the function may leave different in two runs: the header of
its working space's frame, and the frame's last three doublewords, which
nothing writes. -/
def words : List Nat := [1, 2, 3, 4, 5, 102, 103, 104]

/-- `Spec.Camellia.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 420 words
    (Impl.StackScratch.X86.withStackScratchWiped 416 3 96 AesNiKey.expandKey)

end Fn

end VG.Impl.Camellia.X86.AesNiKey
