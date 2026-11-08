module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# XTS-AES: PPC64LE implementation

`vg_aes_xts_encrypt(schedule = r3, rounds = r4, tweak = r5, data = r6, n = r7, scratch = r8)`
and `vg_aes_xts_decrypt` with the same arguments, composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
one block at a time, in place, as on ARMv7 (`VG.Impl.AesXts.Arm`).

They are built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `r14` (schedule), `r15` (rounds), `r16` (the tweak),
`r17` (the next block), `r18` (blocks left) and `r19` (scratch). Each block,
the tweak is XORed into the data block, which is enciphered (or deciphered)
in place, the tweak is XORed in again, and the tweak is multiplied by `α`
(`mulA`): its two words, little-endian, loaded, the low word shifted left by
one bit and XORed with `0x87` if the high word's top bit was set (a mask
from `0 − (hi >> 63)`), and the high word shifted left with the low word's
top bit shifted in.

While at least eight blocks are left they go eight at a time, by one call
(`group`, with `Impl.AesCbc.PPC64LE.groups`): for each block, the tweak
XORed in, saved in slot `j` at the start of the scratch buffer (which the
POWER8 block functions do not write) and multiplied by `α`; the eight blocks
enciphered (or deciphered) in place by one call; and each XORed with its
slot.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (xorInto callArgs advance whole encCall decCall xorAt copy slot fixSlots
  callArgs8 advance8 batched)

/-- The tweak at `r16` times `α`. -/
def mulA : List Instr :=
  [.load .d .r9 .r16 0, .load .d .r10 .r16 8,
   .lsr .d .r11 .r10 63, .li .r12 0, .sub .r11 .r12 .r11, .li .r12 0x87, .logic .and .r11 .r11 .r12,
   .lsr .d .r12 .r9 63, .lsl .r9 .r9 1, .logic .xor .r9 .r9 .r11,
   .lsl .r10 .r10 1, .logic .or .r10 .r10 .r12,
   .store .d .r9 .r16 0, .store .d .r10 .r16 8]

/-- The tweak XORed into the data block, and the arguments of the call. -/
def pre : List Instr := xorInto .r17 .r16 ++ callArgs

/-- The tweak XORed in again, the tweak times `α`, and on to the next block. -/
def post : List Instr := xorInto .r17 .r16 ++ mulA ++ advance

def encBody : Prog isa := .seq (.block pre) (.seq encCall (.block post))

def decBody : Prog isa := .seq (.block pre) (.seq decCall (.block post))

/-! ## Groups of eight blocks -/

/-- Block `j` of the eight at `r17`: the tweak XORed into it, saved in slot
`j`, and multiplied by `α`. -/
def tweakAt (j : Nat) : List Instr := xorAt .r17 (16 * j) .r16 0 ++ copy .r19 (slot j) .r16 0 ++ mulA

/-- The eight blocks' tweaks XORed in and saved, and the arguments of the
call. -/
def pre8 : List Instr := (List.range 8).flatMap tweakAt ++ callArgs8

/-- Eight blocks: the tweaks XORed in and saved, the blocks enciphered (or
deciphered) in place by one call, and each XORed with its tweak again. -/
def group (call : Prog isa) : Prog isa := .seq (.block pre8) (.seq call (.block (fixSlots ++ advance8)))

def encrypt : Prog isa := batched (group encCall) encBody

def decrypt : Prog isa := batched (group decCall) decBody

end VG.Impl.AesXts.PPC64LE
