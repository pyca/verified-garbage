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

While at least eight blocks are left they go eight at a time (`vgroup`,
with `Impl.AesCbc.PPC64LE.batched`), in vector registers: the eight tweaks
computed in `r9` and `r10` and saved in slots 0–7 at the start of the
scratch buffer, and the next one stored at `r16`; the eight blocks read into
`v0`–`v7`, each XORed with its slot, enciphered (or deciphered) together by
the rounds of `Impl.Aes.PPC64LE.Crypto.aes`, XORed with its slot again and
stored in place.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (xorInto callArgs advance encCall decCall slot advance8 batched vsetup xorSlots)

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

/-- The tweak in `r9` (bytes 0–7, little-endian) and `r10` (bytes 8–15)
times `α`, through `r11` and `r12`: `mulA` without its loads and stores. -/
def dbl : List Instr :=
  [.lsr .d .r11 .r10 63, .li .r12 0, .sub .r11 .r12 .r11, .li .r12 0x87, .logic .and .r11 .r11 .r12,
   .lsr .d .r12 .r9 63, .lsl .r9 .r9 1, .logic .xor .r9 .r9 .r11,
   .lsl .r10 .r10 1, .logic .or .r10 .r10 .r12]

/-- The tweak of block `j` stored in slot `j`, and multiplied by `α`. -/
def tweakReg (j : Nat) : List Instr :=
  [.store .d .r9 .r19 (slot j), .store .d .r10 .r19 (slot j + 8)] ++ dbl

/-- The eight blocks' tweaks into slots 0–7, computed in `r9` and `r10`
from the tweak at `r16`, and the next tweak stored back there. -/
def tweaks8 : List Instr :=
  [.load .d .r9 .r16 0, .load .d .r10 .r16 8] ++ (List.range 8).flatMap tweakReg ++
    [.store .d .r9 .r16 0, .store .d .r10 .r16 8]

/-- The eight blocks at `r17` read, XORed with their tweaks, enciphered
(`inverse = false`) or deciphered, XORed with their tweaks again and stored
in place. -/
def vgroup (inverse : Bool) : Prog isa :=
  .seq (.block (tweaks8 ++ vsetup ++
      (Impl.Aes.PPC64LE.Crypto.batchRegs 8).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock false) ++
      [.subi .r6 .r6 128] ++ xorSlots))
    (.seq (Impl.Aes.PPC64LE.Crypto.aes inverse (Impl.Aes.PPC64LE.Crypto.batchRegs 8))
      (.block (xorSlots ++ (Impl.Aes.PPC64LE.Crypto.batchRegs 8).flatMap
        (fun v => Impl.Aes.PPC64LE.Crypto.storeAdvance v) ++ advance8)))

def encrypt : Prog isa := batched (vgroup false) encBody

def decrypt : Prog isa := batched (vgroup true) decBody

end VG.Impl.AesXts.PPC64LE
