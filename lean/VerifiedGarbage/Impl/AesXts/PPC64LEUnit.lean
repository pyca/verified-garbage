module

public import VerifiedGarbage.Impl.AesXts.PPC64LE

/-!
# XTS-AES of whole data units: PPC64LE implementation

`vg_aes_xts_encrypt_unit(schedule = r3, tweak_schedule = r4, rounds = r5, i = r6, data = r7, len = r8, scratch = r9)`
and `vg_aes_xts_decrypt_unit` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitContract` and `aesDecryptUnitContract`),
composed of calls of the verified whole-block functions `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` (`Impl/AesXts/PPC64LE.lean`), as on AArch64
(`VG.Impl.AesXts.AArch64Unit`).

The scratch buffer (2432 bytes): `[0, 2176)` is the working space of the
whole-block functions, `[2176, 2192)` the tweak (`tO`), `[2192, 2208)` a
second tweak (`zO`), `[2208, 2256)` our caller's `r14`–`r19`, and
`[2256, 2264)` our return address (a call replaces the link register).
`r14` holds `schedule`, `r15` `rounds`, `r17` `data`, `r18` `len` and `r19`
the scratch buffer across the calls; `r16` points to the second tweak while
it is multiplied by `α`. A call (`bl`) stores nothing in memory, so no stack
is used.

* The tweak `T = AES-enc(Key2, i)`: `i` is copied to the tweak, and the
  whole-block encryption with `tweak_schedule` enciphers it as one block
  with a zero tweak (`zO`), which is `AES-enc(Key2, i ⊕ 0) ⊕ 0`.
* `encrypt`: the `m = len / 16` whole blocks from `T`, which leaves the
  tweak of block `m`. If `b = len mod 16` is not zero, the last whole block
  is `CC`: its first `b` bytes are swapped with the `b` bytes after it
  (`swap`), making them `Cₘ` and the block `PP = Pₘ ‖ CP`, which is
  enciphered with the tweak of block `m`.
* `decrypt`: without a partial block, the `m` blocks from `T`. Otherwise
  the first `m - 1`, which leaves the tweak of block `m - 1`; the tweak of
  block `m` (that times `α`, as the whole-block functions compute it:
  `Impl.AesXts.PPC64LE.mulA`, on `r16`) at `zO`; the last whole block
  deciphered with it (`PP`); its first `b` bytes swapped with the `b` after
  it, making them `Pₘ` and the block `CC = Cₘ ‖ CP`; and that deciphered
  with the tweak of block `m - 1`.

Only the pointers, `rounds` and `len` can affect timing: the only branches
are on `len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.PPC64LEUnit

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov copy)

/-- The offsets of the tweak and the second tweak in the scratch buffer. -/
def tO : Nat := 2176
def zO : Nat := 2192

/-- The offset of the saved return address in the scratch buffer. -/
def lrOff : Nat := 2256

/-- The registers saved in the scratch buffer, and where (`r19`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r14, 2208), (.r15, 2216), (.r16, 2224), (.r17, 2232), (.r18, 2240), (.r19, 2248)]

/-- Saves the registers and the return address in the scratch buffer at `r9`. -/
def save : List Instr :=
  .mflr .r0 :: .store .d .r0 .r9 lrOff :: saved.map fun (r, d) => .store .d r .r9 d

/-- Restores the return address and the registers, with `r19` (restored
last) the scratch buffer. -/
def restore : List Instr :=
  .load .d .r0 .r19 lrOff :: saved.map (fun (r, d) => .load .d r .r19 d) ++ [.mtlr .r0]

/-- The arguments to the registers kept across the calls. -/
def setup : List Instr := [mov .r14 .r3, mov .r15 .r5, mov .r17 .r7, mov .r18 .r8, mov .r19 .r9]

/-- The second tweak zeroed. -/
def zeroZ : List Instr := [.li .r9 0, .store .d .r9 .r19 zO, .store .d .r9 .r19 (zO + 8)]

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` (in `r4`) from the zero tweak. -/
def tArgs : List Instr :=
  [mov .r3 .r4, mov .r4 .r15, .addi .r5 .r19 zO, .addi .r6 .r19 tO, .li .r7 1, mov .r8 .r19]

def pro : List Instr := save ++ setup ++ copy .r19 tO .r6 0 ++ zeroZ ++ tArgs

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [mov .r3 .r14, mov .r4 .r15, .addi .r5 .r19 tO, mov .r6 .r17, .lsr .d .r7 .r18 4, mov .r8 .r19]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.subi .r7 .r7 1]

/-- The bytes of the whole blocks, `16 (len / 16)`, in `r10`, and the bytes
after them, `b = len mod 16`, in `r11`. -/
def split : List Instr := [.lsr .d .r10 .r18 4, .lsl .r10 .r10 4, .sub .r11 .r18 .r10]

/-- The address of the last whole block into `r12`. -/
def lastAddr : List Instr := [.add .r12 .r17 .r10, .subi .r12 .r12 16]

/-- One byte of the swap: the byte at `r12` swapped with the one 16 bytes
after it, and on to the next (`r11` bytes left). -/
def swapBody : List Instr :=
  [.lbz .r8 .r12 0, .lbz .r9 .r12 16, .stb .r9 .r12 0, .stb .r8 .r12 16, .addi .r12 .r12 1,
   .subi .r11 .r11 1]

/-- The first `r11` bytes of the block at `r12` swapped with the `r11` bytes
after it (`0 < r11 < 16`), one byte at a time. -/
def swap : Prog isa := .loop (.block swapBody) (.nonzero .d .r11)

/-- The arguments of a call on the last whole block (from `r10`, as `split`
leaves it), from the tweak at offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.add .r6 .r17 .r10, .subi .r6 .r6 16, mov .r3 .r14, mov .r4 .r15, .addi .r5 .r19 o, .li .r7 1,
   mov .r8 .r19]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr :=
  [.addi .r16 .r19 zO] ++ copy .r19 zO .r19 tO ++ Impl.AesXts.PPC64LE.mulA

/-- A call of `vg_aes_xts_encrypt`. -/
def encCall : Prog isa := .call "vg_aes_xts_encrypt" Impl.AesXts.PPC64LE.encrypt

/-- A call of `vg_aes_xts_decrypt`. -/
def decCall : Prog isa := .call "vg_aes_xts_decrypt" Impl.AesXts.PPC64LE.decrypt

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak : Prog isa := .seq (.block pro) encCall

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal : Prog isa := .seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) encCall))

def encrypt : Prog isa :=
  .seq tweak (.seq (.block argsAll) (.seq encCall
    (.seq (.block split) (.seq (.ite (.zero .d .r11) (.block []) encSteal) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal : Prog isa :=
  .seq (.block argsHead) (.seq decCall
    (.seq (.block (nextT ++ split ++ argsL zO)) (.seq decCall
      (.seq (.block (split ++ lastAddr)) (.seq swap (.seq (.block (argsL tO)) decCall))))))

def decrypt : Prog isa :=
  .seq tweak (.seq (.block split)
    (.seq (.ite (.zero .d .r11) (.seq (.block argsAll) decCall) decSteal) (.block restore)))

end VG.Impl.AesXts.PPC64LEUnit
