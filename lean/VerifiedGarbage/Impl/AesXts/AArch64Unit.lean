module

public import VerifiedGarbage.Impl.AesXts.AArch64

/-!
# XTS-AES of whole data units: AArch64 implementation

`vg_aes_xts_encrypt_unit(schedule = x0, tweak_schedule = x1, rounds = x2, i = x3, data = x4, len = x5, scratch = x6)`
and `vg_aes_xts_decrypt_unit` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitContract` and `aesDecryptUnitContract`),
composed of calls of the verified whole-block functions `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` (`Impl/AesXts/AArch64.lean`). They are generic
over the implementation of the block functions those call (`Blocks`): each
is emitted once for each (e.g. `vg_aes_xts_encrypt_unit_aes` calls
`vg_aes_xts_encrypt_aes`).

The scratch buffer (2432 bytes): `[0, 2176)` is the working space of the
whole-block functions, `[2176, 2192)` the tweak (`tO`), `[2192, 2208)` a
second tweak (`zO`), and `[2208, 2264)` our caller's callee-saved registers
and our return address `x30`. `x19` holds `schedule`, `x20` `rounds`, `x22`
`len`, `x23` `data` and `x24` the scratch buffer across the calls. A call
(`bl`) stores nothing in memory, so no stack is used.

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
  `Impl.AesXts.AArch64.mulA`, on `x21`) at `zO`; the last whole block
  deciphered with it (`PP`); its first `b` bytes swapped with the `b` after
  it, making them `Pₘ` and the block `CC = Cₘ ‖ CP`; and that deciphered
  with the tweak of block `m - 1`.

The model has no flags: the branches are `cbz`/`cbnz`. Only the pointers,
`rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesXts.AArch64Unit

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov copy)

/-- The offsets of the tweak and the second tweak in the scratch buffer. -/
def tO : Nat := 2176
def zO : Nat := 2192

/-- The registers saved in the scratch buffer, and where (`x24`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 2208), (.x20, 2216), (.x21, 2224), (.x22, 2232), (.x23, 2240), (.x30, 2248), (.x24, 2256)]

def save : List Instr := saved.map fun (r, d) => .str .x r .x6 d

/-- Restores the registers, with `x24` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x24 d

/-- The arguments to the registers kept across the calls. -/
def setup : List Instr := [mov .x24 .x6, mov .x19 .x0, mov .x20 .x2, mov .x23 .x4, mov .x22 .x5]

/-- The second tweak zeroed. -/
def zeroZ : List Instr := [.movz .x .x9 0 0, .str .x .x9 .x24 zO, .str .x .x9 .x24 (zO + 8)]

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` (in `x1`) from the zero tweak. -/
def tArgs : List Instr :=
  [mov .x0 .x1, mov .x1 .x20, .addImm .x .x2 .x24 zO, .addImm .x .x3 .x24 tO, .movz .x .x4 1 0, mov .x5 .x24]

def pro : List Instr := save ++ setup ++ copy .x24 tO .x3 0 ++ zeroZ ++ tArgs

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 tO, mov .x3 .x23, .lsr .x .x4 .x22 4, mov .x5 .x24]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.subImm .x .x4 .x4 1]

/-- The bytes of the whole blocks, `16 (len / 16)`, in `x9`, and the bytes
after them, `b = len mod 16`, in `x10`. -/
def split : List Instr := [.lsr .x .x9 .x22 4, .lsl .x .x9 .x9 4, .sub .x .x10 .x22 .x9]

/-- The address of the last whole block into `x11`. -/
def lastAddr : List Instr := [.add .x .x11 .x23 .x9, .subImm .x .x11 .x11 16]

/-- One byte of the swap: the byte at `x11` swapped with the one 16 bytes
after it, and on to the next (`x10` bytes left). -/
def swapBody : List Instr :=
  [.ldrb .x13 .x11 0, .ldrb .x14 .x11 16, .strb .x14 .x11 0, .strb .x13 .x11 16, .addImm .x .x11 .x11 1,
   .subImm .x .x10 .x10 1]

/-- The first `x10` bytes of the block at `x11` swapped with the `x10` bytes
after it (`0 < x10 < 16`), one byte at a time. -/
def swap : Prog isa := .loop (.block swapBody) (.nonzero .x .x10)

/-- The arguments of a call on the last whole block (from `x9`, as `split`
leaves it), from the tweak at offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.add .x .x3 .x23 .x9, .subImm .x .x3 .x3 16, mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 o,
   .movz .x .x4 1 0, mov .x5 .x24]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr := [.addImm .x .x21 .x24 zO] ++ copy .x24 zO .x24 tO ++ Impl.AesXts.AArch64.mulA

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak (f : Blocks) : Prog isa := .seq (.block pro) (.call f.name f.code)

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal (f : Blocks) : Prog isa :=
  .seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) (.call f.name f.code)))

def encrypt (f : Blocks) : Prog isa :=
  .seq (tweak f) (.seq (.block argsAll) (.seq (.call f.name f.code)
    (.seq (.block split) (.seq (.ite (.zero .x .x10) (.block []) (encSteal f)) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal (f : Blocks) : Prog isa :=
  .seq (.block argsHead) (.seq (.call f.name f.code)
    (.seq (.block (nextT ++ split ++ argsL zO)) (.seq (.call f.name f.code)
      (.seq (.block (split ++ lastAddr)) (.seq swap (.seq (.block (argsL tO)) (.call f.name f.code)))))))

def decrypt (e d : Blocks) : Prog isa :=
  .seq (tweak e) (.seq (.block split)
    (.seq (.ite (.zero .x .x10) (.seq (.block argsAll) (.call d.name d.code)) (decSteal d)) (.block restore)))

end VG.Impl.AesXts.AArch64Unit
