module

public import VerifiedGarbage.Impl.AesXts.RISCV64

/-!
# XTS-AES of whole data units: RISC-V implementation

`vg_aes_xts_encrypt_unit(schedule = a0, tweak_schedule = a1, rounds = a2, i = a3, data = a4, len = a5, scratch = a6)`
and `vg_aes_xts_decrypt_unit` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitContract` and `aesDecryptUnitContract`),
composed of calls of the verified whole-block functions `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` (`Impl/AesXts/RISCV64.lean`), as on PPC64LE
(`VG.Impl.AesXts.PPC64LEUnit`).

The scratch buffer (2432 bytes): `[0, 16)` the tweak (`tO`), `[16, 32)` a
second tweak (`zO`), from `sv = scratch + 32` rounded up to a multiple of 8
(`savePtr`, at most `scratch + 39`) our return address (which each call
replaces) and our caller's `s1`–`s6`, and `[96, 2272)` the working space of
the whole-block functions (`wO`). Every offset is below 2048, as load,
store and `addi` displacements must be. `s1` holds `schedule`, `s2`
`rounds`, `s4` `data`, `s5` `len` and `s6` the scratch buffer across the
calls; `s3` points to the second tweak while it is multiplied by `α`.

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
  `Impl.AesXts.RISCV64.mulA`, on `s3`) at `zO`; the last whole block
  deciphered with it (`PP`); its first `b` bytes swapped with the `b` after
  it, making them `Pₘ` and the block `CC = Cₘ ‖ CP`; and that deciphered
  with the tweak of block `m - 1`.

The tweaks and the data have no stated alignment, so they are copied, zeroed
and swapped a byte at a time.

Only the pointers, `rounds` and `len` can affect timing: the only branches
are on `len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.RISCV64Unit

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)

/-- The offsets of the tweak, the second tweak and the working space of the
whole-block functions in the scratch buffer. -/
def tO : Nat := 0
def zO : Nat := 16
def wO : Nat := 96

/-- `t0 :=` the register `n`'s value plus 32, rounded up to a multiple of 8. -/
def savePtr (n : Reg) : List Instr := [.addi .t0 n 39, .logicImm .and .t0 .t0 (-8)]

/-- Our return address and our caller's registers, and their offsets from `sv`. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48)]

/-- Saves them, with the scratch buffer in `a6`. -/
def save : List Instr := savePtr .a6 ++ saved.map fun (r, d) => .store .d r .t0 d

/-- Restores them, with the scratch buffer in `s6`. -/
def restore : List Instr := savePtr .s6 ++ saved.map fun (r, d) => .load .d r .t0 d

/-- The arguments to the registers kept across the calls. -/
def setup : List Instr := [mov .s1 .a0, mov .s2 .a2, mov .s4 .a4, mov .s5 .a5, mov .s6 .a6]

/-- `i` copied to the tweak. -/
def copyI : List Instr := copyBytes .t3 .a3 .s6 0 tO 16

/-- The second tweak zeroed. -/
def zeroZ : List Instr := storeBytes .t1 .s6 zO (List.replicate 16 0)

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` (in `a1`) from the zero tweak. -/
def tArgs : List Instr :=
  [mov .a0 .a1, mov .a1 .s2, .addi .a2 .s6 zO, .addi .a3 .s6 tO, .li .a4 1, .addi .a5 .s6 wO]

def pro : List Instr := save ++ setup ++ copyI ++ zeroZ ++ tArgs

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [mov .a0 .s1, mov .a1 .s2, .addi .a2 .s6 tO, mov .a3 .s4, .shift .srl .d .a4 .s5 4, .addi .a5 .s6 wO]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.addi .a4 .a4 (-1)]

/-- The bytes of the whole blocks, `16 (len / 16)`, in `t1`, and the bytes
after them, `b = len mod 16`, in `t2`. -/
def split : List Instr := [.shift .srl .d .t1 .s5 4, .shift .sll .d .t1 .t1 4, .sub .t2 .s5 .t1]

/-- The address of the last whole block into `t3`. -/
def lastAddr : List Instr := [.add .t3 .s4 .t1, .addi .t3 .t3 (-16)]

/-- One byte of the swap: the byte at `t3` swapped with the one 16 bytes
after it, and on to the next (`t2` bytes left). -/
def swapBody : List Instr :=
  [.load .b .t4 .t3 0, .load .b .t5 .t3 16, .store .b .t5 .t3 0, .store .b .t4 .t3 16,
   .addi .t3 .t3 1, .addi .t2 .t2 (-1)]

/-- The first `t2` bytes of the block at `t3` swapped with the `t2` bytes
after it (`0 < t2 < 16`), one byte at a time. -/
def swap : Prog isa := .loop (.block swapBody) (.nonzero .t2)

/-- The arguments of a call on the last whole block (from `t1`, as `split`
leaves it), from the tweak at offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.add .a3 .s4 .t1, .addi .a3 .a3 (-16), mov .a0 .s1, mov .a1 .s2, .addi .a2 .s6 o, .li .a4 1,
   .addi .a5 .s6 wO]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr :=
  [.addi .s3 .s6 zO] ++ copyBytes .t3 .s6 .s6 tO zO 16 ++ Impl.AesXts.RISCV64.mulA

/-- A call of `vg_aes_xts_encrypt`. -/
def encCall : Prog isa := .call "vg_aes_xts_encrypt" Impl.AesXts.RISCV64.encrypt

/-- A call of `vg_aes_xts_decrypt`. -/
def decCall : Prog isa := .call "vg_aes_xts_decrypt" Impl.AesXts.RISCV64.decrypt

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak : Prog isa := .seq (.block pro) encCall

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal : Prog isa := .seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) encCall))

def encrypt : Prog isa :=
  .seq tweak (.seq (.block argsAll) (.seq encCall
    (.seq (.block split) (.seq (.ite (.zero .t2) (.block []) encSteal) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal : Prog isa :=
  .seq (.block argsHead) (.seq decCall
    (.seq (.block (nextT ++ split ++ argsL zO)) (.seq decCall
      (.seq (.block (split ++ lastAddr)) (.seq swap (.seq (.block (argsL tO)) decCall))))))

def decrypt : Prog isa :=
  .seq tweak (.seq (.block split)
    (.seq (.ite (.zero .t2) (.seq (.block argsAll) decCall) decSteal) (.block restore)))

end VG.Impl.AesXts.RISCV64Unit
