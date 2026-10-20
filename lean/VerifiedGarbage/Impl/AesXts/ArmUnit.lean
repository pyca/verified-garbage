module

public import VerifiedGarbage.Impl.AesXts.Arm

/-!
# XTS-AES of whole data units: ARMv7 implementation

`vg_aes_xts_encrypt_unit(schedule = r0, tweak_schedule = r1, rounds = r2, i = r3, data, len, scratch)`
and `vg_aes_xts_decrypt_unit` with the same arguments (the last three on the
stack; see `VG.Spec.Xts.aesEncryptUnitContract` and
`aesDecryptUnitContract`), composed of calls of the verified whole-block
functions `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`
(`Impl/AesXts/Arm.lean`), each in a frame that pushes its two stack
arguments, the number of blocks (`r12`) and the working space (`lr`).

The scratch buffer (2432 bytes): `[0, 2176)` is the working space of the
whole-block functions, `[2176, 2192)` the tweak (`tO`), `[2192, 2208)` a
second tweak (`zO`), and `[2208, 2236)` our caller's `r4`–`r7` and `r9`,
our return address `lr`, and `r8`. `r4` holds `schedule`, `r5` `rounds`,
`r7` `len`, `r8` the scratch buffer and `r9` `data` across the calls; the
whole-block functions' `mulA` multiplies the tweak at `r6` by `α`.

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
  block `m` (that times `α`) at `zO`; the last whole block deciphered with
  it (`PP`); its first `b` bytes swapped with the `b` after it, making them
  `Pₘ` and the block `CC = Cₘ ‖ CP`; and that deciphered with the tweak of
  block `m - 1`.

The calls use 16 bytes of stack: the frame of their stack arguments, and
the whole-block functions' frames of theirs. Only the pointers, `rounds`
and `len` can affect timing: the branches are on `len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.ArmUnit

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)

/-- The offsets of the tweak and the second tweak in the scratch buffer. -/
def tO : Nat := 2176
def zO : Nat := 2192

/-- The registers saved in the scratch buffer, and where (`r8`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, 2208), (.r5, 2212), (.r6, 2216), (.r7, 2220), (.r9, 2224), (.lr, 2228), (.r8, 2232)]

/-- Saves them, with the scratch buffer (the third stack argument) in `r12`. -/
def save : List Instr := .ldrSp .r12 8 :: saved.map fun (r, d) => .str r .r12 d

/-- Restores them, with `r8` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r8 d

/-- The arguments to the registers kept across the calls. -/
def setup : List Instr := [mov .r8 .r12, mov .r4 .r0, mov .r5 .r2, .ldrSp .r9 0, .ldrSp .r7 4]

/-- The block at `src + e` copied to `dst + d`: its four words loaded into
`a`, `b`, `c` and `f`, then stored. -/
def copy (a b c f : Reg) (dst : Reg) (d : Nat) (src : Reg) (e : Nat) : List Instr :=
  [.ldr a src e, .ldr b src (e + 4), .ldr c src (e + 8), .ldr f src (e + 12),
   .str a dst d, .str b dst (d + 4), .str c dst (d + 8), .str f dst (d + 12)]

/-- The second tweak zeroed. -/
def zeroZ : List Instr :=
  [.mov .r12 (.imm 0), .str .r12 .r8 zO, .str .r12 .r8 (zO + 4), .str .r12 .r8 (zO + 8), .str .r12 .r8 (zO + 12)]

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` (in `r1`) from the zero tweak. -/
def tArgs : List Instr :=
  [mov .r0 .r1, mov .r1 .r5, .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 zO)),
   .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 tO)), .mov .r12 (.imm 1), mov .lr .r8]

def pro : List Instr := save ++ setup ++ copy .r12 .lr .r0 .r2 .r8 tO .r3 0 ++ zeroZ ++ tArgs

/-- A call of a whole-block function in the frame of its stack arguments. -/
def xcall (n : String) (c : Prog isa) : Prog isa := .frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)

def encCall : Prog isa := xcall "vg_aes_xts_encrypt" Impl.AesXts.Arm.encrypt

def decCall : Prog isa := xcall "vg_aes_xts_decrypt" Impl.AesXts.Arm.decrypt

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 tO)), mov .r3 .r9,
   .mov .r12 (.shifted .r7 .lsr 4), mov .lr .r8]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.dp .sub .r12 .r12 (.imm 1)]

/-- The bytes of the whole blocks, `16 (len / 16)`, in `r0`, and the bytes
after them, `b = len mod 16`, in `r1`; Z set if `b` is zero. -/
def split : List Instr := [.mov .r0 (.shifted .r7 .lsr 4), .mov .r0 (.shifted .r0 .lsl 4), .subs .r1 .r7 (.reg .r0)]

/-- The address of the last whole block into `r2`. -/
def lastAddr : List Instr := [.dp .add .r2 .r9 (.reg .r0), .dp .sub .r2 .r2 (.imm 16)]

/-- One byte of the swap: the byte at `r2` swapped with the one 16 bytes
after it, and on to the next (`r1` bytes left, Z set when none are). -/
def swapBody : List Instr :=
  [.ldrb .r3 .r2 0, .ldrb .r12 .r2 16, .strb .r12 .r2 0, .strb .r3 .r2 16, .dp .add .r2 .r2 (.imm 1),
   .subs .r1 .r1 (.imm 1)]

/-- The first `r1` bytes of the block at `r2` swapped with the `r1` bytes
after it (`0 < r1 < 16`), one byte at a time. -/
def swap : Prog isa := .loop (.block swapBody) .ne

/-- The arguments of a call on the last whole block (from `r0`, as `split`
leaves it), from the tweak at offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.dp .add .r3 .r9 (.reg .r0), .dp .sub .r3 .r3 (.imm 16), mov .r0 .r4, mov .r1 .r5,
   .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 o)), .mov .r12 (.imm 1), mov .lr .r8]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr :=
  [.dp .add .r6 .r8 (.imm (BitVec.ofNat 32 zO))] ++ copy .r0 .r1 .r2 .r3 .r8 zO .r8 tO ++ Impl.AesXts.Arm.mulA

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak : Prog isa := .seq (.block pro) encCall

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal : Prog isa := .seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) encCall))

def encrypt : Prog isa :=
  .seq tweak (.seq (.block argsAll) (.seq encCall
    (.seq (.block split) (.seq (.ite .eq (.block []) encSteal) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal : Prog isa :=
  .seq (.block argsHead) (.seq decCall
    (.seq (.block (nextT ++ split ++ argsL zO)) (.seq decCall
      (.seq (.block (split ++ lastAddr)) (.seq swap (.seq (.block (argsL tO)) decCall))))))

def decrypt : Prog isa :=
  .seq tweak (.seq (.block split)
    (.seq (.ite .eq (.seq (.block argsAll) decCall) decSteal) (.block restore)))

end VG.Impl.AesXts.ArmUnit
