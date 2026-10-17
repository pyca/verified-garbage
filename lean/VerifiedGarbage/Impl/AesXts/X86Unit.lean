module

public import VerifiedGarbage.Impl.AesXts.X86

/-!
# XTS-AES of whole data units: x86 (32-bit) implementation

`vg_aes_xts_encrypt_unit(schedule, tweak_schedule, rounds, i, data, len, scratch)`
and `vg_aes_xts_decrypt_unit` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitContract` and `aesDecryptUnitContract`), every
argument on the stack (cdecl), composed of calls of the verified
whole-block functions `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`
(`Impl/AesXts/X86.lean`), each in a frame that pushes its six arguments.
They are generic over the implementation of the block functions those call
(`Blocks`): each is emitted once for each (e.g.
`vg_aes_xts_encrypt_unit_aesni` calls `vg_aes_xts_encrypt_aesni`).

The scratch buffer (2432 bytes): `[0, 2176)` is the working space of the
whole-block functions, `[2176, 2192)` the tweak (`tO`), `[2192, 2208)` a
second tweak (`zO`), and `[2208, 2224)` our caller's `ebx`, `esi`, `edi`
and `ebp`. The arguments are reloaded from the stack for each call; `esi`
keeps `b = len mod 16` across the calls.

* The tweak `T = AES-enc(Key2, i)`: `i` is copied to the tweak, and the
  whole-block encryption with `tweak_schedule` enciphers it as one block
  with a zero tweak (`zO`), which is `AES-enc(Key2, i ⊕ 0) ⊕ 0`.
* `encrypt`: the `m = len / 16` whole blocks from `T`, which leaves the
  tweak of block `m`. If `b` is not zero, the last whole block is `CC`: its
  first `b` bytes are swapped with the `b` bytes after it (`swap`), making
  them `Cₘ` and the block `PP = Pₘ ‖ CP`, which is enciphered with the
  tweak of block `m`.
* `decrypt`: without a partial block, the `m` blocks from `T`. Otherwise
  the first `m - 1`, which leaves the tweak of block `m - 1`; the tweak of
  block `m` (that times `α`, as the whole-block functions compute it:
  `Impl.AesXts.X86.mulA`, on `ebx`) at `zO`; the last whole block
  deciphered with it (`PP`); its first `b` bytes swapped with the `b`
  after it, making them `Pₘ` and the block `CC = Cₘ ‖ CP`; and that
  deciphered with the tweak of block `m - 1`.

The calls use 52 bytes of stack: the frame of their six arguments, the
return address, and the whole-block functions' 24. Only the pointers,
`rounds` and `len` can affect timing: the branches are on `len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86Unit

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_)

/-- The offsets of the tweak and the second tweak in the scratch buffer. -/
def tO : Nat := 2176
def zO : Nat := 2192

/-- The callee-saved registers, and where they are saved in the scratch buffer. -/
def saved : List (Reg × Nat) := [(.ebx, 2208), (.esi, 2212), (.edi, 2216), (.ebp, 2220)]

/-- Saves them, with the scratch buffer in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restores them, with the scratch buffer (the stack argument 6) loaded into `eax`. -/
def restore : List Instr := .mov .eax (argOp 6) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- The block at `src + e` copied to `dst + d`, a word at a time through `r`. -/
def copy (r dst : Reg) (d : Nat) (src : Reg) (e : Nat) : List Instr :=
  [.mov r (.mem (at_ src e)), .store (at_ dst d) r, .mov r (.mem (at_ src (e + 4))), .store (at_ dst (d + 4)) r,
   .mov r (.mem (at_ src (e + 8))), .store (at_ dst (d + 8)) r, .mov r (.mem (at_ src (e + 12))),
   .store (at_ dst (d + 12)) r]

/-- `i` to the tweak (the scratch buffer in `ebp`). -/
def copyI : List Instr := .mov .ecx (argOp 3) :: copy .edx .ebp tO .ecx 0

/-- The second tweak zeroed. -/
def zeroZ : List Instr := Impl.CmacAes.X86.zero4 .ebp zO

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` from the zero tweak. -/
def tArgs : List Instr :=
  [.mov .eax (argOp 1), .mov .ecx (argOp 2), .mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 zO)),
   .mov .ebx (.reg .ebp), .alu .add .ebx (.imm (BitVec.ofNat 32 tO)), .mov .edi (.imm 1)]

def pro : List Instr :=
  ([.mov .eax (argOp 6)] : List Instr) ++ save ++ ([.mov .ebp (.reg .eax)] : List Instr) ++ copyI ++ zeroZ ++ tArgs

/-- A call of `vg_aes_xts_*(eax, ecx, edx, ebx, edi, ebp)`, its arguments
pushed last to first. -/
def xcall (f : Blocks) : Prog isa := .frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call f.name f.code) (.pop .eax 6)

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [.mov .ebp (argOp 6), .mov .eax (argOp 0), .mov .ecx (argOp 2), .mov .edx (.reg .ebp),
   .alu .add .edx (.imm (BitVec.ofNat 32 tO)), .mov .ebx (argOp 4), .mov .edi (argOp 5), .shift .shr .edi 4]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.alu .sub .edi (.imm 1)]

/-- The bytes after the whole blocks, `b = len mod 16`, in `esi`; ZF set if
there are none. -/
def split : List Instr := [.mov .esi (argOp 5), .alu .and .esi (.imm 15)]

/-- The address of the last whole block into `edx`, and `b` into `ecx`
(`data` loaded into a register first, so that the taint analysis sees the
address is public). -/
def lastAddr : List Instr :=
  [.mov .edx (argOp 5), .alu .sub .edx (.reg .esi), .mov .ecx (argOp 4), .alu .add .edx (.reg .ecx),
   .alu .sub .edx (.imm 16), .mov .ecx (.reg .esi)]

/-- One byte of the swap: the byte at `edx` swapped with the one 16 bytes
after it, and on to the next (`ecx` bytes left, ZF set when none are). -/
def swapBody : List Instr :=
  [.movzx8 .eax (at_ .edx 0), .movzx8 .ebx (at_ .edx 16), .store8 (at_ .edx 0) .bl, .store8 (at_ .edx 16) .al,
   .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- The first `ecx` bytes of the block at `edx` swapped with the `ecx` bytes
after it (`0 < ecx < 16`), one byte at a time. -/
def swap : Prog isa := .loop (.block swapBody) .ne

/-- The arguments of a call on the last whole block, from the tweak at
offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.mov .ebx (argOp 5), .alu .sub .ebx (.reg .esi), .alu .add .ebx (argOp 4), .alu .sub .ebx (.imm 16),
   .mov .ebp (argOp 6), .mov .eax (argOp 0), .mov .ecx (argOp 2), .mov .edx (.reg .ebp),
   .alu .add .edx (.imm (BitVec.ofNat 32 o)), .mov .edi (.imm 1)]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr :=
  ([.mov .ebp (argOp 6)] : List Instr) ++ copy .eax .ebp zO .ebp tO ++
    ([.mov .ebx (.reg .ebp), .alu .add .ebx (.imm (BitVec.ofNat 32 zO))] : List Instr) ++ Impl.AesXts.X86.mulA

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak (f : Blocks) : Prog isa := .seq (.block pro) (xcall f)

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal (f : Blocks) : Prog isa := .seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) (xcall f)))

def encrypt (f : Blocks) : Prog isa :=
  .seq (tweak f) (.seq (.block argsAll) (.seq (xcall f)
    (.seq (.block split) (.seq (.ite .e (.block []) (encSteal f)) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal (f : Blocks) : Prog isa :=
  .seq (.block argsHead) (.seq (xcall f)
    (.seq (.block (nextT ++ argsL zO)) (.seq (xcall f)
      (.seq (.block lastAddr) (.seq swap (.seq (.block (argsL tO)) (xcall f)))))))

def decrypt (e d : Blocks) : Prog isa :=
  .seq (tweak e) (.seq (.block split)
    (.seq (.ite .e (.seq (.block argsAll) (xcall d)) (decSteal d)) (.block restore)))

end VG.Impl.AesXts.X86Unit
