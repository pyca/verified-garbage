module

public import VerifiedGarbage.Impl.AesXts.X86_64

/-!
# XTS-AES of whole data units: x86-64 implementation

`vg_aes_xts_encrypt_unit(schedule = rdi, tweak_schedule = rsi, rounds = rdx, i = rcx, data = r8, len = r9, scratch = [rsp + 8])`
and `vg_aes_xts_decrypt_unit` with the same arguments (see
`VG.Spec.Xts.aesEncryptUnitContract` and `aesDecryptUnitContract`),
composed of calls of the verified whole-block functions `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt`. They are generic over the implementation they
call (`Xts`, a pair of whole-block functions): each is emitted once for each
(e.g. `vg_aes_xts_encrypt_unit_vaes_vpclmul` calls
`vg_aes_xts_encrypt_vaes_vpclmul`).

The scratch buffer (2432 bytes): `[0, 2176)` is the working space of the
whole-block functions, `[2176, 2192)` the tweak (`tO`), `[2192, 2208)` a
second tweak (`zO`), and `[2208, 2256)` our caller's callee-saved registers.
`rbx` holds `schedule`, `rbp` `rounds`, `r12` `data`, `r13` `len` and `r15`
the scratch buffer across the calls.

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
  `Impl.AesXts.X86_64.mulA`) at `zO`; the last whole block deciphered with
  it (`PP`); its first `b` bytes swapped with the `b` after it, making them
  `Pₘ` and the block `CC = Cₘ ‖ CP`; and that deciphered with the tweak of
  block `m - 1`.

Only the pointers, `rounds` and `len` can affect timing: the branches are on
`len`.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64Unit

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)

/-- An implementation of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` to
call: their symbols and code. -/
structure Xts where
  enc : Blocks
  dec : Blocks

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The offsets of the tweak, the second tweak and the saved registers in
the scratch buffer. -/
def tO : Nat := 2176
def zO : Nat := 2192

def saved : List (Reg × Nat) :=
  [(.rbx, 2208), (.rbp, 2216), (.r12, 2224), (.r13, 2232), (.r14, 2240), (.r15, 2248)]

/-- The scratch buffer (the stack argument) into `rax`. -/
def ldS : List Instr := [.mov .rax (.mem (at_ .rsp 8))]

/-- The registers saved in the scratch buffer. -/
def save : List Instr := saved.map fun p => .store { base := .rax, disp := p.2 } p.1

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun p => .mov p.1 (.mem { base := .r15, disp := p.2 })

/-- The arguments to the registers kept across the calls. -/
def setup : List Instr :=
  [.mov .r15 (.reg .rax), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r12 (.reg .r8),
   .mov .r13 (.reg .r9)]

/-- The second tweak zeroed. -/
def zeroZ : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .r15 zO) .rax, .store (at_ .r15 (zO + 8)) .rax]

/-- The arguments of the whole-block encryption of the tweak with
`tweak_schedule` (in `rsi`) from the zero tweak. -/
def tArgs : List Instr :=
  [.mov .rdi (.reg .rsi), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm (BitVec.ofNat 32 zO)),
   .mov .rcx (.reg .r15), .alu .add .rcx (.imm (BitVec.ofNat 32 tO)), .mov32 .r8 (.imm 1), .mov .r9 (.reg .r15)]

/-- `i` copied to the tweak, the second tweak zeroed, and the arguments of
the call enciphering the tweak. -/
def tweakIn : List Instr := Impl.AesCbc.X86_64.copy .r15 tO .rcx 0 ++ zeroZ ++ tArgs

def pro : List Instr := save ++ setup ++ tweakIn

/-- The arguments of a call on the whole blocks, `len / 16` of them, from
the tweak. -/
def argsAll : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm (BitVec.ofNat 32 tO)),
   .mov .rcx (.reg .r12), .mov .r8 (.reg .r13), .shift .shr .r8 4, .mov .r9 (.reg .r15)]

/-- The arguments of a call on all but the last whole block. -/
def argsHead : List Instr := argsAll ++ [.alu .sub .r8 (.imm 1)]

/-- The bytes of the whole blocks, `16 (len / 16)`, in `rax`, and the bytes
after them, `b = len mod 16`, in `r8`; ZF is set if there are none. -/
def split : List Instr :=
  [.mov .rax (.reg .r13), .shift .shr .rax 4, .shift .shl .rax 4, .mov .r8 (.reg .r13), .alu .sub .r8 (.reg .rax)]

/-- The address of the last whole block into `rdx`. -/
def lastAddr : List Instr := [.mov .rdx (.reg .r12), .alu .add .rdx (.reg .rax), .alu .sub .rdx (.imm 16)]

/-- The swap's registers: the last whole block in `rdx`, the bytes after it
in `r8` (from `split`) and the index in `rcx`. -/
def stealPre : List Instr := lastAddr ++ [.mov32 .rcx (.imm 0)]

def lo : MemOp := { base := .rdx, index := some .rcx }
def hi : MemOp := { base := .rdx, index := some .rcx, disp := 16 }

/-- The first `r8` bytes of the block at `rdx` swapped with the `r8` bytes
after it (`0 < r8 < 16`), one byte at a time. -/
def swapBody : List Instr :=
  [.movzx8 .rax lo, .movzx8 .r9 hi, .store8 lo .r9, .store8 hi .rax, .alu .add .rcx (.imm 1),
   .alu .cmp .rcx (.reg .r8)]

def swap : Prog isa := .loop (.block swapBody) .ne

/-- The arguments of a call on the block at `rdx`, from the tweak at
offset `o` of the scratch buffer. -/
def argsL (o : Nat) : List Instr :=
  [.mov .rcx (.reg .rdx), .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
   .alu .add .rdx (.imm (BitVec.ofNat 32 o)), .mov32 .r8 (.imm 1), .mov .r9 (.reg .r15)]

/-- The tweak times `α`, at `zO`. -/
def nextT : List Instr :=
  [.mov .rax (.mem (at_ .r15 tO)), .mov .rcx (.mem (at_ .r15 (tO + 8)))] ++ Impl.AesXts.X86_64.mulA ++
  [.store (at_ .r15 zO) .rax, .store (at_ .r15 (zO + 8)) .rcx]

/-- The tweak, `T = AES-enc(Key2, i)`. -/
def tweak (f : Blocks) : Prog isa := .seq (.block ldS) (.seq (.block pro) (.call f.name f.code))

/-- The steal for encryption: `Cₘ` and `PP`, and `PP` enciphered. -/
def encSteal (f : Blocks) : Prog isa :=
  .seq (.block stealPre) (.seq swap (.seq (.block (argsL tO)) (.call f.name f.code)))

def encrypt (x : Xts) : Prog isa :=
  .seq (tweak x.enc) (.seq (.block argsAll) (.seq (.call x.enc.name x.enc.code)
    (.seq (.block split) (.seq (.ite .e (.block []) (encSteal x.enc)) (.block restore)))))

/-- The decryption of a data unit with a partial block, after the tweak. -/
def decSteal (f : Blocks) : Prog isa :=
  .seq (.block argsHead) (.seq (.call f.name f.code)
    (.seq (.block (nextT ++ split ++ lastAddr ++ argsL zO)) (.seq (.call f.name f.code)
      (.seq (.block (split ++ stealPre)) (.seq swap (.seq (.block (argsL tO)) (.call f.name f.code)))))))

def decrypt (x : Xts) : Prog isa :=
  .seq (tweak x.enc) (.seq (.block split)
    (.seq (.ite .e (.seq (.block argsAll) (.call x.dec.name x.dec.code)) (decSteal x.dec)) (.block restore)))

end VG.Impl.AesXts.X86_64Unit
