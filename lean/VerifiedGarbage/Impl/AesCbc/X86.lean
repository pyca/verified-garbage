module

public import VerifiedGarbage.Impl.CmacAes.X86

/-!
# AES-CBC: x86 (32-bit) implementation

`vg_aes_cbc_encrypt(schedule, rounds, iv, data, n, scratch)` (see
`VG.Spec.Cbc.aesEncryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time,
in place. It is generic over the implementation it calls (`Blocks`):
it is emitted once for each implementation, but with one that has a chain
(`Impl/Aes/X86/Chain.lean`) it makes no call: it keeps the
chaining value in `xmm0` for all the blocks (`encryptChain`). Decryption,
whose blocks do not depend on each other, is `Impl/AesCbc/X86/Groups.lean`,
many blocks a call, and, with AES-NI, `Impl/AesCbc/X86/Decrypt.lean`, which
makes no call.

It is built from AES-CMAC's pieces (`Impl/CmacAes/X86.lean`), whose
arguments are in the same places: `setup` saves our caller's `ebx`, `esi`,
`edi` and `ebp` in the scratch buffer and points `esi` at the first block,
`advance` moves it to the next and sets ZF once it reaches `data + 16 n`,
and `restore 5` restores the registers. Only `esi` is kept across the calls;
the other arguments are reloaded from the stack. Blocks are XORed a word at
a time with `xor4`, and copied as a zeroed block XORed with the source.

Each call pushes the five arguments of the block function (`schedule`,
`rounds`, the block, `n = 1` and the working space, last to first) in a frame
of its own, popped (into `eax`) when it returns: with the return address the
call stores, it uses the 24 bytes below `esp`. The callee preserves `ebx`,
`esi`, `edi` and `ebp`.

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function, `[2048, 2064)` where CFB8 and CTR keep a block across the
call, and `[2064, 2080)` our caller's registers. `encryptZ`
zeroes `[2048, 2080)` before it returns (`zeroSaved`), so that
of the scratch buffer only the bytes the block function writes are left
changed.

* `encryptZ`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `encryptChain`: the keys set up once, the chaining value loaded from `iv`
  into `xmm0` once and stored there once; each block is XORed into it,
  enciphered there, and stored over the block.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks Chain)
open VG.Impl.CmacAes.X86 (argOp at_ setup advance restore xor4 zero4)

/-- The offset of the block that CFB8 and CTR save in the scratch buffer. -/
def cOff : Nat := 2048

/-- The call of `b(eax, ecx, ebx, edi, ebp)`, its arguments pushed last to
first. -/
def blkCall (b : Blocks) : Prog isa :=
  .frame (.push [.ebp, .edi, .ebx, .ecx, .eax]) (.call b.name b.code) (.pop .eax 5)

/-- The arguments of the block function: the schedule and the rounds (our
stack arguments 0 and 1), the block at `esi`, `n = 1`, and the working space
(our stack argument 5). -/
def callArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .esi), .mov .edi (.imm 1), .mov .ebp (argOp 5)]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop body .ne)) (.block (restore 5)))

/-- After the registers are restored: `[2048, 2080)` of the scratch buffer,
where the modes save a block and the registers, zeroed. -/
def zeroSaved : List Instr := [.mov .ecx (argOp 5)] ++ zero4 .ecx cOff ++ zero4 .ecx (cOff + 16)

/-- `whole body`, then `zeroSaved`: of the scratch buffer, only what the
block function writes is left changed. -/
def wholeZ (body : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop body .ne)) (.block (restore 5 ++ zeroSaved)))

/-! ## `vg_aes_cbc_encrypt` -/

/-- `Pⱼ ⊕ Cⱼ₋₁` in place, and the arguments of the call. -/
def encPre : List Instr := ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ callArgs

/-- The block copied to the chaining value, and on to the next block. -/
def encPost : List Instr := ([.mov .ebx (argOp 2)] : List Instr) ++ zero4 .ebx 0 ++ xor4 .ebx .esi .ebx 0 0 0 ++ advance

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody (b : Blocks) : Prog isa := .seq (.block encPre) (.seq (blkCall b) (.block encPost))

/-- `vg_aes_cbc_encrypt` around `b`, leaving of the scratch buffer only what
`b` writes changed. -/
def encryptZ (b : Blocks) : Prog isa := wholeZ (encBody b)

/-- A mode's code around a chain (`Impl/Aes/X86/Chain.lean`): it keeps the
chaining value in a register and calls nothing. It uses no stack, and of the
scratch buffer only what the chain writes and the 16 bytes where it saves the
registers, which it zeroes. -/
def wholeChain (c : Chain) (m : Chain.Mode) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (c.mid m)) (.block (restore 5 ++ zeroSaved)))

/-- `vg_aes_cbc_encrypt` around a chain. -/
def encryptChain (c : Chain) : Prog isa := wholeChain c Chain.cbc

end VG.Impl.AesCbc.X86
