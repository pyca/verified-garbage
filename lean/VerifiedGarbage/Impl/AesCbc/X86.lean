module

public import VerifiedGarbage.Impl.CmacAes.X86

/-!
# AES-CBC: x86 (32-bit) implementation

`vg_aes_cbc_encrypt(schedule, rounds, iv, data, n, scratch)` and
`vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on one block at a time,
in place. They are generic over the implementation they call (`Blocks`):
each is emitted once for each implementation (e.g.
`vg_aes_cbc_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

They are built from AES-CMAC's pieces (`Impl/CmacAes/X86.lean`), whose
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
block function, `[2048, 2064)` the ciphertext block that decryption keeps
across the call, and `[2064, 2080)` our caller's registers.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each block: `Cⱼ` saved in the scratch buffer, deciphered in
  place, XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to
  the chaining value.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp setup advance restore xor4 zero4)

/-- The offset of the saved ciphertext block in the scratch buffer. -/
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

/-! ## `vg_aes_cbc_encrypt` -/

/-- `Pⱼ ⊕ Cⱼ₋₁` in place, and the arguments of the call. -/
def encPre : List Instr := ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ callArgs

/-- The block copied to the chaining value, and on to the next block. -/
def encPost : List Instr := ([.mov .ebx (argOp 2)] : List Instr) ++ zero4 .ebx 0 ++ xor4 .ebx .esi .ebx 0 0 0 ++ advance

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody (b : Blocks) : Prog isa := .seq (.block encPre) (.seq (blkCall b) (.block encPost))

def encrypt (b : Blocks) : Prog isa := whole (encBody b)

/-! ## `vg_aes_cbc_decrypt` -/

/-- `Cⱼ` saved in the scratch buffer, and the arguments of the call. -/
def decPre : List Instr := ([.mov .ebp (argOp 5)] : List Instr) ++ zero4 .ebp cOff ++ xor4 .ebp .esi .ebp cOff 0 cOff ++ callArgs

/-- `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁` in place, the saved `Cⱼ` copied to the chaining
value, and on to the next block. -/
def decPost : List Instr :=
  ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ ([.mov .ebp (argOp 5)] : List Instr) ++ zero4 .ebx 0 ++
    xor4 .ebx .ebp .ebx 0 cOff 0 ++ advance

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved `Cⱼ`
the chaining value. -/
def decBody (b : Blocks) : Prog isa := .seq (.block decPre) (.seq (blkCall b) (.block decPost))

def decrypt (b : Blocks) : Prog isa := whole (decBody b)

end VG.Impl.AesCbc.X86
