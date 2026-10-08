import VerifiedGarbage.Impl.CmacAes.Arm
import VerifiedGarbage.Impl.Aes.Arm.Blocks

/-!
# AES-CBC: 32-bit ARM implementation

`vg_aes_cbc_encrypt(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), composed of calls
of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on one
block at a time, in place.

They are built from AES-CMAC's pieces (`Impl/CmacAes/Arm.lean`), whose
arguments are in the same places: `save` saves our caller's `r4`–`r10` and
our return address `lr` in the scratch buffer, `setup` keeps the arguments in
`r4` (schedule), `r5` (rounds), `r6` (the chaining value), `r7` (the next
block), `r8` (blocks left) and `r10` (scratch) across the calls and sets Z if
there are no blocks, `advance` moves on to the next block, and `restore`
restores the registers. Blocks are XORed a word at a time with `xor4`
(through `r12` and `lr`), and copied as a zeroed block XORed with the source.

The block functions take the working space on the stack: a frame pushes it
(`push {r12, lr}`) around each call, and its pop loads `r12` back. So the
functions use 8 bytes of stack.

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function, `[2048, 2064)` the ciphertext block that decryption keeps
across the call, and `[2064, 2096)` our caller's registers.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each block: `Cⱼ` saved in the scratch buffer, deciphered in
  place, XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to
  the chaining value.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesCbc.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov save setup restore advance xor4)

/-- The offset of the saved ciphertext block in the scratch buffer. -/
def cOff : Nat := 2048

/-- `vg_aes_encrypt_blocks`, with the working space in `r12` pushed as its
stack argument. -/
def encFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_encrypt_blocks" Impl.Aes.Arm.encryptBlocks) (.pop .r12 8)

/-- `vg_aes_decrypt_blocks`, likewise. -/
def decFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_decrypt_blocks" Impl.Aes.Arm.decryptBlocks) (.pop .r12 8)

/-- The arguments of the block function for the block at `r7`: the schedule,
the rounds, the block, `n = 1`, and the working space. -/
def callArgs : List Instr := [mov .r0 .r4, mov .r1 .r5, mov .r2 .r7, .mov .r3 (.imm 1), mov .r12 .r10]

/-- The block at `b + d` zeroed, through `r12`. -/
def zero4 (b : Reg) (d : Nat) : List Instr :=
  [.mov .r12 (.imm 0), .str .r12 b d, .str .r12 b (d + 4), .str .r12 b (d + 8), .str .r12 b (d + 12)]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

/-! ## `vg_aes_cbc_encrypt` -/

/-- `Pⱼ ⊕ Cⱼ₋₁` in place, and the arguments of the call. -/
def encPre : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ callArgs

/-- The block copied to the chaining value, and on to the next block. -/
def encPost : List Instr := zero4 .r6 0 ++ xor4 .r6 .r7 .r6 0 0 0 ++ advance

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody : Prog isa := .seq (.block encPre) (.seq encFrame (.block encPost))

def encrypt : Prog isa := whole encBody

/-! ## `vg_aes_cbc_decrypt` -/

/-- `Cⱼ` saved in the scratch buffer, and the arguments of the call. -/
def decPre : List Instr := zero4 .r10 cOff ++ xor4 .r10 .r7 .r10 cOff 0 cOff ++ callArgs

/-- `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁` in place, the saved `Cⱼ` copied to the chaining
value, and on to the next block. -/
def decPost : List Instr :=
  xor4 .r7 .r6 .r7 0 0 0 ++ zero4 .r6 0 ++ xor4 .r6 .r10 .r6 0 cOff 0 ++ advance

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved `Cⱼ`
the chaining value. -/
def decBody : Prog isa := .seq (.block decPre) (.seq decFrame (.block decPost))

def decrypt : Prog isa := whole decBody

end VG.Impl.AesCbc.Arm
