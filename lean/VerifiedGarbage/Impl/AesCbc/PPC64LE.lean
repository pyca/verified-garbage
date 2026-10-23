module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Blocks

/-!
# AES-CBC: PPC64LE implementation

`vg_aes_cbc_encrypt(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch = r8)`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), composed of calls
of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on one
block at a time, in place, as on x86-64 (`VG.Impl.AesCbc.X86_64`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function, `[2048, 2064)` the ciphertext block that decryption keeps
across the call, `[2064, 2112)` our caller's `r14`–`r19`, and
`[2112, 2120)` our return address (a call replaces the link register).

Both keep their arguments in `r14` (schedule), `r15` (rounds), `r16` (the
chaining value), `r17` (the next block), `r18` (blocks left) and `r19`
(scratch) across the calls, which preserve them. Blocks are moved and XORed
a 64-bit word at a time through `r9` and `r10`.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each block: `Cⱼ` saved in the scratch buffer, deciphered in
  place, XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to
  the chaining value.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-- The offset of the saved ciphertext block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The offset of the saved return address in the scratch buffer. -/
def lrOff : Nat := 2112

def saved : List (Reg × Nat) :=
  [(.r14, 2064), (.r15, 2072), (.r16, 2080), (.r17, 2088), (.r18, 2096), (.r19, 2104)]

/-- Saves the registers and the return address in the scratch buffer at `r8`. -/
def save : List Instr :=
  .mflr .r0 :: .store .d .r0 .r8 lrOff :: saved.map fun (r, d) => .store .d r .r8 d

/-- The arguments to their registers. -/
def setup : List Instr :=
  [mov .r14 .r3, mov .r15 .r4, mov .r16 .r5, mov .r17 .r6, mov .r18 .r7, mov .r19 .r8]

/-- Restores the return address and the registers, with `r19` (restored
last) the scratch buffer. -/
def restore : List Instr :=
  .load .d .r0 .r19 lrOff :: saved.map (fun (r, d) => .load .d r .r19 d) ++ [.mtlr .r0]

/-- The arguments of the block function for the block at `r17`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def callArgs : List Instr := [mov .r3 .r14, mov .r4 .r15, mov .r5 .r17, .li .r6 1, mov .r7 .r19]

/-- The block at `dst` XORed with the block at `src`, in place. -/
def xorInto (dst src : Reg) : List Instr :=
  [.load .d .r9 dst 0, .load .d .r10 src 0, .logic .xor .r9 .r9 .r10, .store .d .r9 dst 0,
   .load .d .r9 dst 8, .load .d .r10 src 8, .logic .xor .r9 .r9 .r10, .store .d .r9 dst 8]

/-- The block at `src + s` copied to `dst + d`. -/
def copy (dst : Reg) (d : Nat) (src : Reg) (s : Nat) : List Instr :=
  [.load .d .r9 src s, .store .d .r9 dst d, .load .d .r9 src (s + 8), .store .d .r9 dst (d + 8)]

/-- On to the next block. -/
def advance : List Instr := [.addi .r17 .r17 16, .subi .r18 .r18 1]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .d .r18) (.block []) (.loop body (.nonzero .d .r18))) (.block restore))

/-- A call of `vg_aes_encrypt_blocks`. -/
def encCall : Prog isa := .call "vg_aes_encrypt_blocks" Impl.Aes.PPC64LE.encryptBlocks

/-- A call of `vg_aes_decrypt_blocks`. -/
def decCall : Prog isa := .call "vg_aes_decrypt_blocks" Impl.Aes.PPC64LE.decryptBlocks

/-! ## `vg_aes_cbc_encrypt` -/

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody : Prog isa :=
  .seq (.block (xorInto .r17 .r16 ++ callArgs))
    (.seq encCall (.block (copy .r16 0 .r17 0 ++ advance)))

def encrypt : Prog isa := whole encBody

/-! ## `vg_aes_cbc_decrypt` -/

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved
`Cⱼ` the chaining value. -/
def decBody : Prog isa :=
  .seq (.block (copy .r19 cOff .r17 0 ++ callArgs))
    (.seq decCall (.block (xorInto .r17 .r16 ++ copy .r16 0 .r19 cOff ++ advance)))

def decrypt : Prog isa := whole decBody

end VG.Impl.AesCbc.PPC64LE
