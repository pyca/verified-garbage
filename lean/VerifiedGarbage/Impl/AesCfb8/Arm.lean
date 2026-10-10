import VerifiedGarbage.Impl.AesCbc.Arm

/-!
# AES-CFB8: 32-bit ARM implementation

`vg_aes_cfb8_encrypt(schedule = r0, rounds = r1, iv = r2, data = r3, len = [sp], scratch = [sp + 4])`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time.

They are built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose
arguments are in the same places, with `len` counting bytes: the registers
saved in the scratch buffer and the arguments kept in `r4` (schedule), `r5`
(rounds), `r6` (the input block), `r7` (the next byte), `r8` (bytes left)
and `r10` (scratch), and each call in a frame that pushes the working space.
Each byte, the input block is copied to the scratch buffer (at `cOff`,
zeroed and XORed with it) and enciphered there, its first byte is XORed into
the data byte, and the input block is shifted left by a byte (four
unaligned words), with the ciphertext byte (the output when encrypting, the
input when decrypting, in `r12`) shifted in.

Only the pointers, `rounds` and `len` can affect timing: the only branches
are on `len`.
-/

namespace VG.Impl.AesCfb8.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Impl.AesCbc.Arm (cOff whole encFrame zero4)

/-- The input block copied to `r10 + cOff`, and the arguments of the block
function for it: the schedule, the rounds, the block, `n = 1`, and the
working space. -/
def pre : List Instr :=
  zero4 .r10 cOff ++ xor4 .r10 .r6 .r10 cOff 0 cOff ++
  [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r10 (.imm 2048), .mov .r3 (.imm 1), mov .r12 .r10]

/-- The input block at `r6` shifted left by a byte, with the low byte of
`r12` shifted in: the words at `r6 + 1`, `+ 5`, `+ 9` and `+ 12` stored at
`r6`, `+ 4`, `+ 8` and `+ 11`. -/
def shift : List Instr :=
  [.ldr .r0 .r6 1, .ldr .r1 .r6 5, .ldr .r2 .r6 9, .ldr .r3 .r6 12, .str .r0 .r6 0, .str .r1 .r6 4,
   .str .r2 .r6 8, .str .r3 .r6 11, .strb .r12 .r6 15]

/-- On to the next byte (Z is set when none are left). -/
def advance : List Instr := [.dp .add .r7 .r7 (.imm 1), .subs .r8 .r8 (.imm 1)]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  ([.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .r12 .r12 (.reg .lr), .strb .r12 .r7 0] : List Instr) ++ shift ++ advance

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  ([.ldrb .r12 .r7 0, .ldrb .lr .r10 cOff, .dp .eor .lr .lr (.reg .r12), .strb .lr .r7 0] : List Instr) ++ shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block pre) (.seq encFrame (.block post))

def encrypt : Prog isa := whole (body encPost)

def decrypt : Prog isa := whole (body decPost)

end VG.Impl.AesCfb8.Arm
