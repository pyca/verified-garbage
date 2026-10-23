module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# AES-CFB8: PPC64LE implementation

`vg_aes_cfb8_encrypt(schedule = r3, rounds = r4, iv = r5, data = r6, len = r7, scratch = r8)`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time, as on
x86-64 (`VG.Impl.AesCfb8.X86_64`).

They are built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
arguments are the same but for `len` counting bytes: the registers and the
return address saved in the scratch buffer and the arguments kept in `r14`
(schedule), `r15` (rounds), `r16` (the input block), `r17` (the next byte),
`r18` (bytes left) and `r19` (scratch). Each byte, the input block is
copied to the scratch buffer (at `cOff`) and enciphered there, its first
byte is XORed into the data byte, and the input block is shifted left by a
byte, with the ciphertext byte (the output when encrypting, the input when
decrypting, in `r9`) shifted in: as on AArch64, each of its two words
becomes its upper seven bytes with the next byte above them (`ld` and `std`
take displacements that are multiples of 4, so the words are not loaded
unaligned).

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov cOff copy whole encCall)

/-- The input block copied to `r19 + cOff`, and the arguments of the block
function for it: the schedule, the rounds, the block, `n = 1`, and the
working space. -/
def pre : List Instr :=
  copy .r19 cOff .r16 0 ++
  ([mov .r3 .r14, mov .r4 .r15, .addi .r5 .r19 cOff, .li .r6 1, mov .r7 .r19] : List Instr)

/-- The input block at `r16` shifted left by a byte, with `r9` (a byte)
shifted in. -/
def shift : List Instr :=
  [.load .d .r10 .r16 0, .load .d .r11 .r16 8, .lsr .d .r10 .r10 8, .lsl .r12 .r11 56,
   .logic .or .r10 .r10 .r12, .lsr .d .r11 .r11 8, .lsl .r12 .r9 56, .logic .or .r11 .r11 .r12,
   .store .d .r10 .r16 0, .store .d .r11 .r16 8]

/-- On to the next byte. -/
def advance : List Instr := [.addi .r17 .r17 1, .subi .r18 .r18 1]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  ([.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r9 .r9 .r10, .stb .r9 .r17 0] : List Instr) ++
    shift ++ advance

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  ([.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r10 .r10 .r9, .stb .r10 .r17 0] : List Instr) ++
    shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block pre) (.seq encCall (.block post))

def encrypt : Prog isa := whole (body encPost)

def decrypt : Prog isa := whole (body decPost)

end VG.Impl.AesCfb8.PPC64LE
