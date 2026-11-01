module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# AES-CMAC: PPC64LE implementation

`vg_cmac_aes_subkeys(schedule = r3, rounds = r4, subkeys = r5, scratch = r6)`,
`vg_cmac_aes_update(schedule = r3, rounds = r4, state = r5, data = r6, n = r7, scratch = r8)`
and `vg_cmac_aes_finalize(key = r3, rounds = r4, state = r5, last = r6, last_len = r7, scratch = r8)`
(see `VG.Proof.Cmac.aesSubkeysContract` and the others), composed of calls of
the verified `vg_aes_encrypt_blocks` on one block in place.

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of
`vg_aes_encrypt_blocks`, `[2048, 2064)` the last block `Mₙ` of `finalize`,
and `[2064, 2120)` our caller's nonvolatile registers and our return address
(a call replaces the link register). A call (`bl`) stores nothing in memory,
so no stack is used.

* `subkeys` zeroes the first block of `subkeys` and enciphers it in place
  (`L = CIPH_K(0)`), then doubles it there (`K1`) and into the second block
  (`K2`): the block as a big-endian 128-bit integer in `r9:r10` (`ldbrx`),
  shifted left by one bit, and XORed with `0x87` masked by the bit shifted
  out (a mask from `0 − (hi >> 63)`). `r14` holds `subkeys` and `r15` the
  scratch buffer across the call.
* `update` is built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
  arguments are the same, with the chaining value at `state`: each block,
  the state becomes `C ⊕ Mᵢ` and is enciphered in place.
* `finalize` saves `r14` and the return address, and forms `Mₙ` in the
  scratch buffer: `Mₙ* ⊕ K1` for a complete block, else `Mₙ*` copied a byte
  at a time onto zeros, `0x80` after it, and XORed with `K2`. It XORs it
  into the state and enciphers the state in place, keeping only the scratch
  buffer (in `r14`) across the call.

The model has no flags: the branches are on `n`, on `last_len - 16` and on
`last_len`. Only the pointers, `rounds`, `n` and `last_len` can affect timing:
the doubling is masked.
-/

@[expose] public section

namespace VG.Impl.CmacAes.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov xorInto advance whole encCall)

/-- The offset of the last block in the scratch buffer. -/
def cOff : Nat := 2048

/-! ## `vg_cmac_aes_subkeys` -/

/-- The registers saved in the scratch buffer, and where (`r15`, the base of
the restore, last). -/
def skSaved : List (Reg × Nat) := [(.r0, 2080), (.r14, 2064), (.r15, 2072)]

/-- Saves `r14`, `r15` and the return address, keeps `subkeys` in `r14` and
the scratch buffer in `r15`, zeroes the first block of `subkeys`, and sets up
the arguments of `vg_aes_encrypt_blocks` on it. -/
def subkeysPre : List Instr :=
  .mflr .r0 :: skSaved.map (fun (r, d) => .store .d r .r6 d) ++
    [mov .r14 .r5, mov .r15 .r6, .li .r9 0, .store .d .r9 .r5 0, .store .d .r9 .r5 8, mov .r5 .r14, .li .r6 1,
     mov .r7 .r15]

/-- The block at `r14 + src`, doubled (`VG.Spec.Cmac.dbl 16`), to `r14 + dst`. -/
def dbl (src dst : Nat) : List Instr :=
  [.li .r11 src, .loadRev .d .r9 .r14 .r11, .li .r11 (src + 8), .loadRev .d .r10 .r14 .r11,
   .lsr .d .r11 .r9 63, .li .r12 0, .sub .r11 .r12 .r11, .li .r12 0x87, .logic .and .r11 .r11 .r12,
   .lsr .d .r12 .r10 63, .lsl .r9 .r9 1, .logic .or .r9 .r9 .r12,
   .lsl .r10 .r10 1, .logic .xor .r10 .r10 .r11,
   .li .r11 dst, .storeRev .d .r9 .r14 .r11, .li .r11 (dst + 8), .storeRev .d .r10 .r14 .r11]

/-- `K1` over `L`, `K2` after it, and the return address and the registers
restored. -/
def subkeysPost : List Instr :=
  dbl 0 0 ++ dbl 0 16 ++ skSaved.map (fun (r, d) => .load .d r .r15 d) ++ [.mtlr .r0]

def subkeys : Prog isa := .seq (.block subkeysPre) (.seq encCall (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

/-- The arguments of `vg_aes_encrypt_blocks` on the state: the schedule, the
rounds, the state, `n = 1`, and the working space. -/
def updArgs : List Instr := [mov .r3 .r14, mov .r4 .r15, mov .r5 .r16, .li .r6 1, mov .r7 .r19]

/-- One block: `C ⊕ Mᵢ` in the state (at `r16`; the block at `r17`),
enciphered in place. -/
def body : Prog isa := .seq (.block (xorInto .r16 .r17 ++ updArgs)) (.seq encCall (.block advance))

def update : Prog isa := whole body

/-! ## `vg_cmac_aes_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `r3 + 240`), for a complete last block. -/
def full : List Instr :=
  [.load .d .r9 .r6 0, .load .d .r10 .r3 240, .logic .xor .r9 .r9 .r10, .store .d .r9 .r8 cOff,
   .load .d .r9 .r6 8, .load .d .r10 .r3 248, .logic .xor .r9 .r9 .r10, .store .d .r9 .r8 (cOff + 8)]

/-- The last block zeroed, with `r10` pointing at it, `r11` at the last
bytes and `r12` counting them. -/
def zero : List Instr :=
  [.li .r9 0, .store .d .r9 .r8 cOff, .store .d .r9 .r8 (cOff + 8), .addi .r10 .r8 cOff, mov .r11 .r6,
   mov .r12 .r7]

/-- The `r12` (nonzero) bytes at `r11` copied to `r10`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.lbz .r9 .r11 0, .stb .r9 .r10 0, .addi .r11 .r11 1, .addi .r10 .r10 1, .subi .r12 .r12 1])
    (.nonzero .d .r12)

/-- `0x80` after the bytes (at `r10`), and the block XORed with `K2` (at
`r3 + 256`). -/
def padK2 : List Instr :=
  [.li .r9 0x80, .stb .r9 .r10 0,
   .load .d .r9 .r8 cOff, .load .d .r10 .r3 256, .logic .xor .r9 .r9 .r10, .store .d .r9 .r8 cOff,
   .load .d .r9 .r8 (cOff + 8), .load .d .r10 .r3 264, .logic .xor .r9 .r9 .r10, .store .d .r9 .r8 (cOff + 8)]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)`, for a partial last block (`last_len < 16`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite (.zero .d .r7) (.block []) copy) (.block padK2))

/-- The registers `finalize` saves in the scratch buffer, and where (`r14`,
the base of the restore, last). -/
def finSaved : List (Reg × Nat) := [(.r0, 2064), (.r14, 2072)]

/-- Saves `r14` and the return address in the scratch buffer at `r8`. -/
def finSave : List Instr := .mflr .r0 :: finSaved.map fun (r, d) => .store .d r .r8 d

/-- The state `C ⊕ Mₙ`, the scratch buffer kept in `r14`, and the arguments
of `vg_aes_encrypt_blocks` but the schedule (`r3`), the rounds (`r4`) and the
state (`r5`), which are ours. -/
def finArgs : List Instr :=
  [.load .d .r9 .r5 0, .load .d .r10 .r8 cOff, .logic .xor .r9 .r9 .r10, .store .d .r9 .r5 0,
   .load .d .r9 .r5 8, .load .d .r10 .r8 (cOff + 8), .logic .xor .r9 .r9 .r10, .store .d .r9 .r5 8,
   mov .r14 .r8, .li .r6 1, mov .r7 .r14]

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block (finSave ++ [.subi .r9 .r7 16]))
    (.seq (.ite (.zero .d .r9) (.block full) partialBlock) (.block finArgs))

def finalize : Prog isa :=
  .seq finPre (.seq encCall (.block (finSaved.map (fun (r, d) => .load .d r .r14 d) ++ [.mtlr .r0])))

end VG.Impl.CmacAes.PPC64LE
