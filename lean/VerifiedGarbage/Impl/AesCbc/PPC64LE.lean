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
block function, which the POWER8 block functions do not write, and so holds
the slots of a group of decryption (`[0, 144)`, below), `[2048, 2064)`
the ciphertext block that decryption keeps
across the call, `[2064, 2112)` our caller's `r14`–`r19`, and
`[2112, 2120)` our return address (a call replaces the link register).

Both keep their arguments in `r14` (schedule), `r15` (rounds), `r16` (the
chaining value), `r17` (the next block), `r18` (blocks left) and `r19`
(scratch) across the calls, which preserve them. Blocks are moved and XORed
a 64-bit word at a time through `r9` and `r10`.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each group of eight blocks while at least eight are left
  (`decGroup`): the chaining value and the eight `Cⱼ` saved in slots 0 to 8
  of the scratch buffer, the eight deciphered in place by one call (which
  runs the block function's eight-block loop), each XORed with the slot
  before its own, and slot 8 copied to the chaining value; then each block
  left (`decBody`): `Cⱼ` saved in the scratch buffer, deciphered in place,
  XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to the
  chaining value.

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

/-! ## Groups of eight blocks -/

/-- The block at `src + e` XORed into the block at `dst + d`. -/
def xorAt (dst : Reg) (d : Nat) (src : Reg) (e : Nat) : List Instr :=
  [.load .d .r9 dst d, .load .d .r10 src e, .logic .xor .r9 .r9 .r10, .store .d .r9 dst d,
   .load .d .r9 dst (d + 8), .load .d .r10 src (e + 8), .logic .xor .r9 .r9 .r10, .store .d .r9 dst (d + 8)]

/-- Slot `j` of a group, at `16 j` in the scratch buffer. -/
def slot (j : Nat) : Nat := 16 * j

/-- Slot `0` the chaining value, and slot `j + 1` block `j` at `r17`, for
`j < m`: slot `j` is what block `j` is chained with. -/
def saveSlots (m : Nat) : List Instr :=
  copy .r19 (slot 0) .r16 0 ++ (List.range m).flatMap fun j => copy .r19 (slot (j + 1)) .r17 (16 * j)

/-- Each of the eight blocks at `r17` XORed with its slot. -/
def fixSlots : List Instr := (List.range 8).flatMap fun j => xorAt .r17 (16 * j) .r19 (slot j)

/-- The arguments of the block function for the eight blocks at `r17`. -/
def callArgs8 : List Instr := [mov .r3 .r14, mov .r4 .r15, mov .r5 .r17, .li .r6 8, mov .r7 .r19]

/-- On to the block after the eight. -/
def advance8 : List Instr := [.addi .r17 .r17 128, .subi .r18 .r18 8]

/-- How many groups of eight blocks are left, in `r9`. -/
def countG : List Instr := [.lsr .d .r9 .r18 3]

/-- `group` while at least eight blocks are left, then `one` for each block
left. -/
def groups (group one : Prog isa) : Prog isa :=
  .seq (.block countG)
    (.seq (.ite (.zero .d .r9) (.block []) (.loop (.seq group (.block countG)) (.nonzero .d .r9)))
      (.ite (.zero .d .r18) (.block []) (.loop one (.nonzero .d .r18))))

/-- The registers saved and the arguments set up, `groups group one`, and
the registers restored. -/
def batched (group one : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite (.zero .d .r18) (.block []) (groups group one)) (.block restore))

/-- Eight blocks: `Cⱼ₋₁` saved in slot `j` (the chaining value for the
first), and the last `Cⱼ` in slot 8, deciphered in place by one call, each
XORed with its slot, and slot 8 the chaining value. -/
def decGroup : Prog isa :=
  .seq (.block (saveSlots 8 ++ callArgs8))
    (.seq decCall (.block (fixSlots ++ copy .r16 0 .r19 (slot 8) ++ advance8)))

def decrypt : Prog isa := batched decGroup decBody

end VG.Impl.AesCbc.PPC64LE
