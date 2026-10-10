module

public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`, in terms of `Spec/Cbc.lean`,
for any target: `A` is the target's calling convention. The signatures fix
where the arguments are, the memory each function may access,
disjointness, and that the pointers, the number of rounds and the number of
blocks are public (see `TCB/Sig.lean`). The key schedule, the chaining
value and the data are secret.

Each reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `n` whole blocks in place, from
the chaining value in `iv`, which it replaces with the one to continue from
(`Cbc.next`): so a caller may encrypt or decrypt a message in pieces of
whole blocks, keeping `iv` between calls. Padding is the caller's.

Each takes a `scratch` buffer of working space, room for that of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`[u64; 256]`) and 128
bytes more (eight blocks, e.g. of ciphertext that decryption in place must
keep until it has decrypted the block after each). `stack` is the number of
bytes of stack below the stack pointer that an implementation's calls and
frames use (see `Sig.contract`).
-/

@[expose] public section

namespace VG.Spec.Cbc

/-- The `n` blocks of 16 bytes at `p`. -/
def blocksAt (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (List.range n).map fun i => Aes.bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16

/-- `vg_aes_cbc_encrypt(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 272])`,
and `vg_aes_cbc_decrypt` with the same signature. `rounds` is public;
`scratch` is working space. -/
def aesSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CBC encryption (§6.2) by AES with `w`, from the chaining value
at `iv`, and the chaining value with the last ciphertext block (unchanged
if `n = 0`). -/
def aesEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := encrypt ciph (Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CBC decryption (§6.2) by AES with `w`, from the chaining value
at `iv`, and the chaining value with the last ciphertext block, the last
block at `data` on entry (unchanged if `n = 0`). -/
def aesDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciphInv := aesInvWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      let cs := blocksAt m data n.toNat
      blocksAt m' data n.toNat = decrypt ciphInv (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs)
    (stack := stack)

/-- The `# Safety` items the two functions share. -/
def aesSafety : List String := [
  "`rounds` must be 10, 12 or 14.",
  "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_cbc_encrypt` on every target. -/
def aesEncryptApi : Api where
  module := "aes_cbc"
  name := "vg_aes_cbc_encrypt"
  sig := aesSig
  contracts := some fun A stack => aesEncryptContract A stack
  summary := "AES-CBC encryption (NIST SP 800-38A §6.2) of whole blocks, in place: replaces the \
    `n` 16-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` is the \
    block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so that a further \
    call continues the message. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
    schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it. No padding is added.\n\n\
    Contract: `VG.Spec.Cbc.aesEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := aesSafety

/-- `vg_aes_cbc_decrypt` on every target. -/
def aesDecryptApi : Api where
  module := "aes_cbc"
  name := "vg_aes_cbc_decrypt"
  sig := aesSig
  contracts := some fun A stack => aesDecryptContract A stack
  summary := "AES-CBC decryption (NIST SP 800-38A §6.2) of whole blocks, in place: replaces the \
    `n` 16-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` is the \
    block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry (leaving it \
    unchanged if `n = 0`), so that a further call continues the message. `CIPH⁻¹_K` is the \
    AES inverse cipher (FIPS 197 §5.3) with `rounds` rounds and the key schedule in the \
    first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it. No \
    padding is removed.\n\n\
    Contract: `VG.Spec.Cbc.aesDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := aesSafety

end VG.Spec.Cbc
