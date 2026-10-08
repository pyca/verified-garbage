import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# XTS-AES: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, in terms of
`Spec/Xts.lean`, for any target: `A` is the target's calling convention.
The signature fixes where the arguments are, the memory each function may
access, disjointness, and that the pointers, the number of rounds and the
number of blocks are public (see `TCB/Sig.lean`). The key schedule, the
tweak and the data are secret.

Each reads the AES key schedule of `Key1` that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `n` whole blocks in place, from
the tweak in `tweak` (`T ⊗ αʲ` for the first block's `j`), which it
replaces with the one to continue from (`Xts.next`): so a caller may
process a data unit in pieces of whole blocks, keeping `tweak` between
calls. Computing `T = AES-enc(Key2, i)` and ciphertext stealing are the
caller's.

Each takes CBC's `scratch` buffer (`Spec/Cbc/Contract.lean`): room for the
working space of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
(`[u64; 256]`) and 128 bytes more. `stack` is the number of bytes of stack
below the stack pointer that an implementation's calls and frames use (see
`Sig.contract`).
-/

namespace VG.Spec.Xts

/-- `vg_aes_xts_encrypt(schedule: *const [u8; 240], rounds: usize, tweak: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 272])`,
and `vg_aes_xts_decrypt` with the same signature. `rounds` is public;
`scratch` is working space. -/
def aesSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("tweak", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` of `Key1` in the
first `16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at
`data` with their XTS-AES encryption (§5.3.1 for each block) by AES with
`w`, the first with the tweak at `tweak` and each next with the tweak times
`α`, and the tweak with the one after the last block, `⊗ αⁿ` (unchanged if
`n = 0`). -/
def aesEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _tweak _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds tweak data n _scratch m m' _ =>
      let enc := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Cbc.blocksAt m' data n.toNat = crypt enc (Aes.bytesAt m tweak 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' tweak 16 = next (Aes.bytesAt m tweak 16) n.toNat)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` of `Key1` in the
first `16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at
`data` with their XTS-AES decryption (§5.4.1 for each block) by the AES
inverse cipher with `w`, the first with the tweak at `tweak` and each next
with the tweak times `α`, and the tweak with the one after the last block,
`⊗ αⁿ` (unchanged if `n = 0`). -/
def aesDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _tweak _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds tweak data n _scratch m m' _ =>
      let dec := Cbc.aesInvWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Cbc.blocksAt m' data n.toNat = crypt dec (Aes.bytesAt m tweak 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' tweak 16 = next (Aes.bytesAt m tweak 16) n.toNat)
    (stack := stack)

/-- `vg_aes_xts_encrypt` on every target. -/
def aesEncryptApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_encrypt"
  sig := aesSig
  contracts := some fun A stack => aesEncryptContract A stack
  summary := "XTS-AES encryption (IEEE Std 1619-2007 §5.3.1, NIST SP 800-38E) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `Pⱼ` at `data` with `Cⱼ = AES-enc(Key1, Pⱼ ⊕ Tⱼ) ⊕ Tⱼ`, \
    where `T₀` is the tweak at `*tweak` and `Tⱼ₊₁ = Tⱼ ⊗ α` (§5.2), and `*tweak` with `Tₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the data unit. \
    `AES-enc(Key1, ·)` is AES (FIPS 197) with `rounds` rounds and the key schedule in the first \
    `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it. The caller \
    computes the first tweak, `AES-enc(Key2, i)`, and steals ciphertext for a partial last \
    block.\n\n\
    Contract: `VG.Spec.Xts.aesEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the tweak or the data."
  safety := Cbc.aesSafety

/-- `vg_aes_xts_decrypt` on every target. -/
def aesDecryptApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_decrypt"
  sig := aesSig
  contracts := some fun A stack => aesDecryptContract A stack
  summary := "XTS-AES decryption (IEEE Std 1619-2007 §5.4.1, NIST SP 800-38E) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `Cⱼ` at `data` with `Pⱼ = AES-dec(Key1, Cⱼ ⊕ Tⱼ) ⊕ Tⱼ`, \
    where `T₀` is the tweak at `*tweak` and `Tⱼ₊₁ = Tⱼ ⊗ α` (§5.2), and `*tweak` with `Tₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the data unit. \
    `AES-dec(Key1, ·)` is the AES inverse cipher (FIPS 197 §5.3) with `rounds` rounds and the \
    key schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
    writes it. The caller computes the first tweak, `AES-enc(Key2, i)`, and steals ciphertext \
    for a partial last block.\n\n\
    Contract: `VG.Spec.Xts.aesDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule, the tweak or the data."
  safety := Cbc.aesSafety

end VG.Spec.Xts
