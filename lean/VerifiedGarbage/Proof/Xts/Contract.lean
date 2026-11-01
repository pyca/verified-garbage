module

public import VerifiedGarbage.Spec.Xts.Contract

/-!
# XTS-AES: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` read the AES key schedule of
`Key1` that `vg_aes_expand_key` (`VG.Spec.Aes.expandKeyContract`) writes,
`16 (rounds + 1)` bytes, at the start of a 240-byte buffer, and transform
`n` whole blocks in place, from the tweak in `tweak` (`T ⊗ αʲ` for the first
block's `j`), which they replace with the one to continue from
(`Xts.next`): so a caller may process a data unit in pieces of whole
blocks, keeping `tweak` between calls. Computing `T = AES-enc(Key2, i)` and
ciphertext stealing are the caller's (`vg_aes_xts_encrypt_unit` and
`vg_aes_xts_decrypt_unit`). They take CBC's `scratch` buffer
(`Spec/Cbc/Contract.lean`): room for the working space of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`[u64; 256]`) and 128
bytes more.
-/

@[expose] public section

namespace VG.Proof.Xts

open VG.Spec VG.Spec.Xts

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

end VG.Proof.Xts
