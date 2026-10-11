import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Spec.Cfb

/-!
# SEED-CFB128: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 128-bit segments, the block
size (NIST SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher),
with SEED's encryption (RFC 4269 §2, `Spec/Seed.lean`; `cipher`,
`Spec/Seed/Cbc.lean`) as `CIPH_K`, in both directions, under the 128-byte
schedule that `vg_seed_expand_key` writes.

`vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt` transform `n` whole
blocks in place, from the block in `iv`, which they replace with the one to
continue from, the last ciphertext block (`Cbc.next`): a caller may encrypt or
decrypt a message in pieces of whole blocks, keeping `iv` between calls. A
partial last segment is the caller's.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

namespace VG.Spec.Seed

/-- `vg_seed_cfb128_encrypt(schedule: *const [u8; 128], iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_seed_cfb128_decrypt` with the same signature. -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB128 encryption (§6.3) by SEED, from the block at `iv`, and that
block with the last ciphertext block (unchanged if `n = 0`). -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat)
      Cbc.blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB128 decryption (§6.3) by SEED, from the block at `iv`, and that
block with the last ciphertext block, the last block at `data` on entry
(unchanged if `n = 0`). -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.blocksAt m data n.toNat
      Cbc.blocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_seed_cfb128_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "seed_cfb"
  name := "vg_seed_cfb128_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "SEED-CFB128 encryption (NIST SP 800-38A §6.3, with 128-bit segments; RFC 4269 §2) of \
    whole blocks, in place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is SEED \
    encryption under the schedule written by `vg_seed_expand_key`.\n\n\
    Contract: `VG.Spec.Seed.cfbEncryptContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_seed_cfb128_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "seed_cfb"
  name := "vg_seed_cfb128_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "SEED-CFB128 decryption (NIST SP 800-38A §6.3, with 128-bit segments; RFC 4269 §2) of \
    whole blocks, in place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is SEED encryption (also for decryption) under the \
    schedule written by `vg_seed_expand_key`.\n\n\
    Contract: `VG.Spec.Seed.cfbDecryptContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Seed
