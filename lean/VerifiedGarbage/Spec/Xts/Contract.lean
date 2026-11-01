module

public import VerifiedGarbage.Spec.Xts
public import VerifiedGarbage.Spec.Cbc.Contract

/-!
# XTS-AES: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`, in terms of
`Spec/Xts.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers, the number of rounds and the
number of bytes are public (see `TCB/Sig.lean`). The key schedules, the
tweak value and the data are secret.

Each transforms a whole data unit of any length from 16 bytes to 2²⁰
blocks in place, from the AES key schedules of `Key1` and `Key2` that
`vg_aes_expand_key` (`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds +
1)` bytes, each at the start of a 240-byte buffer, and the tweak value `i`,
as `Xts.aesXtsEncrypt` and `Xts.aesXtsDecrypt` do (§5.3.2, §5.4.2, with
ciphertext stealing for a partial last block).

They take room for the working space of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` and CBC's 128 bytes more (`[u64; 272]`), and 256
bytes more (e.g. for the tweaks, a block and saved registers). `stack` is
the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (see `Sig.contract`).
-/

@[expose] public section

namespace VG.Spec.Xts

/-! ## Whole data units -/

/-- The most blocks a data unit may have: 2²⁰, the limit NIST SP 800-38E
sets on the length of a data unit (see also IEEE Std 1619-2007 §5.1), as
the Rust caller's `MAX_BLOCKS`. -/
def maxBlocks : Nat := 2 ^ 20

/-- The key schedules at `schedule` and `tweakSchedule` are those of the
two halves of the XTS-AES key `key = Key1 ‖ Key2` (32, 48 or 64 bytes,
§5.1) with `Nr = rounds` rounds: `16 (rounds + 1)` bytes each, of `Key1`
at `schedule` and of `Key2` at `tweakSchedule`, as `vg_aes_expand_key`
writes them. -/
def KeySchedules (mem : Mem) (schedule tweakSchedule : Addr) (rounds : Nat)
    (key : List Byte) : Prop :=
  let k1 := key.take (key.length / 2)
  let k2 := key.drop (key.length / 2)
  (key.length = 32 ∨ key.length = 48 ∨ key.length = 64) ∧ rounds = Aes.rounds (k1.length / 4) ∧
    Aes.bytesAt mem schedule (16 * (rounds + 1)) = Aes.expandKey k1 ∧
    Aes.bytesAt mem tweakSchedule (16 * (rounds + 1)) = Aes.expandKey k2

/-- `vg_aes_xts_encrypt_unit(schedule: *const [u8; 240], tweak_schedule: *const [u8; 240], rounds: usize, i: *const [u8; 16], data: *mut u8, len: usize, scratch: *mut [u64; 304])`,
and `vg_aes_xts_decrypt_unit` with the same signature. `rounds` is public;
`scratch` is working space. -/
def aesUnitSig : Sig where
  params := [("schedule", .array false .u8 240), ("tweak_schedule", .array false .u8 240),
    ("rounds", .int .usize true), ("i", .array false .u8 16), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 304)]

/-- The data-unit functions' precondition: `rounds` of 10, 12 or 14, and a
data unit of at least 16 bytes (§5.1) and at most `maxBlocks` blocks. -/
def aesUnitPre (pb : Nat) : Curry (aesUnitSig.words pb) (Mem → Prop) :=
  fun _schedule _tweakSchedule rounds _i _data len _scratch _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      16 ≤ len.toNat ∧ len.toNat ≤ 16 * maxBlocks

/-- If the key schedules at `schedule` and `tweak_schedule` are those of an
XTS-AES key `key` with `Nr = rounds` rounds: replaces the data unit of `len`
bytes at `data` with its XTS-AES encryption under `key` with the tweak value
at `i` (§5.3.2, `aesXtsEncrypt`). -/
def aesEncryptUnitPost (pb : Nat) : aesUnitSig.Post pb :=
  fun schedule tweakSchedule rounds i data len _scratch m m' _ =>
    ∀ key, KeySchedules m schedule tweakSchedule rounds.toNat key →
      aesXtsEncrypt key (Aes.bytesAt m i 16) (Aes.bytesAt m data len.toNat) =
        some (Aes.bytesAt m' data len.toNat)

/-- If the key schedules at `schedule` and `tweak_schedule` are those of an
XTS-AES key `key` with `Nr = rounds` rounds: replaces the data unit of `len`
bytes at `data` with its XTS-AES decryption under `key` with the tweak value
at `i` (§5.4.2, `aesXtsDecrypt`). -/
def aesDecryptUnitPost (pb : Nat) : aesUnitSig.Post pb :=
  fun schedule tweakSchedule rounds i data len _scratch m m' _ =>
    ∀ key, KeySchedules m schedule tweakSchedule rounds.toNat key →
      aesXtsDecrypt key (Aes.bytesAt m i 16) (Aes.bytesAt m data len.toNat) =
        some (Aes.bytesAt m' data len.toNat)

/-- `aesUnitPre` and `aesEncryptUnitPost`. The key schedules, the tweak
value and the data are secret. -/
def aesEncryptUnitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUnitSig.contract A (pre := aesUnitPre A.ptrBits) (post := aesEncryptUnitPost A.ptrBits)
    (stack := stack)

/-- `aesUnitPre` and `aesDecryptUnitPost`. The key schedules, the tweak
value and the data are secret. -/
def aesDecryptUnitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUnitSig.contract A (pre := aesUnitPre A.ptrBits) (post := aesDecryptUnitPost A.ptrBits)
    (stack := stack)

/-- The `# Safety` items the two data-unit functions share. -/
def aesUnitSafety : List String := [
  "`rounds` must be 10, 12 or 14.",
  "`len` must be at least 16 and at most `16 << 20` (2²⁰ blocks).",
  "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_xts_encrypt_unit` on every target. -/
def aesEncryptUnitApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_encrypt_unit"
  sig := aesUnitSig
  contracts := some fun A stack => aesEncryptUnitContract A stack
  summary := "XTS-AES encryption (IEEE Std 1619-2007 §5.3.2, NIST SP 800-38E) of a whole data \
    unit, in place: replaces the `len` bytes at `data`, at least 16 and at most 2²⁰ blocks, \
    with their encryption under the key `Key1 ‖ Key2` with the tweak value `*i`. With `m` \
    whole blocks `P₀ … Pₘ₋₁` and `b` bytes `Pₘ` after them, each `Pⱼ` for `j < m` (`j < m - 1` \
    if `b > 0`) becomes `Cⱼ = AES-enc(Key1, Pⱼ ⊕ Tⱼ) ⊕ Tⱼ`, where `Tⱼ = T ⊗ αʲ` (§5.2) and \
    `T = AES-enc(Key2, i)`. If `b > 0`, ciphertext stealing makes `Cₘ` the first `b` bytes of \
    `CC`, the encryption of `Pₘ₋₁` with `Tₘ₋₁`, and `Cₘ₋₁` the encryption with `Tₘ` of `Pₘ` \
    followed by the other `16 - b` bytes of `CC`. `AES-enc(Key1, ·)` and `AES-enc(Key2, ·)` are AES \
    (FIPS 197) with `rounds` rounds and the key schedules in the first `16 * (rounds + 1)` \
    bytes of `*schedule` and `*tweak_schedule`, as `vg_aes_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Xts.aesEncryptUnitContract`. Constant time: only the pointers, \
    `rounds` and `len` may affect timing, not the key schedules, the tweak value or the data."
  safety := aesUnitSafety

/-- `vg_aes_xts_decrypt_unit` on every target. -/
def aesDecryptUnitApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_decrypt_unit"
  sig := aesUnitSig
  contracts := some fun A stack => aesDecryptUnitContract A stack
  summary := "XTS-AES decryption (IEEE Std 1619-2007 §5.4.2, NIST SP 800-38E) of a whole data \
    unit, in place: replaces the `len` bytes at `data`, at least 16 and at most 2²⁰ blocks, \
    with their decryption under the key `Key1 ‖ Key2` with the tweak value `*i`. With `m` \
    whole blocks `C₀ … Cₘ₋₁` and `b` bytes `Cₘ` after them, each `Cⱼ` for `j < m` (`j < m - 1` \
    if `b > 0`) becomes `Pⱼ = AES-dec(Key1, Cⱼ ⊕ Tⱼ) ⊕ Tⱼ`, where `Tⱼ = T ⊗ αʲ` (§5.2) and \
    `T = AES-enc(Key2, i)`. If `b > 0`, ciphertext stealing makes `Pₘ` the first `b` bytes of \
    `PP`, the decryption of `Cₘ₋₁` with `Tₘ`, and `Pₘ₋₁` the decryption with `Tₘ₋₁` of `Cₘ` \
    followed by the other `16 - b` bytes of `PP`. `AES-dec(Key1, ·)` is the AES inverse cipher (FIPS \
    197 §5.3) and `AES-enc(Key2, ·)` AES, with `rounds` rounds and the key schedules in the \
    first `16 * (rounds + 1)` bytes of `*schedule` and `*tweak_schedule`, as \
    `vg_aes_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Xts.aesDecryptUnitContract`. Constant time: only the pointers, \
    `rounds` and `len` may affect timing, not the key schedules, the tweak value or the data."
  safety := aesUnitSafety

end VG.Spec.Xts
