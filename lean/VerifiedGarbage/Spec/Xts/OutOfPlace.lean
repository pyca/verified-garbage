module

public import VerifiedGarbage.Spec.Xts.Contract

/-!
# XTS-AES of whole data units, out of place

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_xts_encrypt_unit_to` and `vg_aes_xts_decrypt_unit_to`: the data-unit
functions of `Spec/Xts/Contract.lean` (`aesEncryptUnitContract`,
`aesDecryptUnitContract`) that read the data unit from one buffer, `src`,
and write its encryption or decryption to another, `dst`, so that a caller
whose input and output are separate buffers need not first copy the input
to the output to transform it in place.

The output and the input are different buffers: the signatures make `dst`
overlap no other buffer (`Sig.contract`), so it never overlaps `src`, not
even as the same buffer; a caller transforming a data unit in place calls
the functions of `Spec/Xts/Contract.lean`. The output has its own length
argument, `dst_len`, which the precondition requires to be the length of
the input, `len`. The other arguments, the key schedules, the tweak value,
what is public and what is secret, and the working space are those of the
in-place functions. Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Xts

/-- `vg_aes_xts_encrypt_unit_to(schedule: *const [u8; 240], tweak_schedule: *const [u8; 240], rounds: usize, i: *const [u8; 16], src: *const u8, len: usize, dst: *mut u8, dst_len: usize, scratch: *mut [u64; 304])`,
and `vg_aes_xts_decrypt_unit_to` with the same signature: `aesUnitSig` with
the data read from `src` and written to `dst`. `rounds` is public; `scratch`
is working space. -/
def aesUnitToSig : Sig where
  params := [("schedule", .array false .u8 240), ("tweak_schedule", .array false .u8 240),
    ("rounds", .int .usize true), ("i", .array false .u8 16), ("src", .slice false .u8 "len"),
    ("dst", .slice true .u8 "dst_len"), ("scratch", .array true .u64 304)]

/-- The out-of-place data-unit functions' precondition: `aesUnitPre`'s
(`rounds` of 10, 12 or 14, and a data unit of at least 16 bytes and at most
`maxBlocks` blocks), and an output as long as the input. -/
def aesUnitToPre (pb : Nat) : Curry (aesUnitToSig.words pb) (Mem → Prop) :=
  fun _schedule _tweakSchedule rounds _i _src len _dst dstLen _scratch _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      16 ≤ len.toNat ∧ len.toNat ≤ 16 * maxBlocks ∧ dstLen.toNat = len.toNat

/-- If the key schedules at `schedule` and `tweak_schedule` are those of an
XTS-AES key `key` with `Nr = rounds` rounds: the `len` bytes at `dst` are the
XTS-AES encryption under `key`, with the tweak value at `i`, of the data
unit of `len` bytes at `src` (§5.3.2, `aesXtsEncrypt`). (`aesEncryptUnitPost`,
with the data unit read from `src` and written to `dst`.) -/
def aesEncryptUnitToPost (pb : Nat) : aesUnitToSig.Post pb :=
  fun schedule tweakSchedule rounds i src len dst _dstLen _scratch m m' _ =>
    ∀ key, KeySchedules m schedule tweakSchedule rounds.toNat key →
      aesXtsEncrypt key (Aes.bytesAt m i 16) (Aes.bytesAt m src len.toNat) =
        some (Aes.bytesAt m' dst len.toNat)

/-- If the key schedules at `schedule` and `tweak_schedule` are those of an
XTS-AES key `key` with `Nr = rounds` rounds: the `len` bytes at `dst` are the
XTS-AES decryption under `key`, with the tweak value at `i`, of the data
unit of `len` bytes at `src` (§5.4.2, `aesXtsDecrypt`). (`aesDecryptUnitPost`,
with the data unit read from `src` and written to `dst`.) -/
def aesDecryptUnitToPost (pb : Nat) : aesUnitToSig.Post pb :=
  fun schedule tweakSchedule rounds i src len dst _dstLen _scratch m m' _ =>
    ∀ key, KeySchedules m schedule tweakSchedule rounds.toNat key →
      aesXtsDecrypt key (Aes.bytesAt m i 16) (Aes.bytesAt m src len.toNat) =
        some (Aes.bytesAt m' dst len.toNat)

/-- `aesUnitToPre` and `aesEncryptUnitToPost`. The key schedules, the tweak
value and the data are secret. -/
def aesEncryptUnitToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUnitToSig.contract A (pre := aesUnitToPre A.ptrBits) (post := aesEncryptUnitToPost A.ptrBits)
    (stack := stack)

/-- `aesUnitToPre` and `aesDecryptUnitToPost`. The key schedules, the tweak
value and the data are secret. -/
def aesDecryptUnitToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUnitToSig.contract A (pre := aesUnitToPre A.ptrBits) (post := aesDecryptUnitToPost A.ptrBits)
    (stack := stack)

/-- The `# Safety` items the two out-of-place data-unit functions share. -/
def aesUnitToSafety : List String := [
  "`rounds` must be 10, 12 or 14.",
  "`len` must be at least 16 and at most `16 << 20` (2²⁰ blocks).",
  "`dst_len` must equal `len`.",
  "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_xts_encrypt_unit_to` on every target. -/
def aesEncryptUnitToApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_encrypt_unit_to"
  sig := aesUnitToSig
  contracts := some fun A stack => aesEncryptUnitToContract A stack
  summary := "XTS-AES encryption (IEEE Std 1619-2007 §5.3.2, NIST SP 800-38E) of a whole data \
    unit, out of place: writes to the `dst_len = len` bytes at `dst` the encryption of the \
    `len` bytes at `src`, at least 16 and at most 2²⁰ blocks, under the key `Key1 ‖ Key2` \
    with the tweak value `*i`, as `vg_aes_xts_encrypt_unit` would replace them with in \
    place (see `vg_aes_xts_encrypt_unit`). `src` is not written, and `dst` is a buffer of \
    its own: it overlaps no other buffer, `src` included.\n\n\
    Contract: `VG.Spec.Xts.aesEncryptUnitToContract`. Constant time: only the pointers, \
    `rounds`, `len` and `dst_len` may affect timing, not the key schedules, the tweak value \
    or the data."
  safety := aesUnitToSafety

/-- `vg_aes_xts_decrypt_unit_to` on every target. -/
def aesDecryptUnitToApi : Api where
  module := "aes_xts"
  name := "vg_aes_xts_decrypt_unit_to"
  sig := aesUnitToSig
  contracts := some fun A stack => aesDecryptUnitToContract A stack
  summary := "XTS-AES decryption (IEEE Std 1619-2007 §5.4.2, NIST SP 800-38E) of a whole data \
    unit, out of place: writes to the `dst_len = len` bytes at `dst` the decryption of the \
    `len` bytes at `src`, at least 16 and at most 2²⁰ blocks, under the key `Key1 ‖ Key2` \
    with the tweak value `*i`, as `vg_aes_xts_decrypt_unit` would replace them with in \
    place (see `vg_aes_xts_decrypt_unit`). `src` is not written, and `dst` is a buffer of \
    its own: it overlaps no other buffer, `src` included.\n\n\
    Contract: `VG.Spec.Xts.aesDecryptUnitToContract`. Constant time: only the pointers, \
    `rounds`, `len` and `dst_len` may affect timing, not the key schedules, the tweak value \
    or the data."
  safety := aesUnitToSafety

end VG.Spec.Xts
