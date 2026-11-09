module

public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Ofb.Final

/-!
# SM4-OFB of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_sm4_ofb_final`:
the OFB function of `Spec/Sm4/Ofb.lean` (the same `CIPH_K`, schedule, and
public and secret arguments) with the data `len` bytes rather than `n` whole
blocks, so that it also takes a partial last block, as `Spec/Ofb/Final.lean`
defines it (`Ofb.cryptFinal`): a message's last piece, of any length.
Existing contracts are unchanged.

It leaves in `iv` the last output block used, `Oₙ`: the block a further call
continues from when `len` is a multiple of 16, and keystream after a partial
last block, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.Sm4

/-- `vg_sm4_ofb_final(schedule: *const [u8; 128], iv: *mut [u8; 16], data: *mut u8, len: usize)`:
`ofbSig` with the data `len` bytes. -/
def ofbFinalSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 16),
    ("data", .slice true .u8 "len")]

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their OFB encryption or decryption by SM4, a partial last block included, from
the block at `iv`, and that block with the last output block used
(`Ofb.CryptFinal`). -/
def ofbFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbFinalSig.contract A (post := fun schedule iv data len m m' _ =>
      Ofb.CryptFinal (cipher (scheduleAt m schedule)) 16 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ofb_final` on every target. -/
def ofbFinalApi : Api where
  module := "sm4_ofb"
  name := "vg_sm4_ofb_final"
  sig := ofbFinalSig
  writeArgs := true
  contracts := some fun A stack => ofbFinalContract A stack
  summary := "SM4-OFB encryption or decryption (NIST SP 800-38A §6.4, GB/T 32907-2016 §7.1) of the \
    last piece of a message, of any length, in place: XORs the `len` bytes at `data` with the \
    output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, a partial last block \
    `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and replaces `*iv` with the last output block used, `Oₙ` \
    (leaving it unchanged if `len = 0`): so that a further call continues the message if `len` is \
    a multiple of 16, and otherwise keystream, to be wiped, after which the message must end. \
    `CIPH_K` is SM4 encryption under the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.ofbFinalContract`. Constant time: only the pointers and `len` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Sm4
