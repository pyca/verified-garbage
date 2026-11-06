module

public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.Ofb.Final

/-!
# Triple DES-OFB of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of
`vg_triple_des_ofb_final`: the OFB function of `Spec/TripleDes/Ofb.lean`
(the same `CIPH_K`, schedule, and public and secret arguments) with the data
`len` bytes rather than `n` whole blocks, so that it also takes a partial
last block, as `Spec/Ofb/Final.lean` defines it (`Ofb.cryptFinal`): a
message's last piece, of any length. Existing contracts are unchanged.

It leaves in `iv` the last output block used, `Oₙ`: the block a further call
continues from when `len` is a multiple of 8, and keystream after a partial
last block, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.TripleDes

/-- `vg_triple_des_ofb_final(schedule: *const [u8; 384], iv: *mut [u8; 8], data: *mut u8, len: usize)`:
`ofbSig` with the data `len` bytes. -/
def ofbFinalSig : Sig where
  params := [("schedule", .array false .u8 384), ("iv", .array true .u8 8),
    ("data", .slice true .u8 "len")]

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their OFB encryption or decryption by Triple DES, a partial last block included,
from the block at `iv`, and that block with the last output block used
(`Ofb.CryptFinal`). -/
def ofbFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbFinalSig.contract A (post := fun schedule iv data len m m' _ =>
      Ofb.CryptFinal (cipher (scheduleAt m schedule)) 8 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_triple_des_ofb_final` on every target. -/
def ofbFinalApi : Api where
  module := "triple_des_ofb"
  name := "vg_triple_des_ofb_final"
  sig := ofbFinalSig
  writeArgs := true
  contracts := some fun A stack => ofbFinalContract A stack
  summary := "Triple DES-OFB encryption or decryption (NIST SP 800-38A §6.4, FIPS 46-3) of the \
    last piece of a message, of any length, in place: XORs the `len` bytes at `data` with the \
    output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, a partial last block \
    `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and replaces `*iv` with the last output block used, `Oₙ` \
    (leaving it unchanged if `len = 0`): so that a further call continues the message if `len` is \
    a multiple of 8, and otherwise keystream, to be wiped, after which the message must end. \
    `CIPH_K` is Triple DES encryption under the schedule written by `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.ofbFinalContract`. Constant time: only the pointers and `len` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.TripleDes
