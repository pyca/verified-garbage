import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Spec.Ofb

/-!
# Triple DES-OFB: the contract, on every target

**Trusted** (as every file in `Spec/`). OFB (NIST SP 800-38A §6.4,
`Spec/Ofb.lean`, defined for any block cipher) with Triple DES's encryption
(FIPS 46-3, `Spec/TripleDes.lean`; `cipher`, `Spec/TripleDes/Cbc.lean`) as
`CIPH_K`, on 8-byte blocks, under the 384-byte schedule that
`vg_triple_des_expand_key` writes.

`vg_triple_des_ofb` transforms `n` whole blocks in place, from the block in
`iv`, which it replaces with the one to continue from, the last output block
(`Ofb.next`): a caller may process a message in pieces of whole blocks,
keeping `iv` between calls. A partial last block is the caller's: OFB of a
zero block is the next output block, whose first bytes it XORs in.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

namespace VG.Spec.TripleDes

/-- `vg_triple_des_ofb(schedule: *const [u8; 384], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`. -/
def ofbSig : Sig where
  params := [("schedule", .array false .u8 384), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their OFB encryption or decryption (§6.4) by Triple DES, from the block at
`iv`, and that block with the last output block `Oₙ` (unchanged if
`n = 0`). -/
def ofbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let ciph := cipher (scheduleAt m schedule)
      cbcBlocksAt m' data n.toNat = Ofb.crypt ciph (bytesAt m iv 8) (cbcBlocksAt m data n.toNat) ∧
        bytesAt m' iv 8 = Ofb.next ciph (bytesAt m iv 8) n.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_triple_des_ofb` on every target. -/
def ofbApi : Api where
  module := "triple_des_ofb"
  name := "vg_triple_des_ofb"
  sig := ofbSig
  writeArgs := true
  contracts := some fun A stack => ofbContract A stack
  summary := "Triple DES-OFB encryption or decryption (NIST SP 800-38A §6.4, FIPS 46-3) of whole \
    blocks, in place: XORs the `n` 8-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, and replaces `*iv` with `Oₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. \
    `CIPH_K` is Triple DES encryption under the schedule written by \
    `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.ofbContract`. Constant time: only the pointers and `n` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.TripleDes
