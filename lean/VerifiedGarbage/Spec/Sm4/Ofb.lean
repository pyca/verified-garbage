import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Spec.Ofb

/-!
# SM4-OFB: the contract, on every target

**Trusted** (as every file in `Spec/`). OFB (NIST SP 800-38A §6.4,
`Spec/Ofb.lean`, defined for any block cipher) with SM4's forward function
(GB/T 32907-2016 §7.1, `Spec/Sm4.lean`) as `CIPH_K`, under the 128-byte
schedule that `vg_sm4_expand_key` writes.

`vg_sm4_ofb` transforms `n` whole blocks in place, from the block in `iv`,
which it replaces with the one to continue from, the last output block
(`Ofb.next`): a caller may process a message in pieces of whole blocks,
keeping `iv` between calls. A partial last block is the caller's: OFB of a
zero block is the next output block, whose first bytes it XORs in.

Only the pointers and `n` are public: no part of the chaining value may
affect timing.
-/

namespace VG.Spec.Sm4

/-- `vg_sm4_ofb(schedule: *const [u8; 128], iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`. -/
def ofbSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their OFB encryption or decryption (§6.4) by SM4, from the block at `iv`,
and that block with the last output block `Oₙ` (unchanged if `n = 0`). -/
def ofbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let ciph := cipher (scheduleAt m schedule)
      Cbc.blocksAt m' data n.toNat = Ofb.crypt ciph (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' iv 16 = Ofb.next ciph (Aes.bytesAt m iv 16) n.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ofb` on every target. -/
def ofbApi : Api where
  module := "sm4_ofb"
  name := "vg_sm4_ofb"
  sig := ofbSig
  writeArgs := true
  contracts := some fun A stack => ofbContract A stack
  summary := "SM4-OFB encryption or decryption (NIST SP 800-38A §6.4, GB/T 32907-2016 §7.1) of \
    whole blocks, in place: XORs the `n` 16-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, and replaces `*iv` with `Oₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` \
    is SM4 under the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.ofbContract`. Constant time: only the pointers and `n` may affect \
    timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Sm4
