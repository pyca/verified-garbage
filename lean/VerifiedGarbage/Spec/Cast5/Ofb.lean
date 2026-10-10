import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Spec.Ofb

/-!
# CAST5-OFB: the contract, on every target

**Trusted** (as every file in `Spec/`). OFB (NIST SP 800-38A §6.4,
`Spec/Ofb.lean`, defined for any block cipher) with CAST5's encryption
(RFC 2144 §2, `Spec/Cast5.lean`; `cipher`, `Spec/Cast5/Cbc.lean`) as `CIPH_K`,
on 8-byte blocks, under the subkeys that `vg_cast5_expand_key` writes, with
`rounds` rounds.

`vg_cast5_ofb` transforms `n` whole blocks in place, from the block in `iv`,
which it replaces with the one to continue from, the last output block
(`Ofb.next`): a caller may process a message in pieces of whole blocks,
keeping `iv` between calls. A partial last block is the caller's: OFB of a
zero block is the next output block, whose first bytes it XORs in.

Only the pointers, `rounds` and `n` are public: no part of the chaining value
may affect timing.
-/

namespace VG.Spec.Cast5

/-- `vg_cast5_ofb(schedule: *const [u8; 128], rounds: usize, iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`.
`rounds` is public, 12 or 16 (the precondition). -/
def ofbSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array true .u8 8), ("data", .slice true (.array .u8 8) "n")]

/-- `rounds` is 12 or 16. -/
def ofbPre (pb : Nat) : Curry (ofbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their OFB encryption or decryption (§6.4) by CAST5,
from the block at `iv`, and that block with the last output block `Oₙ`
(unchanged if `n = 0`). -/
def ofbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A (pre := ofbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let ciph := cipher (scheduleAt m schedule) rounds.toNat
      cbcBlocksAt m' data n.toNat = Ofb.crypt ciph (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat) ∧
        Aes.bytesAt m' iv 8 = Ofb.next ciph (Aes.bytesAt m iv 8) n.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_ofb` on every target. -/
def ofbApi : Api where
  module := "cast5_ofb"
  name := "vg_cast5_ofb"
  sig := ofbSig
  writeArgs := true
  contracts := some fun A stack => ofbContract A stack
  summary := "CAST5-OFB encryption or decryption (NIST SP 800-38A §6.4, RFC 2144 §2) of whole blocks, \
    in place: XORs the `n` 8-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, and replaces `*iv` with `Oₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. \
    `CIPH_K` is CAST-128 encryption with `rounds` rounds under the subkeys written by \
    `vg_cast5_expand_key`.\n\n\
    Contract: `VG.Spec.Cast5.ofbContract`. Constant time: only the pointers, `rounds` and \
    `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
