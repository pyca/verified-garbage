import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Spec.Ofb

/-!
# Camellia-OFB: the contract, on every target

**Trusted** (as every file in `Spec/`). OFB (NIST SP 800-38A §6.4,
`Spec/Ofb.lean`, defined for any block cipher) with Camellia's encryption
(RFC 3713 §2.3, `Spec/Camellia.lean`) as `CIPH_K`, under the subkeys of
`rounds` rounds that `vg_camellia_expand_key` writes.

`vg_camellia_ofb` transforms `n` whole blocks in place, from the block in
`iv`, which it replaces with the one to continue from, the last output
block (`Ofb.next`): a caller may process a message in pieces of whole
blocks, keeping `iv` between calls. A partial last block is the caller's:
OFB of a zero block is the next output block, whose first bytes it XORs in.

Only the pointers, `rounds` and `n` are public: no part of the chaining
value may affect timing.
-/

namespace VG.Spec.Camellia

/-- `vg_camellia_ofb(schedule: *const [u8; 272], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`.
`rounds` is public. -/
def ofbSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]

/-- `rounds` is 18 or 24. -/
def ofbPre (pb : Nat) : Curry (ofbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule` (`subkeysAt`): replaces the `n` blocks at `data` with their OFB
encryption or decryption (§6.4) by Camellia, from the block at `iv`, and
that block with the last output block `Oₙ` (unchanged if `n = 0`). Stated
for those numbers of rounds, which the precondition requires, so that it
reads only the buffers. -/
def ofbPost (pb : Nat) : ofbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let ciph := cipher (subkeysAt m schedule rounds.toNat)
    Cbc.blocksAt m' data n.toNat = Ofb.crypt ciph (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat) ∧
      Aes.bytesAt m' iv 16 = Ofb.next ciph (Aes.bytesAt m iv 16) n.toNat

/-- `ofbPre` and `ofbPost`. The subkeys, the chaining value and the data
are secret. -/
def ofbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A (pre := ofbPre A.ptrBits) (post := ofbPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_camellia_ofb` on every target. -/
def ofbApi : Api where
  module := "camellia_ofb"
  name := "vg_camellia_ofb"
  sig := ofbSig
  writeArgs := true
  contracts := some fun A stack => ofbContract A stack
  summary := "Camellia-OFB encryption or decryption (NIST SP 800-38A §6.4, RFC 3713 §2.3) of \
    whole blocks, in place: XORs the `n` 16-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, and replaces `*iv` with `Oₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` \
    is Camellia with `rounds` rounds under the subkeys at `schedule`, as \
    `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.ofbContract`. Constant time: only the pointers, `rounds` and \
    `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
