module

public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Ofb.Final

/-!
# Camellia-OFB of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of
`vg_camellia_ofb_final`: the OFB function of `Spec/Camellia/Ofb.lean` (the
same `CIPH_K`, schedule, and public and secret arguments) with the data
`len` bytes rather than `n` whole blocks, so that it also takes a partial
last block, as `Spec/Ofb/Final.lean` defines it (`Ofb.cryptFinal`): a
message's last piece, of any length. Existing contracts are unchanged.

It leaves in `iv` the last output block used, `Oₙ`: the block a further call
continues from when `len` is a multiple of 16, and keystream after a partial
last block, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.Camellia

/-- `vg_camellia_ofb_final(schedule: *const [u8; 272], rounds: usize, iv: *mut [u8; 16], data: *mut u8, len: usize)`:
`ofbSig` with the data `len` bytes. `rounds` is public. -/
def ofbFinalSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true .u8 "len")]

/-- `rounds` is 18 or 24. -/
def ofbFinalPre (pb : Nat) : Curry (ofbFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _len _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, and every key `K` whose subkeys are at `schedule`
with `rounds` rounds (`KeySchedule`): replaces the `len` bytes at `data` with
their OFB encryption or decryption by Camellia, a partial last block included,
from the block at `iv`, and that block with the last output block used
(`Ofb.CryptFinal`). -/
def ofbFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbFinalSig.contract A (pre := ofbFinalPre A.ptrBits)
    (post := fun schedule rounds iv data len m m' _ =>
      ∀ key, KeySchedule m schedule rounds.toNat key →
        Ofb.CryptFinal (cipher (expandKey key)) 16 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_camellia_ofb_final` on every target. -/
def ofbFinalApi : Api where
  module := "camellia_ofb"
  name := "vg_camellia_ofb_final"
  sig := ofbFinalSig
  writeArgs := true
  contracts := some fun A stack => ofbFinalContract A stack
  summary := "Camellia-OFB encryption or decryption (NIST SP 800-38A §6.4, RFC 3713 §2.3) of the \
    last piece of a message, of any length, in place: XORs the `len` bytes at `data` with the \
    output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, a partial last block \
    `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and replaces `*iv` with the last output block used, `Oₙ` \
    (leaving it unchanged if `len = 0`): so that a further call continues the message if `len` is \
    a multiple of 16, and otherwise keystream, to be wiped, after which the message must end. \
    `CIPH_K` is Camellia encryption with `rounds` rounds under the subkeys at `schedule`, as \
    `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.ofbFinalContract`. Constant time: only the pointers, `rounds` and \
    `len` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
