module

public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Ofb.Final

/-!
# CAST5-OFB of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of
`vg_cast5_ofb_final`: the OFB function of `Spec/Cast5/Ofb.lean` (the same
`CIPH_K`, schedule, and public and secret arguments) with the data `len`
bytes rather than `n` whole blocks, so that it also takes a partial last
block, as `Spec/Ofb/Final.lean` defines it (`Ofb.cryptFinal`): a message's
last piece, of any length. Existing contracts are unchanged.

It leaves in `iv` the last output block used, `Oₙ`: the block a further call
continues from when `len` is a multiple of 8, and keystream after a partial
last block, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.Cast5

/-- `vg_cast5_ofb_final(schedule: *const [u8; 128], rounds: usize, iv: *mut [u8; 8], data: *mut u8, len: usize)`:
`ofbSig` with the data `len` bytes. `rounds` is public. -/
def ofbFinalSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array true .u8 8), ("data", .slice true .u8 "len")]

/-- `rounds` is 12 or 16. -/
def ofbFinalPre (pb : Nat) : Curry (ofbFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _len _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- For `rounds` of 12 or 16, and every key `K` whose subkeys are at `schedule`
with `rounds` rounds (`KeySchedule`): replaces the `len` bytes at `data` with
their OFB encryption or decryption by CAST5, a partial last block included, from
the block at `iv`, and that block with the last output block used
(`Ofb.CryptFinal`). -/
def ofbFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbFinalSig.contract A (pre := ofbFinalPre A.ptrBits)
    (post := fun schedule rounds iv data len m m' _ =>
      ∀ key, KeySchedule m schedule rounds.toNat key →
        Ofb.CryptFinal (cipher (expandKey key) (Cast5.rounds key.length)) 8 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_ofb_final` on every target. -/
def ofbFinalApi : Api where
  module := "cast5_ofb"
  name := "vg_cast5_ofb_final"
  sig := ofbFinalSig
  writeArgs := true
  contracts := some fun A stack => ofbFinalContract A stack
  summary := "CAST5-OFB encryption or decryption (NIST SP 800-38A §6.4, RFC 2144 §2) of the last \
    piece of a message, of any length, in place: XORs the `len` bytes at `data` with the output \
    blocks `Oⱼ = CIPH_K(Oⱼ₋₁)`, where `O₀` is the block at `*iv`, a partial last block `Pₙ*` of \
    `u` bytes with `MSB_u(Oₙ)`, and replaces `*iv` with the last output block used, `Oₙ` (leaving \
    it unchanged if `len = 0`): so that a further call continues the message if `len` is a \
    multiple of 8, and otherwise keystream, to be wiped, after which the message must end. \
    `CIPH_K` is CAST5 encryption with `rounds` rounds under the subkeys at `schedule`, as \
    `vg_cast5_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Cast5.ofbFinalContract`. Constant time: only the pointers, `rounds` and \
    `len` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
