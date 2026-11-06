module

public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Ctr.Final

/-!
# Camellia-CTR of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of
`vg_camellia_ctr_final`: the CTR function of `Spec/Camellia/Ctr.lean` (the
same `CIPH_K`, schedule, and public and secret arguments) with the data
`len` bytes rather than `n` whole blocks, so that it also takes a partial
last block, as `Spec/Ctr/Final.lean` defines it (`Ctr.cryptFinal`): a
message's last piece, of any length. Existing contracts are unchanged.

It leaves in `ctr` the counter block after the last one used, `Tₙ₊₁`: the
block a further call continues from when `len` is a multiple of 16; after a
partial last block the message must end.
-/

@[expose] public section

namespace VG.Spec.Camellia

/-- `vg_camellia_ctr_final(schedule: *const [u8; 272], rounds: usize, ctr: *mut [u8; 16], data: *mut u8, len: usize)`:
`ctrSig` with the data `len` bytes. `rounds` is public. -/
def ctrFinalSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("ctr", .array true .u8 16), ("data", .slice true .u8 "len")]

/-- `rounds` is 18 or 24. -/
def ctrFinalPre (pb : Nat) : Curry (ctrFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _ctr _data _len _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, and every key `K` whose subkeys are at `schedule`
with `rounds` rounds (`KeySchedule`): replaces the `len` bytes at `data` with
their CTR encryption or decryption by Camellia, a partial last block included,
from the block at `ctr`, and that block with `Tₙ₊₁` (`Ctr.CryptFinal`). -/
def ctrFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrFinalSig.contract A (pre := ctrFinalPre A.ptrBits)
    (post := fun schedule rounds ctr data len m m' _ =>
      ∀ key, KeySchedule m schedule rounds.toNat key →
        Ctr.CryptFinal (cipher (expandKey key)) m m' ctr data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_camellia_ctr_final` on every target. -/
def ctrFinalApi : Api where
  module := "camellia_ctr"
  name := "vg_camellia_ctr_final"
  sig := ctrFinalSig
  writeArgs := true
  contracts := some fun A stack => ctrFinalContract A stack
  summary := "Camellia-CTR encryption or decryption (NIST SP 800-38A §6.5, RFC 3713 §2.3) of the \
    last piece of a message, of any length, in place: XORs the `len` bytes at `data` with the \
    output blocks `Oⱼ = CIPH_K(Tⱼ)`, where `T₁` is the block at `*ctr` and \
    `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` (Appendix B.1's standard incrementing function on the whole block, \
    read as a big-endian integer), a partial last block `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and \
    replaces `*ctr` with `Tₙ₊₁` (leaving it unchanged if `len = 0`), so that a further call \
    continues the message if `len` is a multiple of 16; after a partial last block the message \
    must end. `CIPH_K` is Camellia encryption with `rounds` rounds under the subkeys at \
    `schedule`, as `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.ctrFinalContract`. Constant time: only the pointers, `rounds` and \
    `len` may affect timing, not the subkeys, the counter block or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
