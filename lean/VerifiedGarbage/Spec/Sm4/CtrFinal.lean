module

public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Ctr.Final

/-!
# SM4-CTR of a message's last piece: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_sm4_ctr_final`:
the CTR function of `Spec/Sm4/Ctr.lean` (the same `CIPH_K`, schedule, and
public and secret arguments) with the data `len` bytes rather than `n` whole
blocks, so that it also takes a partial last block, as `Spec/Ctr/Final.lean`
defines it (`Ctr.cryptFinal`): a message's last piece, of any length.
Existing contracts are unchanged.

It leaves in `ctr` the counter block after the last one used, `Tₙ₊₁`: the
block a further call continues from when `len` is a multiple of 16; after a
partial last block the message must end.
-/

@[expose] public section

namespace VG.Spec.Sm4

/-- `vg_sm4_ctr_final(schedule: *const [u8; 128], ctr: *mut [u8; 16], data: *mut u8, len: usize)`:
`ctrSig` with the data `len` bytes. -/
def ctrFinalSig : Sig where
  params := [("schedule", .array false .u8 128), ("ctr", .array true .u8 16),
    ("data", .slice true .u8 "len")]

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their CTR encryption or decryption by SM4, a partial last block included, from
the block at `ctr`, and that block with `Tₙ₊₁` (`Ctr.CryptFinal`). -/
def ctrFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrFinalSig.contract A (post := fun schedule ctr data len m m' _ =>
      Ctr.CryptFinal (cipher (scheduleAt m schedule)) m m' ctr data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ctr_final` on every target. -/
def ctrFinalApi : Api where
  module := "sm4_ctr"
  name := "vg_sm4_ctr_final"
  sig := ctrFinalSig
  writeArgs := true
  contracts := some fun A stack => ctrFinalContract A stack
  summary := "SM4-CTR encryption or decryption (NIST SP 800-38A §6.5, draft-ribose-cfrg-sm4-10 \
    §7.1) of the last piece of a message, of any length, in place: XORs the `len` bytes at `data` \
    with the output blocks `Oⱼ = CIPH_K(Tⱼ)`, where `T₁` is the block at `*ctr` and \
    `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` (Appendix B.1's standard incrementing function on the whole block, \
    read as a big-endian integer), a partial last block `Pₙ*` of `u` bytes with `MSB_u(Oₙ)`, and \
    replaces `*ctr` with `Tₙ₊₁` (leaving it unchanged if `len = 0`), so that a further call \
    continues the message if `len` is a multiple of 16; after a partial last block the message \
    must end. `CIPH_K` is SM4 encryption under the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.ctrFinalContract`. Constant time: only the pointers and `len` may \
    affect timing, not the schedule, the counter block or the data."
  safety := []

end VG.Spec.Sm4
