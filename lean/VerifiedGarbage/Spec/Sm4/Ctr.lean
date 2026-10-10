module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Ctr.Contract

/-!
# SM4-CTR: the contract, on every target

**Trusted** (as every file in `Spec/`). CTR (NIST SP 800-38A §6.5,
`Spec/Ctr.lean`, defined for any block cipher) with SM4's forward function
(draft-ribose-cfrg-sm4-10 §7.1, `Spec/Sm4.lean`) as `CIPH_K`, under the
128-byte schedule that `vg_sm4_expand_key` writes.

`vg_sm4_ctr` transforms `n` whole blocks in place, from the counter block
in `ctr`, which it replaces with the one to continue from (`Ctr.next`): a
caller may process a message in pieces of whole blocks, keeping `ctr`
between calls. A partial last block is the caller's: CTR of a zero block is
the next output block, whose first bytes it XORs in. The counter is
incremented as one 128-bit big-endian integer (SP 800-38A Appendix B.1).

Unlike `vg_aes_ctr` (`Spec/Ctr/Contract.lean`), no part of the counter
block may affect timing: only the pointers and `n` are public.
-/

@[expose] public section

namespace VG.Spec.Sm4

/-- SM4's forward function `CIPH_K` under the schedule `k`, on blocks as
lists of 16 bytes (`Cbc.Cipher`). -/
def cipher (k : Schedule) : Cbc.Cipher := fun b =>
  (encryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- `vg_sm4_ctr(schedule: *const [u8; 128], ctr: *mut [u8; 16], data: *mut [u8; 16], n: usize)`. -/
def ctrSig : Sig where
  params := [("schedule", .array false .u8 128), ("ctr", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CTR encryption or decryption (§6.5) by SM4, from the counter block at
`ctr`, and that block with `Tₙ₊₁`, its `n`-th increment modulo `2¹²⁸`
(unchanged if `n = 0`). -/
def ctrContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrSig.contract A
    (post := fun schedule ctr data n m m' _ =>
      Cbc.blocksAt m' data n.toNat =
          Ctr.crypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m ctr 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' ctr 16 = Ctr.next (Aes.bytesAt m ctr 16) n.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ctr` on every target. -/
def ctrApi : Api where
  module := "sm4_ctr"
  name := "vg_sm4_ctr"
  sig := ctrSig
  writeArgs := true
  contracts := some fun A stack => ctrContract A stack
  summary := "SM4-CTR encryption or decryption (NIST SP 800-38A §6.5, draft-ribose-cfrg-sm4-10 §7.1) \
    of whole blocks, in place: XORs the `n` 16-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Tⱼ)`, where `T₁` is the block at `*ctr` and `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` \
    (Appendix B.1's standard incrementing function on the whole block, read as a big-endian \
    integer), and replaces `*ctr` with `Tₙ₊₁` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is SM4 under the schedule written by \
    `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.ctrContract`. Constant time: only the pointers and `n` may affect \
    timing, not the schedule, the counter block or the data."
  safety := []

end VG.Spec.Sm4
