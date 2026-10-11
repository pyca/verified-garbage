module

public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Camellia-CTR: the contract, on every target

**Trusted** (as every file in `Spec/`). CTR (NIST SP 800-38A §6.5,
`Spec/Ctr.lean`, defined for any block cipher) with Camellia's encryption
(RFC 3713 §2.3, `Spec/Camellia.lean`) as `CIPH_K`, under the subkeys of
`rounds` rounds that `vg_camellia_expand_key` writes.

`vg_camellia_ctr` transforms `n` whole blocks in place, from the counter
block in `ctr`, which it replaces with the one to continue from
(`Ctr.next`): a caller may process a message in pieces of whole blocks,
keeping `ctr` between calls. A partial last block is the caller's: CTR of a
zero block is the next output block, whose first bytes it XORs in. The
counter is incremented as one 128-bit big-endian integer (SP 800-38A
Appendix B.1).

Only the pointers, `rounds` and `n` are public: no part of the counter block
may affect timing.
-/

@[expose] public section

namespace VG.Spec.Camellia

/-- Camellia's encryption `CIPH_K` under the subkeys `sk`, on blocks as
lists of 16 bytes (`Cbc.Cipher`). -/
def cipher (sk : Subkeys) : Cbc.Cipher := fun b =>
  (encryptBlock sk (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- `vg_camellia_ctr(schedule: *const [u8; 272], rounds: usize, ctr: *mut [u8; 16], data: *mut [u8; 16], n: usize)`.
`rounds` is public. -/
def ctrSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("ctr", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]

/-- `rounds` is 18 or 24. -/
def ctrPre (pb : Nat) : Curry (ctrSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _ctr _data _n _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule` (`subkeysAt`): replaces the `n` blocks at `data` with their CTR
encryption or decryption (§6.5) by Camellia, from the counter block at
`ctr`, and that block with `Tₙ₊₁`, its `n`-th increment modulo `2¹²⁸`
(unchanged if `n = 0`). Stated for those numbers of rounds, which the
precondition requires, so that it reads only the buffers. -/
def ctrPost (pb : Nat) : ctrSig.Post pb := fun schedule rounds ctr data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    Cbc.blocksAt m' data n.toNat =
        Ctr.crypt (cipher (subkeysAt m schedule rounds.toNat)) (Aes.bytesAt m ctr 16)
          (Cbc.blocksAt m data n.toNat) ∧
      Aes.bytesAt m' ctr 16 = Ctr.next (Aes.bytesAt m ctr 16) n.toNat

/-- `ctrPre` and `ctrPost`. The subkeys, the counter block and the data are
secret. -/
def ctrContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctrSig.contract A (pre := ctrPre A.ptrBits) (post := ctrPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_camellia_ctr` on every target. -/
def ctrApi : Api where
  module := "camellia_ctr"
  name := "vg_camellia_ctr"
  sig := ctrSig
  writeArgs := true
  contracts := some fun A stack => ctrContract A stack
  summary := "Camellia-CTR encryption or decryption (NIST SP 800-38A §6.5, RFC 3713 §2.3) of \
    whole blocks, in place: XORs the `n` 16-byte blocks at `data` with the output blocks \
    `Oⱼ = CIPH_K(Tⱼ)`, where `T₁` is the block at `*ctr` and `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` \
    (Appendix B.1's standard incrementing function on the whole block, read as a big-endian \
    integer), and replaces `*ctr` with `Tₙ₊₁` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is Camellia with `rounds` rounds under the \
    subkeys at `schedule`, as `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.ctrContract`. Constant time: only the pointers, `rounds` and \
    `n` may affect timing, not the subkeys, the counter block or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
