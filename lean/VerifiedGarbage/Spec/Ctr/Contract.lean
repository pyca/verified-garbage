import VerifiedGarbage.Spec.Ctr
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# AES-CTR: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_aes_ctr`, in
terms of `Spec/Ctr.lean`, for any target: `A` is the target's calling
convention. The signature fixes where the arguments are, the memory the
function may access, disjointness, and that the pointers, the number of
rounds and the number of blocks are public (see `TCB/Sig.lean`). The key
schedule, the counter block and the data are secret.

It reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `n` whole blocks in place, from
the counter block in `ctr`, which it replaces with the one to continue from
(`Ctr.next`): so a caller may process a message in pieces of whole blocks,
keeping `ctr` between calls. A partial last block is the caller's: CTR of a
zero block is the next output block, whose first bytes it XORs in.

It takes the `scratch` buffer of CBC's functions (`Spec/Cbc/Contract.lean`):
room for the working space of `vg_aes_encrypt_blocks` (`[u64; 256]`) and
128 bytes more. `stack` is the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (see
`Sig.contract`).
-/

namespace VG.Spec.Ctr

/-- `vg_aes_ctr(schedule: *const [u8; 240], rounds: usize, ctr: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("ctr", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their CTR encryption or decryption (§6.5) by AES with `w`, from the
counter block at `ctr`, and that block with `Tₙ₊₁`, its `n`-th increment
modulo `2¹²⁸` (unchanged if `n = 0`). -/
def aesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _ctr _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds ctr data n _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Cbc.blocksAt m' data n.toNat = crypt ciph (Aes.bytesAt m ctr 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' ctr 16 = next (Aes.bytesAt m ctr 16) n.toNat)
    (stack := stack)

/-- `vg_aes_ctr` on every target. -/
def aesApi : Api where
  module := "aes_ctr"
  name := "vg_aes_ctr"
  sig := aesSig
  contracts := some fun A stack => aesContract A stack
  summary := "AES-CTR encryption or decryption (NIST SP 800-38A §6.5) of whole blocks, in \
    place: XORs the `n` 16-byte blocks at `data` with the output blocks `Oⱼ = CIPH_K(Tⱼ)`, \
    where `T₁` is the block at `*ctr` and `Tⱼ₊₁ = Tⱼ + 1 mod 2¹²⁸` (Appendix B.1's standard \
    incrementing function on the whole block, read as a big-endian integer), and replaces \
    `*ctr` with `Tₙ₊₁` (leaving it unchanged if `n = 0`), so that a further call continues \
    the message. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the \
    first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Ctr.aesContract`. Constant time: only the pointers, `rounds` and `n` \
    may affect timing, not the key schedule, the counter block or the data."
  safety := Cbc.aesSafety

end VG.Spec.Ctr
