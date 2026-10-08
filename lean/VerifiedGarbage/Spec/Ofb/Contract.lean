import VerifiedGarbage.Spec.Ofb
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# AES-OFB: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_aes_ofb`, in
terms of `Spec/Ofb.lean`, for any target: `A` is the target's calling
convention. The signature fixes where the arguments are, the memory the
function may access, disjointness, and that the pointers, the number of
rounds and the number of blocks are public (see `TCB/Sig.lean`). The key
schedule, the chaining value and the data are secret.

It reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer, and transforms `n` whole blocks in place, from
the block in `iv`, which it replaces with the one to continue from
(`Ofb.next`): so a caller may process a message in pieces of whole blocks,
keeping `iv` between calls. A partial last block is the caller's: OFB of a
zero block is the next output block, whose first bytes it XORs in.

It takes the `scratch` buffer of CBC's functions (`Spec/Cbc/Contract.lean`):
room for the working space of `vg_aes_encrypt_blocks` (`[u64; 256]`) and
128 bytes more. `stack` is the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (see
`Sig.contract`).
-/

namespace VG.Spec.Ofb

/-- `vg_aes_ofb(schedule: *const [u8; 240], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesSig : Sig := Cbc.aesSig

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `n` blocks at `data`
with their OFB encryption or decryption (§6.4) by AES with `w`, from the
block at `iv`, and that block with the last output block `Oₙ` (unchanged
if `n = 0`). -/
def aesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n _scratch m m' _ =>
      let ciph := Cbc.aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Cbc.blocksAt m' data n.toNat = crypt ciph (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat) ∧
        Aes.bytesAt m' iv 16 = next ciph (Aes.bytesAt m iv 16) n.toNat)
    (stack := stack)

/-- `vg_aes_ofb` on every target. -/
def aesApi : Api where
  module := "aes_ofb"
  name := "vg_aes_ofb"
  sig := aesSig
  contracts := some fun A stack => aesContract A stack
  summary := "AES-OFB encryption or decryption (NIST SP 800-38A §6.4) of whole blocks, in \
    place: XORs the `n` 16-byte blocks at `data` with the output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)`, \
    where `O₀` is the block at `*iv`, and replaces `*iv` with `Oₙ` (leaving it unchanged if \
    `n = 0`), so that a further call continues the message. `CIPH_K` is AES (FIPS 197) with \
    `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` bytes of \
    `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Ofb.aesContract`. Constant time: only the pointers, `rounds` and `n` \
    may affect timing, not the key schedule, the chaining value or the data."
  safety := Cbc.aesSafety

end VG.Spec.Ofb
