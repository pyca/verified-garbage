module

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.Sm4.Ctr

/-!
# SM4-GCM: SM4's counter mode with GCM's increment, the contract on every target

**Trusted** (as every file in `Spec/`). SM4-GCM is GCM (NIST SP 800-38D,
`Spec/Gcm.lean`, defined for any 128-bit block cipher) with SM4's forward
function (draft-ribose-cfrg-sm4-10 §7.1, `Spec/Sm4.lean`) as `CIPH_K`: the
`AEAD_SM4_GCM` of RFC 8998 §3.5.1 ("works as specified in [GCM], using SM4
as the block cipher"), with a 16-byte key. `gcmEncrypt` and `gcmDecrypt`
are GCM-AE and GCM-AD (§7.1, §7.2) for it.

One function is implemented in assembly: `vg_sm4_ctr32`, counter mode over
whole blocks with GCM's `inc₃₂` (§6.5 steps 5–7, `Gcm.ctr32`), from the
128-byte schedule that `vg_sm4_expand_key` writes. It is the block-cipher
work of GCM: with a zero block and a zero counter block it computes the hash
subkey `H = CIPH_K(0¹²⁸)` (§7.1 step 1); from `inc₃₂(J₀)` it encrypts or
decrypts the text (step 3), a partial last block being the caller's (CTR of
a zero block is the next keystream block, whose first bytes it XORs in); and
from `J₀` on the block `S` it computes the unmasked tag `GCTR_K(J₀, S)`
(step 6). GHASH is `vg_ghash` (`Spec/Gcm/Contract.lean`), and the rest of
GCM is its Rust caller's.

Unlike `vg_sm4_ctr` (`Spec/Sm4/Ctr.lean`), which increments the whole
counter block as a 128-bit integer (SP 800-38A Appendix B.1), only the
rightmost 32 bits of the counter block are incremented, modulo 2³² (§6.2),
the leftmost 96 bits being left as they are. No part of the counter block
may affect timing: only the pointers and `n` are public.
-/

@[expose] public section

namespace VG.Spec.Sm4

/-- `CIPH_K` for GCM: SM4's forward function under the schedule `k`, on GCM's
128-bit blocks (the first byte the most significant, `Gcm.toBytes`). -/
def gcmCipher (k : Schedule) (x : Gcm.Block) : Gcm.Block := Gcm.ofBytes (cipher k (Gcm.toBytes x))

/-- `CIPH_K` for GCM under the 16-byte SM4 key `key` (§7.3's key schedule). -/
def gcmCipherOfKey (key : List Byte) : Gcm.Block → Gcm.Block :=
  gcmCipher (expandKey (Vector.ofFn fun i => key.getD i.val 0))

/-- SM4-GCM authenticated encryption (RFC 8998 §3.5.1, GCM-AE of SP 800-38D
§7.1) under the 16-byte key `key`, with a tag of `t` bytes. -/
def gcmEncrypt (key : List Byte) (t : Nat) (iv p a : List Byte) : List Byte × List Byte :=
  Gcm.encrypt (gcmCipherOfKey key) t iv p a

/-- SM4-GCM authenticated decryption (RFC 8998 §3.5.1, GCM-AD of SP 800-38D
§7.2) under the 16-byte key `key`, with a tag of `t` bytes. -/
def gcmDecrypt (key : List Byte) (t : Nat) (iv c a tag : List Byte) : Option (List Byte) :=
  Gcm.decrypt (gcmCipherOfKey key) t iv c a tag

/-- `vg_sm4_ctr32(schedule: *const [u8; 128], counter: *mut [u8; 16], data: *mut [u8; 16], n: usize)`. -/
def ctr32Sig : Sig where
  params := [("schedule", .array false .u8 128), ("counter", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)` into
the `n` blocks at `data`, where `CB₁` is the block at `counter` and
`CBᵢ₊₁ = inc₃₂(CBᵢ)`, `CIPH_K` being SM4 under the schedule, and leaves
`inc₃₂ⁿ(CB₁)` at `counter`. The schedule, the counter and the data are
secret. -/
def ctr32Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctr32Sig.contract A
    (post := fun schedule counter data n m m' _ =>
      Gcm.blocksAt m' data n.toNat =
          Gcm.ctr32 (gcmCipher (scheduleAt m schedule)) (Gcm.blockAt m counter)
            (Gcm.blocksAt m data n.toNat) ∧
        Gcm.blockAt m' counter = Nat.repeat Gcm.inc32 n.toNat (Gcm.blockAt m counter))
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ctr32` on every target. -/
def ctr32Api : Api where
  module := "sm4_gcm"
  name := "vg_sm4_ctr32"
  sig := ctr32Sig
  writeArgs := true
  contracts := some fun A stack => ctr32Contract A stack
  summary := "SM4 counter mode with GCM's 32-bit increment (NIST SP 800-38D §6.5, on whole \
    blocks; draft-ribose-cfrg-sm4-10 §7.1): XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)` into the `n` \
    16-byte blocks at `data`, in place, where `CB₁` is the counter block `*counter` and \
    `CBᵢ₊₁ = inc₃₂(CBᵢ)` (§6.2: the rightmost 32 bits, read as a big-endian integer, \
    incremented modulo 2³², the leftmost 96 bits unchanged), and leaves `inc₃₂ⁿ(CB₁)` in \
    `*counter` (unchanged if `n = 0`), so that a further call continues the message. \
    `CIPH_K` is SM4 under the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.ctr32Contract`. Constant time: only the pointers and `n` may affect \
    timing, not the schedule, the counter block or the data."
  safety := []

end VG.Spec.Sm4
