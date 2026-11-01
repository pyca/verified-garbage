module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm

/-!
# SM4: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

* `vg_sm4_ecb` is ECB in either direction, which it takes as a public
  argument: an implementation may share one body between the two
  directions, and its ECB functions then call it.
* `vg_sm4_ctr32` is counter mode over whole blocks with GCM's `inc₃₂`
  (§6.5 steps 5–7, `Gcm.ctr32`), from the 128-byte schedule that
  `vg_sm4_expand_key` writes: the block-cipher work of SM4-GCM. With a zero
  block and a zero counter block it computes the hash subkey
  `H = CIPH_K(0¹²⁸)` (§7.1 step 1); from `inc₃₂(J₀)` it encrypts or
  decrypts the text (step 3), a partial last block being the caller's (CTR
  of a zero block is the next keystream block, whose first bytes it XORs
  in); and from `J₀` on the block `S` it computes the unmasked tag
  `GCTR_K(J₀, S)` (step 6). Unlike `vg_sm4_ctr` (`Spec/Sm4/Ctr.lean`),
  which increments the whole counter block as a 128-bit integer (SP 800-38A
  Appendix B.1), only the rightmost 32 bits of the counter block are
  incremented, modulo 2³² (§6.2). No part of the counter block may affect
  timing: only the pointers and `n` are public.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG.Spec VG.Spec.Sm4

/-- The direction `decrypt` selects: 0 to encrypt, otherwise decrypt. -/
def directionOf (decrypt : Nat) : Direction := if decrypt = 0 then .encrypt else .decrypt

/-- `vg_sm4_ecb(schedule, data, n, decrypt: usize)`: the ECB functions'
arguments, then the direction (0 to encrypt, 1 to decrypt), which is public. -/
def ecbDirSig : Sig where
  params := ecbSig.params ++ [("decrypt", .int .usize true)]

/-- For `decrypt` of 0 or 1: replaces the `n` blocks at `data` with their
encryption (`decrypt = 0`) or decryption (`decrypt = 1`) under the round keys
at `schedule`. -/
def ecbDirContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbDirSig.contract A
    (pre := fun _schedule _data _n decrypt _ => decrypt.toNat ≤ 1)
    (post := fun schedule data n decrypt m m' _ =>
      blocksAt m' data n.toNat =
        ecb (scheduleAt m schedule) (directionOf decrypt.toNat) (blocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

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

end VG.Proof.Sm4
