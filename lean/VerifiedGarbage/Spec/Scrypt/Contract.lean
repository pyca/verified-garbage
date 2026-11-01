module

public import VerifiedGarbage.Spec.Scrypt
public import VerifiedGarbage.TCB.Artifact

/-!
# scrypt: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contract of scrypt
(`vg_scrypt`), in terms of `Spec/Scrypt.lean`, for any target: `A` is the
target's calling convention. The signature fixes where the arguments are,
the memory the function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`). The function may overwrite its
arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the functions it calls; `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls and frames use (see `Sig.contract`), which depends on the target.

`vg_scrypt` computes the whole of scrypt (`Scrypt.scrypt`): the two
PBKDF2-HMAC-SHA-256 steps and scryptROMix of each of the `p` blocks. The
caller provides the memory, whose size depends on the parameters.

scryptROMix reads the blocks `V[j]` at indices `j` computed from the
password (§5), so its memory accesses depend on them: the contract declares
that they leak (`Scrypt.roMixIndices` of each block, through
`Sig.contract`'s `leak`), and nothing else secret.
-/

@[expose] public section

namespace VG.Spec.Scrypt

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_scrypt(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, r: usize, b: *mut [u8; 128], blen: usize, v: *mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize, out: *mut u8, out_len: usize)`.
The block size parameter `r` and the lengths are public. `b`, of
`blen = p * r` 128-byte chunks, holds `B`; `v`, of `vlen = N * r` chunks, is
scryptROMix's `V`; `scratch`, of `slen = r + 16` chunks, is working space. -/
def scryptSig : Sig where
  params := [("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("r", .int .usize true), ("b", .slice true (.array .u8 128) "blen"),
    ("v", .slice true (.array .u8 128) "vlen"), ("scratch", .slice true (.array .u8 128) "slen"),
    ("out", .slice true .u8 "out_len")]

/-- The blocks `B[0], …, B[p - 1]` of scrypt's step 1: its `p` chunks of
`128 * r` bytes of `PBKDF2-HMAC-SHA256 (P, S, 1, p * 128 * r)`. -/
def blocks (pw s : List Byte) (r p : Nat) : List (List Byte) :=
  let b := (Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r)).getD []
  (List.range p).map fun i => (b.drop (128 * r * i)).take (128 * r)

/-- If `r` is positive, `blen = p * r` and `vlen = N * r` for parameters
`N`, `r`, `p` and `out_len` that are `valid` and that PBKDF2 accepts
(`out_len ≤ (2³² − 1) · 32`), and `slen = r + 16`: writes
`scrypt (P, S, N, r, p, out_len)` of the `password_len` bytes `P` at
`password` and the `salt_len` bytes `S` at `salt` to the `out_len` bytes at
`out`. The password, the salt and the derived key are secret, but the
indices `j` of each scryptROMix's step 3 (`roMixIndices` of each block
`B[i]`, in order) may leak. -/
def scryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scryptSig.contract A
    (pre := fun _password _passwordLen _salt _saltLen r _b blen _v vlen _scratch slen _out outLen
        _m =>
      0 < r.toNat ∧ blen.toNat % r.toNat = 0 ∧ vlen.toNat % r.toNat = 0 ∧
        valid (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat ∧
        outLen.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r.toNat + 16)
    (post := fun password passwordLen salt saltLen r _b blen _v vlen _scratch _slen out outLen m
        m' _ =>
      scrypt (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
        (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat =
        some (bytesAt m' out outLen.toNat))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun password passwordLen salt saltLen r _b blen _v vlen _scratch _slen _out
        _outLen m =>
      (blocks (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat) r.toNat
        (blen.toNat / r.toNat)).flatMap (roMixIndices r.toNat (vlen.toNat / r.toNat)))

/-- `vg_scrypt` on every target. -/
def scryptApi : Api where
  module := "scrypt"
  name := "vg_scrypt"
  sig := scryptSig
  writeArgs := true
  contracts := some fun A stack => scryptContract A stack
  summary := "scrypt (RFC 7914 §6) with block size parameter `r`, cost parameter `N = vlen / r` \
    and parallelization parameter `p = blen / r`: writes the `out_len`-byte key derived from the \
    `password_len` bytes at `password` and the `salt_len` bytes at `salt` to `out`.\n\n\
    Contract: `VG.Spec.Scrypt.scryptContract`. Not constant time in the indices: timing may \
    depend on the pointers, the lengths, `r`, `N`, `p` and the indices `j` of step 3 of each \
    scryptROMix, which are derived from the password and the salt and so leak information about \
    them (as in every scrypt that indexes `V` directly), but on nothing else."
  safety := [
    "`r` must be positive, `blen` must be `p * r` and `vlen` must be `N * r` for parameters that \
      RFC 7914 §6 accepts (`N` a power of two greater than 1 and less than `2^(16 r)`, \
      `0 < p ≤ (2^32 - 1) * 32 / (128 r)`, `0 < out_len ≤ (2^32 - 1) * 32`), and `slen` must be \
      `r + 16`.",
    "`b`, `v` and `scratch` are working space: their contents on return are unspecified."]

end VG.Spec.Scrypt
