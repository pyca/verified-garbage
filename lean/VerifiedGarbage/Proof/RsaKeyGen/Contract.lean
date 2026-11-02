module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-!
# RSA key generation: the contract of its internal function

Not trusted: the contract of an internal function (`Rust.Internal`), which only
verified code calls, that its proofs and its callers' compose. Only the
callers' contracts, in `Spec/`, are trusted.

An implementation of `vg_rsa_keygen_key` may call one helper, which the Rust
does not: `vg_rsa_keygen_inverse`, a binary extended GCD on numbers in its
working space, so that the code of its several inversions is emitted once.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec VG.Spec.RsaKeyGen
open VG.Spec.Rsa (bytesAt os2ip)

/-- The octets of each number of `vg_rsa_keygen_inverse`'s working space for a
length of `len` octets: `8 ⌈len / 8⌉`. -/
def inverseBytes (len : Nat) : Nat := 8 * ((len + 7) / 8)

/-- Number `j` of the working space at `ws` for a length of `len` octets: the
`inverseBytes len` octets at `ws + 160 + j (inverseBytes len + 8)`, least
significant first. The first 160 octets are a header the function may use,
and the 8 octets after each number are working space too. -/
def inverseNum (m : Mem) (ws : Addr) (len j : Nat) : Nat :=
  os2ip (bytesAt m (ws + BitVec.ofNat 64 (160 + j * (inverseBytes len + 8))) (inverseBytes len)).reverse

/-- The octets of the working space `vg_rsa_keygen_inverse` may write, by
offset: the header's octets 100 to 111, and the numbers 0 to 7 and 11 to 14,
each with the 8 octets after it. -/
def inverseWrites (len i : Nat) : Prop :=
  (100 ≤ i ∧ i < 112) ∨ ∃ j, (j < 8 ∨ (11 ≤ j ∧ j < 15)) ∧
    160 + j * (inverseBytes len + 8) ≤ i ∧ i < 160 + (j + 1) * (inverseBytes len + 8)

/-- `vg_rsa_keygen_inverse(ws: *mut u64, ws_len: usize, len: usize)`. -/
def inverseSig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("len", .int .usize true)]

/-- With `a` the number 0 of the working space and `m` the number 8, odd and
more than 1, and the numbers 1, 2, 3, 9 and 10 `m`, 1, 0, `2^(8 B) − m` and
0 (`B = inverseBytes len`): leaves `gcd(a, m)` in the number 1, and in the
number 3 an `x < m` with `x a ≡ gcd(a, m) (mod m)`, which is `a⁻¹ mod m`
when the gcd is 1; it writes nothing else but the octets `inverseWrites`
names. Constant time. -/
def inverseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inverseSig.contract A
    (pre := fun ws wsLen len m =>
      1 ≤ len.toNat ∧ len.toNat ≤ 1024 ∧
        160 + 15 * (inverseBytes len.toNat + 8) ≤ 8 * wsLen.toNat ∧
        inverseNum m ws len.toNat 8 % 2 = 1 ∧ 1 < inverseNum m ws len.toNat 8 ∧
        inverseNum m ws len.toNat 1 = inverseNum m ws len.toNat 8 ∧
        inverseNum m ws len.toNat 2 = 1 ∧ inverseNum m ws len.toNat 3 = 0 ∧
        inverseNum m ws len.toNat 9 + inverseNum m ws len.toNat 8 = 2 ^ (8 * inverseBytes len.toNat) ∧
        inverseNum m ws len.toNat 10 = 0)
    (post := fun ws wsLen len m m' _ =>
      (∀ i, i < 8 * wsLen.toNat → ¬ inverseWrites len.toNat i →
        m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)) ∧
      inverseNum m' ws len.toNat 1 = Nat.gcd (inverseNum m ws len.toNat 0) (inverseNum m ws len.toNat 8) ∧
        (inverseNum m ws len.toNat 8 : Int) ∣
          (inverseNum m' ws len.toNat 3 : Int) * inverseNum m ws len.toNat 0 - inverseNum m' ws len.toNat 1 ∧
        inverseNum m' ws len.toNat 3 < inverseNum m ws len.toNat 8)
    (stack := stack)

end VG.Proof.RsaKeyGen
