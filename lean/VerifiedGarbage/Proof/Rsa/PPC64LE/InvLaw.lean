module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-! # The contract of the batched inverse on PPC64LE

`InvLaw`: what `Impl/Rsa/PPC64LE/InvBatch.lean`'s `inverse` does, for its
callers to use without importing the algebra of its proof
(`IbInverse.lean`'s `inverse_ok`); the registration supplies the instance
(`Instances.lean`).

From `x` in array 0 and an odd `m` in array 8, both below `2^(32 n)` for `n`
in `r11` (`1 ≤ n ≤ w`), it leaves `gcd(x, m)` in array 1 and, for `m > 1`,
`y < m` with `y x ≡ gcd(x, m) (mod m)` in array 3, `w` digits each; it writes
only arrays 1–7 and 11–14 and the registers `r0` and `r3`–`r12`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.KeyWorkspace (num)

/-- The arrays the inverse writes. -/
abbrev invBatchArrs : List Nat := [1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14]

/-- The registers the inverse changes. -/
abbrev invBatchRegs : List Reg := [.r10, .r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r11, .r12]

class InvLaw : Prop where
  inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
      (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) {x m : Nat}
      (hx : num s.mem B w 0 = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w 8 = m)
      (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
      WP isa VG.Impl.Rsa.PPC64LE.InvBatch.inverse s fun t => Ws t B Z w N ∧
        KeyWorkspace.Keep B w invBatchArrs [] s.mem t.mem ∧ Keep invBatchRegs s t ∧
        (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
          (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m)

end VG.Proof.Rsa.PPC64LE
