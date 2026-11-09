module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: after p's check

In the working space of `Domain/Body.lean`, p in array 0, x's, `y`'s and
`rand`'s addresses in the header's words 8, 10 and 11: the status after
`vg_ffdh_derive_public`'s body (`gkSt`), and the octets outside the working
space (`out_scr`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The status of x: 2 out of range, else 1 if `1 < g^x mod p < p − 1`, else 3. -/
def gkSt (x g p b : Nat) : Nat :=
  if ¬ (0 < x ∧ x < b) then 2 else if 1 < g ^ x % p ∧ g ^ x % p < p - 1 then 1 else 3

/-- What a change at x's `k` octets keeps: the working space. -/
theorem out_scr {X B : Addr} {Z k : Nat} {m m' : Mem} (h : Outside X 0 k m m')
    (hsep : ∀ y, ofs B y < Z → k ≤ ofs X y) : Outside B Z (2 ^ 64) m m' := fun y hy => h y (Or.inr (by
  rcases hy with hy | hy
  · have := hsep y hy; omega
  · have := (y - B).isLt; simp only [ofs] at hy; omega))

end VG.Proof.Ffdh.PPC64LE.GenerateKey
