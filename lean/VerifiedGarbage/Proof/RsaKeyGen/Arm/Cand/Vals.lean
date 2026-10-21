module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Base
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A candidate on ARMv7: the numbers, as the specification has them

The candidate's octets `xB` (the first `out_len` of `rand`), its number `xv`
and the candidate `cv`; octets of `rand` from an offset (`seg_bytesAt`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm

/-- The candidate's octets, their number, and the candidate. -/
abbrev xB (P : CP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.nP) P.L
def xv (P : CP) (σ : State) : Nat := Spec.Rsa.os2ip (xB P σ)
def cv (P : CP) (σ : State) : Nat := Spec.RsaKeyGen.candidate (8 * P.L) (xv P σ)

theorem seg_bytesAt (m : Mem) (p : Addr) {a n k : Nat} (h : a + n ≤ k) :
    VG.Proof.RsaKeyGen.seg (Spec.Rsa.bytesAt m p k) a n = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) n :=
  VG.Proof.RsaKeyGen.seg_bytesAt m p h

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n :=
  VG.Proof.RsaKeyGen.rand_bytes_length m p n

section
variable {P : CP} {σ : State}

theorem xB_seg (h : P.L ≤ P.rl) : xB P σ = VG.Proof.RsaKeyGen.seg (rB P σ) 0 P.L := by
  rw [seg_bytesAt _ _ (by omega), BitVec.add_zero]

theorem xv_lt (P : CP) (σ : State) : xv P σ < 2 ^ (8 * P.L) := by
  have := VG.Proof.Rsa.lt_of_os2ip (xB P σ)
  rw [bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

theorem cv_shape (pre : In P σ) : PrimeShape (8 * P.L) (cv P σ) :=
  VG.Proof.RsaKeyGen.candidate_shape (by have := pre.k1; omega) _

end

end VG.Proof.RsaKeyGen.Arm.Cand
