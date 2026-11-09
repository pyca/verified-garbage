module

public import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: `DB ⊕= MGF1(H, dbLen)`

The digest of the seed and the counter at `oDig` (`Dg`), and `min(hLen, x)`
by a mask (`minSel`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)
variable {lo db : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dbv : State → Nat → Byte}

/-- The digest of the seed and the counter at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < h.D, m (sa scr (oDig + i)) = (h.ok.hH.SH.H.hash x).getD i 0

/-- `min(hLen, x)`, by a mask. -/
theorem minSel {x D : Nat} (hx : x < 2 ^ 32) (hD : D < 2 ^ 32) :
    ((BitVec.ofNat 32 x - BitVec.ofNat 32 D) &&&
        (if decide ((BitVec.ofNat 32 x).toNat < (BitVec.ofNat 32 D).toNat) = true then BitVec.allOnes 32 else 0)) +
      BitVec.ofNat 32 D = BitVec.ofNat 32 (min D x) := by
  rw [toNat_ofNat_lt hx, toNat_ofNat_lt hD]
  by_cases e : x < D
  · rw [ite_eq_left (by simp [e]), BitVec.and_allOnes, BitVec.sub_add_cancel, Nat.min_eq_right (by omega_arith)]
  · rw [ite_eq_right (by simp [e]), Nat.min_eq_left (by omega_arith)]
    simp

end VG.Proof.RsaPss.X86
