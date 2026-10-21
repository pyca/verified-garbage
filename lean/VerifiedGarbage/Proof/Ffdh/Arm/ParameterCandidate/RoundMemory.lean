module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Omega

/-! Local controller stores leave all shared primality constants unchanged. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt)

theorem RoundData.after_workspaceEq {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m) (equal : WorkspaceEq (VG.Arm.State.addr base) (8 * capacity) m m') :
    RoundData base capacity w n m' := by
  have headerFits : 128 ≤ 8 * capacity := Nat.le_trans (by
    simp only [arrAt, VG.Spec.Rsa.Mont.hdrBytes]
    omega : 128 ≤ arrAt w 28) h.fits
  refine h.after_reads (fun _ fit => equal.word (bits := 64) (by omega)) ?_ ?_
  · intro q member
    have bound : q < 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have arrayFits := Nat.le_trans (array_end_le (w := w) bound) h.fits
    unfold numAt
    rw [equal.read (arrAt w q) (8 * w) (by omega)]
  · have arrayFits := Nat.le_trans (array_end_le (w := w) (j := 27) (k := 28) (by decide)) h.fits
    exact equal.word (bits := 64) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
