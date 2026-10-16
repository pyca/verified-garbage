module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentScanCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public-exponent validation has no dependency on any secret memory -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem exponentTest_ct : RelCT isa
    (fun s t => s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4) exponentTest (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem exponentCheck_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      exponentCheck (fun _ _ => True) := by
  let Q := fun s : State =>
    s.gpr .r3 = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
    s.gpr .r4 = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb))
  have wp (s : State) (h : ExponentInput ep eb s) : WP isa exponentScan s Q := by
    refine WP.mono (exponentScan_ok s positive h.1.countFit h.1.sourceFit h.1.read h.1.bytes h.2.1 h.2.2) ?_
    rintro t ⟨lo, hi, _, _⟩
    exact ⟨lo, hi⟩
  exact (pair_posts (exponentScan_ct positive) wp).seq
    (exponentTest_ct.mono (fun _ _ h => ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
