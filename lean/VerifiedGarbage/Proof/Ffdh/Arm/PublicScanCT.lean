module

public import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.PublicScan
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The public-prefix scan follows only the identical public exponent bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.PublicScan
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.PublicScan

structure Input (base src : BitVec 32) (len : Nat) (bs : List Byte) (s : State) : Prop where
  source : Octets base src len bs s
  pointer : s.gpr .r1 = src
  count : s.gpr .r2 = BitVec.ofNat 32 bs.length

theorem enter_ct : RelCT isa (fun _ _ => True) (.block enter) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

theorem leave_ct : RelCT isa (fun _ _ => True) (.block leave) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

private theorem enter_input (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (h : Input base src len bs s) :
    WP isa (.block enter) s (KeyScanState base src len bs) := by
  refine WP.mono (enter_ok s) ?_
  rintro t ⟨⟨ptr,count,_,_,mem⟩,rest⟩
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.source.after_frame frame rest (by simp),ptr.trans h.pointer,count.trans h.count⟩

theorem code_ct {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (positive : 0 < bs.length) (fits : bs.length < 2^32) :
    RelCT isa (fun s t => Input base src len bs s ∧ Input base src len bs t ∧ s.sp = t.sp)
      code (fun _ _ => True) := by
  unfold code
  have scan : RelCT isa
      (fun s t => KeyScanState base src len bs s ∧ KeyScanState base src len bs t ∧ s.sp = t.sp)
      scan (fun _ _ => True) := keyScan_ct positive fits
  exact relCT_chain
    (enter_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => enter_input s h) (fun s h => enter_input s h)
    (scan.seq leave_ct)

end VG.Proof.Ffdh.Arm.PublicScan
