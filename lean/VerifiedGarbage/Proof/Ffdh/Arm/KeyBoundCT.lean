module

meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundArgs
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundArgs
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
meta import VerifiedGarbage.Proof.Ffdh.Arm.QTest

/-! The complete bound selection, scan, and saved mask have public traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyBoundSelect_ct {p : Inputs} {slots : List Nat} (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ (.block [.ldrSp .r4 60]) (.block [.ldrSp .r4 24])) (fun _ _ => True) := by
  let Q := fun s : State => s.z = !p.hasQ
  have tests := qTest_ct.mono (P' := fun (s t : State) => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : Context p slots s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q :=
    WP.mono (qTest_ok s h h28 h32) (fun _ h => h.1.1)
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (.block [.ldrSp .r4 60]) (.block [.ldrSp .r4 24])) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by change s.z = !p.hasQ at h; simp only [eval, h, Bool.not_not])
    · intro _; exact (loadStack_ct .r4 60).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
    · intro _; exact (loadStack_ct .r4 24).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests wp wp branches

theorem keyBoundArgs_ct {p : Inputs} {slots : List Nat} (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundArgs (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundArgs
  exact (relCT_keep_sp (keyBoundSelect_ct h28 h32) (fun _ _ h => h.2.2)).seq
    ((loadStack_ct .r6 32).mono (fun _ _ h => h) (fun _ _ _ => trivial))

theorem keyBoundTail_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear ++ VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave)) (fun _ _ => True) := by
  have smear : RelCT isa (fun _ _ => True) (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  have save : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) (fun _ _ => True) := by
    change RelCT isa _ (.block ([.addSp .r12 0] ++ [.str .r6 .r12 20, .str .r3 .r12 68])) _
    have stores : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
        (.block [.str .r6 .r12 20, .str .r3 .r12 68]) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
      intro s t h
      apply Taint.agree_ofRegs
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1
    exact RelCT.block_append (stackAddr_ct.seq stores)
  exact RelCT.block_append ((relCT_keep_sp (smear.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun _ _ h => h)).seq save)

theorem keyBound_ct {p : Inputs} {slots : List Nat}
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound (fun _ _ => True) := by
  have wp (s : State) (h : Context p slots s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundArgs s
        (KeyScanState p.base p.boundSource p.len p.boundOctets) := by
    refine WP.mono (keyBoundArgs_ok s h h24 h28 h32 h60) ?_
    rintro t ⟨⟨ptr, count, mem⟩, rest⟩
    have context := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
    exact ⟨context.boundBytes, ptr, by rw [p.boundOctetsLength]; exact count⟩
  have scan := keyScan_ct (base := p.base) (src := p.boundSource) (len := p.len)
    (by rw [p.boundOctetsLength]; have := p.minLength; omega)
    (by rw [p.boundOctetsLength]; have := p.maxLength; omega)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound
  exact relCT_chain (keyBoundArgs_ct h28 h32) wp wp
    ((relCT_keep_sp scan (fun _ _ h => h.2.2)).seq keyBoundTail_ct)

end VG.Proof.Ffdh.Arm
