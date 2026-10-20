module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Shared-value encoding uses public output pointers and fixed lengths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure ExportArgsReady (p : Inputs) (s : State) : Prop where
  ready : SmallFnReady p.base p.len p.w 6 s
  dst : s.gpr .r4 = p.output
  count : s.gpr .r6 = BitVec.ofNat 32 p.k

theorem exportResultArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) (fun _ _ => True) := by
  have index : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r2 (.imm 6)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact (RelCT.block_append ((relCT_keep_sp index (fun _ _ h => h)).seq
    (stackLoads_ct [(.r4, 4), (.r6, 32)]))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem exportResult_ct {p : Inputs} {slots : List Nat} (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult (fun _ _ => True) := by
  have args := exportResultArgs_ct.mono
    (P' := fun (s t : State) => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) (h : ImportAtInput p slots s) :
      WP isa (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) s (ExportArgsReady p) := by
    refine WP.mono (exportResultArgs_ok s h.context h4 h32) ?_
    rintro u ⟨⟨index, dst, count, mem⟩, rest⟩
    have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
    exact ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, index⟩, dst, count⟩
  have bytes := (exportBE_ct (base := p.base) (dst := p.output) (len := p.len) (w := p.w)
    (o := 6) (k := p.k) (by decide) (by have := p.minLength; omega)).mono
    (P' := fun (s t : State) => ExportArgsReady p s ∧ ExportArgsReady p t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.1.dst, h.2.1.dst, h.1.count, h.2.1.count⟩)
    (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult
  exact relCT_chain args wp wp bytes

end VG.Proof.Ffdh.Arm
