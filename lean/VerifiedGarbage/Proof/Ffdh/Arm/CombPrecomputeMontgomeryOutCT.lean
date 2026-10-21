module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState

/-! Serializing the public modulus/R-squared prefix uses fixed public addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem montgomeryOut_ct {p : Inputs} {sp : BitVec 32} :
    RelCT isa (fun s t => Memory p sp s ∧ Memory p sp t ∧ s.sp=t.sp)
      VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut (fun _ _ => True) := by
  have pos := p.width.1
  let dst := p.output+BitVec.ofNat 32 24
  have args (s : State) (h : Memory p sp s) :
      WP isa (.block [.ldrSp .r4 4,.dp .add .r4 .r4 (.imm 24)]) s
        (ExportState p.base dst p.len p.w (16*p.w)) := by
    have size : 24+16*p.w≤bytes p := by
      simp only [bytes,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
        Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries]
      change 24+16*p.w≤8*(3+(2*p.w+32*p.w))
      omega
    have dstAddr : State.addr dst=off (State.addr p.output) 24 := addr_add (by have := h.output.fits; omega)
    have dstNat : dst.toNat=p.output.toNat+24 := by
      dsimp [dst]
      change (p.output.toNat+24)%2^32=_
      exact Nat.mod_eq_of_lt (by have := h.output.fits; omega)
    refine WP.mono (montgomeryOutArgs_ok s h) ?_
    rintro t ⟨⟨out,ptr,mem⟩,rest⟩
    refine ⟨h.ready.workspace.congr rest.wr,by rw [mem]; exact h.ready.layout,
      by rw [mem]; exact h.ready.width,ptr,out,by omega,?_,?_,?_⟩
    · rw [dstNat]
      have := h.output.fits
      omega
    · rw [rest.wr,dstAddr]
      exact CallLay.inRegions_sub h.output.writable size (by have := h.output.fits; omega)
    · rw [dstAddr]
      exact h.workspaceSeparate.sub_right (Offset.sub_base _ size)
  have add : RelCT isa (fun _ _ => True) (.block [.dp .add .r4 .r4 (.imm 24)]) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have argsCT := RelCT.block_append ((loadStack_ct .r4 4).seq (add.mono (fun _ _ _ => trivial) (fun _ _ h => h)))
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut
  exact relCT_chain (argsCT.mono (fun _ _ h => h.2.2) (fun _ _ h => h)) args args
    ((relCT_keep_sp (precomputeOut_ct.mono (fun _ _ h => ⟨h.1,h.2.1⟩) (fun _ _ h => h))
      (fun _ _ h => h.2.2)).seq ((loadStack_ct .r0 0).mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.CombBuilder
