module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleHead
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
meta import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment

/-! Only canonical public width bits select the sampler's three immediate shifts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm VG.Proof.Bignum.Arm

theorem mask_ct : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9)
    VG.Impl.Ffdh.Arm.CachedSample.mask (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by simpa using h)

theorem head_ct {p : Inputs} {slots : List Nat} (h52 : 52 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.CachedSample.head) (fun _ _ => True) := by
  have pointer (s : State) (h : Context p slots s) :
      WP isa (.block [.ldrSp .r9 52]) s (fun t => t.gpr .r9 = p.cachedContext) := by
    refine WP.mono (localLoad_ok s .r9 h.locals (by decide : 52 + 4 ≤ 72)) ?_
    rintro t ⟨loaded, _, _⟩
    exact loaded.trans (h.saved 52 h52)
  have first := ((loadStack_ct .r9 52).mono
    (P' := fun (s t : State) => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)).wp
      (fun s t h => ⟨pointer s h.1, pointer t h.2.1⟩)
  have tail : RelCT isa (fun s t => s.gpr .r9 = p.cachedContext ∧ t.gpr .r9 = p.cachedContext)
      (.block [.ldr .r6 .r9 8, .ldr .r10 .r9 0,
        .dp .sub .r10 .r10 (.imm 1), .dp .and .r10 .r10 (.imm 7),
        .mov .r9 (.imm 7), .dp .sub .r9 .r9 (.reg .r10), .mov .r3 (.imm 255)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.trans h.2.symm)
  exact RelCT.block_append (first.seq (tail.mono (fun _ _ h => h.2) (fun _ _ h => h)))

theorem bound_ct {p : Inputs} {slots : List Nat} (h52 : 52 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.CachedSample.bound (fun _ _ => True) := by
  have next (s : State) (h : Context p slots s ∧ CachedGenerationContext p s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CachedSample.head) s (fun t => t.gpr .r9 = shiftCount (bits p)) :=
    WP.mono (head_ok s h.1 h.2 h52) (fun _ post => post.1.2.1)
  have prepared : RelCT isa (fun s t => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.CachedSample.head)
      (fun s t => s.gpr .r9 = t.gpr .r9 ∧ s.sp = t.sp) := ((relCT_keep_sp ((head_ct h52).mono
    (P' := fun (s t : State) => (Context p slots s ∧ CachedGenerationContext p s) ∧
      (Context p slots t ∧ CachedGenerationContext p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨next s h.1, next t h.2.1⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1.trans h.2.2.symm, h.1⟩)
  have masks := relCT_keep_sp (mask_ct.mono
    (P' := fun (s t : State) => s.gpr .r9 = t.gpr .r9 ∧ s.sp = t.sp)
    (fun _ _ h => h.1) (fun _ _ h => h)) (fun _ _ h => h.2)
  have stores : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
      (.block [.str .r6 .r12 20, .str .r3 .r12 68]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1)
  have save : RelCT isa (fun s t => s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) (fun _ _ => True) :=
    RelCT.block_append (stackAddr_ct.seq stores)
  exact prepared.seq (masks.seq save)

end VG.Proof.Ffdh.Arm.CachedSample
