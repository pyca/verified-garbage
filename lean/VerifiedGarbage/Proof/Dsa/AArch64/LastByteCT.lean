module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.OddCheck
import VerifiedGarbage.Proof.Dsa.AArch64.LastByte
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.OddCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.LastByte
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of the final-byte reads in public domain checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lastByte_ct (fp fl : Field) (r : Reg) (pointer : ShapePublic → Addr) (bytes : ShapePublic → List Byte)
    (hptr : ∀ p s, ShapeContext p s → word s.mem p.base fp.offset = pointer p)
    (hlen : ∀ p s, ShapeContext p s → word s.mem p.base fl.offset = BitVec.ofNat 64 (bytes p).length)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block [Core.field .x1 fp, Core.field .x9 fl]) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1, .x9])
      (.block [.subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0]) h₂).isSome = true) :
    RelCT isa (Two ShapeContext) (.block [Core.field .x1 fp, Core.field .x9 fl,
      .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0]) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := [Core.field .x1 fp, Core.field .x9 fl])
    (l₂ := [.subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0])
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x1 = pointer p ∧
    s.gpr .x9 = BitVec.ofNat 64 (bytes p).length) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.x0)) ht₁ ?_) ?_
  · intro p s h
    brun [field_enc fp, field_enc fl, Core.field, h.x0, fieldAddress, hptr p s h, hlen p s h,
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 p.extentBound),
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 p.extentBound)]
  · exact two_taint [.x1, .x9] (pins_of (fun p r => if r = .x1 then pointer p else BitVec.ofNat 64 (bytes p).length) (by
      intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) ht₂

theorem oddCheck_ct : RelCT isa (Two ShapeContext) (.block oddCheck) (fun _ _ => True) := by
  have hp := lastByte_ct .p .pLen .x3 ShapePublic.pPointer ShapePublic.pBytes
    (fun _ _ h => h.pPointer) (fun _ _ h => h.pLength) (by taint_decide) (by taint_decide)
  have hq := lastByte_ct .q .qLen .x2 ShapePublic.qPointer ShapePublic.qBytes
    (fun _ _ h => h.qPointer) (fun _ _ h => h.qLength) (by taint_decide) (by taint_decide)
  have hp' : RelCT isa (Two ShapeContext)
      (.block [Core.field .x1 .p, Core.field .x9 .pLen,
        .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb .x3 .x1 0]) (Two ShapeContext) := by
    refine two_post hp ?_
    intro p s h
    have hi : p.pBytes.length - 1 < p.pBytes.length := by have := p.pPositive; omega
    exact WP.mono (lastByte_ok h.scr h.x0 p.extentBound .p .pLen .x3 h.pPointer h.pLength
      p.pPositive p.pBound (h.pSource.rd _ hi) (h.pSource.val _ hi))
      fun t ⟨_, hm, hk⟩ => h.sameMem hm hk (by decide)
  have hq' : RelCT isa (Two ShapeContext)
      (.block [Core.field .x1 .q, Core.field .x9 .qLen,
        .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb .x2 .x1 0]) (Two BasePublic) := by
    refine two_post (Ψ := fun p s => BasePublic p.base s) hq ?_ |>.mono
      (fun _ _ h => h) (fun _ _ h => ?_)
    · intro p s h
      have hi : p.qBytes.length - 1 < p.qBytes.length := by have := p.qPositive; omega
      exact WP.mono (lastByte_ok h.scr h.x0 p.extentBound .q .qLen .x2 h.qPointer h.qLength
        p.qPositive p.qBound (h.qSource.rd _ hi) (h.qSource.val _ hi))
        fun t ⟨_, _, hk⟩ => (hk.gpr .x0 (by decide)).trans h.x0
    · obtain ⟨p, h1, h2⟩ := h
      exact ⟨p.base, h1, h2⟩
  unfold oddCheck
  rw [List.append_assoc, List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq hp' ?_
  apply RelCT.block_append
  exact RelCT.seq hq' (two_taint [.x0] pins_base (by taint_decide))

end VG.Proof.Dsa.AArch64
