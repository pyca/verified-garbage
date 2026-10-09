import VerifiedGarbage.Proof.Ed25519.X86.CallTaint
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Impl.Ed25519.X86.PointMul

/-!
# Constant time of the point arithmetic blocks

The field products are calls of `vg_gf25519_r32_mul`, which the taint
analysis cannot follow, so the code is related run by run: the inversion
by `RF` (`pointAffine_rf`), and the sixteen additions of a batch by `AR`,
with what the analysis knows public across the calls (`esi`, the batch's
index at byte 28; `accumulate16_ar`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519.X86.Field32 (RF RF.agree)

theorem pointEncode_ct (x : BitVec 32) : RelCT isa (RF x) pointEncode (fun _ _ => True) :=
  RelCT.seq (pointAffine_rf x)
    (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => RF.agree h) (by taint_decide))

/-- What the batch's additions need public: `edi` and its index. -/
abbrev τB : VG.X86.Taint.T := ptR [.edi] [28]

/-- ... and the counter `esi`. -/
abbrev τBS : VG.X86.Taint.T := ptR [.edi, .esi] [28]

theorem accumulate16_ar (x : BitVec 32) : RelCT isa (AR x τB) accumulate16 (AR x τB) := by
  have hb := ptR_base [.edi, .esi] [28]
  have body : RelCT isa (AR x τBS) accumulateBody fun s t => isa.eval .ne s = isa.eval .ne t ∧ AR x τBS s t :=
    (block_to x (by decide +kernel) hb).seq <|
      ((block_to x (by decide +kernel) hb).seq <|
        (fieldProg_ar x (by decide +kernel) hb pointAddOps (by decide +kernel)).seq
          (block_to x (by decide +kernel) hb)).seq
      (block_cond x .ne (by decide +kernel) hb)
  exact ((block_to x (τ := τB) (is := [.mov .esi (.imm 16)]) (σ := τBS) (by decide +kernel) hb).seq
    (loop_inv body)).mono (fun _ _ h => h) fun _ _ h => h.weaken (by decide +kernel)

theorem accumulate16_ct_regs (x : BitVec 32) : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x 28 = wd t.mem x 28)
    accumulate16 (fun s t => s.gpr .edi = t.gpr .edi) :=
  (accumulate16_ar x).mono
    (fun _ _ h => ⟨ptR_agree h.1 h.2.1 h.2.2.1 (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact h.1.ctx.edi.trans h.2.1.ctx.edi.symm)
        (fun o ho => by rw [List.mem_singleton.mp ho]; exact ⟨by decide, h.2.2.2.2⟩),
      h.1, h.2.1, h.2.2.2.1⟩)
    fun _ _ h => h.2.1.ctx.edi.trans h.2.2.1.ctx.edi.symm

end VG.Proof.Ed25519.X86
