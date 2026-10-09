import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum

/-!
# Constant time of the point arithmetic blocks

## The encoding

The point encoding's inversion calls `vg_gf25519_r32_pow250`, which the
analysis follows (`callTaint₀`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

/-! ## The checks -/

theorem pointEncode_ct {x : BitVec 32} : RelCT isa (CallCTPre x) pointEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ pointEncode h).isSome = true := by
    taint_decide_sum [VG.Proof.X25519.X86.pow250Sum]
  exact VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ h => callTaint₀_agree h) hc

def PowersCTPre (x : BitVec 32) (s t : State) : Prop :=
  PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 24 = wd t.mem x 24

/-- What is public at the loop of doublings of `double16`. -/
def doubleTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi], flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)] }

/-! The body of the loop of doublings, which both `powersBody 1024 16` and
`powersBody 1024 32` run: analysed once, as a summary. -/

taint_summary doubleSum : taint doubleTaint (.block doubleBody)

theorem powersBody16_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 1024 16 true) (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (pointTaint 24) (powersBody 1024 16 true) h).isSome = true := by
    taint_decide_sum [doubleSum]
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ hc
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBody32_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 1024 32 true) (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (pointTaint 24) (powersBody 1024 32 true) h).isSome = true := by
    taint_decide_sum [doubleSum]
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ hc
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBodyLocal_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 5120 16 false) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ (by taint_decide)
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem accumulate16_ct_regs (x : BitVec 32) : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28)
    accumulate16 (fun s t => s.gpr .edi = t.gpr .edi) := by
  have h : RelCT isa (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28) accumulate16 (fun s t => ∀ r ∈ ([.edi] : List Reg), s.gpr r = t.gpr r) := by
    apply ctTaintRegs (τ := pointTaint 28) _ [.edi] (by taint_decide)
    intro s t h
    exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .edi (List.mem_singleton_self _))

theorem accumulate16_ct (x : BitVec 32) : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28)
    accumulate16 (fun _ _ => True) :=
  (accumulate16_ct_regs x).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ed25519.X86
