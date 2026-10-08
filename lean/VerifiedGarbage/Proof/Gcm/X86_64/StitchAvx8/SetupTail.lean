import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Seeds
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Memory
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Bump

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

def counterTail : List Instr :=
  (List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7) ++
  (List.range 8).flatMap prepCounter ++ [.alu32 .add .r8 (.imm 8)]

theorem counterTail_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) :
    WP isa (.block counterTail) s fun t => Env s₀ P t ∧ Templates s₀ 0 0 t.mem ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ Frame [counterR s₀] s.mem t.mem := by
  rw [counterTail, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyTemplates_ok hp s hE hC 8 (by decide)) fun u ⟨hu, hc, hf, hm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedTemplates_ok hp u hu (by
    intro i hi; simpa only [Nat.not_lt_zero, ite_false, Nat.repeat] using hc i hi)
    (by rw [hf.gpr .r8 (by decide)]; exact hv) 8 (by decide)) fun v ⟨hvE, hvT, hvF, hvM⟩ => ?_
  refine WP.mono (bump_ok v) fun t ⟨ht8, htG, htM, htX, htR, htW⟩ => ?_
  refine ⟨hvE.move (fun r _ _ h8 _ => htG r h8) htM htR htW,
    htM ▸ hvT.done, ?_, ?_, ?_, htM ▸ hm.trans hvM⟩
  · rw [ht8, hvF.gpr .r8 (by decide), hf.gpr .r8 (by decide), hv]
  · intro r hax h8; rw [htG r h8, hvF.gpr r hax, hf.gpr r hax]
  · intro r l; rw [htX, hvF.lane, hf.lane]

end VG.Proof.Gcm.X86_64.StitchAvx8
