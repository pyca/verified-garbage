module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportStep
import VerifiedGarbage.Proof.Framework.Offset

/-! # Each native import step extends the reversed-word prefix -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Import

theorem StateAt.step {g : Geometry} {s₀ s : State} (C : Context g s₀) {i : Nat}
    (S : StateAt g s₀ i s) (index : i < g.count) :
    WP isa (.block step) s fun t => StateAt g s₀ (i + 1) t ∧ t.zf = some (decide (i + 1 = g.count)) := by
  have source : s.ea (at_ .esi) = g.sourceAt i := by
    change addr (s.gpr .esi) 0 = _
    rw [S.source]
    exact source_address C index
  have destination : s.ea (at_ .ebx) = g.destAt i := by
    change addr (s.gpr .ebx) 0 = _
    rw [S.destination]
    exact dest_address C index
  have hr := C.readable i index
  have hw := C.writable i index
  rw [← S.keeps.2.1, ← S.keeps.2.2] at hr
  rw [← S.keeps.2.2] at hw
  refine WP.mono (step_ok s _ _ source destination hr hw) fun t ⟨M, Ps, Pd, Pc, Z, K⟩ => ?_
  have input : s.mem.readW (g.sourceAt i) 32 = s₀.mem.readW (g.sourceAt i) 32 :=
    S.frame.readW (r := g.sourceRegion) (w := 32)
      (Offset.contains_base _ (by omega) (by have := C.sourceFit; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.separate) (by decide)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, S.keeps.trans K⟩, ?_⟩
  · rw [Ps, S.source]
    unfold Geometry.sourcePtr
    rw [BitVec.add_assoc]
    change g.src + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  · rw [Pd, S.destination]
    unfold Geometry.destPtr
    rw [BitVec.sub_sub]
    change _ - (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  · rw [Pc, S.count]
    change BitVec.ofNat 32 (g.count - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j copied
    rw [M]
    by_cases same : j = i
    · subst j
      rw [Mem.readW_writeW_self32, input]
    · have sep : Mem.Sep (g.destAt j) 4 (g.destAt i) 4 := by
        apply Offset.sep (g.dst.setWidth 64)
        · omega
        · have := C.destFit; omega
        · have := C.destFit; omega
      rw [Mem.readW_writeW_sep sep (by decide)]
      exact S.copied j (by omega)
  · rw [M]
    exact S.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by have := C.destFit; omega))
  · rw [Z, S.count]
    change some (BitVec.ofNat 32 (g.count - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
      ofNat_beq_zero (by have := C.sourceFit; omega)]
    simp only [show g.count - i - 1 = 0 ↔ i + 1 = g.count by omega]

end VG.Proof.RsaKeyGen.X86.Import
