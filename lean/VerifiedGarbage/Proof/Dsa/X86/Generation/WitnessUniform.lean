module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Witness
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Combine existing comparison masks into the sampler's uniform flag. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Ecdsa.X86

private theorem mask_flag (p : Prop) [Decidable p] :
    mask32 p >>> 31 = BitVec.ofNat 32 (if p then 1 else 0) := by
  by_cases h : p <;> simp only [mask32, h, ite_true, ite_false] <;> decide

theorem witness_uniform {s : State} {base : Addr} {bytes : Nat} {p q : Prop} [Decidable p] [Decidable q]
    (scr : Scr s base bytes) (fit : witnessUniform + 4 ≤ bytes)
    (stored : s.mem.readW (off base witnessUniform) 32 = mask32 p)
    (eax : s.gpr .eax = mask32 q) :
    WP isa (.block witnessRangeFinish) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (if p ∧ q then 1 else 0) ∧
      w32 t.mem base witnessUniform = (if p ∧ q then 1 else 0) ∧
      t.zf = some (decide (¬ (p ∧ q))) ∧
      Outside base witnessUniform 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold witnessRangeFinish
  refine wp_logicS (.inl rfl) (readSrc_sc scr (d := witnessUniform) (by omega)) fun a A => ?_
  have ea : a.gpr .eax = mask32 (p ∧ q) := by
    rw [A.gpr, eax, stored]
    simp only [ite_true]
    rw [BitVec.and_comm, mask32_and]
  refine wp_shr (by decide) fun b B _ => ?_
  have eb : b.gpr .eax = BitVec.ofNat 32 (if p ∧ q then 1 else 0) := by
    rw [B.gpr, ea, mask_flag]
  have Kb := A.keeps.trans B.keeps
  have SB := scr.of_keeps Kb (by decide)
  refine wp_storeS (SB.ea (d := witnessUniform) (by omega)) (SB.write fit)
    fun c C => wp_cmpS rfl fun t T zf => WP.block_nil ?_
  have et : t.gpr .eax = BitVec.ofNat 32 (if p ∧ q then 1 else 0) := by rw [T.gpr, C.gpr, eb]
  have frame : Outside base witnessUniform 4 s.mem t.mem := by
    rw [T.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scr.nowrap; omega)
  refine ⟨et, ?_, ?_, frame, (Kb.trans (C.keeps _)).trans (T.keeps _)⟩
  · rw [w32, T.mem, C.mem, Mem.readW_writeW_self32, eb]
    by_cases h : p ∧ q <;> simp [h]
  · rw [zf, C.gpr, eb]
    by_cases h : p ∧ q <;> simp [h]

end VG.Proof.Dsa.X86.Generation
