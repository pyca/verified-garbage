module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Tape status and exhaustion preserve the persistent search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem tapeStatus_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block tapeStatus) s fun t =>
      t.zf = some (words 19 == 3) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold tapeStatus
  refine wp_movS (F.readWord R (by decide : 19 < 37)) fun a sa _ =>
    wp_cmpi fun t at' _ zt => WP.block_nil ?_
  refine ⟨?_, at'.mem.trans sa.mem, sa.keeps.trans (at'.keeps _)⟩
  rw [zt, sa.gpr]
  change some (words 19 - 3 == (0 : BitVec 32)) = _
  by_cases h : words 19 = 3
  · simp [h]
  · have hsub : words 19 - 3 ≠ 0 := by
      intro eq
      have he := congrArg (fun v : BitVec 32 => v + 3) eq
      rw [BitVec.sub_add_cancel] at he
      exact h he
    simp only [beq_eq_false_iff_ne.mpr hsub, beq_eq_false_iff_ne.mpr h]

theorem tapeExhausted_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block (frameStatus 3 ++ ([.mov .eax (.imm 1), .alu .cmp .eax (.imm 0)] : List Instr))) s fun t =>
      t.zf = some false ∧ SearchFrame t base ∧ FrameWords t.mem base (frameUpdate words 19 3) ∧
      Outside base 76 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold frameStatus
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_storeS (Fa.ea (by decide : 19 < 37)) (Fa.writable (by decide : 19 < 37)) fun b ab =>
    wp_movS rfl fun c bc _ => wp_cmpi fun t ct _ zt => WP.block_nil ?_
  have K := ((sa.keeps.trans (ab.keeps _)).trans bc.keeps).trans (ct.keeps _)
  have mem : t.mem = s.mem.writeW (off base 76) (3 : BitVec 32) := by
    rw [ct.mem, bc.mem, ab.mem, sa.gpr, sa.mem]; rfl
  refine ⟨by rw [zt, bc.gpr]; rfl, F.keeps K (by decide), ?_, ?_, K⟩
  · rw [mem]; exact R.write (by decide : 19 < 37) 3
  · rw [mem]; exact writeW32_outside _ _ _ (by decide)
end VG.Proof.Dsa.X86.Generation
