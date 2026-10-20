module
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundState

/-! # The public Miller–Rabin loop counter and terminal branch -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem roundStop_ok {s : State} : WP isa (.block roundStop) s fun t =>
    t.zf = some true ∧ t.mem = s.mem ∧ Keeps clob s t := by
  unfold roundStop
  refine wp_movS rfl fun a sa _ => wp_cmpi fun t aft _ zt => WP.block_nil ?_
  exact ⟨by rw [zt, sa.gpr]; rfl, aft.mem.trans sa.mem, (sa.keeps.mono (by decide)).trans (aft.keeps _)⟩

theorem roundNext_ok {base : Addr} {n m size k : Nat} {s : State} (R : RoundReady base n m size s)
    (hk : 1 ≤ k) (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (.block roundNext) s fun t => RoundReady base n m size t ∧
      t.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (k - 1) ∧
      t.zf = some (decide (k = 1)) ∧ Outside base roundCount 4 s.mem t.mem ∧ Keeps clob s t := by
  have room : roundCount + 4 ≤ size := by have := R.room; unfold roundCount roundStatus at *; omega
  unfold roundNext
  refine wp_movS (v := BitVec.ofNat 32 k) (by rw [readSrc_sc R.context.scr room, count]) fun a sa _ =>
    wp_subi fun b ab _ _ => ?_
  have Kb : Keeps clob s b := (sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))
  have sb := R.context.scr.of_keeps Kb (by decide)
  have value : b.gpr .eax = BitVec.ofNat 32 (k - 1) := by
    rw [ab.gpr, sa.gpr]
    exact sub_ofNat hk
  refine wp_storeS (sb.ea (by omega)) (sb.write room) fun c bc => wp_cmpi fun t ct _ zt => WP.block_nil ?_
  have K : Keeps clob s t := (Kb.trans (bc.keeps _)).trans (ct.keeps _)
  have O : Outside base roundCount 4 s.mem t.mem := by
    rw [ct.mem, bc.mem, ab.mem, sa.mem]
    exact writeW32_outside _ _ _ (by have := R.context.scr.nowrap; omega)
  refine ⟨R.control (.inl rfl) O K (by decide) (by decide), ?_, ?_, O, K⟩
  · rw [ct.mem, bc.mem, Mem.readW_writeW_self32, value]
  · rw [zt, bc.gpr, value]
    change some (BitVec.ofNat 32 (k - 1) - BitVec.ofNat 32 0 == (0 : BitVec 32)) = _
    rw [sub_beq (by omega) (by decide)]
    simp only [show (k - 1 = 0) ↔ k = 1 by omega]
end VG.Proof.Dsa.X86.Generation
