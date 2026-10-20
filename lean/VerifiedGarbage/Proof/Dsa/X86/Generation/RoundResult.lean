module
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundEffects

/-! # Accepting an initial terminal residue and returning the round result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem roundAccept_ok {base : Addr} {n m size : Nat} {s : State} (R : RoundReady base n m size s) :
    WP isa (.block roundAccept) s fun t => RoundReady base n m size t ∧
      t.mem.readW (off base roundStatus) 32 = 1 ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
  unfold roundAccept
  refine wp_movS rfl fun a sa _ => ?_
  have K : Keeps clob s a := sa.keeps.mono (by decide)
  have scr := R.context.scr.of_keeps K (by decide)
  refine wp_storeS (scr.ea (by have := R.room; omega)) (scr.write R.room) fun t at' => WP.block_nil ?_
  have O : Outside base roundStatus 4 s.mem t.mem := by
    rw [at'.mem, sa.mem]
    exact writeW32_outside _ _ _ (by have := R.context.scr.nowrap; have := R.room; omega)
  have K' := K.trans (at'.keeps _)
  exact ⟨R.control (.inr rfl) O K' (by decide) (by decide),
    by rw [at'.mem, Mem.readW_writeW_self32, sa.gpr], roundWrites_control O (.inr rfl), K'⟩

theorem roundCountTest_ok {base : Addr} {n m size k : Nat} {s : State} (R : RoundReady base n m size s)
    (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (.block roundCountTest) s fun t => t.zf = some (decide (k = 0)) ∧ t.mem = s.mem ∧ Keeps clob s t := by
  unfold roundCountTest
  have room : roundCount + 4 ≤ size := by have := R.room; unfold roundCount roundStatus at *; omega
  refine wp_movS (v := BitVec.ofNat 32 k) (by rw [readSrc_sc R.context.scr room, count]) fun a sa _ =>
    wp_cmpi fun t aft _ zt => WP.block_nil ?_
  refine ⟨?_, aft.mem.trans sa.mem, (sa.keeps.mono (by decide)).trans (aft.keeps _)⟩
  rw [zt, sa.gpr]
  change some (BitVec.ofNat 32 k - BitVec.ofNat 32 0 == (0 : BitVec 32)) = _
  rw [sub_beq bound (by decide)]

theorem roundResult_ok {base : Addr} {n m size : Nat} {s : State} (R : RoundReady base n m size s) :
    WP isa (.block roundResult) s fun t =>
      t.gpr .eax = s.mem.readW (off base roundStatus) 32 &&& 1 ∧ t.mem = s.mem ∧ Keeps clob s t := by
  unfold roundResult
  refine wp_movS (readSrc_sc R.context.scr R.room) fun a sa _ => wp_logicS (.inl rfl) rfl fun t at' => WP.block_nil ?_
  exact ⟨by rw [at'.gpr, sa.gpr]; rfl, at'.mem.trans sa.mem, (sa.keeps.mono (by decide)).trans (at'.keeps.mono (by decide))⟩

theorem mask32_low (b : Bool) : mask32 (b = true) &&& 1 = BitVec.ofNat 32 b.toNat := by
  cases b <;> decide +kernel
end VG.Proof.Dsa.X86.Generation
