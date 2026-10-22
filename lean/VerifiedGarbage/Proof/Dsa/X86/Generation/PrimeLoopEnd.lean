module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MillerRabin
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Only the continuation status takes another witness iteration. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

private theorem status_test {status : Nat} (bound : status ≤ 4) :
    ((BitVec.ofNat 32 status - 4) == 0) = decide (status = 4) := by
  rcases (by omega : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 ∨ status = 4) with
    rfl | rfl | rfl | rfl | rfl <;> decide

theorem prime_loop_end {s : State} {base : Addr} {bytes status : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (bound : status ≤ 4)
    (value : s.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 status) :
    WP isa (.block primeLoopEnd) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 status ∧ t.zf = some (decide (status = 4)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  have fit : primeStatus + 4 ≤ bytes := Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity
  unfold primeLoopEnd
  refine wp_movS (readSrc_sc scr (d := primeStatus) (by omega)) fun a A _ =>
    wp_cmpS rfl fun t T zf => WP.block_nil ?_
  refine ⟨by rw [T.gpr, A.gpr, value], ?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [zf, A.gpr, value, status_test bound]

end VG.Proof.Dsa.X86.Generation
