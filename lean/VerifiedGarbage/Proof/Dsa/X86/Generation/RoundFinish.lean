module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundPolicy
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Store the policy status and expose its loop condition. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

private theorem status_equal {status : Nat} (valid : status = 1 ∨ status = 3 ∨ status = 4) :
    ((BitVec.ofNat 32 status - 4) == 0) = decide (status = 4) := by
  rcases valid with rfl | rfl | rfl <;> decide

theorem round_finish {s : State} {base : Addr} {bytes status : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (valid : status = 1 ∨ status = 3 ∨ status = 4)
    (value : s.gpr .eax = BitVec.ofNat 32 status) :
    WP isa (.block roundFinish) s fun t =>
      t.mem = s.mem.writeW (off base primeStatus) (BitVec.ofNat 32 status) ∧
      t.zf = some (decide (status = 4)) ∧ Keeps [] s t := by
  have fit : primeStatus + 4 ≤ bytes := Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity
  unfold roundFinish
  refine wp_storeS (scr.ea (d := primeStatus) (by omega)) (scr.write fit) fun a A =>
    wp_cmpS rfl fun t T zf => WP.block_nil ?_
  refine ⟨?_, ?_, (A.keeps _).trans (T.keeps _)⟩
  · rw [T.mem, A.mem, value]
  · rw [zf, A.gpr, value, status_equal valid]

end VG.Proof.Dsa.X86.Generation
