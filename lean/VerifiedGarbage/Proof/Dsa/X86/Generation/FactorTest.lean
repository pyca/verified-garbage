module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! # Count one factor and test the next low bit -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem factorTest_ok {s : State} {base : Addr} {size n count : Nat}
    (S : Scr s base size) (hn : 0 < n) (room : slot n 8 + 8 * n ≤ size)
    (bx : s.gpr .ebx = BitVec.ofNat 32 count) :
    WP isa (.block (factorTest n)) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (count + 1) ∧
      t.zf = some (decide (val32 s.mem base (slot n 8) (2 * n) % 2 = 0)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold factorTest
  refine wp_addi fun a sa => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (d := slot n 8) (by omega)) fun b ab _ =>
    wp_logicS (.inl rfl) rfl fun c bc => wp_cmpi fun t ct _ zt => WP.block_nil ?_
  refine ⟨?_, ?_, by rw [ct.mem, bc.mem, ab.mem, sa.mem], ?_⟩
  · rw [ct.gpr, bc.other _ (by decide), ab.other _ (by decide), sa.gpr, bx]
    exact (BitVec.ofNat_add _ _).symm
  · rw [zt, bc.gpr, ab.gpr, sa.mem, ite_eq_left rfl]
    have lo : s.mem.readW (off base (slot n 8)) 32 &&& 1 = BitVec.ofNat 32 (w32 s.mem base (slot n 8) % 2) := by
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega : w32 s.mem base (slot n 8) % 2 < 2 ^ 32)).symm
    rw [lo]
    change some (BitVec.ofNat 32 (w32 s.mem base (slot n 8) % 2) - BitVec.ofNat 32 0 == (0 : BitVec 32)) = _
    rw [sub_beq (by omega) (by decide)]
    have parity := val32_parity s.mem base (slot n 8) (2 * n - 1)
    rw [show 2 * n - 1 + 1 = 2 * n by omega] at parity
    rw [parity]
  · exact (((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bc.keeps.mono (by decide))).trans (ct.keeps _)
end VG.Proof.Dsa.X86.Generation
