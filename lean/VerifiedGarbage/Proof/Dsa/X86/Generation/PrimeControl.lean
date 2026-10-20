module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Prime-test status stores and whole-draw availability checks -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem primeMark_ok {s : State} {base : Addr} {size status : Nat} (S : Scr s base size)
    (room : primeStatus + 4 ≤ size) :
    WP isa (.block (primeMark status)) s fun t =>
      t.mem = s.mem.writeW (off base primeStatus) (BitVec.ofNat 32 status) ∧
      Outside base primeStatus 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold primeMark
  refine wp_movS rfl fun a sa _ => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write room) fun t at' => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off base primeStatus) (BitVec.ofNat 32 status) := by rw [at'.mem, sa.gpr, sa.mem]
  exact ⟨mem, by rw [mem]; exact writeW32_outside _ _ _ (by have := S.nowrap; omega), sa.keeps.trans (at'.keeps _)⟩

theorem primeTapeCheck_ok {s : State} {base : Addr} {size len used draw : Nat}
    (S : Scr s base size) (room : primeTapeLen + 4 ≤ size)
    (used_le : used ≤ len) (len32 : len < 2 ^ 32) (draw32 : draw < 2 ^ 32)
    (length : s.mem.readW (off base primeTapeLen) 32 = BitVec.ofNat 32 len)
    (consumed : s.mem.readW (off base primeUsed) 32 = BitVec.ofNat 32 used) :
    WP isa (.block (primeTapeCheck draw)) s fun t =>
      t.cf = some (decide (len - used < draw)) ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  unfold primeTapeCheck
  refine wp_movS (v := BitVec.ofNat 32 len) (by rw [readSrc_sc S room, length]) fun a sa _ => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  have ur : primeUsed + 4 ≤ size := by unfold primeUsed primeTapeLen at *; omega
  refine wp_subS (v := BitVec.ofNat 32 used) (by rw [readSrc_sc Sa ur, sa.mem, consumed]) fun b ab _ =>
    wp_cmpi fun t bt ct _ => WP.block_nil ?_
  refine ⟨?_, by rw [bt.mem, ab.mem, sa.mem], (sa.keeps.trans ab.keeps).trans (bt.keeps _)⟩
  rw [ct, ab.gpr, sa.gpr, sub_ofNat used_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : len - used < 2 ^ 32), Nat.mod_eq_of_lt draw32]
end VG.Proof.Dsa.X86.Generation
