module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Bounded complete-chunk checks and cursor reset for parameter tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem tapeReset_ok {s : State} {base : Addr} {words : Nat → BitVec 32} (F : SearchFrame s base)
    (R : FrameWords s.mem base words) (slots : TapeSlots) (hi : slots.used < 37) :
    WP isa (.block (tapeReset slots)) s fun t => SearchFrame t base ∧
      FrameWords t.mem base (frameUpdate words slots.used 0) ∧
      Outside base (4 * slots.used) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold tapeReset
  refine wp_movS rfl fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_storeS (Fa.ea hi) (Fa.writable hi) fun t at' => WP.block_nil ?_
  have K := sa.keeps.trans (at'.keeps [.eax])
  have mem : t.mem = s.mem.writeW (off base (4 * slots.used)) (0 : BitVec 32) := by rw [at'.mem, sa.gpr, sa.mem]
  exact ⟨F.keeps K (by decide), by rw [mem]; exact R.write hi 0,
    by rw [mem]; exact writeW32_outside _ _ _ (by omega), K⟩

theorem chunkCheck_ok {s : State} {base : Addr} {words : Nat → BitVec 32} {used total width : Nat}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) (slots : TapeSlots)
    (usedSlot : slots.used < 37) (totalSlot : slots.total < 37)
    (usedLe : used ≤ total) (totalBound : total < 2 ^ 32) (widthBound : width < 2 ^ 32)
    (usedValue : words slots.used = BitVec.ofNat 32 used) (totalValue : words slots.total = BitVec.ofNat 32 total) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold chunkCheck
  refine wp_movS (v := BitVec.ofNat 32 total) (by rw [F.readWord R totalSlot, totalValue]) fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_movS (v := BitVec.ofNat 32 used) (by rw [Fa.readSlot usedSlot, sa.mem, R _ usedSlot, usedValue])
    fun b ab _ => wp_subS rfl fun c bc _ => wp_cmpi fun t ct cf _ => WP.block_nil ?_
  refine ⟨?_, ct.mem.trans (bc.mem.trans (ab.mem.trans sa.mem)),
    (((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bc.keeps.mono (by decide))).trans (ct.keeps _)⟩
  rw [cf, bc.gpr, ab.gpr, ab.other _ (by decide), sa.gpr, sub_ofNat usedLe,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 32), Nat.mod_eq_of_lt widthBound]
end VG.Proof.Dsa.X86.Generation
