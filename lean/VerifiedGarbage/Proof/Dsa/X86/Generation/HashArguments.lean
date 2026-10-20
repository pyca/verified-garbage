module
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Register setup for the three streaming-hash calls -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem hashHead_ok {s : State} : WP isa (.block hashHead) s fun t =>
    t.gpr .ebx = s.gpr .ebp + 512#32 ∧ t.mem = s.mem ∧ Keeps [.ebx] s t := by
  unfold hashHead
  refine wp_movS rfl fun a sa _ => wp_addi fun t au => WP.block_nil ⟨?_, ?_, sa.keeps.trans au.keeps⟩
  · rw [au.gpr, sa.gpr]; rfl
  · rw [au.mem, sa.mem]

theorem hashUpdateArgs_ok (len : Nat) {s : State} : WP isa (.block (hashUpdateArgs len)) s fun t =>
    t.gpr .edx = s.gpr .esi ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧ t.gpr .eax = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold hashUpdateArgs
  refine wp_movS rfl fun a sa _ => wp_movS rfl fun b ab _ => wp_movS rfl fun t bt _ => WP.block_nil ?_
  exact ⟨by rw [bt.other _ (by decide), ab.other _ (by decide), sa.gpr],
    by rw [bt.other _ (by decide), ab.gpr], bt.gpr, by rw [bt.mem, ab.mem, sa.mem],
    ((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bt.keeps.mono (by decide))⟩

theorem hashFinalizeArgs_ok (len : Nat) {s : State} : WP isa (.block (hashFinalizeArgs len)) s fun t =>
    t.gpr .edx = s.gpr .edi ∧ t.gpr .eax = BitVec.ofNat 32 len ∧ t.gpr .ecx = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold hashFinalizeArgs
  refine wp_movS rfl fun a sa _ => wp_movS rfl fun b ab _ => wp_movS rfl fun t bt _ => WP.block_nil ?_
  exact ⟨by rw [bt.other _ (by decide), ab.other _ (by decide), sa.gpr],
    by rw [bt.other _ (by decide), ab.gpr], bt.gpr, by rw [bt.mem, ab.mem, sa.mem],
    ((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bt.keeps.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
