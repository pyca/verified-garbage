module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Rejecting a trial candidate or advancing to the next divisor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialCheckReject_ok {s t : State} {base : Addr} (C : TrialContext s base t) :
    WP isa (.block trialCheckReject) t fun u => TrialContext s base u ∧
      trialSlot u.mem base 12 = 0 ∧ u.zf = some true := by
  unfold trialCheckReject
  refine wp_movS rfl fun a ta _ => ?_
  have Ca := C.upd ta (by decide)
  refine wp_storeS (Ca.frame.ea (by decide)) (Ca.frame.write (by decide)) fun b ab =>
    wp_cmpi fun u bu _ zu => WP.block_nil ?_
  exact ⟨(Ca.store ab (by decide)).fupd bu,
    by rw [bu.mem, ab.mem, ta.gpr, trialSlot_self], by rw [zu, ab.gpr, ta.gpr]; rfl⟩

theorem trialCheckNext_ok {s t : State} {base : Addr} {i entries : Nat}
    (C : TrialContext s base t) (hi : i < entries) (he : entries ≤ 1024)
    (idx : trialSlot t.mem base 8 = BitVec.ofNat 32 i) :
    WP isa (.block (trialCheckNext entries)) t fun u => TrialContext s base u ∧
      trialSlot u.mem base 8 = BitVec.ofNat 32 (i + 1) ∧
      (∀ d, d + 4 ≤ 8 ∨ 12 ≤ d → d + 4 ≤ 16 → trialSlot u.mem base d = trialSlot t.mem base d) ∧
      u.zf = some (decide (i + 1 = entries)) := by
  unfold trialCheckNext
  refine wp_movS (v := BitVec.ofNat 32 i) (by rw [C.frame.read (by decide), idx]) fun a ta _ =>
    wp_addi fun b ab => ?_
  have Cb := (C.upd ta (by decide)).upd ab (by decide)
  have bx : b.gpr .eax = BitVec.ofNat 32 (i + 1) := by rw [ab.gpr, ta.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  refine wp_storeS (Cb.frame.ea (by decide)) (Cb.frame.write (by decide)) fun c bc =>
    wp_cmpi fun u cu _ zu => WP.block_nil ?_
  refine ⟨(Cb.store bc (by decide)).fupd cu, ?_, ?_, ?_⟩
  · rw [cu.mem, bc.mem, bx, trialSlot_self]
  · intro d hd hd'
    rw [cu.mem, bc.mem, trialSlot_ne _ (by decide) hd' (by omega), ab.mem, ta.mem]
  · rw [zu, bc.gpr, bx, sub_beq (by omega) (by omega)]
end VG.Proof.Dsa.X86.Generation
