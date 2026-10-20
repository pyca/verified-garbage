module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Initialize the public trial-loop control words -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialCheckEntry_ok {s t : State} {base : Addr} {input table : BitVec 32}
    (C : TrialContext s base t) (si : t.gpr .esi = input) (di : t.gpr .edi = table) :
    WP isa (.block trialCheckEntry) t fun u => TrialContext s base u ∧
      trialSlot u.mem base 0 = input ∧ trialSlot u.mem base 4 = table ∧
      trialSlot u.mem base 8 = 0 ∧ trialSlot u.mem base 12 = 1 := by
  unfold trialCheckEntry
  refine wp_storeS (C.frame.ea (by decide)) (C.frame.write (by decide)) fun a ta => ?_
  have Ca := C.store ta (by decide)
  refine wp_storeS (Ca.frame.ea (by decide)) (Ca.frame.write (by decide)) fun b ab =>
    wp_movS rfl fun c bc _ => ?_
  have Cc := (Ca.store ab (by decide)).upd bc (by decide)
  refine wp_storeS (Cc.frame.ea (by decide)) (Cc.frame.write (by decide)) fun d cd =>
    wp_movS rfl fun e de _ => ?_
  have Ce := (Cc.store cd (by decide)).upd de (by decide)
  refine wp_storeS (Ce.frame.ea (by decide)) (Ce.frame.write (by decide)) fun u eu => WP.block_nil ?_
  have mem : u.mem = (((t.mem.writeW (off base 0) input).writeW (off base 4) table).writeW
      (off base 8) (0 : BitVec 32)).writeW (off base 12) (1 : BitVec 32) := by
    rw [eu.mem, de.gpr, de.mem, cd.mem, bc.gpr, bc.mem, ab.mem, ta.gpr, di, ta.mem, si]
  refine ⟨Ce.store eu (by decide), ?_, ?_, ?_, ?_⟩
  · rw [mem, trialSlot_ne _ (by decide) (by decide) (by decide),
      trialSlot_ne _ (by decide) (by decide) (by decide), trialSlot_ne _ (by decide) (by decide) (by decide), trialSlot_self]
  · rw [mem, trialSlot_ne _ (by decide) (by decide) (by decide),
      trialSlot_ne _ (by decide) (by decide) (by decide), trialSlot_self]
  · rw [mem, trialSlot_ne _ (by decide) (by decide) (by decide), trialSlot_self]
  · rw [mem, trialSlot_self]
end VG.Proof.Dsa.X86.Generation
