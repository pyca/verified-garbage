module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateArguments
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Populate the isolated cdecl outgoing argument frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem validateOutgoingPrefix_ok {G : GenerationGeometry} {s : State} (count : Nat) (bound : count ≤ 6)
    (sp : s.gpr .esp = G.frame - 24#32) (write : (⟨validateArgsBase G, 24⟩ : Region) ∈ s.wr)
    (regs : ValidateRegs G s) :
    WP isa (.block ((List.range count).map fun i => .store (at_ .esp (4 * i)) (validateReg i))) s fun t =>
      (∀ i < count, t.mem.readW (off (validateArgsBase G) (4 * i)) 32 = validateValue G i) ∧
      Frame [⟨validateArgsBase G, 24⟩] s.mem t.mem ∧ Keeps [] s t := by
  induction count with
  | zero => exact WP.block_nil ⟨by intro i hi; omega, Frame.refl _ _, Keeps.refl _ _⟩
  | succ count ih =>
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega)) fun a ⟨slots, Oa, Ka⟩ => ?_)
    have esp : a.gpr .esp = G.frame - 24#32 := (Ka.1 _ (by decide)).trans sp
    have stack := G.stackSize
    have upper := G.frame.isLt
    have sn : (a.gpr .esp).toNat = G.frame.toNat - 24 := by rw [esp]; exact sub_toNat (by omega)
    have address : a.ea (at_ .esp (4 * count)) = off (validateArgsBase G) (4 * count) := by
      change (a.gpr .esp + BitVec.ofNat 32 (4 * count)).setWidth 64 = _
      rw [show (a.gpr .esp + BitVec.ofNat 32 (4 * count)).setWidth 64 = off ((a.gpr .esp).setWidth 64) (4 * count)
        from addr_eq (by omega), esp]
      rfl
    have writable : InRegions a.wr (off (validateArgsBase G) (4 * count)) 4 :=
      ⟨_, by rw [Ka.2.2]; exact write, Offset.contains_base _ (by omega) (by omega)⟩
    refine wp_storeS address writable fun t at' => WP.block_nil ?_
    have v : a.gpr (validateReg count) = validateValue G count := (Ka.1 _ (by intro h; cases h)).trans (regs count (by omega))
    have mem : t.mem = a.mem.writeW (off (validateArgsBase G) (4 * count)) (validateValue G count) := by rw [at'.mem, v]
    refine ⟨?_, ?_, Ka.trans (at'.keeps [])⟩
    · intro i hi
      by_cases eq : i = count
      · subst i; rw [mem, Mem.readW_writeW_self32]
      · rw [mem, Mem.readW_writeW_sep (Offset.sep (validateArgsBase G) (by omega) (by omega) (by omega)) (by decide)]
        exact slots i (by omega)
    · rw [mem]
      exact Oa.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem validateOutgoing_ok {G : GenerationGeometry} {s : State}
    (sp : s.gpr .esp = G.frame - 24#32) (write : (⟨validateArgsBase G, 24⟩ : Region) ∈ s.wr)
    (regs : ValidateRegs G s) :
    WP isa (.block validateOutgoing) s fun t => ValidateSlots G t ∧
      Frame [⟨validateArgsBase G, 24⟩] s.mem t.mem ∧ Keeps [] s t :=
  validateOutgoingPrefix_ok 6 (Nat.le_refl _) sp write regs
end VG.Proof.Dsa.X86.Generation
