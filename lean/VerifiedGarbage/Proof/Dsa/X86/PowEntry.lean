module

public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # IA-32 shared DSA exponentiation: register spills -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.X86.Spill
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Pow

private theorem slots_fit : Fits 24 slots := by decide

theorem saveMem_outside (m : Mem) (base : Addr) (g : Reg → BitVec 32) :
    Outside base 8 16 m (saveMem m (off base) g slots) := by
  unfold slots saveMem
  exact (((writeW32_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
    ((writeW32_outside _ _ _ (by decide)).mono (by decide) (by decide))).trans
    (((writeW32_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW32_outside _ _ _ (by decide)).mono (by decide) (by decide)))

structure Entry (s : State) (base : Addr) (size : Nat) : Prop where
  arg : InRegions (s.rd ++ s.wr) (argAddr s 0) 4
  base_eq : (VG.X86.arg s 0).setWidth 64 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32
  stk : StkOk (s.gpr .esp) base size

theorem save_ok {s : State} {base : Addr} {size : Nat} (h : Entry s base size) (hz : 24 ≤ size) :
    WP isa (.block save) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr slots ∧
      Outside base 8 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  have nw := h.nowrap
  have ha : (VG.X86.arg s 0).toNat = base.toNat := by
    rw [← h.base_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (VG.X86.arg s 0).isLt; omega)]
  unfold save
  refine wp_ldm rfl h.arg fun u U => ?_
  change WP isa (.block (saveCode .eax slots ++ [.mov .edi (.reg .eax)])) u _
  refine save_ofNat_ok slots slots_fit (by rw [U.gpr]; change (VG.X86.arg s 0).toNat + 24 ≤ _; omega) ?_ ?_
  · intro p hp
    rw [U.gpr]
    change InRegions u.wr (off ((VG.X86.arg s 0).setWidth 64) p.2) 4
    rw [h.base_eq, U.wr]
    exact ⟨_, h.wr, Offset.contains_base base (by have := slots_fit.1 p hp; omega)
      (by have := slots_fit.1 p hp; omega)⟩
  · intro v V
    refine wp_mov fun t T => WP.block_nil ?_
    have M : t.mem = saveMem s.mem (off base) s.gpr slots := by
      rw [T.mem, V.mem, U.mem, U.gpr]
      change saveMem s.mem (off ((VG.X86.arg s 0).setWidth 64)) u.gpr slots = _
      rw [h.base_eq]
      apply saveMem_congr slots s.mem (fun _ _ => rfl)
      intro p hp
      apply U.other
      have : p.1 ≠ Reg.eax := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> decide
      exact this
    refine ⟨⟨?_, ?_, h.nowrap, ?_⟩, ?_, ?_, ?_⟩
    · rw [T.gpr, V.gpr, U.gpr]; exact h.base_eq
    · rw [T.wr, V.wr, U.wr]; exact h.wr
    · rw [T.other _ (by decide), V.gpr, U.other _ (by decide)]; exact h.stk
    · rw [M]; exact saveMem_saved_ofNat _ base _ slots_fit (by decide)
    · rw [M]; exact saveMem_outside _ _ _
    · refine ⟨fun r hr => ?_, by rw [T.rd, V.rd, U.rd], by rw [T.wr, V.wr, U.wr]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [T.other _ hr.2, V.gpr, U.other _ hr.1]

theorem restore_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 32}
    (hs : Scr s base size) (hz : 24 ≤ size) (h : Saved s.mem (off base) g slots) :
    WP isa (.block restore) s fun t => Restored s t g slots := by
  change WP isa (.block (restoreCode .edi ([(.ebx, 8), (.esi, 12), (.ebp, 16)] ++ [(.edi, 20)]) ++ [])) s _
  refine restoreBase_ok _ (by decide) ?_ ?_ (fun _ H => WP.block_nil H)
  · intro p hp
    have hd := slots_fit.1 p hp
    rw [addr_eq (by rw [hs.edi_toNat]; have := hs.nowrap; omega), hs.edi]
    exact hs.read (by omega)
  · intro p hp
    have hd := slots_fit.1 p hp
    rw [addr_eq (by rw [hs.edi_toNat]; have := hs.nowrap; omega), hs.edi]
    exact h p hp

end VG.Proof.Dsa.X86.Pow
