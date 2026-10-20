module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # Persistent search slots remain outside callees' temporary stack frames -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

structure SearchFrame (s : State) (base : Addr) : Prop where
  esp : (s.gpr .esp).setWidth 64 = base
  write : (⟨base, frameBytes⟩ : Region) ∈ s.wr
  nowrap : base.toNat + frameBytes ≤ 2 ^ 32

theorem SearchFrame.esp_toNat {s : State} {base : Addr} (F : SearchFrame s base) :
    (s.gpr .esp).toNat = base.toNat := by
  rw [← F.esp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

theorem SearchFrame.ea {s : State} {base : Addr} (F : SearchFrame s base) {i : Nat} (hi : i < 37) :
    s.ea (frameSlot i) = off base (4 * i) := by
  change addr (s.gpr .esp) (4 * i) = _
  rw [addr_eq (by have := F.nowrap; have := F.esp_toNat; unfold frameBytes at *; omega), F.esp]

theorem SearchFrame.writable {s : State} {base : Addr} (F : SearchFrame s base) {i : Nat} (hi : i < 37) :
    InRegions s.wr (off base (4 * i)) 4 :=
  ⟨⟨base, frameBytes⟩, F.write, Offset.contains_base _ (by unfold frameBytes; omega) (by omega)⟩

theorem SearchFrame.readSlot {s : State} {base : Addr} (F : SearchFrame s base) {i : Nat} (hi : i < 37) :
    readSrc s (.mem (frameSlot i)) = some (s.mem.readW (off base (4 * i)) 32) := by
  show s.load32 (s.ea (frameSlot i)) = _
  rw [F.ea hi, State.load32]
  apply ite_eq_left
  obtain ⟨r, hr, hc⟩ := F.writable hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem SearchFrame.keeps {s t : State} {base : Addr} {rs : List Reg} (F : SearchFrame s base)
    (K : Keeps rs s t) (sp : .esp ∉ rs) : SearchFrame t base :=
  ⟨by rw [K.1 _ sp]; exact F.esp, by rw [K.2.2]; exact F.write, F.nowrap⟩
end VG.Proof.Dsa.X86.Generation
