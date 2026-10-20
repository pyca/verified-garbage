module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialCheck
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # The trial loop's four-word control frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure TrialFrame (s : State) (base : Addr) : Prop where
  esp : (s.gpr .esp).setWidth 64 = base
  wr : (⟨base, 16⟩ : Region) ∈ s.wr
  fit : base.toNat + 16 ≤ 2 ^ 32

def trialSlot (m : Mem) (base : Addr) (d : Nat) : BitVec 32 := m.readW (off base d) 32

theorem TrialFrame.espNat {s : State} {base : Addr} (F : TrialFrame s base) : (s.gpr .esp).toNat = base.toNat := by
  rw [← F.esp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]

theorem TrialFrame.ea {s : State} {base : Addr} (F : TrialFrame s base) {d : Nat} (hd : d < 16) :
    s.ea (trialSp d) = off base d := by
  change addr (s.gpr .esp) d = _
  rw [addr_eq (by have := F.espNat; have := F.fit; omega), F.esp]

theorem TrialFrame.write {s : State} {base : Addr} (F : TrialFrame s base) {d n : Nat} (hd : d + n ≤ 16) :
    InRegions s.wr (off base d) n := ⟨_, F.wr, Offset.contains_base _ hd (by omega)⟩

theorem TrialFrame.read {s : State} {base : Addr} (F : TrialFrame s base) {d : Nat} (hd : d + 4 ≤ 16) :
    readSrc s (.mem (trialSp d)) = some (trialSlot s.mem base d) := by
  show s.load32 (s.ea (trialSp d)) = _
  rw [F.ea (by omega)]
  have read : InRegions (s.rd ++ s.wr) (off base d) 4 :=
    ⟨_, List.mem_append_right _ F.wr, Offset.contains_base _ hd (by omega)⟩
  simp only [State.load32, read, ite_true, trialSlot]

theorem TrialFrame.keeps {s t : State} {base : Addr} {rs : List Reg} (F : TrialFrame s base)
    (K : Keeps rs s t) (hsp : Reg.esp ∉ rs) : TrialFrame t base :=
  ⟨by rw [K.1 _ hsp]; exact F.esp, by rw [K.2.2]; exact F.wr, F.fit⟩

theorem trialSlot_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 32) :
    trialSlot (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self32 _ _ _

theorem trialSlot_ne {m : Mem} {base : Addr} {d e : Nat} (v : BitVec 32)
    (hd : d + 4 ≤ 16) (he : e + 4 ≤ 16) (apart : d + 4 ≤ e ∨ e + 4 ≤ d) :
    trialSlot (m.writeW (off base d) v) base e = trialSlot m base e :=
  Mem.readW_writeW_sep (Offset.sep base (apart.symm) (by omega) (by omega)) (by decide)

theorem trialFrame_store {m : Mem} {base : Addr} {d : Nat} (hd : d + 4 ≤ 16) (v : BitVec 32) :
    Frame [⟨base, 16⟩] m (m.writeW (off base d) v) :=
  (Frame.refl _ _).write (by simp) v (Offset.contains_base _ hd (by omega))
end VG.Proof.Dsa.X86.Generation
