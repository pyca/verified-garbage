module

public import VerifiedGarbage.Proof.Bignum.X86.PublicSave
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.TCB.X86.Target

/-! # Saved registers and return address survive the public RSA body -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem publicFrame_saved {base out : Addr} {bytes len : Nat} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩] m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 16 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (S : Saved m (off base) g PublicFn.savedRegisters) : Saved m' (off base) g PublicFn.savedRegisters := by
  intro p hp
  have B : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨base, 16⟩) (Offset.contains_base _ B (by omega)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.base_disjoint base (Nat.le_refl 16) (by omega)
  · apply A.sub_left
    intro a ha
    change (a - base).toNat + 1 ≤ bytes
    change (a - base).toNat + 1 ≤ 16 at ha
    omega

theorem publicFrame_full {base out : Addr} {bytes len : Nat} {m m' : Mem}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩] m m') (low : 16 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩] m m' := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega)⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩

theorem publicRestored_abi {s t u : State} (R : Restored t u s.gpr PublicFn.savedRegisters)
    (sp : t.gpr .esp = s.gpr .esp)
    (ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s u := by
  refine ⟨?_, by rw [R.mem]; exact ret⟩
  intro reg hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact (R.other _ (by decide)).trans sp

end VG.Proof.Bignum.X86
