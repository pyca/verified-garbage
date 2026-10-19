module

public import VerifiedGarbage.Proof.Bignum.X86.CrtSave
public import VerifiedGarbage.Proof.Bignum.X86.CrtBodyFrame
public import VerifiedGarbage.TCB.X86.Target

/-! # The complete CRT body preserves saved registers and the return address -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem frame_saved {base out : Addr} {bytes len : Nat} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame (bodyRegions base out bytes len) m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 48 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (S : Saved m (off base) g Crt.savedRegisters) : Saved m' (off base) g Crt.savedRegisters := by
  intro p hp
  have B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
    simp only [Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨off base 32, 16⟩)
    (Offset.contains base B.1 (by omega) (by decide)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [bodyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base base (by decide) (by decide)
  · exact Offset.disjoint base (.inl (by decide)) (by decide) (by omega)
  · exact A.sub_left (Offset.sub_base base (by omega))

theorem frame_full {base out : Addr} {bytes len : Nat} {m m' : Mem}
    (F : Frame (bodyRegions base out bytes len) m m') (low : 48 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩] m m' := by
  apply F.sub
  intro r hr
  simp only [bodyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega)⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩

theorem restored_abi {s t u : State} (R : Restored t u s.gpr Crt.savedRegisters)
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

end VG.Proof.Bignum.X86.Crt
