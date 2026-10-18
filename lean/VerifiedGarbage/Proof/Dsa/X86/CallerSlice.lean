module

public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer

/-! # Readable subcomponents of caller-owned packed buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallerBuffer.slice {s : State} {base : Addr} {size full offset count : Nat} {source dest : Pointer}
    (B : CallerBuffer s base size source full) (hc : 0 < count) (hb : offset + count ≤ full)
    (hp : pointerValue base s dest = pointerValue base s source + BitVec.ofNat 32 offset) :
    CallerBuffer s base size dest count := by
  have F := B.fits
  have off32 : offset < 2 ^ 32 := by omega
  have fit : (pointerValue base s source).toNat + offset < 2 ^ 32 := by omega
  have P : (pointerValue base s dest).setWidth 64 =
      (pointerValue base s source).setWidth 64 + BitVec.ofNat 64 offset := by
    rw [hp]
    exact addr_eq fit
  have N : (pointerValue base s dest).toNat = (pointerValue base s source).toNat + offset := by
    rw [hp, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt off32, Nat.mod_eq_of_lt fit]
  refine ⟨B.room, by rw [N]; omega, ?_, ?_, ?_⟩
  · intro d k hd
    rw [P, Offset.add_add]
    exact B.read (offset + d) k (by omega)
  · rw [P]
    exact B.apart.sub_left (Offset.sub_base _ hb)
  · rw [P]
    exact B.stack.sub_left (Offset.sub_base _ hb)

end VG.Proof.Dsa.X86
