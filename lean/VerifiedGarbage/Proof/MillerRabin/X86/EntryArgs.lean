module

public import VerifiedGarbage.Proof.MillerRabin.X86.FrameContext
import VerifiedGarbage.Proof.Framework.Offset

/-! # Incoming cdecl arguments remain readable above the allocated frame -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

abbrev entryFrame (s : State) : Region :=
  ⟨byteAddr ((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp), VG.Impl.MillerRabin.X86.frameBytes⟩

namespace RoundABI

theorem arg_above_frame {s : State} (A : RoundABI s) {i : Nat} (hi : i < 2) :
    argAddr s i = off (entryFrame s).base (VG.Impl.MillerRabin.X86.frameBytes + 4 + 4 * i) := by
  have low := A.stackLow
  have bound := A.stackBound
  have sp := (s.gpr .esp).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, allocFrame_esp, byteAddr, off, VG.Impl.MillerRabin.X86.frameBytes,
    BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  change 1172 ≤ (s.gpr .esp).toNat at low
  omega

theorem argument_readable {s t : State} (A : RoundABI s) (rd : t.rd = s.rd) {i : Nat} (hi : i < 2) :
    InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
  rw [rd, A.rd]
  refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
  have bound := A.stackBound
  have address : argAddr s i = off (argAddr s 0) (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [argAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [address]
  exact Offset.contains_base _ (by omega) (by omega)

theorem read_argument {s t : State} (A : RoundABI s) {i : Nat} (hi : i < 2)
    (sp : t.gpr .esp = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp)
    (rd : t.rd = s.rd) (F : Frame [entryFrame s] s.mem t.mem) :
    readSrc t (.mem (VG.Impl.MillerRabin.X86.sp (VG.Impl.MillerRabin.X86.frameBytes + 4 + 4 * i))) =
      some (arg s i) := by
  have address : t.ea (VG.Impl.MillerRabin.X86.sp (VG.Impl.MillerRabin.X86.frameBytes + 4 + 4 * i)) = argAddr s i := by
    rw [State.ea, VG.Impl.MillerRabin.X86.sp, VG.Impl.Mont.X86.at_, sp, allocFrame_esp]
    apply congrArg (BitVec.setWidth 64)
    apply BitVec.eq_of_toNat_eq
    have low := A.stackLow
    have bound := A.stackBound
    have splt := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, VG.Impl.MillerRabin.X86.frameBytes]
    change 1172 ≤ (s.gpr .esp).toNat at low
    omega
  have unchanged : t.mem.readW (argAddr s i) 32 = s.mem.readW (argAddr s i) 32 := by
    refine F.readW (r := ⟨argAddr s i, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    rw [List.mem_singleton.mp hr, A.arg_above_frame hi]
    exact Offset.disjoint_base _ (by omega) (by change 1132 + 4 + 4 * i + 4 ≤ 2 ^ 64; omega)
  show t.load32 (t.ea _) = _
  rw [address, State.load32, ite_eq_left (A.argument_readable rd hi), unchanged]
  rfl

end RoundABI
end VG.Proof.MillerRabin.X86
