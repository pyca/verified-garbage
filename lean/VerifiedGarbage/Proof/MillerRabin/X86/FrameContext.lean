module

public import VerifiedGarbage.Proof.MillerRabin.X86.ABI
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset

/-! # The allocated frame and its existing Montgomery-call room -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

namespace RoundABI

theorem ws_fit {s : State} (A : RoundABI s) : (wsOf s).toNat + bytesOf s ≤ 2 ^ 32 := by
  simpa only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using A.bound

theorem allocated_sp {s : State} (A : RoundABI s) :
    ((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp).toNat =
      (s.gpr .esp).toNat - VG.Impl.MillerRabin.X86.frameBytes := by
  rw [allocFrame_esp, sub_toNat (by
    change 1132 ≤ (s.gpr .esp).toNat
    have := A.stackLow
    change 1172 ≤ (s.gpr .esp).toNat at this
    omega)]

theorem below_apart {s : State} (A : RoundABI s) :
    (below (s.gpr .esp) stackBytes).Disjoint ⟨wsOf s, bytesOf s⟩ := by
  change (⟨(s.gpr .esp - BitVec.ofNat 32 stackBytes).setWidth 64, stackBytes⟩ : Region).Disjoint _
  rw [Taint.sub_setWidth A.stackLow]
  exact A.belowScratch

theorem frame_apart {s : State} (A : RoundABI s) :
    (⟨byteAddr ((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp),
      VG.Impl.MillerRabin.X86.frameBytes⟩ : Region).Disjoint ⟨wsOf s, bytesOf s⟩ := by
  exact A.below_apart.sub_left (below_sub (by decide) A.stackLow)

theorem call_room {s t : State} (A : RoundABI s)
    (sp : t.gpr .esp = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp) :
    CallRoom (t.gpr .esp) (wsOf s) (bytesOf s) := by
  refine ⟨?_, ?_⟩
  · rw [sp, A.allocated_sp]
    have := A.stackLow
    change 1172 ≤ (s.gpr .esp).toNat at this
    change 40 ≤ (s.gpr .esp).toNat - 1132
    omega
  · rw [sp, allocFrame_esp]
    exact A.below_apart.sub_left (below_inner (a := 40) (k := VG.Impl.MillerRabin.X86.frameBytes)
      (by decide) A.stackLow)

theorem context {s t : State} (A : RoundABI s)
    (sp : t.gpr .esp = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp)
    (wr : t.wr = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).wr)
    (edi : t.gpr .edi = arg s 0) : ProtectedContext t (wsOf s) (bytesOf s) := by
  have room := A.call_room sp
  have stackFit : (t.gpr .esp).toNat + VG.Impl.MillerRabin.X86.frameBytes ≤ 2 ^ 32 := by
    rw [sp, A.allocated_sp]
    have := (s.gpr .esp).isLt
    change (s.gpr .esp).toNat - 1132 + 1132 ≤ 2 ^ 32
    omega
  have apart : Region.Disjoint ⟨wsOf s, bytesOf s⟩
      ⟨byteAddr (t.gpr .esp), VG.Impl.MillerRabin.X86.frameBytes⟩ := by
    rw [sp]
    exact A.frame_apart.symm
  refine ⟨⟨by rw [edi], ?_, A.ws_fit, ?_⟩, ?_, stackFit, apart⟩
  · rw [wr, allocFrame_wr, A.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · have size : 0 < bytesOf s := by
      obtain ⟨_, _, _, _, fit, _⟩ := A.layout
      change Spec.Rsa.Mont.arrAt _ 28 ≤ _ at fit
      simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] at fit
      change 0 < (arg s 1).toNat * 8
      omega
    apply VG.Proof.Weierstrass.X86.stkOk_of (z := 40) (by decide) room.low A.ws_fit size
    change (⟨(t.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩ : Region).Disjoint _
    rw [← Taint.sub_setWidth room.low]
    exact room.apart
  · rw [wr, sp, allocFrame_wr]
    exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩

end RoundABI
end VG.Proof.MillerRabin.X86
