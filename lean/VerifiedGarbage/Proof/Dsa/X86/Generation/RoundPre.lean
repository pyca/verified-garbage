module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundGeometry
public import VerifiedGarbage.Proof.MillerRabin.Workspace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! The generic prepared-round callee receives the unchanged shared contract. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86

theorem round_callee_arguments {s g : State} {base : Addr} {bytes : Nat}
    (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (first : g.mem.readW ((g.gpr .esp).setWidth 64) 32 =
      s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic)
    (second : g.mem.readW ((g.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32) :
    arg (roundCallee g base) 0 = s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic ∧
      arg (roundCallee g base) 1 = 1536#32 := by
  have gn : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    rw [stack, VG.X86.sub_toNat (by have := room.low; omega)]
  have argument : ∀ i < 2, arg (roundCallee g base) i =
      g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 := by
    intro i hi
    change arg g.callEntry i = _
    rw [arg_callEntry (by have := room.low; omega) (by have := (s.gpr .esp).isLt; omega)]
    have address := VG.Proof.Bignum.X86.byteAddr_add (a := g.gpr .esp) (k := 4 * i)
      (by have := (s.gpr .esp).isLt; omega)
    change (g.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 = _ at address
    rw [address]
    rfl
  exact ⟨(by
      have e := argument 0 (by decide)
      simp only [Nat.mul_zero, BitVec.add_zero] at e
      exact e.trans first),
    (argument 1 (by decide)).trans second⟩

theorem round_callee_abi {s g : State} {base : Addr} {bytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (F : Frame [below (s.gpr .esp) 8] s.mem g.mem)
    (first : g.mem.readW ((g.gpr .esp).setWidth 64) 32 =
      s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic)
    (second : g.mem.readW ((g.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic)) :
    RoundABI (roundCallee g base) := by
  obtain ⟨a0, a1⟩ := round_callee_arguments room stack first second
  have pointer : (s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic).setWidth 64 =
      off base Layout.arithmetic := scr.ea (by change 28672 < bytes; omega)
  have ws : wsOf (roundCallee g base) = off base Layout.arithmetic := by
    rw [wsOf, a0]; exact pointer
  have size : bytesOf (roundCallee g base) = 12288 := by rw [bytesOf, a1]; rfl
  have fit := round_compact_fit capacity
  have compactSub := Offset.sub_base base fit
  have ret : (roundCallee g base).gpr .esp = s.gpr .esp - 12#32 := by
    change g.gpr .esp - 4 = _
    rw [stack]
    change s.gpr .esp - 8#32 - 4#32 = _
    rw [BitVec.sub_sub]; rfl
  have cn : ((roundCallee g base).gpr .esp).toNat = (s.gpr .esp).toNat - 12 := by
    rw [ret, VG.X86.sub_toNat (by have := room.low; omega)]
  obtain ⟨Lg, Pg, _⟩ := VG.Proof.MillerRabin.Workspace.workspace_congr
    (round_workspace_same room capacity stack F) L P
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 1172 ≤ ((roundCallee g base).gpr .esp).toNat
    rw [cn]; have := room.low; omega
  · rw [cn]; have := (s.gpr .esp).isLt; omega
  · rw [ws, size]; rfl
  · rw [round_args_address stack, ws, size]
    exact (room.apart.sub_left (below_sub (by decide) room.low)).sub_right compactSub
  · rw [ret, ws, size]
    exact (room.apart.sub_left (fun x hx => below_sub (show 12 ≤ 1184 by decide) room.low x
      (Region.sub_prefix (show 4 ≤ 12 by decide) x hx))).sub_right compactSub
  · rw [ret, ws, size]
    change Region.Disjoint ⟨(s.gpr .esp - 12#32).setWidth 64 - 1172#64, 1172⟩ _
    have low : 1172 ≤ (s.gpr .esp - 12#32).toNat := by
      rw [VG.X86.sub_toNat (by have := room.low; omega)]
      have := room.low
      omega
    rw [← Taint.sub_setWidth low]
    exact (room.apart.sub_left (below_inner (a := 1172) (k := 12) (by decide) room.low)).sub_right compactSub
  · rw [a0, size]
    have bound := workspace_pointer_fits scr fit (by decide : 0 < 12288)
    exact bound
  · rw [ws, a1]; exact Lg
  · rw [ws]; exact Pg

end VG.Proof.Dsa.X86.Generation
