module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public cdecl arguments remain available throughout recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (stackAddress)
open VG.Impl.Rsa.X86.Keys

theorem KS.argument {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) (apart : ∀ r ∈ stageR g, Region.Disjoint ⟨stackAddress s0 i, 4⟩ r) :
    CallArgument s g.B g.Z i v :=
  arg.frame h.rest (by decide) h.frame apart

/-- An argument of the stage's call, through the stage's writes. -/
theorem KS.arg {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) (hi : i ≤ 11) : CallArgument s g.B g.Z i v := by
  have esp0 : s0.gpr .esp = g.sp := (h.rest.1 _ (by decide)).symm.trans h.sp
  have low := h.room.low
  have top := h.top
  refine h.argument arg fun r hr => ?_
  simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | ⟨p, rfl, rfl⟩
  · have ea : (stackAddress s0 i).toNat = g.sp.toNat + (4 + 4 * i) := by
      simp only [stackAddress, VG.X86.addr, VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, BitVec.toNat_add,
        BitVec.toNat_ofNat, esp0]
      omega
    have eb : ((g.sp - BitVec.ofNat 32 40).setWidth 64).toNat = g.sp.toNat - 40 := by
      rw [VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega)]
    exact (Region.disjoint_of_le (r₁ := below g.sp 40) (.inl (by dsimp only; rw [eb, ea]; omega))
      (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm
  · refine arg.stack.apart.sub_right ?_
    have := Offset.sub g.B (d := 16) (n := g.Z - 16) (e := 0) (k := g.Z) (Nat.zero_le _)
      (by have := h.ws.hdr_le; unfold hdr at this; omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

end VG.Proof.Rsa.X86.Recover
