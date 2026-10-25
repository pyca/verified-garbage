module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosStep
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvanceInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The initial one-limb step establishes the parity needed by the paired loop. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem body_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n i : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (hi : i+1<n) :
    WP isa VG.Impl.Bignum.Arm.Fios.body s fun t =>
      Inv s0 x q base acc b mod n (i+1) t ∧ t.z=decide (i+1+1=n) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have ws := ctx.workspace.congr inv.rest.wr
  rw [VG.Impl.Bignum.Arm.Fios.body,WP.seq_iff]
  refine WP.mono (step_ok s ws (by omega) (by omega) (by omega) inv.bPtr inv.mPtr inv.outPtr) ?_
  rintro u ⟨value,mem,rest⟩
  have oldT := inv.outside.w32 (d:=acc+4*(i+1)) (by omega) (by omega)
  have oldB := inv.outside.w32 (d:=b+4*(i+1))
    (by rcases ctx.accB with h|h <;> omega) (by omega)
  have oldM := inv.outside.w32 (d:=mod+4*(i+1))
    (by rcases ctx.accM with h|h <;> omega) (by omega)
  rw [inv.scalar,inv.quotient,oldB,oldM,show acc+4*i+4=acc+4*(i+1) by omega,oldT] at value
  have writes := writeW32_outside s.mem (State.addr base) (d:=acc+4*i) (u.gpr .r6) (by omega)
  rw [←mem] at writes
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem u.mem :=
    (inv.outside.mono (Nat.le_refl _) (by omega)).trans (writes.mono (by omega) (by omega))
  have low := writes.val32 (d:=acc) (k:=i) (by omega) (by omega)
  have top : w32 u.mem (State.addr base) (acc+4*i)=(u.gpr .r6).toNat := by rw [mem,w32_write_self]
  have stored : val32 u.mem (State.addr base) acc (i+1)=
      val32 s.mem (State.addr base) acc i+2^(32*i)*(u.gpr .r6).toNat := by
    rw [val32_succ,low,top]
  have segment : (u.gpr .r6).toNat+2^(32*1)*((u.gpr .r7).toNat+(u.gpr .r8).toNat)=
      val32 s0.mem (State.addr base) (acc+4*(i+1)) 1+
      x.toNat*val32 s0.mem (State.addr base) (b+4*(i+1)) 1+
      q.toNat*val32 s0.mem (State.addr base) (mod+4*(i+1)) 1+
      ((s.gpr .r7).toNat+(s.gpr .r8).toNat) := by
    simp only [val32,Nat.mul_zero,Nat.add_zero]
    omega
  exact advance_inv ctx inv (Or.inl rfl) (by omega)
    (rest.mono (by decide)) outside (prefix_extend inv.value segment stored)

end VG.Proof.Bignum.Arm.Fios
