module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosPair
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvanceInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosValue
import VerifiedGarbage.Proof.Bignum.Arm.FiosMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The pipelined pair advances the integrated quotient invariant by two limbs. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem pairBody_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n i : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (hi : i+3≤n) :
    WP isa VG.Impl.Bignum.Arm.Fios.pairBody s fun t =>
      Inv s0 x q base acc b mod n (i+2) t ∧ t.z=decide (i+2+1=n) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have ws := ctx.workspace.congr inv.rest.wr
  rw [VG.Impl.Bignum.Arm.Fios.pairBody,WP.seq_iff]
  refine WP.mono (pair_ok s ws (by omega) (by omega) (by omega)
    (by rcases ctx.accM with h|h <;> omega) inv.bPtr inv.mPtr inv.outPtr) ?_
  rintro u ⟨value,mem,rest⟩
  rw [inv.scalar,inv.quotient] at value
  have oldT := inv.outside.val32 (d:=acc+4*(i+1)) (k:=2) (by omega) (by omega)
  have oldB := inv.outside.val32 (d:=b+4*(i+1)) (k:=2)
    (by rcases ctx.accB with h|h <;> omega) (by omega)
  have oldM := inv.outside.val32 (d:=mod+4*(i+1)) (k:=2)
    (by rcases ctx.accM with h|h <;> omega) (by omega)
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := pair_memory nowrap' (by omega) mem
  have outside : Outside (State.addr base) acc (4*(i+2)) s0.mem u.mem :=
    (inv.outside.mono (Nat.le_refl _) (by omega)).trans (writes.mono (by omega) (by omega))
  have segment : ((u.gpr .r6).toNat+2^32*(u.gpr .r10).toNat)+
      2^(32*2)*((u.gpr .r7).toNat+(u.gpr .r8).toNat)=
      val32 s.mem (State.addr base) (acc+4*(i+1)) 2+
      x.toNat*val32 s.mem (State.addr base) (b+4*(i+1)) 2+
      q.toNat*val32 s.mem (State.addr base) (mod+4*(i+1)) 2+
      ((s.gpr .r7).toNat+(s.gpr .r8).toNat) := by
    simp only [val32,Nat.mul_zero,Nat.add_zero]
    rw [show acc+4*(i+1)=acc+4*i+4 by omega,
      show acc+4*i+4+4=acc+4*i+8 by omega]
    omega
  rw [oldT,oldB,oldM] at segment
  exact advance_inv ctx inv (Or.inr rfl) (by omega) rest outside
    (prefix_extend inv.value segment stored)

end VG.Proof.Bignum.Arm.Fios
