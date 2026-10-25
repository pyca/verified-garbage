module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosTop
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Combine both final carries with the untouched high accumulator words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem finish_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Ctx s0 base size acc b mod n) (positive : 1<n)
    (inv : Inv s0 x q base acc b mod n (n-1) s)
    (capacity : val32 s0.mem (State.addr base) acc (n+2)+
      x.toNat*val32 s0.mem (State.addr base) b n+
      q.toNat*val32 s0.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.Fios.top s fun t =>
      2^32*val32 t.mem (State.addr base) acc (n+1)=
        val32 s0.mem (State.addr base) acc (n+2)+
        x.toNat*val32 s0.mem (State.addr base) b n+
        q.toNat*val32 s0.mem (State.addr base) mod n ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s0.mem t.mem ∧
      VG.Proof.X25519.Arm.Rest roundClobbers s0 t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  let P := 2^(32*(n-1))
  let H := val32 s0.mem (State.addr base) (acc+4*n) 2
  let C := (s.gpr .r7).toNat+(s.gpr .r8).toNat
  have power : 2^(32*n)=2^32*P := by
    dsimp only [P]
    calc
      _ = 2^(32*((n-1)+1)) := by congr 1;omega
      _ = _ := pow32_succ (n-1)
  have split := val32_append s0.mem (State.addr base) acc n 2
  have total : 2^32*(val32 s.mem (State.addr base) acc (n-1)+P*(H+C))=
      val32 s0.mem (State.addr base) acc (n+2)+
      x.toNat*val32 s0.mem (State.addr base) b n+
      q.toNat*val32 s0.mem (State.addr base) mod n := by
    have prior := inv.value
    rw [show n-1+1=n by omega,power] at prior
    rw [split,power]
    dsimp only [H,C]
    grind
  have power2 : 2^32*(P*2^64)=2^(32*(n+2)) := by
    dsimp only [P]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega
  have topBound : H+C<2^64 := by
    rw [←total,←power2] at capacity
    have small : 2^32*(P*(H+C))<2^32*(P*2^64) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) capacity
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left small)
  have old0 := inv.outside.w32 (d:=acc+4*n) (by omega) (by omega)
  have old1 := inv.outside.w32 (d:=acc+4*n+4) (by omega) (by omega)
  have bound : w32 s.mem (State.addr base) (acc+4*(n-1)+4)+
      2^32*w32 s.mem (State.addr base) (acc+4*(n-1)+8)+
      (s.gpr .r7).toNat+(s.gpr .r8).toNat<2^64 := by
    rw [show acc+4*(n-1)+4=acc+4*n by omega,
      show acc+4*(n-1)+8=acc+4*n+4 by omega,old0,old1]
    simpa only [H,C,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topBound
  refine WP.mono (top_ok s (ctx.workspace.congr inv.rest.wr) (by omega) inv.outPtr bound) ?_
  rintro t ⟨value,mem,ptr,rest⟩
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨outside,whole⟩ := rowCarry_memory (base:=State.addr base) (o:=acc) (n:=n-1)
    nowrap' (by omega) mem
  have topValue : (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=H+C := by
    rw [show acc+4*(n-1)+4=acc+4*n by omega,
      show acc+4*(n-1)+8=acc+4*n+4 by omega,old0,old1] at value
    simpa only [H,C,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using value
  refine ⟨?_,?_,?_,?_⟩
  · rw [show n+1=(n-1)+2 by omega,whole,topValue]
    exact total
  · rw [ptr]
    congr 2
    omega
  · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (outside.mono (by omega) (by omega))
  · exact inv.rest.trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm.Fios
