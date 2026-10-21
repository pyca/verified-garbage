module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosFirst
import VerifiedGarbage.Proof.Bignum.Arm.FiosStepInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosLoop
import VerifiedGarbage.Proof.Bignum.Arm.FiosFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! One integrated UMAAL row computes a Montgomery quotient without an intermediate product pass. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Ctx s base size acc b mod n) (positive : 4≤n) (even : n%2=0)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 b)
    (modulus : s.gpr .r4=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carryA : s.gpr .r7=0) (carryM : s.gpr .r8=0)
    (inverse : (val32 s.mem (State.addr base) mod n*(s.gpr .r2).toNat+1)%2^32=0)
    (capacity : ∀ q<2^32, val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
      q*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.Fios.code s fun t =>
      (∃ q<2^32, 2^32*val32 t.mem (State.addr base) acc (n+1)=
        val32 s.mem (State.addr base) acc (n+2)+
        (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
        q*val32 s.mem (State.addr base) mod n) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧
      VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have small : n<2^32 := by omega
  have split : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega
      _ = _ := rfl
  have inverseLow : (w32 s.mem (State.addr base) mod*(s.gpr .r2).toNat+1)%2^32=0 := by
    rw [split,Nat.add_mul,Nat.add_right_comm,Nat.mul_assoc,Nat.add_mul_mod_self_left] at inverse
    exact inverse
  rw [VG.Impl.Bignum.Arm.Fios.code,WP.seq_iff]
  refine WP.mono (first_ok s ctx.workspace (by have := ctx.bFits;omega)
    (by have := ctx.mFits;omega) (by omega) source modulus ptr count (by omega) small carryA carryM inverseLow) ?_
  rintro u ⟨fv,_fq,_qb,p0,p12,p4,lr,scalar,mem,rest⟩
  let x := s.gpr .r1
  let q := u.gpr .r2
  have initial : Inv s x q base acc b mod n 0 u := by
    refine ⟨by omega,?_,?_,?_,?_,scalar,rfl,?_,?_,rest⟩
    · simpa only [Nat.mul_zero,Nat.add_zero] using p0
    · simpa only [Nat.zero_add,Nat.mul_one] using p12
    · simpa only [Nat.zero_add,Nat.mul_one] using p4
    · simpa only [Nat.zero_add] using lr
    · rw [mem];exact Outside.refl _ _ _ _
    · simpa only [x,q,val32,Nat.zero_add,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.mul_one] using fv
  rw [WP.seq_iff]
  refine WP.mono (body_ok ctx initial (by omega)) ?_
  rintro v ⟨iv,_zv⟩
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx iv (by omega) (by omega)) ?_
  intro w iw
  refine WP.mono (finish_ok ctx (by omega) iw (capacity q.toNat q.isLt)) ?_
  rintro t ⟨value,pt,outside,rt⟩
  exact ⟨⟨q.toNat,q.isLt,value⟩,pt,outside,rt⟩

end VG.Proof.Bignum.Arm.Fios
