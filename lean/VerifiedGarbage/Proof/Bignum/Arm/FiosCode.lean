module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosFirst
import VerifiedGarbage.Proof.Bignum.Arm.FiosStepInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvanceInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosValue
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Mem
import Init.Prelude
import VerifiedGarbage.Proof.Mont.Words32

/-! ### `Bignum.Arm.FiosPairInv`, which only this module used -/

section

/-! The pipelined pair advances the integrated quotient invariant by two limbs. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosMemory.lean`, which only this module imported.
section

/-! Two adjacent quotient stores extend a previously written prefix. -/

section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem pair_memory {mem mem' : Mem} {base : Addr} {size o i : Nat} {lo hi : BitVec 32}
    (nowrap : base.toNat+size≤2^32) (fit : o+4*(i+2)≤size)
    (hm : mem'=(mem.writeW (off base (o+4*i)) lo).writeW (off base (o+4*i+4)) hi) :
    Outside base (o+4*i) 8 mem mem' ∧
      val32 mem' base o (i+2)=val32 mem base o i+2^(32*i)*(lo.toNat+2^32*hi.toNat) := by
  have w0 := writeW32_outside mem base (d:=o+4*i) lo (by omega)
  have w1 := writeW32_outside (mem.writeW (off base (o+4*i)) lo)
    base (d:=o+4*i+4) hi (by omega)
  rw [←hm] at w1
  have outside : Outside base (o+4*i) 8 mem mem' :=
    (w0.mono (by omega) (by omega)).trans (w1.mono (by omega) (by omega))
  have low := outside.val32 (d:=o) (k:=i) (by omega) (by omega)
  have top0 : w32 mem' base (o+4*i)=lo.toNat := by
    rw [hm,w32_write_ne nowrap (by omega) (by omega) (by omega),w32_write_self]
  have top1 : w32 mem' base (o+4*i+4)=hi.toNat := by rw [hm,w32_write_self]
  refine ⟨outside,?_⟩
  rw [val32_append mem' base o i 2,low,val32,val32,val32,top0,top1,Nat.mul_zero,Nat.add_zero]

end VG.Proof.Bignum.Arm.Fios
end

end

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
  refine WP.mono (pair_ok s ws (by omega_using [hi, inf]) (by omega_using [hi, modf]) (by omega_using [hi, outf])
    (by rcases ctx.accM with h|h <;> omega_arith) inv.bPtr inv.mPtr inv.outPtr) ?_
  rintro u ⟨value,mem,rest⟩
  rw [inv.scalar,inv.quotient] at value
  have oldT := inv.outside.val32 (d:=acc+4*(i+1)) (k:=2) (by omega_using []) (by omega_using [hi, nowrap, outf])
  have oldB := inv.outside.val32 (d:=b+4*(i+1)) (k:=2)
    (by rcases ctx.accB with h|h <;> omega_arith) (by omega_using [hi, nowrap, inf])
  have oldM := inv.outside.val32 (d:=mod+4*(i+1)) (k:=2)
    (by rcases ctx.accM with h|h <;> omega_arith) (by omega_using [hi, nowrap, modf])
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := pair_memory nowrap' (by omega_using [hi, outf]) mem
  have outside : Outside (State.addr base) acc (4*(i+2)) s0.mem u.mem :=
    (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using []))
  have segment : ((u.gpr .r6).toNat+2^32*(u.gpr .r10).toNat)+
      2^(32*2)*((u.gpr .r7).toNat+(u.gpr .r8).toNat)=
      val32 s.mem (State.addr base) (acc+4*(i+1)) 2+
      x.toNat*val32 s.mem (State.addr base) (b+4*(i+1)) 2+
      q.toNat*val32 s.mem (State.addr base) (mod+4*(i+1)) 2+
      ((s.gpr .r7).toNat+(s.gpr .r8).toNat) := by
    simp only [val32,Nat.mul_zero,Nat.add_zero]
    rw [show acc+4*(i+1)=acc+4*i+4 by omega_using [],
      show acc+4*i+4+4=acc+4*i+8 by omega_using []]
    omega_using [value]
  rw [oldT,oldB,oldM] at segment
  exact advance_inv ctx inv (Or.inr rfl) (by omega_using [hi]) rest outside
    (prefix_extend inv.value segment stored)

end VG.Proof.Bignum.Arm.Fios

end

end

/-! One integrated UMAAL row computes a Montgomery quotient without an intermediate product pass. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosLoop.lean`, which only this module imported.
section

/-! The public pair count decreases to zero while the full quotient identity is preserved. -/

section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem loop_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n i : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (positive : i+1<n) (even : (n-(i+1))%2=0) :
    WP isa VG.Impl.Bignum.Arm.Fios.loop s (Inv s0 x q base acc b mod n (n-1)) := by
  let I := fun k t => ∃ j, j+1+2*k=n ∧ 0<k ∧ Inv s0 x q base acc b mod n j t
  unfold VG.Impl.Bignum.Arm.Fios.loop
  refine WP.loop (M:=isa) I ?_ ((n-(i+1))/2) s ?_
  · intro k t h
    obtain ⟨j,hjk,hk,hj⟩ := h
    refine WP.mono (pairBody_ok ctx hj (by omega)) ?_
    rintro u ⟨hu,hz⟩
    by_cases last : j+2+1=n
    · left
      refine ⟨?_,?_⟩
      · change some (!u.z)=some false
        simp only [hz,last,decide_true,Bool.not_true]
      · have index : j+2=n-1 := by omega
        simpa only [index] using hu
    · right
      refine ⟨?_,k-1,by omega,j+2,by omega,by omega,hu⟩
      change some (!u.z)=some true
      simp only [hz,last,decide_false,Bool.not_false]
  · exact ⟨i,by omega,by omega,inv⟩

end VG.Proof.Bignum.Arm.Fios
end

end

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
  have small : n<2^32 := by omega_using [nowrap, outf]
  have split : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega_using [positive]
      _ = _ := rfl
  have inverseLow : (w32 s.mem (State.addr base) mod*(s.gpr .r2).toNat+1)%2^32=0 := by
    rw [split,Nat.add_mul,Nat.add_right_comm,Nat.mul_assoc,Nat.add_mul_mod_self_left] at inverse
    exact inverse
  rw [VG.Impl.Bignum.Arm.Fios.code,WP.seq_iff]
  refine WP.mono (first_ok s ctx.workspace (by have := ctx.bFits;omega_using [positive, this])
    (by have := ctx.mFits;omega_using [positive, this]) (by omega_using [outf]) source modulus ptr count (by omega_using [positive]) small carryA carryM inverseLow) ?_
  rintro u ⟨fv,_fq,_qb,p0,p12,p4,lr,scalar,mem,rest⟩
  let x := s.gpr .r1
  let q := u.gpr .r2
  have initial : Inv s x q base acc b mod n 0 u := by
    refine ⟨by omega_using [positive],?_,?_,?_,?_,scalar,rfl,?_,?_,rest⟩
    · simpa only [Nat.mul_zero,Nat.add_zero] using p0
    · simpa only [Nat.zero_add,Nat.mul_one] using p12
    · simpa only [Nat.zero_add,Nat.mul_one] using p4
    · simpa only [Nat.zero_add] using lr
    · rw [mem];exact Outside.refl _ _ _ _
    · simpa only [x,q,val32,Nat.zero_add,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.mul_one] using fv
  rw [WP.seq_iff]
  refine WP.mono (body_ok ctx initial (by omega_using [positive])) ?_
  rintro v ⟨iv,_zv⟩
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx iv (by omega_using [positive]) (by omega_using [even])) ?_
  intro w iw
  refine WP.mono (finish_ok ctx (by omega_using [positive]) iw (capacity q.toNat q.isLt)) ?_
  rintro t ⟨value,pt,outside,rt⟩
  exact ⟨⟨q.toNat,q.isLt,value⟩,pt,outside,rt⟩

end VG.Proof.Bignum.Arm.Fios
