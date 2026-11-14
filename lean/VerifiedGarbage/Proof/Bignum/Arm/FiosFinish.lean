module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.Arm.FiosTop`, which only this module used -/

section

/-! Add the two independent FIOS carries to the high quotient words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp op2_imm dpVal)

theorem top_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d+12≤size)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 d)
    (bound : w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
      (s.gpr .r7).toNat+(s.gpr .r8).toNat<2^64) :
    WP isa VG.Impl.Bignum.Arm.Fios.top s fun t =>
      (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=
        w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
          (s.gpr .r7).toNat+(s.gpr .r8).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r3)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r4) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (d+8) ∧ Rest [.r0,.r3,.r4] s t := by
  rw [VG.Impl.Bignum.Arm.Fios.top,WP.seq_iff]
  have loads : WP isa (.block [.ldr .r3 .r0 4,.ldr .r4 .r0 8]) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) (d+4)) 32 ∧
      u.gpr .r4=s.mem.readW (off (State.addr base) (d+8)) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r4] s u := by
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide) (ws.ea ptr (by omega_using [fit]))
      (ws.read (by omega_using [fit])) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) (d+8)) (by decide)
      (by rw [h.other .r0 (by decide)];exact ws.ea ptr (by omega_using [fit]))
      (by rw [h.rd,h.wr];exact ws.read (by omega_using [fit])) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r3 (by decide)).trans h.gpr,by rw [k.gpr,h.mem],
      k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono loads ?_
  rintro u ⟨low,high,memU,restU⟩
  have carry7 : u.gpr .r7=s.gpr .r7 := restU.gpr .r7 (by decide)
  have carry8 : u.gpr .r8=s.gpr .r8 := restU.gpr .r8 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok u .r7 (by
    rw [low,high,carry7];dsimp only [w32] at bound;omega_using [bound])) ?_
  rintro v ⟨value7,frame7⟩
  have carry8v : v.gpr .r8=s.gpr .r8 :=
    (frame7.regs .r8 (by decide)).trans carry8
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok v .r8 (by
    rw [value7,low,high,carry7,carry8v];dsimp only [w32] at bound;omega_using [bound])) ?_
  rintro z ⟨value8,frame8⟩
  have frame := frame7.trans frame8
  have pz : z.gpr .r0=base+BitVec.ofNat 32 d :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  have mz : z.mem=s.mem := frame.mem.trans memU
  have wz : z.wr=s.wr := frame.wr.trans restU.wr
  have wsz := ws.congr wz
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using wsz.ea pz (imm:=0) (by omega_using [fit]))
    (by rw [wz];exact ws.write (by omega_using [fit])) fun a ha => ?_
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    (by rw [ha.gpr];exact wsz.ea pz (by omega_using [fit]))
    (by rw [ha.wr,wz];exact ws.write (by omega_using [fit])) fun b hb => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
    rw [value7,low,high,carry7,carry8v] at value8
    simpa only [w32,Nat.mul_comm] using value8
  · rw [ht.mem,hb.mem,ha.mem,mz,ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
  · rw [ht.gpr,dpVal,hb.gpr,ha.gpr,pz]
    exact Offset.add_add _ _ _
  · have rz : Rest [.r3,.r4] s z := restU.trans ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩
    exact (rz.mono (by decide)).trans ((ha.rest _).trans
      ((hb.rest _).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.Fios

end

end


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
      _ = 2^(32*((n-1)+1)) := by congr 1;omega_using [positive]
      _ = _ := pow32_succ (n-1)
  have split := val32_append s0.mem (State.addr base) acc n 2
  have total : 2^32*(val32 s.mem (State.addr base) acc (n-1)+P*(H+C))=
      val32 s0.mem (State.addr base) acc (n+2)+
      x.toNat*val32 s0.mem (State.addr base) b n+
      q.toNat*val32 s0.mem (State.addr base) mod n := by
    have prior := inv.value
    rw [show n-1+1=n by omega_using [positive],power] at prior
    rw [split,power]
    dsimp only [H,C]
    grind
  have power2 : 2^32*(P*2^64)=2^(32*(n+2)) := by
    dsimp only [P]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega_using [positive]
  have topBound : H+C<2^64 := by
    rw [←total,←power2] at capacity
    have small : 2^32*(P*(H+C))<2^32*(P*2^64) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) capacity
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left small)
  have old0 := inv.outside.w32 (d:=acc+4*n) (by omega_using []) (by omega_using [nowrap, outf])
  have old1 := inv.outside.w32 (d:=acc+4*n+4) (by omega_using []) (by omega_using [nowrap, outf])
  have bound : w32 s.mem (State.addr base) (acc+4*(n-1)+4)+
      2^32*w32 s.mem (State.addr base) (acc+4*(n-1)+8)+
      (s.gpr .r7).toNat+(s.gpr .r8).toNat<2^64 := by
    rw [show acc+4*(n-1)+4=acc+4*n by omega_using [positive],
      show acc+4*(n-1)+8=acc+4*n+4 by omega_using [positive],old0,old1]
    simpa only [H,C,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topBound
  refine WP.mono (top_ok s (ctx.workspace.congr inv.rest.wr) (by omega_using [positive, outf]) inv.outPtr bound) ?_
  rintro t ⟨value,mem,ptr,rest⟩
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨outside,whole⟩ := rowCarry_memory (base:=State.addr base) (o:=acc) (n:=n-1)
    nowrap' (by omega_using [outf]) mem
  have topValue : (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=H+C := by
    rw [show acc+4*(n-1)+4=acc+4*n by omega_using [positive],
      show acc+4*(n-1)+8=acc+4*n+4 by omega_using [positive],old0,old1] at value
    simpa only [H,C,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using value
  refine ⟨?_,?_,?_,?_⟩
  · rw [show n+1=(n-1)+2 by omega_using [positive],whole,topValue]
    exact total
  · rw [ptr]
    congr 2
    omega_using [positive]
  · exact (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (outside.mono (by omega_using []) (by omega_using [positive]))
  · exact inv.rest.trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm.Fios
