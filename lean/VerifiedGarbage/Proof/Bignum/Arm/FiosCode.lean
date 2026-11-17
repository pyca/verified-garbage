module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Mem
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvance
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory

/-! ### `Bignum.Arm.FiosLoads`, which this module and modules that import it used -/

section

/-! Workspace reads used by the pipelined integrated Montgomery row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem loadsA_ok (s : State) (dst : Reg) (hne : dst ≠ .r3)
    {base : BitVec 32} {size a d ka kd : Nat}
    (ws : Workspace s base size) (hka : ka<4096) (hkd : kd<4096)
    (fa : a+ka+4≤size) (fd : d+kd+4≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (.block [.ldr .r3 .r12 ka,.ldr dst .r0 kd]) s fun t =>
      t.gpr .r3=s.mem.readW (off (State.addr base) (a+ka)) 32 ∧
      t.gpr dst=s.mem.readW (off (State.addr base) (d+kd)) 32 ∧
      t.mem=s.mem ∧ Rest [.r3,dst] s t := by
  refine wp_ldr (a:=off (State.addr base) (a+ka)) hka (ws.ea pa (by omega_using [fa])) (ws.read fa) fun u hu => ?_
  refine wp_ldr (a:=off (State.addr base) (d+kd)) hkd
    (by rw [hu.other .r0 (by decide)];exact ws.ea pd (by omega_using [fd]))
    (by rw [hu.rd,hu.wr];exact ws.read fd) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (Ne.symm hne),hu.gpr]
  · rw [ht.gpr,hu.mem]
  · exact ht.mem.trans hu.mem
  · exact (hu.rest (by simp)).trans (ht.rest (by simp))

theorem loadsM_ok (s : State) {base : BitVec 32} {size m k : Nat}
    (ws : Workspace s base size) (hk : k<4096) (fm : m+k+4≤size)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m) :
    WP isa (.block [.ldr .r5 .r4 k]) s fun t =>
      t.gpr .r5=s.mem.readW (off (State.addr base) (m+k)) 32 ∧
      t.mem=s.mem ∧ Rest [.r5] s t := by
  refine wp_ldr (a:=off (State.addr base) (m+k)) hk (ws.ea pm (by omega_using [fm])) (ws.read fm) fun t ht => WP.block_nil ?_
  exact ⟨ht.gpr,ht.mem,ht.rest (by simp)⟩

end VG.Proof.Bignum.Arm.Fios

end

end

/-! ### `Bignum.Arm.FiosFinish`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Bignum.Arm.FiosStepInv`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.FiosValue`, which this module and modules that import it used -/

section

/-! Extend the quotient prefix using the two independent carry chains. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont

/-- The prefix algebra is independent of whether one or two limbs are scanned. -/
theorem prefix_extend {mem0 mem mem' : Mem} {base : Addr} {acc b mod i k x q oldCarry newCarry low : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*oldCarry=
      val32 mem0 base acc (i+1)+x*val32 mem0 base b (i+1)+q*val32 mem0 base mod (i+1))
    (step : low+2^(32*k)*newCarry=
      val32 mem0 base (acc+4*(i+1)) k+x*val32 mem0 base (b+4*(i+1)) k+
      q*val32 mem0 base (mod+4*(i+1)) k+oldCarry)
    (stored : val32 mem' base acc (i+k)=val32 mem base acc i+2^(32*i)*low) :
    2^32*val32 mem' base acc (i+k)+2^(32*((i+k)+1))*newCarry=
      val32 mem0 base acc ((i+k)+1)+x*val32 mem0 base b ((i+k)+1)+
      q*val32 mem0 base mod ((i+k)+1) := by
  have power : 2^(32*((i+k)+1))=2^(32*(i+1))*2^(32*k) := by
    rw [←Nat.pow_add]
    congr 1
    omega_using []
  rw [stored,power,show i+k+1=(i+1)+k by omega_using [],
    val32_append mem0 base acc (i+1) k,val32_append mem0 base b (i+1) k,
    val32_append mem0 base mod (i+1) k]
  have scaled := congrArg (fun z => 2^(32*(i+1))*z) step
  rw [pow32_succ] at prior scaled ⊢
  generalize 2^(32*i)=P at *
  generalize 2^(32*k)=Q at *
  grind

end VG.Proof.Bignum.Arm.Fios

end

end

/-! ### `Bignum.Arm.FiosAdvanceInv`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.FiosPair`, which only this module used -/

section

/-! Two product limbs are issued before their independent cancellation chain. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_str)

abbrev pairClobbers : List Reg := [.r3,.r5,.r6,.r7,.r8,.r10]

private theorem framed {s t : State} {rs : List Reg}
    (h : MacFrame rs s t) : Rest rs s t := ⟨h.regs,h.rd,h.wr,h.sp⟩

/-- The original arrays can overlap one another, but not the quotient stores. -/
theorem pair_ok (s : State) {base : BitVec 32} {size a m d : Nat}
    (ws : Workspace s base size) (fa : a+8≤size) (fm : m+8≤size) (fd : d+12≤size)
    (sep : d+8≤m ∨ m+8≤d)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa VG.Impl.Bignum.Arm.Fios.pairStep s fun t =>
      (t.gpr .r6).toNat+2^32*(t.gpr .r10).toNat+
        2^64*((t.gpr .r7).toNat+(t.gpr .r8).toNat)=
        (s.gpr .r1).toNat*(w32 s.mem (State.addr base) a+2^32*w32 s.mem (State.addr base) (a+4))+
        (s.gpr .r2).toNat*(w32 s.mem (State.addr base) m+2^32*w32 s.mem (State.addr base) (m+4))+
        (w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8))+
        (s.gpr .r7).toNat+(s.gpr .r8).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r6)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r10) ∧
      Rest pairClobbers s t := by
  unfold VG.Impl.Bignum.Arm.Fios.pairStep
  rw [WP.seq_iff]
  refine WP.mono (loadsA_ok s .r6 (by decide) ws (by decide) (by decide) (by omega_using [fa]) (by omega_using [fd]) pa pd) ?_
  rintro u0 ⟨ua0,ut0,mu0,ru0⟩
  simp only [Nat.add_zero] at ua0
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u0 .r6 .r7 .r3 .r1 (by decide)) ?_
  rintro v0 ⟨vp0,rv0⟩
  rw [ua0,ut0,ru0.gpr .r1 (by decide),ru0.gpr .r7 (by decide)] at vp0
  obtain rV0 : Rest pairClobbers s v0 :=
    (ru0.mono (by decide)).trans ((framed rv0).mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (loadsA_ok v0 .r10 (by decide) (ws.congr rV0.wr) (by decide) (by decide) fa fd
    ((rV0.gpr .r12 (by decide)).trans pa)
    ((rV0.gpr .r0 (by decide)).trans pd)) ?_
  rintro u1 ⟨ua1,ut1,mu1,ru1⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u1 .r10 .r7 .r3 .r1 (by decide)) ?_
  rintro v1 ⟨vp1,rv1⟩
  obtain mv0 : v0.mem=s.mem := rv0.mem.trans mu0
  rw [ua1,ut1,mv0,ru1.gpr .r1 (by decide),rV0.gpr .r1 (by decide),
    ru1.gpr .r7 (by decide)] at vp1
  obtain rV1 : Rest pairClobbers s v1 :=
    rV0.trans ((ru1.mono (by decide)).trans ((framed rv1).mono (by decide)))
  obtain mv1 : v1.mem=s.mem := rv1.mem.trans (mu1.trans mv0)
  rw [WP.seq_iff]
  refine WP.mono (loadsM_ok v1 (ws.congr rV1.wr) (by decide) (by omega_using [fm])
    ((rV1.gpr .r4 (by decide)).trans pm)) ?_
  rintro n0 ⟨nm0,mn0,rn0⟩
  simp only [Nat.add_zero] at nm0
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok n0 .r6 .r8 .r5 .r2 (by decide)) ?_
  rintro c0 ⟨vc0,rc0⟩
  obtain n0lo : n0.gpr .r6=v0.gpr .r6 := by
    rw [rn0.gpr .r6 (by decide),rv1.regs .r6 (by decide),ru1.gpr .r6 (by decide)]
  obtain cr0 : v1.gpr .r8=s.gpr .r8 := by
    rw [rv1.regs .r8 (by decide),ru1.gpr .r8 (by decide),rv0.regs .r8 (by decide),ru0.gpr .r8 (by decide)]
  rw [nm0,mv1,rn0.gpr .r2 (by decide),rV1.gpr .r2 (by decide),n0lo,
    rn0.gpr .r8 (by decide),cr0] at vc0
  obtain rC0 : Rest pairClobbers s c0 :=
    rV1.trans ((rn0.mono (by decide)).trans ((framed rc0).mono (by decide)))
  obtain mc0 : c0.mem=s.mem := rc0.mem.trans (mn0.trans mv1)
  obtain cp0 : c0.gpr .r7=v1.gpr .r7 := by
    rw [rc0.regs .r7 (by decide),rn0.gpr .r7 (by decide)]
  rw [WP.seq_iff]
  change WP isa (.block [.str .r6 .r0 0]) c0 _
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using ((ws.congr rC0.wr).ea ((rC0.gpr .r0 (by decide)).trans pd) (imm:=0) (by omega_using [fd])))
    (by rw [rC0.wr];exact ws.write (by omega_using [fd])) fun st hst => WP.block_nil ?_
  rw [WP.seq_iff]
  obtain rST : Rest pairClobbers s st := rC0.trans (hst.rest _)
  obtain mst : st.mem=s.mem.writeW (off (State.addr base) d) (c0.gpr .r6) := by rw [hst.mem,mc0]
  obtain outside : Outside (State.addr base) d 4 s.mem st.mem := by
    rw [mst];exact writeW32_outside _ _ _ (by have := ws.nowrap;omega_using [fd, this])
  obtain oldM1 : st.mem.readW (off (State.addr base) (m+4)) 32=
      s.mem.readW (off (State.addr base) (m+4)) 32 :=
    outside_read32 outside (by rcases sep with h|h <;> omega_using [h]) (by have := ws.nowrap;omega_using [fm, this])
  refine WP.mono (loadsM_ok st (ws.congr rST.wr) (by decide) fm
    ((rST.gpr .r4 (by decide)).trans pm)) ?_
  rintro n1 ⟨nm1,mn1,rn1⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok n1 .r10 .r8 .r5 .r2 (by decide)) ?_
  rintro c1 ⟨vc1,rc1⟩
  obtain n1lo : n1.gpr .r10=v1.gpr .r10 := by
    rw [rn1.gpr .r10 (by decide),hst.gpr,rc0.regs .r10 (by decide),rn0.gpr .r10 (by decide)]
  rw [nm1,oldM1,rn1.gpr .r2 (by decide),rST.gpr .r2 (by decide),
    n1lo,rn1.gpr .r8 (by decide),hst.gpr] at vc1
  obtain rC1 : Rest pairClobbers s c1 :=
    rST.trans ((rn1.mono (by decide)).trans ((framed rc1).mono (by decide)))
  obtain mc1 : c1.mem=s.mem.writeW (off (State.addr base) d) (c0.gpr .r6) :=
    rc1.mem.trans (mn1.trans mst)
  obtain out0 : c1.gpr .r6=c0.gpr .r6 := by rw [rc1.regs .r6 (by decide),rn1.gpr .r6 (by decide),hst.gpr]
  obtain cp1 : c1.gpr .r7=v1.gpr .r7 := by
    rw [rc1.regs .r7 (by decide),rn1.gpr .r7 (by decide),hst.gpr,cp0]
  obtain value : (c1.gpr .r6).toNat+2^32*(c1.gpr .r10).toNat+
      2^64*((c1.gpr .r7).toNat+(c1.gpr .r8).toNat)=
      (s.gpr .r1).toNat*(w32 s.mem (State.addr base) a+2^32*w32 s.mem (State.addr base) (a+4))+
      (s.gpr .r2).toNat*(w32 s.mem (State.addr base) m+2^32*w32 s.mem (State.addr base) (m+4))+
      (w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8))+
      (s.gpr .r7).toNat+(s.gpr .r8).toNat := by
    rw [out0,cp1]
    dsimp only [w32]
    rw [Nat.mul_comm _ (s.gpr .r1).toNat] at vp0 vp1
    rw [Nat.mul_comm _ (s.gpr .r2).toNat] at vc0 vc1
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (s.gpr .r1).toNat (2^32),Nat.mul_left_comm (s.gpr .r2).toNat (2^32)]
    omega_using [vp0, vp1, vc0, vc1]
  change WP isa (.block [.str .r10 .r0 4]) c1 _
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    ((ws.congr rC1.wr).ea ((rC1.gpr .r0 (by decide)).trans pd) (by omega_using [fd]))
    (by rw [rC1.wr];exact ws.write (by omega_using [fd])) fun t ht => WP.block_nil ?_
  exact ⟨by rw [ht.gpr];exact value,
    by rw [ht.mem,mc1,←out0,ht.gpr],rC1.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.Fios

end

end


/-! Advance public pointers after a proved quotient-prefix update. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem advance_inv {s0 s u : State} {x q base : BitVec 32} {size acc b mod n i k : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (hk : k=1 ∨ k=2) (bound : i+k+1≤n) (rs : Rest pairClobbers s u)
    (outside : Outside (State.addr base) acc (4*(i+k)) s0.mem u.mem)
    (value : 2^32*val32 u.mem (State.addr base) acc (i+k)+
      2^(32*((i+k)+1))*((u.gpr .r7).toNat+(u.gpr .r8).toNat)=
      val32 s0.mem (State.addr base) acc ((i+k)+1)+
      x.toNat*val32 s0.mem (State.addr base) b ((i+k)+1)+
      q.toNat*val32 s0.mem (State.addr base) mod ((i+k)+1)) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r4 .r4 (.imm (BitVec.ofNat 32 (4*k))),
      .subs .lr .lr (.imm (BitVec.ofNat 32 k))]) u fun t =>
      Inv s0 x q base acc b mod n (i+k) t ∧ t.z=decide (i+k+1=n) := by
  refine WP.mono (advance_ok u k hk) ?_
  rintro t ⟨p0,p12,p4,count,zero,mem,rt⟩
  obtain small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega_arith
  refine ⟨⟨bound,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [p0,rs.gpr .r0 (by decide),inv.outPtr,Offset.add_add]
    congr 2
    omega_using []
  · rw [p12,rs.gpr .r12 (by decide),inv.bPtr,Offset.add_add]
    congr 2
    omega_using []
  · rw [p4,rs.gpr .r4 (by decide),inv.mPtr,Offset.add_add]
    congr 2
    omega_using []
  · rw [count,rs.gpr .lr (by decide),inv.count,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hk]) (by omega_using [bound])]
    congr 1
    omega_using []
  · rw [rt.gpr .r1 (by decide),rs.gpr .r1 (by decide),inv.scalar]
  · rw [rt.gpr .r2 (by decide),rs.gpr .r2 (by decide),inv.quotient]
  · rw [mem];exact outside
  · rw [mem,rt.gpr .r7 (by decide),rt.gpr .r8 (by decide)];exact value
  · exact inv.rest.trans ((rs.mono (by decide)).trans
      (rt.mono (by decide)))
  · rw [zero,rs.gpr .lr (by decide),inv.count,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hk]) (by omega_using [bound]),ofNat_beq_zero (by omega_using [small])]
    simp only [show n-(i+1)-k=0 ↔ i+k+1=n by omega_using [bound]]

end VG.Proof.Bignum.Arm.Fios

end

end

/-! The initial one-limb step establishes the parity needed by the paired loop. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosStep.lean`, which only this module imported.
section

/-! A fused step scans each old accumulator word once and writes the quotient below it. -/

section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

/-- The two carries remain separate machine words, but contribute their full integer sum. -/
theorem step_ok (s : State) {base : BitVec 32} {size a m d : Nat}
    (ws : Workspace s base size) (fa : a+4≤size) (fm : m+4≤size) (fd : d+8≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa VG.Impl.Bignum.Arm.Fios.step s fun t =>
      (t.gpr .r6).toNat+2^32*((t.gpr .r7).toNat+(t.gpr .r8).toNat)=
        (s.gpr .r1).toNat*w32 s.mem (State.addr base) a+
        (s.gpr .r2).toNat*w32 s.mem (State.addr base) m+
        w32 s.mem (State.addr base) (d+4)+(s.gpr .r7).toNat+(s.gpr .r8).toNat ∧
      t.mem=s.mem.writeW (off (State.addr base) d) (t.gpr .r6) ∧
      Rest [.r3,.r5,.r6,.r7,.r8] s t := by
  rw [VG.Impl.Bignum.Arm.Fios.step,WP.seq_iff]
  have loads : WP isa (.block VG.Impl.Bignum.Arm.Fios.loads) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) a) 32 ∧
      u.gpr .r5=s.mem.readW (off (State.addr base) m) 32 ∧
      u.gpr .r6=s.mem.readW (off (State.addr base) (d+4)) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r5,.r6] s u := by
    unfold VG.Impl.Bignum.Arm.Fios.loads
    refine wp_ldr (a:=off (State.addr base) a) (by decide)
      (by simpa only [Nat.add_zero] using ws.ea pa (imm:=0) (by omega)) (ws.read fa) fun u hu => ?_
    refine wp_ldr (a:=off (State.addr base) m) (by decide)
      (by rw [hu.other .r4 (by decide)];simpa only [Nat.add_zero] using ws.ea pm (imm:=0) (by omega))
      (by rw [hu.rd,hu.wr];exact ws.read fm) fun v hv => ?_
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide)
      (by rw [hv.other .r0 (by decide),hu.other .r0 (by decide)];exact ws.ea pd (by omega))
      (by rw [hv.rd,hv.wr,hu.rd,hu.wr];exact ws.read fd) fun w hw => WP.block_nil ?_
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [hw.other .r3 (by decide),hv.other .r3 (by decide),hu.gpr]
    · rw [hw.other .r5 (by decide),hv.gpr,hu.mem]
    · rw [hw.gpr,hv.mem,hu.mem]
    · rw [hw.mem,hv.mem,hu.mem]
    · exact (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide)))
  refine WP.mono loads ?_
  rintro u ⟨ua,um,ud,mu,ru⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u .r6 .r7 .r3 .r1 (by decide)) ?_
  rintro v ⟨vp,rv⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok v .r6 .r8 .r5 .r2 (by decide)) ?_
  rintro w ⟨wc,rw'⟩
  have value : (w.gpr .r6).toNat+2^32*((w.gpr .r7).toNat+(w.gpr .r8).toNat)=
      (s.gpr .r1).toNat*w32 s.mem (State.addr base) a+
      (s.gpr .r2).toNat*w32 s.mem (State.addr base) m+
      w32 s.mem (State.addr base) (d+4)+(s.gpr .r7).toNat+(s.gpr .r8).toNat := by
    rw [rv.regs .r5 (by decide),rv.regs .r2 (by decide),rv.regs .r8 (by decide)] at wc
    rw [ru.gpr .r1 (by decide),ru.gpr .r7 (by decide),ua,ud] at vp
    rw [ru.gpr .r2 (by decide),ru.gpr .r8 (by decide),um] at wc
    rw [rw'.regs .r7 (by decide)]
    dsimp only [w32]
    have h := two_products vp wc
    simpa only [Nat.mul_comm] using h
  have rests : Rest [.r3,.r5,.r6,.r7,.r8] s w :=
    (ru.mono (by decide)).trans
      ((show Rest [.r6,.r7] u v from ⟨rv.regs,rv.rd,rv.wr,rv.sp⟩).mono (by decide) |>.trans
        ((show Rest [.r6,.r8] v w from ⟨rw'.regs,rw'.rd,rw'.wr,rw'.sp⟩).mono (by decide)))
  have memW : w.mem=s.mem := rw'.mem.trans (rv.mem.trans mu)
  have ptrW : w.gpr .r0=base+BitVec.ofNat 32 d := (rests.gpr .r0 (by decide)).trans pd
  change WP isa (.block [.str .r6 .r0 0]) w _
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using (ws.congr rests.wr).ea ptrW (imm:=0) (by omega))
    (by rw [rests.wr];exact ws.write (by omega)) fun t ht => WP.block_nil ?_
  exact ⟨by rw [ht.gpr];exact value,
    by rw [ht.mem,memW,ht.gpr],rests.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.Fios
end

end

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
  refine WP.mono (step_ok s ws (by omega_using [hi, inf]) (by omega_using [hi, modf]) (by omega_using [hi, outf]) inv.bPtr inv.mPtr inv.outPtr) ?_
  rintro u ⟨value,mem,rest⟩
  have oldT := inv.outside.w32 (d:=acc+4*(i+1)) (by omega_using []) (by omega_using [hi, nowrap, outf])
  have oldB := inv.outside.w32 (d:=b+4*(i+1))
    (by rcases ctx.accB with h|h <;> omega_arith) (by omega_using [hi, nowrap, inf])
  have oldM := inv.outside.w32 (d:=mod+4*(i+1))
    (by rcases ctx.accM with h|h <;> omega_arith) (by omega_using [hi, nowrap, modf])
  rw [inv.scalar,inv.quotient,oldB,oldM,show acc+4*i+4=acc+4*(i+1) by omega_using [],oldT] at value
  have writes := writeW32_outside s.mem (State.addr base) (d:=acc+4*i) (u.gpr .r6) (by omega_using [hi, nowrap, outf])
  rw [←mem] at writes
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem u.mem :=
    (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using []))
  have low := writes.val32 (d:=acc) (k:=i) (by omega_using []) (by omega_using [hi, nowrap, outf])
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
    omega_using [value]
  exact advance_inv ctx inv (Or.inl rfl) (by omega_using [hi])
    (rest.mono (by decide)) outside (prefix_extend inv.value segment stored)

end VG.Proof.Bignum.Arm.Fios

end

end

/-! ### `Bignum.Arm.FiosFirst`, which this module and modules that import it used -/

section

/-! The first integrated product determines a scalar which cancels its low word. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mul wp_dp wp_subs op2_imm dpVal)

private theorem firstLoads_ok (s : State) {base : BitVec 32} {size a m d : Nat}
    (ws : Workspace s base size) (fa : a+4≤size) (fm : m+4≤size) (fd : d+4≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios.firstLoads) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) a) 32 ∧
      u.gpr .r5=s.mem.readW (off (State.addr base) m) 32 ∧
      u.gpr .r6=s.mem.readW (off (State.addr base) d) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r5,.r6] s u := by
  unfold VG.Impl.Bignum.Arm.Fios.firstLoads
  refine wp_ldr (a:=off (State.addr base) a) (by decide)
    (by simpa only [Nat.add_zero] using ws.ea pa (imm:=0) (by omega_using [fa])) (ws.read fa) fun u hu => ?_
  refine wp_ldr (a:=off (State.addr base) m) (by decide)
    (by rw [hu.other .r4 (by decide)];simpa only [Nat.add_zero] using ws.ea pm (imm:=0) (by omega_using [fm]))
    (by rw [hu.rd,hu.wr];exact ws.read fm) fun v hv => ?_
  refine wp_ldr (a:=off (State.addr base) d) (by decide)
    (by rw [hv.other .r0 (by decide),hu.other .r0 (by decide)]
        simpa only [Nat.add_zero] using ws.ea pd (imm:=0) (by omega_using [fd]))
    (by rw [hv.rd,hv.wr,hu.rd,hu.wr];exact ws.read fd) fun w hw => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hw.other .r3 (by decide),hv.other .r3 (by decide),hu.gpr]
  · rw [hw.other .r5 (by decide),hv.gpr,hu.mem]
  · rw [hw.gpr,hv.mem,hu.mem]
  · rw [hw.mem,hv.mem,hu.mem]
  · exact (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide)))

theorem first_ok (s : State) {base : BitVec 32} {size a m d n : Nat}
    (ws : Workspace s base size) (fa : a+4≤size) (fm : m+4≤size) (fd : d+4≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d)
    (cnt : s.gpr .lr=BitVec.ofNat 32 n) (hn : 0<n) (hn32 : n<2^32)
    (c7 : s.gpr .r7=0) (c8 : s.gpr .r8=0)
    (inverse : (w32 s.mem (State.addr base) m*(s.gpr .r2).toNat+1)%2^32=0) :
    WP isa VG.Impl.Bignum.Arm.Fios.first s fun t =>
      2^32*((t.gpr .r7).toNat+(t.gpr .r8).toNat)=
        w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a+
          (t.gpr .r2).toNat*w32 s.mem (State.addr base) m ∧
      t.gpr .r2=s.gpr .r2*BitVec.ofNat 32
        (w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a) ∧
      (t.gpr .r2).toNat<2^32 ∧ t.gpr .r0=base+BitVec.ofNat 32 d ∧
      t.gpr .r12=base+BitVec.ofNat 32 (a+4) ∧ t.gpr .r4=base+BitVec.ofNat 32 (m+4) ∧
      t.gpr .lr=BitVec.ofNat 32 (n-1) ∧ t.gpr .r1=s.gpr .r1 ∧ t.mem=s.mem ∧
      Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.Fios.first,WP.seq_iff]
  refine WP.mono (firstLoads_ok s ws fa fm fd pa pm pd) ?_
  rintro u ⟨ua,um,ud,mu,ru⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u .r6 .r7 .r3 .r1 (by decide)) ?_
  rintro v ⟨vp,rv⟩
  have vp' : (v.gpr .r6).toNat+2^32*(v.gpr .r7).toNat=
      w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a := by
    rw [ua,ud,ru.gpr .r1 (by decide),ru.gpr .r7 (by decide),c7] at vp
    simpa only [w32,show (0 : BitVec 32).toNat=0 from rfl,Nat.add_zero,Nat.zero_add,Nat.mul_comm,Nat.add_comm] using vp
  have low : v.gpr .r6=BitVec.ofNat 32
      (w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have := (v.gpr .r6).isLt
    omega
  rw [WP.seq_iff]
  refine wp_mul fun w hw => WP.block_nil ?_
  have q : w.gpr .r2=s.gpr .r2*BitVec.ofNat 32
      (w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a) := by
    rw [hw.gpr,rv.regs .r2 (by decide),ru.gpr .r2 (by decide),low]
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok w .r6 .r8 .r5 .r2 (by decide)) ?_
  rintro z ⟨zc,rz⟩
  have zc' : (z.gpr .r6).toNat+2^32*(z.gpr .r8).toNat=
      w32 s.mem (State.addr base) m*(w.gpr .r2).toNat+(v.gpr .r6).toNat := by
    rw [hw.other .r5 (by decide),rv.regs .r5 (by decide),um,
      hw.other .r6 (by decide),hw.other .r8 (by decide),rv.regs .r8 (by decide),
      ru.gpr .r8 (by decide),c8] at zc
    simpa only [w32,show (0 : BitVec 32).toNat=0 from rfl,Nat.add_zero] using zc
  have z0 : z.gpr .r6=0 := by
    apply BitVec.eq_of_toNat_eq
    have cancel := mont_low
      (w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a)
      (s.gpr .r2).toNat (w32 s.mem (State.addr base) m) inverse
    have lowN := congrArg BitVec.toNat low
    rw [BitVec.toNat_ofNat] at lowN
    have qN := congrArg BitVec.toNat q
    rw [BitVec.toNat_mul,BitVec.toNat_ofNat] at qN
    have qN' : (w.gpr .r2).toNat=
        ((w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a)*
          (s.gpr .r2).toNat)%2^32 := by
      rw [qN,Nat.mul_mod,Nat.mod_mod,← Nat.mul_mod,Nat.mul_comm]
    rw [qN',lowN] at zc'
    have zr := (z.gpr .r6).isLt
    change (z.gpr .r6).toNat=0
    rw [Nat.mul_comm] at cancel
    omega
  have value : 2^32*((z.gpr .r7).toNat+(z.gpr .r8).toNat)=
      w32 s.mem (State.addr base) d+(s.gpr .r1).toNat*w32 s.mem (State.addr base) a+
        (w.gpr .r2).toNat*w32 s.mem (State.addr base) m := by
    rw [rz.regs .r7 (by decide),hw.other .r7 (by decide)]
    rw [z0] at zc'
    change 0+2^32*(z.gpr .r8).toNat=_ at zc'
    rw [Nat.mul_comm (w32 s.mem (State.addr base) m) (w.gpr .r2).toNat] at zc'
    omega
  have rests : Rest [.r2,.r3,.r5,.r6,.r7,.r8] s z :=
    (ru.mono (by decide)).trans
      ((show Rest [.r6,.r7] u v from ⟨rv.regs,rv.rd,rv.wr,rv.sp⟩).mono (by decide) |>.trans
        ((hw.rest (by decide)).trans
          ((show Rest [.r6,.r8] w z from ⟨rz.regs,rz.rd,rz.wr,rz.sp⟩).mono (by decide))))
  have mz : z.mem=s.mem := rz.mem.trans (hw.mem.trans (rv.mem.trans mu))
  change WP isa (.block VG.Impl.Bignum.Arm.Fios.firstNext) z _
  unfold VG.Impl.Bignum.Arm.Fios.firstNext
  refine wp_dp (op2_imm (by decide)) fun s1 h1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 h2 => ?_
  refine wp_subs (op2_imm (by decide)) fun t ht _ => WP.block_nil ?_
  refine ⟨?_,?_,(t.gpr .r2).isLt,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r7 (by decide),ht.other .r8 (by decide),h2.other .r7 (by decide),
      h2.other .r8 (by decide),h1.other .r7 (by decide),h1.other .r8 (by decide),
      ht.other .r2 (by decide),h2.other .r2 (by decide),h1.other .r2 (by decide),
      rz.regs .r2 (by decide)]
    exact value
  · rw [ht.other .r2 (by decide),h2.other .r2 (by decide),h1.other .r2 (by decide),rz.regs .r2 (by decide)]
    exact q
  · rw [ht.other .r0 (by decide),h2.other .r0 (by decide),h1.other .r0 (by decide),
      rests.gpr .r0 (by decide),pd]
  · rw [ht.other .r12 (by decide),h2.other .r12 (by decide),h1.gpr,dpVal,
      rests.gpr .r12 (by decide),pa]
    exact Offset.add_add _ _ _
  · rw [ht.other .r4 (by decide),h2.gpr,dpVal,h1.other .r4 (by decide),rests.gpr .r4 (by decide),pm]
    exact Offset.add_add _ _ _
  · rw [ht.gpr,h2.other .lr (by decide),h1.other .lr (by decide),rests.gpr .lr (by decide),cnt]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) (by omega)
  · rw [ht.other .r1 (by decide),h2.other .r1 (by decide),h1.other .r1 (by decide),rests.gpr .r1 (by decide)]
  · rw [ht.mem,h2.mem,h1.mem,mz]
  · exact (rests.mono (by decide)).trans
      ((h1.rest (by decide)).trans
        ((h2.rest (by decide)).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.Fios

end

end

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
