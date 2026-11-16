module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.FiosLoads
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvance
import VerifiedGarbage.Proof.Framework.AddrArith

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
