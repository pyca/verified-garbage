module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.FiosLoads
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

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
  refine WP.mono (loadsA_ok s .r6 (by decide) ws (by decide) (by decide) (by omega) (by omega) pa pd) ?_
  rintro u0 ⟨ua0,ut0,mu0,ru0⟩
  simp only [Nat.add_zero] at ua0
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u0 .r6 .r7 .r3 .r1 (by decide)) ?_
  rintro v0 ⟨vp0,rv0⟩
  rw [ua0,ut0,ru0.gpr .r1 (by simp),ru0.gpr .r7 (by simp)] at vp0
  have rV0 : Rest pairClobbers s v0 :=
    (ru0.mono (by simp [pairClobbers])).trans ((framed rv0).mono (by simp [pairClobbers]))
  rw [WP.seq_iff]
  refine WP.mono (loadsA_ok v0 .r10 (by decide) (ws.congr rV0.wr) (by decide) (by decide) fa fd
    ((rV0.gpr .r12 (by simp [pairClobbers])).trans pa)
    ((rV0.gpr .r0 (by simp [pairClobbers])).trans pd)) ?_
  rintro u1 ⟨ua1,ut1,mu1,ru1⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u1 .r10 .r7 .r3 .r1 (by decide)) ?_
  rintro v1 ⟨vp1,rv1⟩
  have mv0 : v0.mem=s.mem := rv0.mem.trans mu0
  rw [ua1,ut1,mv0,ru1.gpr .r1 (by simp),rV0.gpr .r1 (by simp [pairClobbers]),
    ru1.gpr .r7 (by simp)] at vp1
  have rV1 : Rest pairClobbers s v1 :=
    rV0.trans ((ru1.mono (by simp [pairClobbers])).trans ((framed rv1).mono (by simp [pairClobbers])))
  have mv1 : v1.mem=s.mem := rv1.mem.trans (mu1.trans mv0)
  rw [WP.seq_iff]
  refine WP.mono (loadsM_ok v1 (ws.congr rV1.wr) (by decide) (by omega)
    ((rV1.gpr .r4 (by simp [pairClobbers])).trans pm)) ?_
  rintro n0 ⟨nm0,mn0,rn0⟩
  simp only [Nat.add_zero] at nm0
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok n0 .r6 .r8 .r5 .r2 (by decide)) ?_
  rintro c0 ⟨vc0,rc0⟩
  have n0lo : n0.gpr .r6=v0.gpr .r6 := by
    rw [rn0.gpr .r6 (by simp),rv1.regs .r6 (by simp),ru1.gpr .r6 (by simp)]
  have cr0 : v1.gpr .r8=s.gpr .r8 := by
    rw [rv1.regs .r8 (by simp),ru1.gpr .r8 (by simp),rv0.regs .r8 (by simp),ru0.gpr .r8 (by simp)]
  rw [nm0,mv1,rn0.gpr .r2 (by simp),rV1.gpr .r2 (by simp [pairClobbers]),n0lo,
    rn0.gpr .r8 (by simp),cr0] at vc0
  have rC0 : Rest pairClobbers s c0 :=
    rV1.trans ((rn0.mono (by simp [pairClobbers])).trans ((framed rc0).mono (by simp [pairClobbers])))
  have mc0 : c0.mem=s.mem := rc0.mem.trans (mn0.trans mv1)
  have cp0 : c0.gpr .r7=v1.gpr .r7 := by
    rw [rc0.regs .r7 (by simp),rn0.gpr .r7 (by simp)]
  rw [WP.seq_iff]
  change WP isa (.block [.str .r6 .r0 0]) c0 _
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using ((ws.congr rC0.wr).ea ((rC0.gpr .r0 (by simp [pairClobbers])).trans pd) (imm:=0) (by omega)))
    (by rw [rC0.wr];exact ws.write (by omega)) fun st hst => WP.block_nil ?_
  rw [WP.seq_iff]
  have rST : Rest pairClobbers s st := rC0.trans (hst.rest _)
  have mst : st.mem=s.mem.writeW (off (State.addr base) d) (c0.gpr .r6) := by rw [hst.mem,mc0]
  have outside : Outside (State.addr base) d 4 s.mem st.mem := by
    rw [mst];exact writeW32_outside _ _ _ (by have := ws.nowrap;omega)
  have oldM1 : st.mem.readW (off (State.addr base) (m+4)) 32=
      s.mem.readW (off (State.addr base) (m+4)) 32 :=
    outside_read32 outside (by rcases sep with h|h <;> omega) (by have := ws.nowrap;omega)
  refine WP.mono (loadsM_ok st (ws.congr rST.wr) (by decide) fm
    ((rST.gpr .r4 (by simp [pairClobbers])).trans pm)) ?_
  rintro n1 ⟨nm1,mn1,rn1⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok n1 .r10 .r8 .r5 .r2 (by decide)) ?_
  rintro c1 ⟨vc1,rc1⟩
  have n1lo : n1.gpr .r10=v1.gpr .r10 := by
    rw [rn1.gpr .r10 (by simp),hst.gpr,rc0.regs .r10 (by simp),rn0.gpr .r10 (by simp)]
  rw [nm1,oldM1,rn1.gpr .r2 (by simp),rST.gpr .r2 (by simp [pairClobbers]),
    n1lo,rn1.gpr .r8 (by simp),hst.gpr] at vc1
  have rC1 : Rest pairClobbers s c1 :=
    rST.trans ((rn1.mono (by simp [pairClobbers])).trans ((framed rc1).mono (by simp [pairClobbers])))
  have mc1 : c1.mem=s.mem.writeW (off (State.addr base) d) (c0.gpr .r6) :=
    rc1.mem.trans (mn1.trans mst)
  have out0 : c1.gpr .r6=c0.gpr .r6 := by rw [rc1.regs .r6 (by simp),rn1.gpr .r6 (by simp),hst.gpr]
  have cp1 : c1.gpr .r7=v1.gpr .r7 := by
    rw [rc1.regs .r7 (by simp),rn1.gpr .r7 (by simp),hst.gpr,cp0]
  have value : (c1.gpr .r6).toNat+2^32*(c1.gpr .r10).toNat+
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
    omega
  change WP isa (.block [.str .r10 .r0 4]) c1 _
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    ((ws.congr rC1.wr).ea ((rC1.gpr .r0 (by simp [pairClobbers])).trans pd) (by omega))
    (by rw [rC1.wr];exact ws.write (by omega)) fun t ht => WP.block_nil ?_
  exact ⟨by rw [ht.gpr];exact value,
    by rw [ht.mem,mc1,←out0,ht.gpr],rC1.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.Fios
