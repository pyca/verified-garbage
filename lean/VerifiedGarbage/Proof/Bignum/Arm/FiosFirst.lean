module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith

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
    (by simpa only [Nat.add_zero] using ws.ea pa (imm:=0) (by omega)) (ws.read fa) fun u hu => ?_
  refine wp_ldr (a:=off (State.addr base) m) (by decide)
    (by rw [hu.other .r4 (by decide)];simpa only [Nat.add_zero] using ws.ea pm (imm:=0) (by omega))
    (by rw [hu.rd,hu.wr];exact ws.read fm) fun v hv => ?_
  refine wp_ldr (a:=off (State.addr base) d) (by decide)
    (by rw [hv.other .r0 (by decide),hu.other .r0 (by decide)]
        simpa only [Nat.add_zero] using ws.ea pd (imm:=0) (by omega))
    (by rw [hv.rd,hv.wr,hu.rd,hu.wr];exact ws.read fd) fun w hw => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hw.other .r3 (by decide),hv.other .r3 (by decide),hu.gpr]
  · rw [hw.other .r5 (by decide),hv.gpr,hu.mem]
  · rw [hw.gpr,hv.mem,hu.mem]
  · rw [hw.mem,hv.mem,hu.mem]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (hw.rest (by simp)))

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
    rw [ua,ud,ru.gpr .r1 (by simp),ru.gpr .r7 (by simp),c7] at vp
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
    rw [hw.gpr,rv.regs .r2 (by simp),ru.gpr .r2 (by simp),low]
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok w .r6 .r8 .r5 .r2 (by decide)) ?_
  rintro z ⟨zc,rz⟩
  have zc' : (z.gpr .r6).toNat+2^32*(z.gpr .r8).toNat=
      w32 s.mem (State.addr base) m*(w.gpr .r2).toNat+(v.gpr .r6).toNat := by
    rw [hw.other .r5 (by decide),rv.regs .r5 (by simp),um,
      hw.other .r6 (by decide),hw.other .r8 (by decide),rv.regs .r8 (by simp),
      ru.gpr .r8 (by simp),c8] at zc
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
    rw [rz.regs .r7 (by simp),hw.other .r7 (by decide)]
    rw [z0] at zc'
    change 0+2^32*(z.gpr .r8).toNat=_ at zc'
    rw [Nat.mul_comm (w32 s.mem (State.addr base) m) (w.gpr .r2).toNat] at zc'
    omega
  have rests : Rest [.r2,.r3,.r5,.r6,.r7,.r8] s z :=
    (ru.mono (by simp)).trans
      ((show Rest [.r6,.r7] u v from ⟨rv.regs,rv.rd,rv.wr,rv.sp⟩).mono (by simp) |>.trans
        ((hw.rest (by simp)).trans
          ((show Rest [.r6,.r8] w z from ⟨rz.regs,rz.rd,rz.wr,rz.sp⟩).mono (by simp))))
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
      rz.regs .r2 (by simp)]
    exact value
  · rw [ht.other .r2 (by decide),h2.other .r2 (by decide),h1.other .r2 (by decide),rz.regs .r2 (by simp)]
    exact q
  · rw [ht.other .r0 (by decide),h2.other .r0 (by decide),h1.other .r0 (by decide),
      rests.gpr .r0 (by simp),pd]
  · rw [ht.other .r12 (by decide),h2.other .r12 (by decide),h1.gpr,dpVal,
      rests.gpr .r12 (by simp),pa]
    exact Offset.add_add _ _ _
  · rw [ht.other .r4 (by decide),h2.gpr,dpVal,h1.other .r4 (by decide),rests.gpr .r4 (by simp),pm]
    exact Offset.add_add _ _ _
  · rw [ht.gpr,h2.other .lr (by decide),h1.other .lr (by decide),rests.gpr .lr (by simp),cnt]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) (by omega)
  · rw [ht.other .r1 (by decide),h2.other .r1 (by decide),h1.other .r1 (by decide),rests.gpr .r1 (by simp)]
  · rw [ht.mem,h2.mem,h1.mem,mz]
  · exact (rests.mono (by simp [roundClobbers])).trans
      ((h1.rest (by simp [roundClobbers])).trans
        ((h2.rest (by simp [roundClobbers])).trans (ht.rest (by simp [roundClobbers]))))

end VG.Proof.Bignum.Arm.Fios
