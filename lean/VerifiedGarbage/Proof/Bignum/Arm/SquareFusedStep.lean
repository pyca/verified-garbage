module

import VerifiedGarbage.Proof.Bignum.Arm.SquareDiag
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareFusedArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry

/-! The fused UMAAL diagonal doubles each cross-product pair before adding its square. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov op2_reg op2_imm op2_lsr)

theorem squareMacU_ok (s : State) :
    WP isa (.block squareMacU) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2^32 =
        (s.gpr .r1).toNat * (s.gpr .r1).toNat + (s.gpr .r10).toNat + (s.gpr .r11).toNat ∧
      MacFrame [.r3,.r4] s t := by
  let v := (s.gpr .r1).toNat*(s.gpr .r1).toNat+(s.gpr .r11).toNat+(s.gpr .r10).toNat
  let t := (((s.setReg .r3 (s.gpr .r10)).setReg .r4 (s.gpr .r11)).setReg .r3
    (BitVec.ofNat 32 v)).setReg .r4 (BitVec.ofNat 32 (v/2^32))
  refine WP.of_runBlock ⟨t,?_,?_,?_⟩
  · simp only [squareMacU,runBlock_cons,exec,Op2.eval,Option.map_some,runStep_some,
      runBlock_nil,gpr_setReg,reduceCtorEq,↓reduceIte]
    rfl
  · change v%2^32+(v/2^32)%2^32*2^32=_
    have bound := mac_bound (s.gpr .r1) (s.gpr .r1) (s.gpr .r10) (s.gpr .r11)
    have vb : v<2^64 := by dsimp [v];omega
    have hi : v/2^32<2^32 := by omega
    rw [Nat.mod_eq_of_lt hi]
    dsimp [v]
    omega
  · refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
    intro r hr
    have ne3 : r≠.r3 := by intro h;subst r;exact hr (by simp)
    have ne4 : r≠.r4 := by intro h;subst r;exact hr (by simp)
    simp only [t,gpr_setReg_of_ne _ _ ne4,gpr_setReg_of_ne _ _ ne3]

theorem fusedDiagHead_ok (s : State) {base : BitVec 32} {size A T : Nat} (ws : Workspace s base size)
    (fitA : A+4≤size) (fitT : T+8≤size)
    (p12 : s.gpr .r12=base+BitVec.ofNat 32 A) (p0 : s.gpr .r0=base+BitVec.ofNat 32 T) :
    WP isa (.block fusedDiagHead) s fun t =>
      t.gpr .r1=s.mem.readW (off (State.addr base) A) 32 ∧
      (t.gpr .r10).toNat+2^32*(t.gpr .r5).toNat+2^64*(t.gpr .r6).toNat =
        2*(w32 s.mem (State.addr base) T+2^32*w32 s.mem (State.addr base) (T+4)) ∧
      (t.gpr .r6).toNat≤1 ∧ t.gpr .r11=s.gpr .r11 ∧ t.mem=s.mem ∧
      Rest [.r1,.r5,.r6,.r10] s t := by
  have nowrap := ws.nowrap
  unfold fusedDiagHead
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p12 (imm:=0) (by omega))
    (ws.read fitA) fun s1 u1 => ?_
  refine wp_ldr (a:=off (State.addr base) T) (by decide) (by
      rw [u1.other .r0 (by decide)]
      simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm:=0) (by omega))
    (by rw [u1.rd,u1.wr];exact ws.read (by omega)) fun s2 u2 => ?_
  refine wp_ldr (a:=off (State.addr base) (T+4)) (by decide) (by
      rw [u2.other .r0 (by decide),u1.other .r0 (by decide)]
      exact sq_ea nowrap p0 (by omega))
    (by rw [u2.rd,u2.wr,u1.rd,u1.wr];exact ws.read fitT) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_adds (op2_reg _ _) fun s5 u5 c5 => ?_
  refine wp_adc (op2_reg _ _) fun t u6 _ => WP.block_nil ?_
  have lo : s4.gpr .r10=s.mem.readW (off (State.addr base) T) 32 := by
    rw [u4.other .r10 (by decide),u3.other .r10 (by decide),u2.gpr,u1.mem]
  have hi : s4.gpr .r5=s.mem.readW (off (State.addr base) (T+4)) 32 := by
    rw [u4.other .r5 (by decide),u3.gpr,u2.mem,u1.mem]
  have dlow : t.gpr .r10=s4.gpr .r10+s4.gpr .r10 := by rw [u6.other .r10 (by decide),u5.gpr]
  have dhigh : t.gpr .r5=s4.gpr .r5+s4.gpr .r5+
      (if decide (2^32≤(s4.gpr .r10).toNat+(s4.gpr .r10).toNat) then 1 else 0) := by
    rw [u6.gpr,u5.other .r5 (by decide),c5]
  have top : t.gpr .r6=s4.gpr .r5 >>> 31 := by
    rw [u6.other .r6 (by decide),u5.other .r6 (by decide),u4.gpr]
    rw [u4.other .r5 (by decide)]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [u6.other .r1 (by decide),u5.other .r1 (by decide),u4.other .r1 (by decide),
      u3.other .r1 (by decide),u2.other .r1 (by decide),u1.gpr]
  · rw [dlow,dhigh,top,lo,hi]
    exact fused_double_value _ _
  · rw [top,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have := (s4.gpr .r5).isLt
    omega
  · rw [u6.other .r11 (by decide),u5.other .r11 (by decide),u4.other .r11 (by decide),
      u3.other .r11 (by decide),u2.other .r11 (by decide),u1.other .r11 (by decide)]
  · rw [u6.mem,u5.mem,u4.mem,u3.mem,u2.mem,u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))

theorem fusedDiagStep_ok (s : State) {base : BitVec 32} {size A T : Nat} (ws : Workspace s base size)
    (fitA : A+4≤size) (fitT : T+8≤size)
    (p12 : s.gpr .r12=base+BitVec.ofNat 32 A) (p0 : s.gpr .r0=base+BitVec.ofNat 32 T) :
    WP isa diagStepU s fun t =>
      w32 t.mem (State.addr base) T+2^32*w32 t.mem (State.addr base) (T+4)+
          2^64*(t.gpr .r11).toNat =
        w32 s.mem (State.addr base) A*w32 s.mem (State.addr base) A+
          2*(w32 s.mem (State.addr base) T+2^32*w32 s.mem (State.addr base) (T+4))+
          (s.gpr .r11).toNat ∧
      Outside (State.addr base) T 8 s.mem t.mem ∧ t.gpr .r0=s.gpr .r0 ∧ t.gpr .r12=s.gpr .r12 ∧
      t.gpr .lr=s.gpr .lr ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  rw [diagStepU,WP.seq_iff]
  refine WP.mono (fusedDiagHead_ok s ws fitA fitT p12 p0) ?_
  rintro s1 ⟨a1,d1,c1,carry1,mem1,rest1⟩
  rw [WP.seq_iff]
  refine WP.mono (squareMacU_ok s1) ?_
  rintro s2 ⟨mac2,f2⟩
  have q0 : s2.gpr .r0=s.gpr .r0 := by rw [f2.regs .r0 (by simp),rest1.gpr .r0 (by simp)]
  have mem2 : s2.mem=s.mem := f2.mem.trans mem1
  have wr2 : s2.wr=s.wr := f2.wr.trans rest1.wr
  have ea0 {u : State} (hu : u.gpr .r0=s.gpr .r0) :
      State.addr (u.gpr .r0+BitVec.ofNat 32 0)=off (State.addr base) T := by
    rw [hu];simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm:=0) (by omega)
  have ea4 {u : State} (hu : u.gpr .r0=s.gpr .r0) :
      State.addr (u.gpr .r0+BitVec.ofNat 32 4)=off (State.addr base) (T+4) := by
    rw [hu];exact sq_ea nowrap p0 (by omega)
  unfold fusedDiagTail
  refine wp_adds (op2_reg _ _) fun s3 u3 c3 => ?_
  refine wp_adc (op2_imm (by decide)) fun s4 u4 _ => ?_
  refine wp_str (by decide) (ea0 (by rw [u4.other .r0 (by decide),u3.other .r0 (by decide),q0]))
    (by rw [u4.wr,u3.wr,wr2];exact ws.write (by omega)) fun s5 u5 => ?_
  refine wp_str (by decide) (ea4 (by rw [u5.gpr,u4.other .r0 (by decide),u3.other .r0 (by decide),q0]))
    (by rw [u5.wr,u4.wr,u3.wr,wr2];exact ws.write fitT) fun t u6 => WP.block_nil ?_
  have lo : s4.gpr .r3=s2.gpr .r3 := by
    rw [u4.other .r3 (by decide),u3.other .r3 (by decide)]
  have hi : s4.gpr .r4=s2.gpr .r4+s2.gpr .r5 := by rw [u4.other .r4 (by decide),u3.gpr]
  have carry : s4.gpr .r11=s2.gpr .r6+0+
      (if decide (2^32≤(s2.gpr .r4).toNat+(s2.gpr .r5).toNat) then 1 else 0) := by
    rw [u4.gpr,u3.other .r6 (by decide),c3]
  have memT : t.mem=(s.mem.writeW (off (State.addr base) T) (s2.gpr .r3)).writeW
      (off (State.addr base) (T+4)) (s2.gpr .r4+s2.gpr .r5) := by
    rw [u6.mem,u5.mem,u4.mem,u3.mem,mem2,u5.gpr,hi,lo]
  have top : (s2.gpr .r6).toNat≤1 := by rw [f2.regs .r6 (by simp)];exact c1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [w32]
    rw [u6.gpr,u5.gpr,carry,memT,
      rd_other (d:=T+4) (e:=T) _ (by omega) (by omega) (by omega),rd_self,rd_self]
    have fin := fused_finish_value (s2.gpr .r3) (s2.gpr .r4) (s2.gpr .r5) (s2.gpr .r6) top
    rw [a1,carry1] at mac2
    have dh : (s1.gpr .r5).toNat=(s2.gpr .r5).toNat := by rw [f2.regs .r5 (by simp)]
    have dt : (s1.gpr .r6).toNat=(s2.gpr .r6).toNat := by rw [f2.regs .r6 (by simp)]
    rw [dh,dt] at d1
    change _=(s.mem.readW (off (State.addr base) A) 32).toNat*
      (s.mem.readW (off (State.addr base) A) 32).toNat+
      2*((s.mem.readW (off (State.addr base) T) 32).toNat+
        2^32*(s.mem.readW (off (State.addr base) (T+4)) 32).toNat)+(s.gpr .r11).toNat
    simp only [w32] at d1
    omega
  · rw [memT]
    exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [u6.gpr,u5.gpr,u4.other .r0 (by decide),u3.other .r0 (by decide),q0]
  · rw [u6.gpr,u5.gpr,u4.other .r12 (by decide),u3.other .r12 (by decide),
      f2.regs .r12 (by simp),rest1.gpr .r12 (by simp)]
  · rw [u6.gpr,u5.gpr,u4.other .lr (by decide),u3.other .lr (by decide),
      f2.regs .lr (by simp),rest1.gpr .lr (by simp)]
  · have r1 : Rest roundClobbers s s1 := rest1.mono (by simp [roundClobbers])
    have r2 : Rest roundClobbers s1 s2 := ⟨fun r hr => f2.regs r (by
        intro h;apply hr;cases r <;> simp_all [roundClobbers]),f2.rd,f2.wr,f2.sp⟩
    exact r1.trans (r2.trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest _).trans (u6.rest _)))))

end VG.Proof.Bignum.Arm
