module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.FiosLoads
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Product and cancellation use separate carry registers. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Bignum.Arm.Fios
open VG.Proof.X25519.Arm (Rest wp_str)

private theorem framed {s t : State} {rs : List Reg}
    (h : MacFrame rs s t) : Rest rs s t := ⟨h.regs,h.rd,h.wr,h.sp⟩

theorem productAt_ok (s : State) (dst : Reg) (hdst : dst=.r6 ∨ dst=.r10)
    {base : BitVec 32} {size a d k : Nat}
    (ws : Workspace s base size) (hk : k+4<4096) (fa : a+k+4≤size) (fd : d+k+8≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a) (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.productAt k dst) s fun t =>
      (t.gpr dst).toNat+2^32*(t.gpr .r7).toNat=
        (s.gpr .r1).toNat*w32 s.mem (State.addr base) (a+k)+
        w32 s.mem (State.addr base) (d+k+4)+(s.gpr .r7).toNat ∧
      t.mem=s.mem ∧ Rest [.r3,dst,.r7] s t := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.productAt,WP.seq_iff]
  refine WP.mono (loadsA_ok s dst (by rcases hdst with rfl|rfl <;> decide) ws
    (by omega) hk fa (by omega) pa pd) ?_
  rintro u ⟨a,t,mem,rest⟩
  simp only [←Nat.add_assoc] at t
  refine WP.mono (umaal_ok u dst .r7 .r3 .r1 (by rcases hdst with rfl|rfl <;> decide)) ?_
  rintro v ⟨value,frame⟩
  rw [a,t,rest.gpr .r1 (by rcases hdst with rfl|rfl <;> simp),
    rest.gpr .r7 (by rcases hdst with rfl|rfl <;> simp),Nat.mul_comm _ (s.gpr .r1).toNat] at value
  exact ⟨by simpa only [w32,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using value,
    frame.mem.trans mem,(rest.mono (by simp)).trans ((framed frame).mono (by simp))⟩

theorem cancelAt_ok (s : State) (dst : Reg) (hdst : dst=.r6 ∨ dst=.r10)
    {base : BitVec 32} {size m d k : Nat}
    (ws : Workspace s base size) (hk : k<4096) (fm : m+k+4≤size) (fd : d+k+4≤size)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m) (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.cancelAt k dst) s fun t =>
      (t.gpr dst).toNat+2^32*(t.gpr .r8).toNat=
        (s.gpr dst).toNat+(s.gpr .r2).toNat*w32 s.mem (State.addr base) (m+k)+(s.gpr .r8).toNat ∧
      t.mem=s.mem.writeW (off (State.addr base) (d+k)) (t.gpr dst) ∧
      Rest [.r5,dst,.r8] s t := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.cancelAt,WP.seq_iff]
  refine WP.mono (loadsM_ok s ws hk fm pm) ?_
  rintro u ⟨m,mem,rest⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u dst .r8 .r5 .r2 (by rcases hdst with rfl|rfl <;> decide)) ?_
  rintro v ⟨value,frame⟩
  rw [m,rest.gpr dst (by rcases hdst with rfl|rfl <;> decide),
    rest.gpr .r2 (by decide),rest.gpr .r8 (by decide),Nat.mul_comm _ (s.gpr .r2).toNat] at value
  have rv : Rest [.r5,dst,.r8] s v :=
    (rest.mono (by simp)).trans ((framed frame).mono (by simp))
  have mv : v.mem=s.mem := frame.mem.trans mem
  refine wp_str (a:=off (State.addr base) (d+k)) hk
    ((ws.congr rv.wr).ea ((rv.gpr .r0 (by rcases hdst with rfl|rfl <;> decide)).trans pd) (by omega))
    (by rw [rv.wr];exact ws.write fd) fun t ht => WP.block_nil ?_
  exact ⟨by simpa only [ht.gpr,w32,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using value,
    by rw [ht.mem,mv,ht.gpr],rv.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.FiosPipelined
