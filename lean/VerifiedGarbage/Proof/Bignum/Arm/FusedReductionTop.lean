module

public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! Add the last row carry and store the two high quotient words directly. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp op2_imm dpVal)

theorem top_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d+12≤size)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 d)
    (bound : w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
      (s.gpr .r11).toNat<2^64) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.top s fun t =>
      (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=
        w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
          (s.gpr .r11).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r3)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r4) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (d+8) ∧ Rest [.r0,.r3,.r4] s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.top,WP.seq_iff]
  have loads : WP isa (.block [.ldr .r3 .r0 4,.ldr .r4 .r0 8]) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) (d+4)) 32 ∧
      u.gpr .r4=s.mem.readW (off (State.addr base) (d+8)) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r4] s u := by
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide) (ws.ea ptr (by omega))
      (ws.read (by omega)) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) (d+8)) (by decide)
      (by rw [h.other .r0 (by decide)];exact ws.ea ptr (by omega))
      (by rw [h.rd,h.wr];exact ws.read (by omega)) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r3 (by decide)).trans h.gpr,by rw [k.gpr,h.mem],
      k.mem.trans h.mem,(h.rest (by simp)).trans (k.rest (by simp))⟩
  refine WP.mono loads ?_
  rintro u ⟨low,high,memU,restU⟩
  have carry : u.gpr .r11=s.gpr .r11 := restU.gpr .r11 (by simp)
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok u .r11 (by rw [low,high,carry];dsimp only [w32] at bound;omega)) ?_
  rintro v ⟨value,frame⟩
  have pv : v.gpr .r0=base+BitVec.ofNat 32 d :=
    (frame.regs .r0 (by simp)).trans ((restU.gpr .r0 (by simp)).trans ptr)
  have mv : v.mem=s.mem := frame.mem.trans memU
  have wv : v.wr=s.wr := frame.wr.trans restU.wr
  have wsv := ws.congr wv
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using wsv.ea pv (imm:=0) (by omega))
    (by rw [wv];exact ws.write (by omega)) fun a ha => ?_
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    (by rw [ha.gpr];exact wsv.ea pv (by omega))
    (by rw [ha.wr,wv];exact ws.write (by omega)) fun b hb => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
    rw [low,high,carry] at value
    simpa only [w32,Nat.mul_comm] using value
  · rw [ht.mem,hb.mem,ha.mem,mv,ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
  · rw [ht.gpr,dpVal,hb.gpr,ha.gpr,pv]
    exact Offset.add_add _ _ _
  · have rv : Rest [.r3,.r4] s v := restU.trans ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩
    exact (rv.mono (by simp)).trans ((ha.rest _).trans
      ((hb.rest _).trans (ht.rest (by simp))))

end VG.Proof.Bignum.Arm.FusedReduction
