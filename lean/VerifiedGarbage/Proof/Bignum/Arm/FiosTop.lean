module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide) (ws.ea ptr (by omega))
      (ws.read (by omega)) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) (d+8)) (by decide)
      (by rw [h.other .r0 (by decide)];exact ws.ea ptr (by omega))
      (by rw [h.rd,h.wr];exact ws.read (by omega)) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r3 (by decide)).trans h.gpr,by rw [k.gpr,h.mem],
      k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono loads ?_
  rintro u ⟨low,high,memU,restU⟩
  have carry7 : u.gpr .r7=s.gpr .r7 := restU.gpr .r7 (by decide)
  have carry8 : u.gpr .r8=s.gpr .r8 := restU.gpr .r8 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok u .r7 (by
    rw [low,high,carry7];dsimp only [w32] at bound;omega)) ?_
  rintro v ⟨value7,frame7⟩
  have carry8v : v.gpr .r8=s.gpr .r8 :=
    (frame7.regs .r8 (by decide)).trans carry8
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok v .r8 (by
    rw [value7,low,high,carry7,carry8v];dsimp only [w32] at bound;omega)) ?_
  rintro z ⟨value8,frame8⟩
  have frame := frame7.trans frame8
  have pz : z.gpr .r0=base+BitVec.ofNat 32 d :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  have mz : z.mem=s.mem := frame.mem.trans memU
  have wz : z.wr=s.wr := frame.wr.trans restU.wr
  have wsz := ws.congr wz
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using wsz.ea pz (imm:=0) (by omega))
    (by rw [wz];exact ws.write (by omega)) fun a ha => ?_
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    (by rw [ha.gpr];exact wsz.ea pz (by omega))
    (by rw [ha.wr,wz];exact ws.write (by omega)) fun b hb => ?_
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

theorem top_memory_outside {s t : State} {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d+8≤size)
    (mem : t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r3)).writeW
      (off (State.addr base) (d+4)) (t.gpr .r4)) :
    Outside (State.addr base) d 8 s.mem t.mem := by
  have nowrap := ws.nowrap
  rw [mem]
  exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))

end VG.Proof.Bignum.Arm.Fios
