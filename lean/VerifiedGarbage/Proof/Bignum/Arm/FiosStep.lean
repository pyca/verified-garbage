module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! A fused step scans each old accumulator word once and writes the quotient below it. -/

@[expose] public section
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
    · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (hw.rest (by simp)))
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
    rw [rv.regs .r5 (by simp),rv.regs .r2 (by simp),rv.regs .r8 (by simp)] at wc
    rw [ru.gpr .r1 (by simp),ru.gpr .r7 (by simp),ua,ud] at vp
    rw [ru.gpr .r2 (by simp),ru.gpr .r8 (by simp),um] at wc
    rw [rw'.regs .r7 (by simp)]
    dsimp only [w32]
    have h := two_products vp wc
    simpa only [Nat.mul_comm] using h
  have rests : Rest [.r3,.r5,.r6,.r7,.r8] s w :=
    (ru.mono (by simp)).trans
      ((show Rest [.r6,.r7] u v from ⟨rv.regs,rv.rd,rv.wr,rv.sp⟩).mono (by simp) |>.trans
        ((show Rest [.r6,.r8] v w from ⟨rw'.regs,rw'.rd,rw'.wr,rw'.sp⟩).mono (by simp)))
  have memW : w.mem=s.mem := rw'.mem.trans (rv.mem.trans mu)
  have ptrW : w.gpr .r0=base+BitVec.ofNat 32 d := (rests.gpr .r0 (by simp)).trans pd
  change WP isa (.block [.str .r6 .r0 0]) w _
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using (ws.congr rests.wr).ea ptrW (imm:=0) (by omega))
    (by rw [rests.wr];exact ws.write (by omega)) fun t ht => WP.block_nil ?_
  exact ⟨by rw [ht.gpr];exact value,
    by rw [ht.mem,memW,ht.gpr],rests.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.Fios
