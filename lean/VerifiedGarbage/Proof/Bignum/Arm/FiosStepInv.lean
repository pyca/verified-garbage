module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Impl.Bignum.Arm.Fios

import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvanceInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.TCB.Arm.Isa
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
  refine WP.mono (step_ok s ws (by omega) (by omega) (by omega) inv.bPtr inv.mPtr inv.outPtr) ?_
  rintro u ⟨value,mem,rest⟩
  have oldT := inv.outside.w32 (d:=acc+4*(i+1)) (by omega) (by omega)
  have oldB := inv.outside.w32 (d:=b+4*(i+1))
    (by rcases ctx.accB with h|h <;> omega) (by omega)
  have oldM := inv.outside.w32 (d:=mod+4*(i+1))
    (by rcases ctx.accM with h|h <;> omega) (by omega)
  rw [inv.scalar,inv.quotient,oldB,oldM,show acc+4*i+4=acc+4*(i+1) by omega,oldT] at value
  have writes := writeW32_outside s.mem (State.addr base) (d:=acc+4*i) (u.gpr .r6) (by omega)
  rw [←mem] at writes
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem u.mem :=
    (inv.outside.mono (Nat.le_refl _) (by omega)).trans (writes.mono (by omega) (by omega))
  have low := writes.val32 (d:=acc) (k:=i) (by omega) (by omega)
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
    omega
  exact advance_inv ctx inv (Or.inl rfl) (by omega)
    (rest.mono (by decide)) outside (prefix_extend inv.value segment stored)

end VG.Proof.Bignum.Arm.Fios
