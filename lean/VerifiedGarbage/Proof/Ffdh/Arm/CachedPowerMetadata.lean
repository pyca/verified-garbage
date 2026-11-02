module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment

/-! The canonical public metadata fixes the comb width, spacing and table address. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsl op2_reg op2_imm dpVal)

def bits (p : Inputs) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)
def table (p : Inputs) : BitVec 32 := p.cachedContext+BitVec.ofNat 32 (24+16*p.w)

theorem metadata_ok (s : State) {p : Inputs} (ready : ArithmeticReady p.base p.len p.w s)
    (context : CachedGenerationContext p s) (pointer : s.gpr .r4=p.cachedContext) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPower.metadata) s fun t =>
      t.gpr .r1=BitVec.ofNat 32 (bits p) ∧
      t.gpr .r2=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows (bits p)) ∧
      t.gpr .r4=table p ∧ t.mem=s.mem ∧ Rest [.r1,.r2,.r3,.r4] s t := by
  have count : 3≤p.cachedWords := by
    rw [context.canonical.1,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords]
    omega
  have addr0 : State.addr (s.gpr .r4+BitVec.ofNat 32 0)=State.addr p.cachedContext := by
    rw [pointer,BitVec.add_zero]
  have addr16 : State.addr (s.gpr .r4+BitVec.ofNat 32 16)=off (State.addr p.cachedContext) 16 := by
    rw [pointer]; exact VG.Arm.addr_add (by have := context.fit; omega)
  have read0 : InRegions (s.rd++s.wr) (State.addr p.cachedContext) 4 := by
    simpa only [BitVec.add_zero] using VG.CallLay.inRegions_sub context.readable
      (off:=0) (l:=4) (by omega) (by have := context.fit; omega)
  have read16 : InRegions (s.rd++s.wr) (off (State.addr p.cachedContext) 16) 4 :=
    VG.CallLay.inRegions_sub context.readable (by omega) (by have := context.fit; omega)
  have native := nativeHeader_of_layout s.mem p.base ready.workspace.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at native
  have hN : s.mem.readW (State.addr p.cachedContext) 32=BitVec.ofNat 32 (bits p) := by
    simpa only [Nat.mul_zero,BitVec.add_zero,List.getD_cons_zero,bits] using context.header32 0 (by decide)
  have hd : s.mem.readW (off (State.addr p.cachedContext) 16) 32=
      BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows (bits p)) := by
    simpa only [List.getD_cons_succ,List.getD_cons_zero,bits] using context.header32 2 (by decide)
  have size : 256≤8*p.len := by
    have fits := ready.width ▸ ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at fits
    omega
  unfold VG.Impl.Ffdh.Arm.CachedPower.metadata
  refine wp_ldr (a:=State.addr p.cachedContext) (by decide) addr0 read0 fun a one => ?_
  refine wp_ldr (a:=off (State.addr p.cachedContext) 16) (by decide)
    (by rw [one.other .r4 (by decide)]; exact addr16)
    (by rw [one.rd,one.wr]; exact read16) fun b two => ?_
  refine wp_ldr (a:=off (State.addr p.base) 48) (by decide)
    (by rw [two.other .r0 (by decide),one.other .r0 (by decide),ready.ptr]
        exact VG.Arm.addr_add (by have := ready.workspace.nowrap; omega))
    (by rw [two.rd,two.wr,one.rd,one.wr]; exact ready.workspace.read (by omega)) fun c three => ?_
  refine wp_mov (op2_lsl (by decide)) fun d four => ?_
  refine wp_dp (op2_reg _ _) fun e five => ?_
  refine wp_dp (op2_imm (by decide)) fun t six => WP.block_nil ?_
  have rest : Rest [.r1,.r2,.r3,.r4] s t :=
    (one.rest (by simp)).trans ((two.rest (by simp)).trans ((three.rest (by simp)).trans
      ((four.rest (by simp)).trans ((five.rest (by simp)).trans (six.rest (by simp))))))
  refine ⟨?_,?_,?_,six.mem.trans (five.mem.trans (four.mem.trans (three.mem.trans (two.mem.trans one.mem)))),rest⟩
  · rw [six.other .r1 (by decide),five.other .r1 (by decide),four.other .r1 (by decide),
      three.other .r1 (by decide),two.other .r1 (by decide),one.gpr,hN]
  · rw [six.other .r2 (by decide),five.other .r2 (by decide),four.other .r2 (by decide),
      three.other .r2 (by decide),two.gpr,one.mem,hd]
  · rw [six.gpr,dpVal]
    rw [five.gpr,dpVal,four.other .r4 (by decide),three.other .r4 (by decide),
      two.other .r4 (by decide),one.other .r4 (by decide),pointer]
    rw [four.gpr,three.gpr,two.mem,one.mem,native.count,BitVec.shiftLeft_eq_mul_twoPow]
    change (p.cachedContext+BitVec.ofNat 32 p.w*BitVec.ofNat 32 16)+BitVec.ofNat 32 24=table p
    rw [←BitVec.ofNat_mul,BitVec.add_assoc,←BitVec.ofNat_add]
    simp only [table,Nat.mul_comm p.w 16,Nat.add_comm (16*p.w) 24]

end VG.Proof.Ffdh.Arm.CachedPower
