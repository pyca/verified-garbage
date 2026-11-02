module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp

/-! Public workspace controls supply the gather's fixed register interface. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_imm dpVal)

theorem digitArgs_ok (s : State) {base source table : BitVec 32} {len w bytes N i : Nat}
    (ready : ArithmeticReady base len w s) (controls : Controls base source table bytes N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) s fun t =>
      t.gpr .r4=source ∧ t.gpr .r5=BitVec.ofNat 32 bytes ∧ t.gpr .r6=BitVec.ofNat 32 i ∧
      t.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.gpr .r8=BitVec.ofNat 32 N ∧
      t.mem=s.mem ∧ Rest [.r4,.r5,.r6,.r7,.r8] s t := by
  have size : 256≤8*len := by
    have arrayFits := ready.width ▸ ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at arrayFits
    omega
  have addr (d : Nat) (hd : d<256) : State.addr (s.gpr .r0+BitVec.ofNat 32 d)=off (State.addr base) d := by
    rw [ready.ptr]
    exact addr_add (by have := ready.workspace.nowrap; omega)
  unfold VG.Impl.Bignum.Arm.CombExp.digitArgs
  refine wp_ldr (a:=off (State.addr base) 128) (by decide) (addr 128 (by decide))
    (ready.workspace.read (by omega)) fun a one => ?_
  refine wp_ldr (a:=off (State.addr base) 132) (by decide)
    (by rw [one.other .r0 (by decide)]; exact addr 132 (by decide))
    (by rw [one.rd,one.wr]; exact ready.workspace.read (by omega)) fun b two => ?_
  refine wp_ldr (a:=off (State.addr base) 192) (by decide)
    (by rw [two.other .r0 (by decide),one.other .r0 (by decide)]; exact addr 192 (by decide))
    (by rw [two.rd,two.wr,one.rd,one.wr]; exact ready.workspace.read (by omega)) fun c three => ?_
  refine wp_dp (op2_imm (by decide)) fun d four => ?_
  have kept : Rest [.r4,.r5,.r6,.r7,.r8] s d :=
    ((one.rest (by decide)).trans (two.rest (by decide))).trans
      ((three.rest (by decide)).trans (four.rest (by decide)))
  refine wp_ldr (a:=off (State.addr base) 204) (by decide)
    (by rw [kept.gpr .r0 (by decide)]; exact addr 204 (by decide))
    (by rw [kept.rd,kept.wr]; exact ready.workspace.read (by omega)) fun e five => ?_
  refine wp_ldr (a:=off (State.addr base) 136) (by decide)
    (by rw [five.other .r0 (by decide),kept.gpr .r0 (by decide)]; exact addr 136 (by decide))
    (by rw [five.rd,five.wr,kept.rd,kept.wr]; exact ready.workspace.read (by omega)) fun t six => WP.block_nil ?_
  have memD : d.mem=s.mem := four.mem.trans (three.mem.trans (two.mem.trans one.mem))
  refine ⟨?_,?_,?_,?_,?_,six.mem.trans (five.mem.trans memD),
    (kept.trans (five.rest (by decide))).trans (six.rest (by decide))⟩
  · rw [six.other .r4 (by decide),five.other .r4 (by decide),four.other .r4 (by decide),
      three.other .r4 (by decide),two.other .r4 (by decide),one.gpr,controls.sourcePtr]
  · rw [six.other .r5 (by decide),five.other .r5 (by decide),four.other .r5 (by decide),
      three.other .r5 (by decide),two.gpr,one.mem,controls.byteCount]
  · rw [six.other .r6 (by decide),five.other .r6 (by decide),four.gpr,dpVal,three.gpr,
      two.mem,one.mem,counter]
    change BitVec.ofNat 32 (i+1)-BitVec.ofNat 32 1=BitVec.ofNat 32 i
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [six.other .r7 (by decide),five.gpr,memD,controls.spacing]
  · rw [six.gpr,five.mem,memD,controls.bitCount]

end VG.Proof.Bignum.Arm.CombExp
