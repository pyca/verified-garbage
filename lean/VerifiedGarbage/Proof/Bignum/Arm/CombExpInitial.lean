module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpControl
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp

/-! Montgomery one and the public comb row count initialize the evaluator. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

private theorem operand (q : Nat) (h : q=4 ∨ q=6 ∨ q=7) : Operand q := by
  rcases h with rfl | rfl | rfl <;> simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]

theorem startCount_ok {base source table : BitVec 32} {len w bytes N M g E : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bytes N s) :
    WP isa (.block [.ldr .r1 .r0 204,.str .r1 .r0 192]) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧
      Counter base (Spec.Rsa.FixedBaseComb.rows N) t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256≤8*len := by
    have fits := h.ready.width ▸ h.ready.layout.2.2.1
    simp only [arrAt,Proof.Rsa.Mont.hdrBytes] at fits
    omega
  have address (d : Nat) (hd : d<256) : State.addr (s.gpr .r0+BitVec.ofNat 32 d)=off (State.addr base) d := by
    rw [h.ready.ptr]
    exact addr_add (by have := h.ready.workspace.nowrap; omega)
  refine wp_ldr (a:=off (State.addr base) 204) (by decide) (address 204 (by decide))
    (h.ready.workspace.read (by omega)) fun u first => ?_
  refine wp_str (a:=off (State.addr base) 192) (by decide)
    (by rw [first.other .r0 (by decide)]; exact address 192 (by decide))
    (by rw [first.wr]; exact h.ready.workspace.write (by omega)) fun t last => WP.block_nil ?_
  have mem : t.mem=s.mem.writeW (off (State.addr base) 192) (BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N)) := by
    rw [last.mem,first.mem,first.gpr,controls.spacing]
  have rest : Rest [.r1] s t := (first.rest (by decide)).trans (last.rest _)
  obtain ⟨powerT,frame⟩ := h.after_header (d:=192) (by decide) (by decide) mem rest
    ((rest.gpr .r0 (by decide)).trans h.ready.ptr)
  have r : Rest roundClobbers s t := rest.mono (by decide)
  refine ⟨powerT,A.stable frame r hp,controls.after_counter mem,?_,
    frame.mono (by simpa using A.workspace),r⟩
  change t.mem.readW (off (State.addr base) 192) 32=_
  rw [mem,Mem.readW_writeW_self32]

theorem initial_ok {base source table : BitVec 32} {len w bytes N M g : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (ready : ArithmeticReady base len w s) (hp : P s) (controls : Controls base source table bytes N s)
    (modulus : numAt s.mem (State.addr base) w 0=M) (odd : M%2=1)
    (r2 : numAt s.mem (State.addr base) w 4=2^(128*w)%M) :
    WP isa (VG.Impl.Bignum.Arm.CombExp.initial A.op) s fun t =>
      Power base len w M g 0 t ∧ P t ∧ Controls base source table bytes N t ∧
      Counter base (Spec.Rsa.FixedBaseComb.rows N) t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8≤8*len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Bignum.Arm.CombExp.initial,WP.seq_iff]
  refine WP.mono (smallConst_ok s (1:BitVec 32) ready (o:=7)
    (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU,oneU,_,keepsU,frameU,restU⟩
  change numAt u.mem (State.addr base) w 7=1 at oneU
  have pu := A.stable frameU restU hp
  have modU := (ready.after_array (by decide) keepsU frameU restU readyU.ptr).2.trans modulus
  have r2U := (keeps_array_num keepsU fits (operand 4 (by decide)) (by decide)).trans r2
  have controlsU := controls.after_header (TwoExp.header_of_keeps ready keepsU)
  rw [WP.seq_iff]
  refine WP.mono (A.op_ok u 6 4 7 readyU pu (operand 6 (by decide)) (operand 4 (by decide))
    (operand 7 (by decide)) (by decide) (by rw [oneU]; exact readyU.modulus)) ?_
  rintro v ⟨readyV,modV,boundV,valueV,keepsV,pv,frameV,restV⟩
  rw [modU] at modV boundV valueV
  rw [oneU,Nat.mul_one,r2U] at valueV
  have coprime := coprime_pow2 odd (64*w)
  have encodedOne : numAt v.mem (State.addr base) w 6%M=2^(64*w)%M := by
    apply mont_cancel coprime
    rw [valueV,Nat.mod_mod,←Nat.pow_add,show 64*w+64*w=128*w by omega]
  have power : Power base len w M g 0 v := by
    refine ⟨readyV,modV,coprime,boundV,?_,?_,?_⟩
    · simpa only [Nat.pow_zero,Nat.one_mul] using encodedOne
    · exact (keeps_array_num keepsV fits (operand 7 (by decide)) (by decide)).trans oneU
    · exact (keeps_array_num keepsV fits (operand 4 (by decide)) (by decide)).trans r2U
  have controlsV := controlsU.after_header (TwoExp.header_of_keeps readyU keepsV)
  refine WP.mono (startCount_ok A v power pv controlsV) ?_
  rintro t ⟨powerT,pt,controlsT,counterT,frameT,restT⟩
  exact ⟨powerT,pt,controlsT,counterT,
    (frameU.mono (by simpa using A.workspace)).trans (frameV.trans frameT),
    restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.CombExp
