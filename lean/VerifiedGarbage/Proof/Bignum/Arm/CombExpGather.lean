module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpArgs
import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitValue
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
import VerifiedGarbage.Proof.Bignum.Arm.CombDigitBit

/-! The evaluator's public header produces exactly the mathematical comb digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem gather_ok {base source table : BitVec 32} {len w N M g E i : Nat} {bs : List Byte}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bs.length N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32)
    (bytes : CombDigit.Source source bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    WP isa (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bs.length N t ∧ Counter base (i+1) t ∧
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (digitArgs_ok s h.ready controls counter fits) ?_
  rintro u ⟨src,byteLen,row,stride,width,memU,restU⟩
  have ru : Rest roundClobbers s u := restU.mono (by simp [roundClobbers])
  have frameU : Frame [⟨State.addr base,8*len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have pu := A.stable frameU ru hp
  have powerU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  refine WP.mono (CombDigit.code_digit_ok u (bytes.of_mem memU restU) widthBound size positions widthFit
    bound src byteLen row stride width) ?_
  rintro t ⟨digit,digitBound,memT,restT⟩
  have rt : Rest roundClobbers u t := restT.mono (by simp [CombDigit.clobbers,roundClobbers])
  have frameT : Frame [⟨State.addr base,8*len⟩] u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have mem : t.mem=s.mem := memT.trans memU
  have rest := ru.trans rt
  refine ⟨powerU.of_mem memT restT ((restT.gpr .r0 (by simp [CombDigit.clobbers])).trans powerU.ready.ptr),
    A.stable frameT rt pu,?_,?_,digit,digitBound,mem,rest⟩
  · exact controls.after_header (by intro d hd; rw [mem])
  · change t.mem.readW _ _=_
    rw [mem]
    exact counter

end VG.Proof.Bignum.Arm.CombExp
