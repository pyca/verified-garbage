module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernelAt
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Bignum.Arm.CombExpGatherCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpGather
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStore
import VerifiedGarbage.Proof.Bignum.Arm.CombScanCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
meta import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend

/-! Independent secret exponents use the same five gathers and full table scan. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

private structure GatheredInput (base source table : BitVec 32) (len w bytes N M g E i digit : Nat)
    (P : State→Prop) (s : State) : Prop extends RowInput base source table len w bytes N M g E i P s where
  value : s.gpr .r11=BitVec.ofNat 32 digit
  bound : digit<32

private theorem gathered_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E i : Nat) (bs : List Byte) (length : bs.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) (countFit : i+1<2^32)
    (s : State) (h : RowInput base source table len w bytes N M g E i
      (Persistent base source table sp len w M g N bs) s) :
    WP isa (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) s
      (GatheredInput base source table len w bytes N M g E i
        (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i)
        (Persistent base source table sp len w M g N bs)) := by
  let A := arithmetic backend base source table sp len w M g N bs
  refine WP.mono (gather_ok A s h.power h.persistent (by simpa only [length] using h.controls) h.counter
    countFit h.persistent.2.exponent (by simpa only [length] using widthBound)
    (by simpa only [length] using size) positions widthFit scalarFit) ?_
  rintro t ⟨power,p,controls,counter,digit,_,_,_⟩
  exact ⟨⟨power,p,by simpa only [length] using controls,counter⟩,digit,VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _⟩

private theorem savedScan_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E i digit : Nat) (bs : List Byte)
    (s : State) (h : GatheredInput base source table len w bytes N M g E i digit
      (Persistent base source table sp len w M g N bs) s) :
    WP isa (.block [.str .r11 .r0 196]) s (CombScan.Input base table len w M g N digit) := by
  let A := arithmetic backend base source table sp len w M g N bs
  refine WP.mono (saveDigit_ok A s h.power h.persistent h.controls h.counter) ?_
  rintro t ⟨power,p,controls,_,digitValue,_,_⟩

  exact ⟨power.ready,p.2.entries,p.2.tableSeparate _ (by simp [writeRegions]),h.bound,
    digitValue.trans h.value,controls.tablePtr⟩

private theorem save_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block [.str .r11 .r0 196]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem choose_ct (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E1 E2 i : Nat) (bs1 bs2 : List Byte)
    (length1 : bs1.length=bytes) (length2 : bs2.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit1 : Spec.Rsa.os2ip bs1<2^N) (scalarFit2 : Spec.Rsa.os2ip bs2<2^N)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i
        (Persistent base source table sp len w M g N bs1) s ∧
      RowInput base source table len w bytes N M g E2 i
        (Persistent base source table sp len w M g N bs2) t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombExp.choose (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombExp.choose
  apply RelCT.assoc
  refine relCT_chain (gather_ct (by omega))
    (fun s h => gathered_ok backend base source table sp len w bytes N M g E1 i bs1 length1
      widthBound size (by omega) widthFit scalarFit1 (by omega) s h)
    (fun s h => gathered_ok backend base source table sp len w bytes N M g E2 i bs2 length2
      widthBound size (by omega) widthFit scalarFit2 (by omega) s h) ?_
  exact relCT_chain
    (save_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => savedScan_ok backend base source table sp len w bytes N M g E1 i _ bs1 s h)
    (fun s h => savedScan_ok backend base source table sp len w bytes N M g E2 i _ bs2 s h)
    CombScan.code_ct

end VG.Proof.Bignum.Arm.CombExp
