module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
import VerifiedGarbage.Proof.Bignum.Arm.CombExpGather
import VerifiedGarbage.Proof.Bignum.Arm.CombExpStore
import VerifiedGarbage.Proof.Bignum.Arm.CombScan
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Spec.Rsa.Mont

/-! The concrete gather and complete readonly scan supply the evaluator kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem choose_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) (s : State) (i E : Nat)
    (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) (counterFit : i+1<2^32)
    (h : Power base len w M g E s) (hp : Persistent base source table sp len w M g N bs s)
    (controls : Controls base source table bs.length N s) (counter : Counter base (i+1) s) :
    WP isa VG.Impl.Bignum.Arm.CombExp.choose s fun t =>
      Power base len w M g E t ∧ Persistent base source table sp len w M g N bs t ∧
      Controls base source table bs.length N t ∧ Counter base (i+1) t ∧
      numAt t.mem (State.addr base) w 1<M ∧
      numAt t.mem (State.addr base) w 1%M=
        g^(Spec.Rsa.FixedBaseComb.exponent N (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i))*2^(64*w)%M ∧
      Frame (writeRegions base sp len) s.mem t.mem ∧ Rest roundClobbers s t := by
  let A := arithmetic backend base source table sp len w M g N bs
  have gathered := gather_ok A s h hp controls counter counterFit hp.2.exponent widthBound size positions widthFit scalarFit
  rw [WP.seq_iff] at gathered
  rw [VG.Impl.Bignum.Arm.CombExp.choose,WP.seq_iff]
  refine WP.mono gathered ?_
  intro a gather
  rw [WP.seq_iff]
  refine WP.mono gather ?_
  rintro u ⟨powerU,pu,controlsU,counterU,digitU,_,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveDigit_ok A u powerU pu controlsU counterU) ?_
  rintro v ⟨powerV,pv,controlsV,counterV,digitV,frameV,restV⟩
  have sep : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩ :=
    pv.2.tableSeparate _ (by simp [writeRegions])
  refine WP.mono (CombScan.code_ok v powerV.ready pv.2.entries sep
    (VG.Proof.Rsa.FixedBaseComb.digit_lt N (Spec.Rsa.os2ip bs) i) (digitV.trans digitU) controlsV.tablePtr) ?_
  rintro t ⟨readyT,_,selected,header,arrays,frameT,restT⟩
  have powerT : Power base len w M g E t := by
    refine ⟨readyT,(arrays 0 (by decide) (by decide)).trans powerV.modulus,powerV.coprime,?_,?_,
      (arrays 7 (by decide) (by decide)).trans powerV.one,(arrays 4 (by decide) (by decide)).trans powerV.r2⟩
    · rw [arrays 6 (by decide) (by decide)]; exact powerV.bound
    · rw [arrays 6 (by decide) (by decide)]; exact powerV.value
  have controlsT : Controls base source table bs.length N t :=
    ⟨(header 128 (by decide) (by decide) (by decide)).trans controlsV.sourcePtr,
      (header 132 (by decide) (by decide) (by decide)).trans controlsV.byteCount,
      (header 136 (by decide) (by decide) (by decide)).trans controlsV.bitCount,
      (header 204 (by decide) (by decide) (by decide)).trans controlsV.spacing,
      (header 232 (by decide) (by decide) (by decide)).trans controlsV.tablePtr⟩
  have positive : 0<M := by
    have larger := powerV.ready.modulus
    rw [powerV.modulus] at larger
    omega
  have frameU : Frame (writeRegions base sp len) s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  refine ⟨powerT,A.stable frameT restT pv,controlsT,
    (header 192 (by decide) (by decide) (by decide)).trans counterV,?_,?_,
    frameU.trans (frameV.trans (frameT.mono (by simpa using A.workspace))),restU.trans (restV.trans restT)⟩
  · rw [selected]; exact Nat.mod_lt _ positive
  · rw [selected,Nat.mod_mod,powMod_eq,Nat.mod_mul_mod]

def kernel (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte)
    (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) :
    Kernel base source table len w bs.length N M g (Spec.Rsa.os2ip bs)
      (Persistent base source table sp len w M g N bs) (writeRegions base sp len) where
  arithmetic := arithmetic backend base source table sp len w M g N bs
  choose_ok := by
    intro s i E hi h hp controls counter
    exact choose_ok backend base source table sp len w M g N bs s i E widthBound size
      (by omega) widthFit scalarFit (by omega) h hp controls counter

end VG.Proof.Bignum.Arm.CombExp
