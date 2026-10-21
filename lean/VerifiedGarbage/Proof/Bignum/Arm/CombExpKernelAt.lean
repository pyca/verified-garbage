module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpChoose
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel

/-! Public byte counts index kernels independently of the secret exponent list. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

def kernelAt (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes M g N : Nat) (bs : List Byte) (length : bs.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) :
    Kernel base source table len w bytes N M g (Spec.Rsa.os2ip bs)
      (Persistent base source table sp len w M g N bs) (writeRegions base sp len) where
  arithmetic := arithmetic backend base source table sp len w M g N bs
  choose_ok := by
    intro s i E hi h hp controls counter
    have result := choose_ok backend base source table sp len w M g N bs s i E
      (by simpa only [length] using widthBound) (by simpa only [length] using size)
      (by omega) widthFit scalarFit (by omega) h hp (by simpa only [length] using controls) counter
    refine WP.mono result ?_
    rintro t ⟨power,p,controlsT,counterT,bound,value,frame,rest⟩
    exact ⟨power,p,by simpa only [length] using controlsT,counterT,bound,value,frame,rest⟩

end VG.Proof.Bignum.Arm.CombExp
