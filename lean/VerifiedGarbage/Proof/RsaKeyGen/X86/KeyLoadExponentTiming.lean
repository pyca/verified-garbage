module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHeaderTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Exponent import leaves the public byte pointer available to native arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem loadBE_key_trace (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (argumentTaint false)) (VG.Impl.Bignum.X86.loadBE n out)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  exact erased_relCT (VG.Impl.Bignum.X86.loadBE n out) (VG.Impl.Bignum.X86.loadBE 1 0)
    (VG.Taint.hintOf taint (argumentTaint false) (VG.Impl.Bignum.X86.loadBE 1 0)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by rfl)

theorem loadExponent_trace (E : Environment) :
    RelCT isa (InputPair E) (loadExponent E.n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold loadExponent seqs
  exact RelCT.seq (headerPair_trace E 14 15 (by decide) (by decide) false)
    (RelCT.seq (loadBE_key_trace 1 kEv) (key_public_trace (widenCopy_public E.n 2 aE kEv)))

end VG.Proof.RsaKeyGen.X86.Key
