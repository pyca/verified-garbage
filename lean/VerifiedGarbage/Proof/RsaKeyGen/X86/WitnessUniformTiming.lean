module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Uniform-witness classification scans the same addresses for every input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessUniform
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessUniform

theorem mark_trace (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark src))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem restore_trace (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore src))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem less_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (VG.Impl.Dsa.X86.lessThan w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (VG.Impl.Dsa.X86.lessThan w src modulus) (VG.Impl.Dsa.X86.lessThan 1 0 0)
    (.seq (roundTaint [.edi]) (.block [])
      (.seq (roundTaint [.edi])
        (.seq (roundTaint [.edi, .ebp]) (.block []) (.loop (roundTaint [.edi, .ebp]) (.block []))) (.block [])))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (WitnessLower.code_trace (2 * w) src) (RelCT.seq (mark_trace src)
    (RelCT.seq (less_trace w src modulus) (RelCT.seq (restore_trace src) (checkedBlockInvariant rfl rfl))))

end VG.Proof.RsaKeyGen.X86.WitnessUniform
