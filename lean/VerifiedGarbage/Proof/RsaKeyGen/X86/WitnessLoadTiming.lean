module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks

import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
/-! # Import and sampling reveal the entropy pointer and width, but no random bytes -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLowerTiming.lean`, which only this module imported.
section

/-! # The witness lower-bound scan has fixed public length and addresses -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_trace (n src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code n src)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code n src) (code 2 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (code 2 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessUniformTiming.lean`, which only this module imported.
section

/-! # Uniform-witness classification scans the same addresses for every input -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessFallbackTiming.lean`, which only this module imported.
section

/-! # Both fallback choices execute identical native updates -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_trace (k src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (codeAt k src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (codeAt k src)) (.block (codeAt 2 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (code w src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace (2 * w) src

end VG.Proof.RsaKeyGen.X86.WitnessFallback
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessSampleTiming.lean`, which only this module imported.
section

/-! # Complete witness sampling has a secret-independent trace -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

theorem codeAt_trace (k w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (codeAt k w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (WitnessUniform.code_trace w src modulus) (WitnessFallback.codeAt_trace k src)

theorem code_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace (2 * w) w src modulus

end VG.Proof.RsaKeyGen.X86.WitnessSample
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86 VG.Proof.Dsa.X86

theorem zeros_trace (o n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros o n))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros
  apply blockFlatMap_relCT
  intro j
  exact erased_relCT _ (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (.block []) rfl rfl rfl rfl

theorem codeAt_trace (D k w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  refine RelCT.seq (Import.load_trace (D / 4) (VG.Impl.Bignum.X86.PublicContext.slot w 6)) ?_
  exact RelCT.seq ((zeros_trace _ _).mono (fun _ _ H => taint.le_sound (by decide +kernel) H) (fun _ _ H => H))
    (WitnessSample.codeAt_trace _ w _ _)

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.code w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace _ _ w

end VG.Proof.RsaKeyGen.X86.WitnessLoad
