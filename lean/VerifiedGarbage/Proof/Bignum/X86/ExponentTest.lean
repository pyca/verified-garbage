module
public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentTestMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Bignum.X86.ExponentTests
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The public-exponent decision matches the shared RSA limits exactly -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentTest_ok (s : State) :
    WP isa exponentTest s fun t =>
      t.gpr .eax = BitVec.ofNat 32
        (exponentBounds (s.gpr .ebx) (s.gpr .edx) && !exponentIsOne (s.gpr .ebx) (s.gpr .edx)).toNat ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  rw [exponentTest, WP.seq_iff]
  refine WP.mono (exponentBoundsTest_ok s) ?_
  rintro u ⟨zero, memU, restU⟩
  refine WP.ite (exponentBounds (s.gpr .ebx) (s.gpr .edx)) zero ?_ ?_
  · intro bounds
    rw [WP.seq_iff]
    refine WP.mono (exponentOneTest_ok u) ?_
    rintro v ⟨one, memV, restV⟩
    rw [restU.1 .ebx (by decide), restU.1 .edx (by decide)] at one
    refine WP.ite (exponentIsOne (s.gpr .ebx) (s.gpr .edx)) one ?_ ?_
    · intro invalid
      refine WP.mono (exponentResult_ok v false) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, invalid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
    · intro valid
      refine WP.mono (exponentResult_ok v true) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, valid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
  · intro invalid
    refine WP.mono (exponentResult_ok u false) ?_
    rintro t ⟨value, memT, restT⟩
    exact ⟨by simpa only [invalid, Bool.false_and] using value, memT.trans memU, restU.trans restT⟩

end VG.Proof.Bignum.X86
