module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentTests
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentWords

/-! # The public-exponent decision matches the shared RSA limits exactly -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem exponentTest_ok (s : State) :
    WP isa exponentTest s fun t =>
      t.gpr .r7 = BitVec.ofNat 32
        (exponentBounds (s.gpr .r3) (s.gpr .r4) && !exponentIsOne (s.gpr .r3) (s.gpr .r4)).toNat ∧
      t.mem = s.mem ∧ Rest [.r5, .r7] s t := by
  rw [exponentTest, WP.seq_iff]
  refine WP.mono (exponentBoundsTest_ok s) ?_
  rintro u ⟨zero, memU, restU⟩
  refine WP.ite (exponentBounds (s.gpr .r3) (s.gpr .r4)) (by change some u.z = _; rw [zero]) ?_ ?_
  · intro bounds
    rw [WP.seq_iff]
    refine WP.mono (exponentOneTest_ok u) ?_
    rintro v ⟨one, memV, restV⟩
    rw [restU.gpr .r3 (by simp), restU.gpr .r4 (by simp)] at one
    refine WP.ite (exponentIsOne (s.gpr .r3) (s.gpr .r4)) (by change some v.z = _; rw [one]) ?_ ?_
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

end VG.Proof.Bignum.Arm
