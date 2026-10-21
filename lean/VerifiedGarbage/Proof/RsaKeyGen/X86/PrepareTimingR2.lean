module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Timing
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The short R² phase feeds the prepared constant conversion without leaking residues -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem r2_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (PreparedR2.InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont)
      (Constants.InputPair g capacity p) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, pair⟩ := PreparedR2.code_trace (p := p) verified noSp stack v length bound _ _ _ _ _ _ H E G
  have post {a : State} (I : PreparedR2.Input g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont) a (Constants.Input g capacity p) := by
    obtain ⟨c, A, odd, top⟩ := I
    exact WP.mono (PreparedR2.code_ok verified noSp stack v length A bound odd top)
      fun _ ⟨R, r2, _, _, _⟩ => ⟨c, R, odd, by omega, r2⟩
  exact ⟨trace, pair, wp_result (post H.2.1) E, wp_result (post H.2.2) G⟩

end VG.Proof.RsaKeyGen.X86.Prepare
