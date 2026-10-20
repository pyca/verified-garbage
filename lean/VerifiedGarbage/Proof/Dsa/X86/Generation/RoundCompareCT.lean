module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundEffects

/-! # Comparisons publish only the public residue's terminal cases -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem roundCompare_phase_ct (n : Nat) :
    RelCT isa (Two (RoundAt n)) (roundCompare n) (Two (RoundComparedAt n)) := by
  refine two_post ((roundCompare_relCT n).mono ?_ (fun _ _ _ => trivial)) ?_
  · rintro s t ⟨p, hs, ht⟩
    exact agree_regs (roundCore_pins n p s t hs.1 ht.1)
  · intro p s R
    refine WP.mono (roundCompare_ready R.1) fun t ⟨Rt, zf, _, value, count, _, _⟩ => ?_
    exact ⟨⟨Rt, value.trans R.2.1, count.trans R.2.2.1, R.2.2.2⟩, by rw [zf, R.2.1]⟩

theorem roundSquare_phase_ct (n : Nat) :
    RelCT isa (Two (RoundAt n)) (roundSquare n) (Two fun p => RoundComparedAt n (roundSquared p)) := by
  refine two_post ((roundSquare_ct n).mono ?_ (fun _ _ _ => trivial)) ?_
  · rintro s t ⟨p, hs, ht⟩
    exact roundCore_pins n p s t hs.1 ht.1
  · intro p s R
    refine WP.mono (roundSquare_ok R.1) fun t ⟨Rt, zf, _, value, count, _, _⟩ => ?_
    rw [R.2.1] at zf value
    exact ⟨⟨Rt, value, count.trans R.2.2.1, R.2.2.2⟩, zf⟩
end VG.Proof.Dsa.X86.Generation
