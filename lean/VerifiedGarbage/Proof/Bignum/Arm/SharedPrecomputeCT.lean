module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedR2CT
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # Shared modulus precomputation has a public trace -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem sharedPrecompute_ct {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (PrecomputeInput base src len w k s ∧ P s) ∧
      (PrecomputeInput base src len w k t ∧ P t) ∧ s.sp = t.sp)
      (SharedPrecompute.precompute K.op) (fun _ _ => True) := by
  have imported (s : State) (h : PrecomputeInput base src len w k s ∧ P s) :
      WP isa importModulus s fun t => PrecomputeModulus base len w t ∧ P t := by
    refine (importModulus_ready s h.1).and ?_
    refine WP.mono (importModulus_ok s h.1.workspace h.1.layout h.1.width h.1.positive h.1.fits h.1.sourceFits
      h.1.readable h.1.separate h.1.ptr h.1.source h.1.count h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, _, _, frame, rest⟩
    exact K.stable frame rest h.2
  have inverse (s : State) (h : PrecomputeModulus base len w s ∧ P s) :
      WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧ P t := by
    refine (precomputeInverse_ready s h.1).and ?_
    refine WP.mono (precomputeInverse_ok s h.1.workspace h.1.layout h.1.width h.1.ptr h.1.odd h.1.large
      h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, frame, rest⟩
    exact K.stable frame rest h.2
  unfold SharedPrecompute.precompute
  refine relCT_chain ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) imported imported ?_
  exact relCT_chain ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) inverse inverse (SharedR2.r2_ct K ct countFits)

end VG.Proof.Bignum.Arm
