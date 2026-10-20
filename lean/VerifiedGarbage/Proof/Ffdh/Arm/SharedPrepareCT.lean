module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedPrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # FFDH setup uses shared constant-time Montgomery precomputation -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedPrepare_ct {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (ct : TwoExp.MontgomeryTiming K) (countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32) :
    RelCT isa (fun s t => (PrepareInput base src len k s ∧ P s) ∧
      (PrepareInput base src len k t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedPrepare.code K.op) (fun _ _ => True) := by
  have ready (s : State) (h : PrepareInput base src len k s ∧ P s) :
      WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s fun t =>
        PrecomputeInput base src len (Spec.Rsa.modulusWords k) k t ∧ P t :=
    WP.mono (prepare_input s h.1) fun _ r => ⟨r.1, K.stable r.2.1 r.2.2 h.2⟩
  unfold VG.Impl.Ffdh.Arm.SharedPrepare.code
  exact relCT_chain (prepareInput_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    ready ready (sharedPrecompute_ct K ct countFits)

end VG.Proof.Ffdh.Arm
