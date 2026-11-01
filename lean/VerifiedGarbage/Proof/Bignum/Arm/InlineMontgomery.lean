module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT

/-! Inline Montgomery operations meet the same interface as shared calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

def inlineMontgomery (base : BitVec 32) (len w : Nat) :
    TwoExp.Montgomery base len w (fun _ => True) [⟨State.addr base, 8 * len⟩] where
  op := montOp
  workspace := by simp
  stable := by intros; trivial
  op_ok := by
    intro s o a b ready _ ho ha hb ho0 operand
    refine WP.mono (montOp_ok s ready ho ha hb ho0 operand) ?_
    rintro t ⟨r,m,b,v,k,f,rest⟩
    exact ⟨r,m,b,v,k,trivial,f,rest⟩

theorem inlineMontgomery_ct {base : BitVec 32} {len w : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    TwoExp.MontgomeryTiming (inlineMontgomery base len w) where
  op_ct := by
    intro o a b ho ha hb
    exact (montOp_ct ho ha hb fit).mono
      (fun _ _ h => ⟨⟨h.1.1,h.1.2.2⟩,⟨h.2.1.1,h.2.1.2.2⟩,h.2.2⟩)
      (fun _ _ h => h)

end VG.Proof.Bignum.Arm
