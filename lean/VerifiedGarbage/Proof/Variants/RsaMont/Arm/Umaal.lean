module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareU
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmeticCaller

/-! Shared multiplication and callers use UMAAL product and fused reduction rows;
specialized squaring retains its UMAAL diagonal implementation. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def diagonal : MontBackend where
  mul := MontCallSquareU.code
  verified := by exact montCallSquareU_verified
  correct := by exact montCallWithFn_ok _ montCallSquareU_law
  rawCT := by exact montCallWithFn_ct _ montCallSquareU_law
  stackOk := by exact montCallSquareU_stack
  suffix := "_umaal"
  features := ["umaal"]

def variant : MontBackend where
  mul := umaalArithmetic diagonal.mul
  verified := umaalArithmetic_verified diagonal.verified
  correct := by
    intro s base len w o a b h ho ha hb
    obtain ⟨tr, t, run, post⟩ := diagonal.correct s h ho ha hb
    exact ⟨tr, t, umaalArithmetic_sim diagonal.mul run, post⟩
  rawCT := by
    intro base len w o a b ho ha hb s t tr1 tr2 u v h e1 e2
    obtain ⟨st, su, es, _⟩ := diagonal.correct s h.1 ho ha hb
    obtain ⟨tt, tv, et, _⟩ := diagonal.correct t h.2.1 ho ha hb
    have es' : Exec VG.Arm.isa (umaalArithmetic diagonal.mul) s st su := umaalArithmetic_sim diagonal.mul es
    have et' : Exec VG.Arm.isa (umaalArithmetic diagonal.mul) t tt tv := umaalArithmetic_sim diagonal.mul et
    obtain ⟨rfl, rfl⟩ := Exec.det es' e1
    obtain ⟨rfl, rfl⟩ := Exec.det et' e2
    exact diagonal.rawCT ho ha hb _ _ _ _ _ _ h es et
  stackOk := Nat.le_trans (armStack_umaalArithmetic _) diagonal.stackOk
  caller := umaalArithmeticCaller
  suffix := diagonal.suffix
  features := diagonal.features

end VG.Proof.Variants.RsaMont.Arm.Umaal
