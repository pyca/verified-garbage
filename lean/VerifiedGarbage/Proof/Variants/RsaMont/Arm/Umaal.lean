module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareU
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaalCaller

/-! The shared helper uses UMAAL rows and diagonals; callers inherit UMAAL rows. -/

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
  mul := umaalRows diagonal.mul
  verified := diagonal.verified.subst row_sim
  correct := by
    intro s base len w o a b h ho ha hb
    obtain ⟨tr, t, run, post⟩ := diagonal.correct s h ho ha hb
    exact ⟨tr, t, Exec.subst row_sim run, post⟩
  rawCT := by
    intro base len w o a b ho ha hb s t tr1 tr2 u v h e1 e2
    obtain ⟨st, su, es, _⟩ := diagonal.correct s h.1 ho ha hb
    obtain ⟨tt, tv, et, _⟩ := diagonal.correct t h.2.1 ho ha hb
    have es' : Exec VG.Arm.isa (umaalRows diagonal.mul) s st su := Exec.subst row_sim es
    have et' : Exec VG.Arm.isa (umaalRows diagonal.mul) t tt tv := Exec.subst row_sim et
    obtain ⟨rfl, rfl⟩ := Exec.det es' e1
    obtain ⟨rfl, rfl⟩ := Exec.det et' e2
    exact diagonal.rawCT ho ha hb _ _ _ _ _ _ h es et
  stackOk := Nat.le_trans (armStack_umaalRows _) diagonal.stackOk
  caller := umaalCaller
  suffix := diagonal.suffix
  features := diagonal.features

end VG.Proof.Variants.RsaMont.Arm.Umaal
