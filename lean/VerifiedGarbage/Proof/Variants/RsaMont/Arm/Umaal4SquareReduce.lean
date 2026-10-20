module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareReduceWith
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareReduceWith
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Kernel
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaalCaller

/-! The shared helper unrolls square reduction; products, cross terms and callers retain paired UMAAL rows. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal4SquareReduce
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def diagonal : MontBackend where
  mul := MontCallSquareReduceWith.code RowKernel.umaal4.code
  verified := by exact montCallSquareReduceWith_verified RowKernel.umaal4
  correct := by exact montCallWithFn_ok _ (montCallSquareReduceWith_law RowKernel.umaal4)
  rawCT := by exact montCallWithFn_ct _ (montCallSquareReduceWith_law RowKernel.umaal4)
  stackOk := by exact montCallSquareReduceWith_stack RowKernel.umaal4
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

end VG.Proof.Variants.RsaMont.Arm.Umaal4SquareReduce
