module

public import VerifiedGarbage.Proof.Bignum.Arm.RowKernel
public import VerifiedGarbage.Impl.Bignum.Arm.SquareReduceWith
public import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareReduceWithCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareReduceWithCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SquareReduceWith

/-! The specialized square keeps its existing schedule around the supplied row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt Operand)

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

theorem sqBodyReduceWith_ct (K : RowKernel) :
    RelCT isa (fun s t => SqStart base size out a mod M n sp0 s ∧ SqStart base size out a mod M n sp0 t)
      (sqBodyReduceWith K.code) (fun _ _ => True) := by
  unfold sqBodyReduceWith
  exact sqInit_ct.seq (crossRows_ct.seq (sqDouble_ct.seq (sqDiagU_ct.seq ((sqReduceWith_ct K).seq sqFinish_ct))))

end

theorem squareBodyReduceWith_ct (K : RowKernel) {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t => s.sp = t.sp ∧ SqFnReady base len w o a s ∧ SqFnReady base len w o a t)
      (squareBodyReduceWith K.code) (fun _ _ => True) := by
  have family : ∀ sp0 : BitVec 32, RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
      (SqFnReady base len w o a t ∧ t.sp = sp0)) (squareBodyReduceWith K.code) (fun _ _ => True) := by
    intro sp0
    have ct : RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
        (SqFnReady base len w o a t ∧ t.sp = sp0)) (.block MontFn.bases) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
      intro s t h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.1.1.body.ptr.trans h.2.1.body.ptr.symm
      · exact h.1.1.body.outIndex.trans h.2.1.body.outIndex.symm
      · exact h.1.1.body.aIndex.trans h.2.1.body.aIndex.symm
      · exact h.1.1.body.bIndex.trans h.2.1.body.bIndex.symm
    have wp (s : State) (h : SqFnReady base len w o a s ∧ s.sp = sp0) :
        WP isa (.block MontFn.bases) s
          (SqStart base (8 * len) (arrAt w o) (arrAt w a) (arrAt w 0) (arrAt w 2) (2 * w) sp0) :=
      h.2 ▸ squareBases_ready ho ha s h.1
    unfold squareBodyReduceWith
    exact (pair_posts ct wp).seq (sqBodyReduceWith_ct K)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v ⟨⟨h.2.1, rfl⟩, h.2.2, h.1.symm⟩ e1 e2

end VG.Proof.Bignum.Arm
