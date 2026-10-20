module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Bignum.Arm.CombExpArgs
import VerifiedGarbage.Proof.Bignum.Arm.CombDigitCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CombExp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import Init.Prelude
meta import Init.Prelude
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp

/-! The five public gather controls agree for independent secret exponent bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

private theorem args_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private def Args (source : BitVec 32) (bytes N i : Nat) (s : State) : Prop :=
  s.gpr .r4=source ∧ s.gpr .r5=BitVec.ofNat 32 bytes ∧ s.gpr .r6=BitVec.ofNat 32 i ∧
  s.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N) ∧ s.gpr .r8=BitVec.ofNat 32 N

theorem gather_ct {base source table : BitVec 32} {len w bytes N M g E1 E2 i : Nat}
    {P1 P2 : State→Prop} (fits : i+1<2^32) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i P1 s ∧
      RowInput base source table len w bytes N M g E2 i P2 t ∧ s.sp=t.sp)
      (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) (fun _ _ => True) := by
  have wp (s : State) {P : State→Prop} {E : Nat} (h : RowInput base source table len w bytes N M g E i P s) :
      WP isa (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) s (Args source bytes N i) :=
    WP.mono (digitArgs_ok s h.power.ready h.controls h.counter fits) fun _ h =>
      ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
  have digitCT : RelCT isa (fun s t => Args source bytes N i s ∧ Args source bytes N i t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombDigit.code (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    refine ⟨CombDigit.code_ct s t tr1 tr2 u v trivial trivial ?_ e1 e2,trivial⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.1.1.trans h.2.1.1.symm
    · exact h.1.2.1.trans h.2.1.2.1.symm
    · exact h.1.2.2.1.trans h.2.1.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.1.2.2.2.1.symm
    · exact h.1.2.2.2.2.trans h.2.1.2.2.2.2.symm
  exact relCT_chain
    (args_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => wp s h) (fun s h => wp s h) digitCT

end VG.Proof.Bignum.Arm.CombExp
