module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Public pointers and lengths reloaded from the retained key header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def argumentReg (exporting : Bool) : Reg := if exporting then .ebx else .esi
def headerPair (exporting : Bool) (i j : Nat) : Prog isa := .block [
  .mov (argumentReg exporting) (.mem (VG.Impl.Mont.X86.sc (4 * i))),
  .mov .ecx (.mem (VG.Impl.Mont.X86.sc (4 * j)))]
def argumentTaint (exporting : Bool) : VG.X86.Taint.T := τr [.esp, .edi, argumentReg exporting, .ecx]

theorem headerPair_ok {E : Environment} {s : State} (h : Input E s) {i j : Nat}
    (hi : i < 18) (hj : j < 18) (exporting : Bool) :
    WP isa (headerPair exporting i j) s fun t =>
      t.gpr (argumentReg exporting) = E.argument i ∧ t.gpr .ecx = E.argument j ∧
      Keeps [argumentReg exporting, .ecx] s t := by
  have head := h.ws.hdr_le
  unfold headerPair
  refine wp_movS (readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at head; omega))
    fun a A _ => ?_
  have ws := h.ws.rest A.keeps (by cases exporting <;> decide) (by cases exporting <;> decide)
  refine wp_movS (readSrc_sc ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at head; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨(T.other _ (by cases exporting <;> decide)).trans (A.gpr.trans (h.arguments i hi)), ?_,
    (A.keeps.mono (by simp)).trans (T.keeps.mono (by simp))⟩
  rw [T.gpr, A.mem]
  exact h.arguments j hj

theorem headerPair_trace (E : Environment) (i j : Nat) (hi : i < 18) (hj : j < 18) (exporting : Bool) :
    RelCT isa (InputPair E) (headerPair exporting i j) (VG.X86.Taint.Agree (argumentTaint exporting)) := by
  intro s t tr ur u v P A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (headerPair exporting i j)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (headerPair exporting 0 0) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by cases exporting <;> kernel_rfl)
  obtain ⟨leftPointer, leftCount, leftKeeps⟩ := wp_result (headerPair_ok P.left hi hj exporting) A
  obtain ⟨rightPointer, rightCount, rightKeeps⟩ := wp_result (headerPair_ok P.right hi hj exporting) C
  refine ⟨(raw _ _ _ _ _ _ P.agree A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [leftKeeps.1 .esp (by cases exporting <;> decide), rightKeeps.1 .esp (by cases exporting <;> decide)]
    exact P.stack
  · rw [leftKeeps.1 .edi (by cases exporting <;> decide), rightKeeps.1 .edi (by cases exporting <;> decide)]
    exact BitVec.eq_of_toNat_eq (P.left.ws.workspace.edi_toNat.trans P.right.ws.workspace.edi_toNat.symm)
  · exact leftPointer.trans rightPointer.symm
  · exact leftCount.trans rightCount.symm

end VG.Proof.RsaKeyGen.X86.Key
