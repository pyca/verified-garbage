module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Retained public key arguments determine the register state used by imports and exports -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure InputPair (E : Environment) (s t : State) : Prop where
  left : Input E s
  right : Input E t
  stack : s.gpr .esp = t.gpr .esp

theorem InputPair.agree {E : Environment} {s t : State} (P : InputPair E s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.ws.workspace.edi_toNat.trans P.right.ws.workspace.edi_toNat.symm)

theorem headerSource_ok {E : Environment} {s : State} (h : Input E s) {i : Nat} (hi : i < 18) (r : Reg) :
    WP isa (.block [.mov r (.mem (VG.Impl.Mont.X86.sc (4 * i)))]) s fun t =>
      t.gpr r = E.argument i ∧ Keeps [r] s t := by
  refine wp_movS (readSrc_sc h.ws.workspace (by have H := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at H; omega))
    fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr.trans (h.arguments i hi), T.keeps⟩

theorem primeSource_trace (E : Environment) (i : Nat) (hi : i < 18) :
    RelCT isa (InputPair E) (.block [.mov .esi (.mem (VG.Impl.Mont.X86.sc (4 * i)))])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) := by
  intro s t tr ur u v P A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .esi (.mem (VG.Impl.Mont.X86.sc (4 * i)))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block [.mov .esi (.mem (VG.Impl.Mont.X86.sc 0))]) (.block []) rfl rfl rfl (by rfl)
  obtain ⟨leftValue, leftKeeps⟩ := wp_result (headerSource_ok P.left hi .esi) A
  obtain ⟨rightValue, rightKeeps⟩ := wp_result (headerSource_ok P.right hi .esi) C
  refine ⟨(raw _ _ _ _ _ _ P.agree A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.stack
  · rw [leftKeeps.1 .edi (by decide), rightKeeps.1 .edi (by decide)]
    exact BitVec.eq_of_toNat_eq (P.left.ws.workspace.edi_toNat.trans P.right.ws.workspace.edi_toNat.symm)
  · exact leftValue.trans rightValue.symm

end VG.Proof.RsaKeyGen.X86.Key
