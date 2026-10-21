module

public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Division needs only its divisor's extra word initialized -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86

theorem division_clear {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 4) :
    WP isa (.block [.mov .eax (.imm 0), .store (sc (arr n 2 + 4 * n)) .eax]) s fun t =>
      Ws t B Z n 4 ∧ Outside B (arr n 2 + 4 * n) 4 s.mem t.mem ∧
      w32 t.mem B (arr n 2 + 4 * n) = 0 ∧ Keeps [.eax] s t := by
  have fit := h.arr_fit (j := 2) (by decide)
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps
  refine wp_storeS (hu.workspace.ea (by unfold S at fit; omega))
    (hu.workspace.write (by unfold S at fit; omega)) fun t T => WP.block_nil ?_
  refine ⟨hu.rest (T.keeps []), ?_, ?_, U.keeps.trans (T.keeps _)⟩
  · rw [T.mem, U.mem]
    exact writeW32_outside _ _ _ (by have := h.workspace.nowrap; unfold S at fit; omega)
  · rw [T.mem, U.mem, w32_write_self, U.gpr]
    rfl

end VG.Proof.RsaKeyGen.X86.Key
