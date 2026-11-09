module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNotSlot
import VerifiedGarbage.Proof.Mont.X86.Instr
import Aesop.BuiltinRules

/-! # Handle public exponents zero and one, including degenerate LCMs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dZero_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa dZero s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold dZero
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps
  refine wp_storeS (hu.workspace.ea (by unfold kOk hdr at *; omega))
    (hu.workspace.write (by unfold kOk hdr at *; omega)) fun t T => WP.block_nil ?_
  refine ⟨hu.rest (T.keeps []), ?_, ?_, U.keeps.trans (T.keeps _)⟩
  · rw [T.mem, U.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, U.mem, w32_write_self, U.gpr]
    rfl

end VG.Proof.RsaKeyGen.X86.Key
