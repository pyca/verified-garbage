module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Copy a public-exponent stage's status to a persistent header slot -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem saveSlot_ok {s : State} {B : Addr} {Z n N a d : Nat} (h : Ws s B Z n N)
    (ha : a + 4 ≤ hdr) (hd : d + 4 ≤ hdr) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc a)),
      .store (VG.Impl.Mont.X86.sc d) .eax]) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [d] s.mem t.mem ∧
      slot t.mem B d = slot s.mem B a ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  refine wp_movS (readSrc_sc h.workspace (by omega)) fun u U _ => ?_
  refine WP.mono (store_slot (h.rest U.keeps) hd .eax) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, U.keeps.trans (Kt.mono (by decide))⟩
  · simpa only [U.mem] using Ot
  · rw [value, U.gpr]

end VG.Proof.RsaKeyGen.X86.Key
