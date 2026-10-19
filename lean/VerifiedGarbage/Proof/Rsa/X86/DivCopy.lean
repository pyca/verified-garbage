module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Copying native words in the RSA key workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Div

theorem copyWords_ok {s : State} {base : Addr} {size n src dst : Nat} (hs : Scr s base size)
    (hn : 0 < n) (hsrc : src + 4 * n ≤ size) (hdst : dst + 4 * n ≤ size)
    (sep : dst = src ∨ dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) :
    WP isa (copyWords n src dst) s fun t =>
      Outside base dst (4 * n) s.mem t.mem ∧
      val32 t.mem base dst n = val32 s.mem base src n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold copyWords
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.mono (selectsW_ok (hs.of_keeps U.keeps (by decide)) false U.gpr hn hsrc hsrc hdst sep sep) ?_
  rintro t ⟨frame, value, rest⟩
  refine ⟨?_, ?_, (U.keeps.mono (by decide)).trans (rest.mono (by decide))⟩
  · rw [U.mem] at frame; exact frame
  · rw [U.mem] at value; exact value
end VG.Proof.Rsa.X86.Div
