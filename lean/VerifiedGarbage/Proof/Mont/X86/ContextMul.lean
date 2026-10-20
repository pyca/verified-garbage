module

public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Mont.X86.Context
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State

/-! # Montgomery multiplication within a runtime context -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

theorem context_mul_ok {n size m o a b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (ho : o < 9) (ha : a < 9) (hb : b < 9)
    (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (hB : wordsVal s.mem base (slot n b) n < m) (ha1 : a ≠ 1 := by decide) (hb1 : b ≠ 1 := by decide) :
    WP isa (VG.Impl.Mont.X86.Dynamic.mul (contextMod n) 0 (slot n 2) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n < m ∧
      wordsVal t.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal s.mem base (slot n a) n * wordsVal s.mem base (slot n b) n % m := by
  have hdr := slot_header n 9
  have hdr2 := slot_header n 2
  have sz := h.size_le
  refine WP.mono (mul_ok h.scr h.modulus (by change 4 ≤ size; change slot n 9 ≤ size at sz; omega)
    (.inl (by omega)) h.inverse
    (context_opLay h.size_le ho ha hb ho2 ha2 hb2 ho1) hB
    (by have := slot_sep (n := n) ha1; simp only [contextMod, stride] at *; omega)
    (by have := slot_sep (n := n) hb1; simp only [contextMod, stride] at *; omega)
    (by have := slot_header n 1; simp only [contextMod]; omega)) fun t ⟨K, lt, V⟩ => ?_
  exact ⟨h.keep ho0 K, K, lt, V⟩

end VG.Proof.Mont.X86.Dynamic
