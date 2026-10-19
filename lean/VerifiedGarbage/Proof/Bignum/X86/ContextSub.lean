module

public import VerifiedGarbage.Proof.Mont.X86.DynamicSub
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame

/-! # Reduced subtraction inside a runtime RSA factor workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem contextSub_ok {s : State} {base : Addr} {bytes n m o a b : Nat}
    (H : Context n m base bytes s) (ho : o < 9) (ha : a < 9) (hb : b < 9)
    (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (A : wordsVal s.mem base (slot n a) n < m) (B : wordsVal s.mem base (slot n b) n < m)
    (ha1 : a ≠ 1 := by decide) (hb1 : b ≠ 1 := by decide) :
    WP isa (subW (contextMod n) (slot n 2) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base bytes t ∧ OpKeep (contextMod n) base (slot n 2) (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n =
        (wordsVal s.mem base (slot n a) n + m - wordsVal s.mem base (slot n b) n) % m := by
  refine WP.mono (subW_ok H.scr H.modulus (context_opLay H.size_le ho ha hb ho2 ha2 hb2 ho1)
    (by have := slot_sep (n := n) ha1; simp only [contextMod, stride] at *; omega)
    (by have := slot_sep (n := n) hb1; simp only [contextMod, stride] at *; omega) A B) fun t ⟨K, V⟩ => ?_
  exact ⟨H.keep ho0 K, K, V⟩

end VG.Proof.Bignum.X86
