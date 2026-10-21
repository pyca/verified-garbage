module

import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.Framework.Mem

/-! # The general exponent reduction owns and releases its native stack slots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem framed_ok {base : Addr} {size n src offset candidate exponent : Nat} {s : State}
    (S : Scr s base size) (positive : 0 < n) (sourceFit : src + 4 * n ≤ size)
    (exponentFit : offset + 8 ≤ size) (value : val32 s.mem base src n = candidate)
    (eValue : exponentValue s.mem base offset = exponent) (ePositive : 0 < exponent)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.alloc 20) (VG.Impl.RsaKeyGen.X86.Mod64.array n src offset) (.free 20)) s fun t =>
      Scr t base size ∧ pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      val32 t.mem base src n = candidate ∧ exponentValue t.mem base offset = exponent ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let g : ArrayGeometry := ⟨s.gpr .esp - 20#32, s.gpr .edi, size, n, src, offset⟩
  have baseEq : g.base = base := S.edi
  have valid : g.Valid := ⟨positive, sourceFit, exponentFit, by
    change (⟨g.base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩
    rw [baseEq]
    exact FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))⟩
  have C : ArrayContext g candidate exponent (allocFrame 20 s) := by
    refine ⟨?_, FilterStack.allocated_context (by omega), ?_, ?_⟩
    · rw [baseEq]; exact FilterStack.allocated_scratch S fit separate
    · change val32 s.mem g.base src n = candidate
      rw [baseEq]; exact value
    · change exponentValue s.mem g.base offset = exponent
      rw [baseEq]; exact eValue
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (NoSp.of_all ?_) ?_
  · have bitSafe (e : Nat) : (VG.Impl.RsaKeyGen.X86.Mod64.bit e).all (fun i => !Taint.clobbers i .esp) = true := by rfl
    simp only [Code.allInstrs_eq, VG.Impl.RsaKeyGen.X86.Mod64.array,
      VG.Impl.RsaKeyGen.X86.Mod64.arrayStep, instrs, List.all_append,
      VG.Impl.RsaKeyGen.X86.Mod64.word, VG.Impl.RsaKeyGen.X86.Mod64.steps, List.all_flatMap, bitSafe]
    rfl
  · refine WP.mono (array_ok valid C ePositive) fun t ⟨T, result, O, K⟩ => ?_
    have Kout := FilterStack.freed_keeps K (by decide)
    refine ⟨S.of_keeps Kout (by decide), ?_, ?_, ?_, ?_, Kout⟩
    · rw [freed_gpr _ _ (by decide), freed_gpr _ _ (by decide)]
      exact result
    · rw [← baseEq]; exact T.candidateValue
    · rw [← baseEq]; exact T.exponentEq
    · exact arrayStackFrame O

end VG.Proof.RsaKeyGen.X86.Mod64
