module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame

import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
/-! # A prepared Montgomery product composes with the next round stage -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataMultiply.lean`, which only this module imported.
section

/-! # A prepared product updates only the accumulator's known value -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.multiply {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    {capacity b c : Nat} {p : BitVec 32} (length : g.L = 8 * capacity)
    (M : Modulus g c s.mem) (C : Caller g capacity p s)
    (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1) (rightLt : A b < c)
    (bKnown : b ∈ Js) (yKnown : 6 ∈ Js) (noScratch : ∀ j ∈ Js, j ≠ 2 ∧ j ≠ 3) :
    WP isa (mulY name code b) s fun t =>
      Data g (setAt A 6 (Word32.mm c g.w (A 6) (A b))) Js V Ds t ∧
      Modulus g c t.mem ∧ Caller g capacity p t ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have bv := D.arrayValues b bKnown
  have yv := D.arrayValues 6 yKnown
  refine WP.mono (mulY_ok verified noSp stack v D.context length M right odd
    (by rw [bv.2]; exact rightLt) C.readLen (by rw [C.sp]; exact C.low)
    (by rw [C.sp]; exact C.stackFar)) fun t ⟨Value, O, K, Ct, Mt, F⟩ => ?_
  have caller := C.keepFrame K (by decide) (by rw [C.sp] at F; exact F)
  refine ⟨⟨Ct, ?_, ?_⟩, Mt, caller, O, K⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    by_cases same : j = 6
    · subst j
      exact ⟨index, by rw [setAt_self, Value, yv.2, bv.2]⟩
    · have noScr := noScratch j known
      refine ⟨index, ?_⟩
      rw [O.val32 (v.arrayFit index) (by
        intro r mem
        simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl
        · exact g.readApart noScr.1
        · exact g.readApart noScr.2
        · exact g.readApart same), read, setAt_other A _ same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    refine ⟨scratch, ?_⟩
    rw [O.read32 (by have := scratch_fit scratch; have := v.headerFit; omega) (by
      intro r mem
      simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 2))
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 3))
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 6))), read]

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.multiply {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (b : Nat) (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1) (rightLt : A b < c)
    (bKnown : b ∈ Js) (yKnown : aY ∈ Js) :
    WP isa (mulY name code b) s fun t =>
      Stage g capacity c p (setAt A aY (Word32.mm c g.w (A aY) (A b))) Js V Ds t ∧
      WorkspaceFrame g (montWrites g aY) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  refine WP.mono (S.data.multiply verified noSp stack v length S.modulus S.caller right odd
    rightLt bKnown yKnown S.noScratch) fun t ⟨D, M, C, O, K⟩ => ?_
  exact ⟨⟨D, M, C, S.noScratch⟩, O, K⟩

end VG.Proof.MillerRabin.X86
