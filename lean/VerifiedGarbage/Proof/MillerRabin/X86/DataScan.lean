module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.MillerRabin.X86.ScanFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Scan
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! # A complete fixed-address scan selects the digit's known power -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.scan {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js)
    (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Data g (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) Js V Ds t ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have value := (D.slotValues sValue digitKnown).2
  have digit := digit_lt (V sValue)
  have power := D.arrayValues _ (tableKnown _ digit)
  refine WP.mono (scan_ok v D.context) fun t ⟨Value, O, K, C⟩ => ?_
  rw [value, power.2] at Value
  refine ⟨⟨C, ?_, ?_⟩, O, K⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    by_cases same : j = aX
    · subst j
      exact ⟨index, by rw [setAt_self]; exact Value⟩
    · refine ⟨index, ?_⟩
      have sep := g.readApart same
      have header := v.arrayHeader j
      rw [O.val32 (by
        intro r mem
        simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · right; unfold sEq1; omega
        · dsimp only
          rcases sep with before | after
          · exact Or.inl before
          · right; unfold Geometry.words at *; omega)
        (by have := v.arrayFit index; have := C.ws.nowrap; omega), read, setAt_other A _ same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    have notMask : d ≠ sEq1 := fun eq => maskUnknown (eq ▸ known)
    have apart := scratch_apart scratch (by unfold scratchWord sEq1; simp) notMask
    have bound := scratch_fit scratch
    have header := v.arrayHeader aX
    refine ⟨scratch, ?_⟩
    rw [(WorkspaceFrame.of_outs C.ws.nowrap O).read32 (by have := v.headerFit; omega) (by
      intro r mem
      simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact apart
      · exact Or.inl (Nat.le_trans bound header)), read]

end VG.Proof.MillerRabin.X86
