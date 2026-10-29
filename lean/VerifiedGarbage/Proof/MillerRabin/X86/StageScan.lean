module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame

import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame
import VerifiedGarbage.Proof.MillerRabin.X86.ScanFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Mask
import VerifiedGarbage.Proof.MillerRabin.X86.Select
import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
/-! # Selecting a secret digit keeps the modulus and caller frame reusable -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ScanEntry.lean`, which only this module imported.
section

/-! # One fixed-address scan step only replaces the matching digit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem scanEntry_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) :
    WP isa (.seq (.block (maskIndex j)) (selectEntry j)) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j
          then aTable + j else aX)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  refine WP.seq (WP.mono (maskIndex_ok v C j index) fun a ⟨Mask, O, K, Ca⟩ => ?_)
  refine WP.mono (selectEntry_ok v Ca j index
    (decide ((s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j)) (by simpa using Mask)) ?_
  rintro t ⟨V, Ot, Kt, Ct⟩
  have header := v.arrayHeader aX
  have tableHeader := v.arrayHeader (aTable + j)
  have fitX := v.arrayFit (j := aX) (by decide)
  have fitT := v.arrayFit (j := aTable + j) (by unfold aTable; omega)
  refine ⟨?_, (Outs.of_outside O (by simp [scanWrites])).trans
    (Outs.of_outside Ot (by simp [scanWrites])), (K.mono (by decide)).trans Kt, Ct⟩
  by_cases eq : (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j
  · simp only [eq, decide_true, ↓reduceIte] at V ⊢
    rw [V, O.val32 (by unfold sEq1; omega) (by have := C.ws.nowrap; omega)]
  · simp only [eq, decide_false, Bool.false_eq_true, ↓reduceIte] at V ⊢
    rw [V, O.val32 (by unfold sEq1; omega) (by have := C.ws.nowrap; omega)]

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/Scan.lean`, which only this module imported.
section

/-! # The complete scan returns exactly the secret digit's table entry -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem scanFrom_ok {g : Geometry} (v : g.Valid) (n : Nat) :
    ∀ j, j + n ≤ 16 → ∀ s, Context g s →
    WP isa (scanFrom j n) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if j ≤ (s.mem.readW (off g.W sValue) 32 >>> 28).toNat ∧
            (s.mem.readW (off g.W sValue) 32 >>> 28).toNat < j + n
          then aTable + (s.mem.readW (off g.W sValue) 32 >>> 28).toNat else aX)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  induction n with
  | zero =>
    intro j _ s C
    refine WP.block_nil ⟨?_, Outs.refl _ _ _, Keeps.refl _ _, C⟩
    simp only [Nat.add_zero, show ¬ (j ≤ (s.mem.readW (off g.W sValue) 32 >>> 28).toNat ∧
      (s.mem.readW (off g.W sValue) 32 >>> 28).toNat < j) by omega, ↓reduceIte]
  | succ n ih =>
    intro j bound s C
    unfold scanFrom
    refine WP.assoc (WP.seq (WP.mono (scanEntry_ok v C j (by omega)) fun a ⟨Va, Oa, Ka, Ca⟩ => ?_))
    refine WP.mono (ih (j + 1) (by omega) a Ca) fun t ⟨Vt, Ot, Kt, Ct⟩ => ?_
    have value := scanFrame_value v Oa
    simp only [value] at Vt
    refine ⟨?_, Oa.trans Ot, Ka.trans Kt, Ct⟩
    let d := (s.mem.readW (off g.W sValue) 32 >>> 28).toNat
    change val32 t.mem g.W (g.array aX) g.words =
      val32 s.mem g.W (g.array (if j ≤ d ∧ d < j + (n + 1) then aTable + d else aX)) g.words
    change val32 t.mem g.W (g.array aX) g.words =
      val32 a.mem g.W (g.array (if j + 1 ≤ d ∧ d < j + 1 + n then aTable + d else aX)) g.words at Vt
    change val32 a.mem g.W (g.array aX) g.words =
      val32 s.mem g.W (g.array (if d = j then aTable + j else aX)) g.words at Va
    by_cases later : j + 1 ≤ d ∧ d < j + 1 + n
    · rw [ite_eq_left later] at Vt
      rw [Vt, scanFrame_table v C.ws.nowrap Oa (j := d) (digit_lt _),
        ite_eq_left (by omega : j ≤ d ∧ d < j + (n + 1))]
    · rw [ite_eq_right later] at Vt
      rw [Vt, Va]
      by_cases eq : d = j
      · rw [eq, ite_eq_left rfl, ite_eq_left (by omega : j ≤ j ∧ j < j + (n + 1))]
      · rw [ite_eq_right eq, ite_eq_right (by omega : ¬ (j ≤ d ∧ d < j + (n + 1)))]

theorem scan_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa scan s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (aTable + (s.mem.readW (off g.W sValue) 32 >>> 28).toNat)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  unfold scan
  refine WP.seq (WP.mono (copy_ok v C aX aTable (by decide) (by decide))
    fun a ⟨Va, Oa, Ka, Ca⟩ => ?_)
  refine WP.mono (scanFrom_ok v 15 1 (by decide) a Ca) fun t ⟨Vt, Ot, Kt, Ct⟩ => ?_
  have frame : Outs g.W (scanWrites g) s.mem a.mem := Outs.of_outside Oa (by simp [scanWrites])
  have value := scanFrame_value v frame
  simp only [value] at Vt
  refine ⟨?_, frame.trans Ot, (Ka.mono (by decide)).trans Kt, Ct⟩
  have digit := digit_lt (s.mem.readW (off g.W sValue) 32)
  by_cases zero : (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0
  · simp only [zero, show ¬ (1 ≤ 0 ∧ 0 < 1 + 15) by decide, ↓reduceIte] at Vt
    rw [Vt, Va, zero, Nat.add_zero]
  · rw [ite_eq_left (by omega)] at Vt
    rw [Vt, scanFrame_table v C.ws.nowrap frame digit]

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataScan.lean`, which only this module imported.
section

/-! # A complete fixed-address scan selects the digit's known power -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.scan {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js)
    (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Data g (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) (aX :: Js) V Ds t ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have value := (D.slotValues sValue digitKnown).2
  have digit := digit_lt (V sValue)
  have power := D.arrayValues _ (tableKnown _ digit)
  refine WP.mono (scan_ok v D.context) fun t ⟨Value, O, K, C⟩ => ?_
  rw [value, power.2] at Value
  refine ⟨⟨C, ?_, ?_⟩, O, K⟩
  · intro j known
    by_cases same : j = aX
    · subst j
      exact ⟨by decide, by rw [setAt_self]; exact Value⟩
    · have old : j ∈ Js := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨index, read⟩ := D.arrayValues j old
      refine ⟨index, ?_⟩
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
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.scan {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Stage g capacity c p (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) (aX :: Js) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.scan v tableKnown digitKnown maskUnknown) fun t ⟨D, O, K⟩ => ?_
  have W := WorkspaceFrame.of_outs S.data.context.ws.nowrap O
  have head := v.arrayHeader aX
  have M : Modulus g c t.mem := S.modulus.keep v W (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; decide
    · left; dsimp only; omega) (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; have := v.arrayHeader 0; unfold sEq1; omega
    · exact Or.inl (g.arrayBefore (by decide : 0 < aX)))
  have C := S.caller.keepOuts K (by decide) O (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · have := v.headerFit; unfold sEq1; dsimp only; omega
    · exact v.arrayFit (by decide : aX < 28))
  refine ⟨⟨D, M, C, ?_⟩, ?_, K⟩
  · intro j mem
    rcases List.mem_cons.mp mem with rfl | mem
    · decide
    · exact S.noScratch j mem
  · apply W.cover
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact scalar_roundRange g (d := sEq1) (by unfold scratchWord sEq1; simp)
    · exact array_roundRange g (j := aX) (by unfold roundArray aX; simp) (by unfold Geometry.words; omega)

end VG.Proof.MillerRabin.X86
