module

public import VerifiedGarbage.Proof.MillerRabin.X86.ScanFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.ScanEntry
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The complete scan returns exactly the secret digit's table entry -/

@[expose] public section
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
