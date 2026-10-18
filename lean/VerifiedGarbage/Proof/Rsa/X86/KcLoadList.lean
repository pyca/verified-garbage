module

public import VerifiedGarbage.Proof.Rsa.X86.KcFrames
public import VerifiedGarbage.Proof.Rsa.X86.KcZero

/-! # Importing all key components while preserving the input buffers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

def loadValues (g : CallGeometry) (m : Mem) (A : Nat → Nat) : List (Nat × Nat) → Nat → Nat
  | [] => A
  | (i, j) :: rest => loadValues g m (upd A j (Spec.Rsa.os2ip (inputBytes g m i))) rest

theorem loadValues_frame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) (A : Nat → Nat) (ls : List (Nat × Nat))
    (hi : ∀ p ∈ ls, 2 * p.1 < scratchArg g.full) :
    loadValues g m A ls = loadValues g s.mem A ls := by
  induction ls generalizing A with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨i, j⟩ := p
    simp only [loadValues]
    rw [h.inputFrame frame i (hi (i, j) (by simp))]
    exact ih _ (fun p hp => hi p (by simp [hp]))

theorem loadInputs_ok {g : CallGeometry} {s : State} (h : Inputs g s) (A : Nat → Nat)
    (ha : Arrs s.mem g.base (2 * g.n) A (List.range nArr))
    (top : w32 s.mem g.base (arr (2 * g.n) aVD + 4 * (2 * g.n)) = 0)
    (ls : List (Nat × Nat))
    (hi : ∀ p ∈ ls, 2 * p.1 < scratchArg g.full ∧ p.2 < nArr ∧ p.2 ≠ aVD) :
    WP isa (loadInputs g.n ls) s fun t => Inputs g t ∧
      Keep g.base (2 * g.n) (List.range nArr) [] s.mem t.mem ∧
      Arrs t.mem g.base (2 * g.n) (loadValues g s.mem A ls) (List.range nArr) ∧
      w32 t.mem g.base (arr (2 * g.n) aVD + 4 * (2 * g.n)) = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  induction ls generalizing s A with
  | nil => exact WP.block_nil ⟨h, Keep.refl _ _ _ _ _, ha, top, Keeps.refl _ _⟩
  | cons p ps ih =>
    obtain ⟨i, j⟩ := p
    obtain ⟨hii, hj, hjd⟩ := hi (i, j) (by simp)
    rw [loadInputs, WP.seq_iff]
    refine WP.mono (load_ok h i hii hj) fun u ⟨hu, ku, vu, ru⟩ => ?_
    have au : Arrs u.mem g.base (2 * g.n)
        (upd A j (Spec.Rsa.os2ip (inputBytes g s.mem i))) (List.range nArr) :=
      ha.write ku h.ws vu (fun k hk => by
        by_cases e : k = j
        · exact .inl e
        · exact .inr ⟨List.mem_range.mp hk, by simpa using e⟩) (by simp)
    have tu : w32 u.mem g.base (arr (2 * g.n) aVD + 4 * (2 * g.n)) = 0 := by
      rw [ku.word (by unfold S; omega) (by simpa using hjd) (by simp) (h.ws.fit64 (by decide)), top]
    refine WP.mono (ih hu _ au tu (fun p hp => hi p (by simp [hp]))) fun t ⟨ht, kt, valuesT, tt, rt⟩ => ?_
    have frame := h.keepOutside ku (by simpa using hj) (by simp)
    rw [loadValues_frame h frame _ ps (fun p hp => (hi p (by simp [hp])).1)] at valuesT
    exact ⟨ht, (ku.mono (by simpa using hj) (by simp)).trans kt, valuesT, tt, ru.trans rt⟩
end VG.Proof.Rsa.X86.KeyCheck
