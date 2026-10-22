module

public import VerifiedGarbage.Proof.MillerRabin.X86.WindowTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.WordReady

/-! # Public inner and outer counts consume all exponent words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem eight_windows_ct {σ₁ σ₂ : State} {base : Addr} {bytes w i : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hi : i < 2 * w) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w (8 * (i + 1)) s ∧
      WindowReady σ₂ base bytes w (8 * (i + 1)) t) (.loop win .ne)
      (fun s t => WindowReady σ₁ base bytes w (8 * i) s ∧ WindowReady σ₂ base bytes w (8 * i) t) := by
  refine (count_loop_ct (N := 8) (by decide) (fun j s t =>
    WindowReady σ₁ base bytes w (8 * (i + 1) - j) s ∧
    WindowReady σ₂ base bytes w (8 * (i + 1) - j) t) ?_).mono (fun _ _ h => h) ?_
  · intro j hj
    have upper := C.facts₁.upper
    refine (window_ct C (k := 8 * (i + 1) - j) ⟨by omega, by omega⟩).mono (fun _ _ h => h) ?_
    rintro s t ⟨h₁, h₂, z₁, z₂⟩
    have count : 8 * (i + 1) - j - 1 = 8 * (i + 1) - (j + 1) := by omega
    have endEq : decide ((8 * (i + 1) - j - 1) % 8 = 0) = decide (j + 1 = 8) :=
      decide_eq_decide.mpr (by omega)
    exact ⟨⟨count ▸ h₁, count ▸ h₂⟩, by rw [z₁, endEq], by rw [z₂, endEq]⟩
  · intro s t h
    simpa only [show 8 * (i + 1) - 8 = 8 * i by omega] using h

theorem load_word_ct {σ₁ σ₂ : State} {base : Addr} {bytes w i : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hi : i < 2 * w) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w (8 * (i + 1)) s ∧
      WindowReady σ₂ base bytes w (8 * (i + 1)) t) (.block wordLoad)
      (fun s t => True ∧ WindowReady σ₁ base bytes w (8 * (i + 1)) s ∧
      WindowReady σ₂ base bytes w (8 * (i + 1)) t) := by
  have upper := C.facts₁.upper
  have small : 8 * (i + 1) < 2 ^ 32 := by omega
  have native := C.counter (d := sK) (c := .block wordLoad) (k := 8 * (i + 1)) small (by decide) word_load_cert
  have hp : ∀ s t, (WindowReady σ₁ base bytes w (8 * (i + 1)) s ∧ WindowReady σ₂ base bytes w (8 * (i + 1)) t) →
      (HeaderReady σ₁ base bytes w sK (8 * (i + 1)) s ∧ HeaderReady σ₂ base bytes w sK (8 * (i + 1)) t) := by
    rintro s t ⟨h₁, h₂⟩
    exact ⟨⟨h₁.stage, h₁.count⟩, ⟨h₂.stage, h₂.count⟩⟩
  have core := native.mono hp (fun _ _ h => h)
  apply core.wp
  intro s t h
  constructor
  · exact load_word_ready C.facts₁ hi h.1
  · exact load_word_ready C.facts₂ hi h.2

theorem test_word_ct {σ₁ σ₂ : State} {base : Addr} {bytes w i : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hi : i < 2 * w) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w (8 * i) s ∧ WindowReady σ₂ base bytes w (8 * i) t)
      (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sK)), .alu .cmp .eax (.imm 0)])
      (fun s t => True ∧ (WindowReady σ₁ base bytes w (8 * i) s ∧ s.zf = some (decide (8 * i = 0))) ∧
        (WindowReady σ₂ base bytes w (8 * i) t ∧ t.zf = some (decide (8 * i = 0)))) := by
  have upper := C.facts₁.upper
  have small : 8 * i < 2 ^ 32 := by omega
  have native := C.counter (d := sK) (k := 8 * i) small (by decide) word_test_cert
  have hp : ∀ s t, (WindowReady σ₁ base bytes w (8 * i) s ∧ WindowReady σ₂ base bytes w (8 * i) t) →
      (HeaderReady σ₁ base bytes w sK (8 * i) s ∧ HeaderReady σ₂ base bytes w sK (8 * i) t) := by
    rintro s t ⟨h₁, h₂⟩
    exact ⟨⟨h₁.stage, h₁.count⟩, ⟨h₂.stage, h₂.count⟩⟩
  have core := native.mono hp (fun _ _ h => h)
  apply core.wp
  intro s t h
  constructor
  · exact test_word_ready C.facts₁ h.1 small
  · exact test_word_ready C.facts₂ h.2 small

theorem word_ct {σ₁ σ₂ : State} {base : Addr} {bytes w i : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hi : i < 2 * w) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w (8 * (i + 1)) s ∧
      WindowReady σ₂ base bytes w (8 * (i + 1)) t) word
      (fun s t => WindowReady σ₁ base bytes w (8 * i) s ∧ WindowReady σ₂ base bytes w (8 * i) t ∧
        s.zf = some (decide (i = 0)) ∧ t.zf = some (decide (i = 0))) := by
  have loadCT := load_word_ct C hi
  have testCT := test_word_ct C hi
  unfold VG.Impl.MillerRabin.X86.word seqs
  simp only [List.foldr_cons, List.foldr_nil]
  exact loadCT.seq (((eight_windows_ct C hi).mono (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩)
    (fun _ _ h => h)).seq (testCT.seq (RelCT.nil (fun _ _ ⟨_, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩ =>
      ⟨h₁, h₂, by simpa only [show 8 * i = 0 ↔ i = 0 by omega] using z₁,
        by simpa only [show 8 * i = 0 ↔ i = 0 by omega] using z₂⟩))))

theorem words_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w (16 * w) s ∧ WindowReady σ₂ base bytes w (16 * w) t)
      (.loop word .ne) (fun s t => WindowReady σ₁ base bytes w 0 s ∧ WindowReady σ₂ base bytes w 0 t) := by
  have lower := C.facts₁.lower
  refine (count_loop_ct (N := 2 * w) (by omega) (fun j s t =>
    WindowReady σ₁ base bytes w (16 * w - 8 * j) s ∧ WindowReady σ₂ base bytes w (16 * w - 8 * j) t) ?_).mono
      (fun _ _ h => h) ?_
  · intro j hj
    have count : 16 * w - 8 * j = 8 * ((2 * w - j - 1) + 1) := by omega
    refine (word_ct C (i := 2 * w - j - 1) (by omega)).mono (fun _ _ h => count ▸ h) ?_
    rintro s t ⟨h₁, h₂, z₁, z₂⟩
    have next : 8 * (2 * w - j - 1) = 16 * w - 8 * (j + 1) := by omega
    have endEq : decide (2 * w - j - 1 = 0) = decide (j + 1 = 2 * w) := decide_eq_decide.mpr (by omega)
    exact ⟨⟨next ▸ h₁, next ▸ h₂⟩, by rw [z₁, endEq], by rw [z₂, endEq]⟩
  · intro s t h
    simpa only [show 16 * w - 8 * (2 * w) = 0 by omega] using h

end VG.Proof.MillerRabin.X86
