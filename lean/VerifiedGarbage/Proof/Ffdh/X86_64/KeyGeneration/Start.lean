module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Layout
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # After its entry, the key-generation controller is at the tape's start -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyInput.keys_le {p : KeyPublic} {s : State} (h : KeyInput p s) : p.keys ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -, -⟩ := h.1
  rw [← h.2]; exact hk

theorem KeyInput.scalars_le {p : KeyPublic} {s : State} (h : KeyInput p s) : p.scalars ≤ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -⟩ := h.1
  rw [← h.2]; exact hs

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 6 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw⟩ := h.1
  exact hw

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control
      (p.headers 0 p.keys p.scalars) := by
  have hw := h.width_word
  cases h.2
  intro e he
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [keyOfState, controllerValue, entryValues, headValues, tailValues,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off]
    rfl
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · rfl

theorem key_start {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t => KeyLive p s 0 p.keys p.scalars t := by
  refine WP.mono (entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf' : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.2.1, k.2.2, ?_, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.2]
    exact k.gpr (by decide)
  · intro r hcal hne
    exact k.gpr (by cases r <;> simp_all [calleeSaved])
  · rw [hm]
    change word (writeController s.mem p.control (entryValues s)) p.control (8 * 4) = _
    rw [writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf']
    cases h.2
    rfl
  · rw [h.domain_frame hf']
    cases h.2
    rfl
  · rw [hm]
    exact entry_headers h

end VG.Proof.Ffdh.X86_64.KeyGeneration
