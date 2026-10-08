import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and descriptors agree (`gatherPub`) leak the same trace, related
piece by piece from given states (`Eq2`,
`Proof/AesGcm/X86/Gather/LoopCT.lean`): the frame's words and our arguments
are read and written at `esp`, the same in both runs (the taint analysis
from `esp`); the gathering is constant time by `gather_rel`; and the call is
constant time by its callee's contract, whose public arguments agree
(`sealGather_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86.SealGather
open VG.Proof.AesGcm.X86 (w64)
open VG.Proof.AesGcm.X86.Gather (Eq2 TT rel_seq rel_taint rel_alloc ct_of gather_rel)

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, qa, hdesc⟩ := hq
  have a (i : Nat) (hi : i < 9) := qa i hi
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_taint [.esp] (by simp [hP]) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← a 4 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide)] at g₂
  have hd : ∀ j < Cnt σ₁ * 8,
      e₁.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) = e₂.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega)
    have hx₂ : (dsR σ₂).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← a 4 (by decide), ← a 5 (by decide)]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE h₁.bds.symm hx, h₂.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂) fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, ← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide),
      ← a 3 (by decide)]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, Bs, ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide), qsp]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hg₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hg₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨s0₁, s1₁, s2₁, s3₁, s4₁, s5₁, s6₁⟩ := hg₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂, s3₂, s4₂, s5₂, s6₂⟩ := hg₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, fun i hi => ?_⟩, cv₁, cw₁, cv₂, cw₂,
        by rw [hg₁.esp, hg₂.esp, hP]⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, hg₁.esp, hg₂.esp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a 0 (by decide)
        · rw [s1₁, s1₂]; exact a 1 (by decide)
        · rw [s2₁, s2₂]; exact a 2 (by decide)
        · rw [s3₁, s3₂]; exact a 3 (by decide)
        · rw [s4₁, s4₂]; exact a 6 (by decide)
        · rw [s5₁, s5₂]; exact a 7 (by decide)
        · rw [s6₁, s6₂]; exact a 8 (by decide))
    (called_wp F h₁ hg₁) (called_wp F h₂ hg₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- Our caller's registers back.
  exact rel_taint [.esp] (by simp [hz₁.esp, hz₂.esp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.X86.Gather
