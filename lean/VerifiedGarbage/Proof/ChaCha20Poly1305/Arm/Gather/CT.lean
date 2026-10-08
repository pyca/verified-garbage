import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace, related piece by piece
from given states (`Eq2`, `Proof/AesGcm/Arm/Gather/LoopCT.lean`): the
frame's words are read and written through `r12` at the stack pointer, the
same in both runs (`rel_fp`); the gathering is constant time by
`gather_rel`; and the call is constant time by its callee's contract, whose
public arguments agree (`sealGather_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm.SealGather
open VG.Proof.AesGcm.Arm.Gather (Eq2 TT rel_seq rel_fp rel_alloc ct_of gather_rel)

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q0, q1, q2, q3, qsp, qa, hdesc⟩ := hq
  have a0 := qa 0 (by decide)
  have a1 := qa 1 (by decide)
  have a2 := qa 2 (by decide)
  have a3 := qa 3 (by decide)
  have a4 := qa 4 (by decide)
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_fp (l := entryWords) (show Pf σ₁ = Pf σ₂ from hP) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← a0, ← a1, ← a2, ← a3] at g₂
  have hd : ∀ j < Cnt σ₁ * 8,
      e₁.mem (State.addr (Src σ₁) + BitVec.ofNat 64 j) = e₂.mem (State.addr (Src σ₁) + BitVec.ofNat 64 j) := by
    intro j hj
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₁, -, -, -, -, -, -, -, ods, -⟩ := p₁
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₂, -⟩ := p₂
    have hx : (dsR σ₁).Contains (State.addr (Src σ₁) + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by omega)
    have hx₂ : (dsR σ₂).Contains (State.addr (Src σ₁) + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← a0, ← a1]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE bds₁.symm hx, h₂.keepE bds₂.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂) fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_fp (l := argWords) (by rw [hg₁.sp, hg₂.sp, hP]) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, Bs, q0, q1, q2, q3, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a2, a3, a4]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁⟩ := hc₁.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨r0₂, r1₂, r2₂, r3₂⟩ := hc₂.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₁, s1₁, s2₁⟩ := hc₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂⟩ := hc₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩,
        cv₁, cw₁, cv₂, cw₂⟩
      · rw [r0₁, r0₂, q0]
      · rw [r1₁, r1₂, q1]
      · rw [r2₁, r2₂, q2]
      · rw [r3₁, r3₂, q3]
      · simp only [State.withRegions_sp, State.callEntry_sp, hc₁.sp, hc₂.sp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a2
        · rw [s1₁, s1₂]; exact a3
        · rw [s2₁, s2₂]; exact a4)
    (called_wp F h₁ hc₁) (called_wp F h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_fp (l := [Instr.ldr .lr .r12 12]) (by rw [hz₁.sp, hz₂.sp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.Arm.Gather
