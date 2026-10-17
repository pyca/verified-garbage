module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcTaint
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`G13`), and two runs with the same public data leak the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- Two states of the body have the same stack pointer. -/
theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem start_vp : VP (S P) (.block start) (G1 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => start_wp h

theorem head_vp : VP (G1 P) (.block head) (PsI P P.pl) :=
  VP.taint [.r0] head_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun _ _ h => head_wp h

theorem psLoop_vp : VP (PsI P P.pl) psLoop (PsI P 0) := by
  refine (VP.loop (I := fun k => PsI P k) (fun n => VP.taint [.r0, .r1, .lr] psBody_taint
    (fun _ _ _ _ h₁ h₂ r hr => ?_) fun _ _ h => psBody_wp h) (P.pl - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [show P.pl - 1 + 1 = P.pl by have := h.1.1.pl8; omega]; exact h

theorem sep_vp : VP (PsI P 0) (.block sep) (G4 P) :=
  VP.taint [.r0] sep_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => sep_wp h

theorem msgArgs_vp : VP (G4 P) (.block msgArgs) (G5 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1) fun _ _ h => msgArgs_wp h

theorem msgCopy_vp : VP (G5 P) msgCopy (G6 P) := by
  refine VP.seq (G := fun σ s => G5 P σ s ∧ s.z = decide (P.ml = 0))
    (VP.taint [.lr] cmp_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) fun _ _ h => cmp_wp h) ?_
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [Proof.X25519.Arm.eval_eq, Proof.X25519.Arm.eval_eq, h₁.2, h₂.2])
    (VP.block_nil fun _ _ h => skip_g6 h.1.1 (by have := h.2; rw [Proof.X25519.Arm.eval_eq, h.1.2] at this; simpa using this))
    (VP.ct Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.1.1.2.1, h₂.1.1.2.1], by rw [h₁.1.1.2.2.1, h₂.1.1.2.2.1],
      by rw [h₁.1.1.2.2.2.1, h₂.1.1.2.2.2.1]⟩)
      fun _ _ h => copy_wp h.1.1 (by have := h.2; rw [Proof.X25519.Arm.eval_eq, h.1.2] at this; simpa using this))

theorem callArgs_vp : VP (G6 P) (.block callArgs) (G7 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1) fun _ _ h => callArgs_wp h

theorem maskArgs_vp : VP (G8 P) (.block maskArgs) (G9 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => maskArgs_wp h

theorem maskOut_vp : VP (G9 P) Impl.Bignum.Arm.maskBytes (G10 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨_, _, _, _, _, _, r0₁, lr₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, r0₂, lr₂⟩ := h₂
    exact ⟨by rw [r0₁, r0₂], by rw [lr₁, lr₂]⟩) fun _ _ h => maskOut_wp h

theorem wipeArgs_vp : VP (G10 P) (.block wipeArgs) (G11 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (G11 P) Impl.Bignum.Arm.maskBytes (G12 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (G12 P) (.block [.mov .r0 (.reg .r3)]) (G13 P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem body_vp (c : PdImpl) : VP (S P) (body c.name c.code) (G13 P) :=
  start_vp.seq (head_vp.seq (psLoop_vp.seq (sep_vp.seq (msgArgs_vp.seq (msgCopy_vp.seq (callArgs_vp.seq
    ((call_vp c).seq (maskArgs_vp.seq (maskOut_vp.seq (wipeArgs_vp.seq (wipe_vp.seq fin_vp)))))))))))

end VG.Proof.RsaPkcs1Enc.Arm.Pc
