module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgTail
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.EncodeTaint
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data leak the same trace. The
branch on the encoding's success agrees in two runs: it depends only on the
hash function's number and the lengths (`enc_isNone`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem encArgs_vp : VP (S P) (.block encArgs) (E1 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => encArgs_wp h

theorem encode_vp : VP (E1 P) Impl.RsaPkcs1Sig.Arm.encode (E2 P) :=
  VP.taint [.r0, .r1, .r2, .r3, .lr] encode_taint (fun _ _ _ _ h₁ h₂ r hr => by
    obtain ⟨-, a0, a1, a2, a3, a4⟩ := h₁
    obtain ⟨-, b0, b1, b2, b3, b4⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]) fun _ _ h => encode_wp h

theorem cmp_vp : VP (E2 P) (.block [.cmp .r3 (.imm 0)]) (E3 P) :=
  VP.taint [.r3] cmp_taint (fun σ₁ σ₂ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [encR_r3 h₁.2, encR_r3 h₂.2]
    exact congrArg (fun b : Bool => if b = true then (0 : BitVec 32) else 1) (enc_isNone P σ₁ σ₂))
    fun _ _ h => cmp_wp h

theorem fail_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some true)
    (.seq (.block zeroArgs) (.seq Impl.Bignum.Arm.maskBytes (.block ret0))) (Fin P) :=
  (VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => zeroArgs_wp h).seq
  ((VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => zero_wp h).seq
  (VP.taint [] ret0_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => ret0_wp h))

theorem callArgs_vp : VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false) (.block callArgs) (R1 P) :=
  VP.stk (code := callArgs.tail) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1 h₂.1.1.1)
    fun _ _ h => callArgs_wp (r0_of h)

theorem wipeArgs_vp : VP (R2 P) (.block wipeArgs) (R3 P) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (R3 P) Impl.Bignum.Arm.maskBytes (R4 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (R4 P) (.block [.mov .r0 (.reg .r3)]) (Fin P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem rest_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (fun σ s => E3 P σ s ∧ isa.eval .eq s = some false)
      (rest (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin P) :=
  callArgs_vp.seq ((call_vp v).seq (wipeArgs_vp.seq (wipe_vp.seq fin_vp)))

theorem body_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (body (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin P) :=
  encArgs_vp.seq (encode_vp.seq (cmp_vp.seq (VP.ite (fun σ₁ σ₂ _ _ h₁ h₂ => by
    rw [Proof.X25519.Arm.eval_eq, Proof.X25519.Arm.eval_eq, h₁.2, h₂.2, enc_isNone P σ₁ σ₂]) fail_vp (rest_vp v))))

end VG.Proof.RsaPkcs1Sig.Arm.Sg
