module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfPost
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.EncodeTaint
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data leak the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem lenCheck_vp : VP (S P) (.block lenCheck) (H1 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => lenCheck_wp h

theorem cmp_vp : VP (H1 P) (.block [.cmp .r0 (.imm 0)]) (H2 P) :=
  VP.taint [.r0] cmp_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun _ _ h => cmp_wp h

theorem ret0_vp : VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some true) (.block ret0) (Fin P) :=
  VP.taint [] ret0_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => ret0_wp h

theorem callArgs_vp : VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some false) (.block callArgs) (C1 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1) fun _ _ h => callArgs_wp (c0_of h)

theorem encArgs_vp : VP (C2 P) (.block encArgs) (C3 P) :=
  VP.stk (code := [_, _, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => encArgs_wp h

theorem encode_vp : VP (C3 P) Impl.RsaPkcs1Sig.Arm.encode (C4 P) :=
  VP.taint [.r0, .r1, .r2, .r3, .lr] encode_taint (fun _ _ _ _ h₁ h₂ r hr => by
    obtain ⟨-, -, a0, a1, a2, a3, a4⟩ := h₁
    obtain ⟨-, -, b0, b1, b2, b3, b4⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]) fun _ _ h => encode_wp h

theorem cmpArgs_vp : VP (C4 P) (.block cmpArgs) (C5 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1)
    fun _ _ h => cmpArgs_wp h

theorem compare_vp : VP (C5 P) Impl.Bignum.Arm.compareBytes (C6 P) :=
  VP.ct Bignum.Arm.compareBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨-, -, -, a0, a1, a2, -⟩ := h₁
    obtain ⟨-, -, -, b0, b1, b2, -⟩ := h₂
    exact ⟨by rw [a0, b0], by rw [a1, b1], by rw [a2, b2]⟩) fun _ _ h => compare_wp h

theorem result_vp : VP (C6 P) (.block result) (Fin P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1 h₂.1.1) fun _ _ h => result_wp h

theorem rest_vp (c : PdImpl) :
    VP (fun σ s => H2 P σ s ∧ isa.eval .ne s = some false) (rest c.name c.code) (Fin P) :=
  callArgs_vp.seq ((call_vp c).seq (encArgs_vp.seq (encode_vp.seq (cmpArgs_vp.seq (compare_vp.seq result_vp)))))

theorem body_vp (c : PdImpl) : VP (S P) (body c.name c.code) (Fin P) :=
  lenCheck_vp.seq (cmp_vp.seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [Proof.X25519.Arm.eval_ne, Proof.X25519.Arm.eval_ne, h₁.2, h₂.2]) ret0_vp (rest_vp c)))

end VG.Proof.RsaPkcs1Sig.Arm.Vf
