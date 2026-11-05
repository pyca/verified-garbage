module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptContract
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptVerified
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptContract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCorrect
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCT
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl

/-! # One key-generation attempt: `vg_ffdh_generate_key_cached`, called

The controller calls the backend's `vg_ffdh_generate_key_cached` as emitted
(`attemptCode`, multiplying by calls on BMI2/ADX). Its proof is of the
inlined form (`cg_correct`, `cg_constantTime`), which the call runs but for
the return addresses of the multiplications, in the 8 octets below the
callee's stack pointer.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.Cached
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64

/-- What the attempt needs: `cg`'s precondition, and no buffer in the 8
octets below the stack pointer. -/
def attemptPre (s : State) : Prop := cgPre s ∧ Clear (hole (s.gpr .rsp)) s

def attemptContract : Contract isa where
  pre := attemptPre
  post := cgPost
  pub := cgPub

/-- The attempt, as the controller calls it. -/
def attemptCall (v : RoundImpl) : Prog isa :=
  .call (Spec.Ffdh.cachedGenerateKeyApi.name ++ v.suffix) (attemptCode v)

private theorem inline_correct (v : RoundImpl) (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa (attemptInline v) s tr t ∧ abiPreserved s t ∧ cgContract.post s t :=
  cg_correct v.mont (R2Impl.words v.mont) (attemptInline_mx v) s h

theorem attempt_correct (v : RoundImpl) (s : State) (h : attemptContract.pre s) :
    ∃ tr t, Exec isa (attemptCode v) s tr t ∧ abiPreserved s t ∧ attemptContract.post s t := by
  obtain ⟨hpre, hclear⟩ := h
  obtain ⟨tr, b, he, ha, hp⟩ := inline_correct v s hpre
  rw [← attemptCode_inline] at he
  obtain ⟨hv, u, ta, he', _, _⟩ := Exec.of_inline (attemptCode_inlineOk v) he hclear
  refine ⟨ta, _, he', abiPreserved_patch hv u ha, ?_⟩
  have hw : s.wr = _ := hpre.2.2.1
  have hx := Clear.wr_bytes hclear (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  have hy := Clear.wr_bytes hclear (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hxl, hyl, -, -, -, -, -⟩ := hpre
  rw [hxl] at hx
  rw [hyl] at hy
  simp only [attemptContract, cgPost, State.patch, bytesAt_overlay hx, bytesAt_overlay hy]
  exact hp

theorem attempt_constantTime (v : RoundImpl) :
    ConstantTime isa attemptContract.pre attemptContract.pub (attemptCode v) := by
  refine ConstantTime.of_inline (attemptCode_inlineOk v) (fun s h => ?_) (fun _ h => h.2)
    (fun _ _ _ _ hp => hp.1) ?_
  · obtain ⟨tr, t, he, -, -⟩ := inline_correct v s h.1
    exact ⟨tr, t, by rw [attemptCode_inline]; exact he⟩
  · rw [attemptCode_inline]
    have ct := cg_constantTime v.mont (R2Impl.words v.mont)
    exact fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

/-! ## The stack the attempt uses -/

/-- Code without calls or frames uses no stack. -/
theorem depth_noCalls : ∀ {c : Prog isa}, c.noCalls = true → c.x86_64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, depth_noCalls h.2, Nat.max_self]
  | .ite _ t e, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, depth_noCalls h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noCalls] at h
    simp only [Code.x86_64Depth, depth_noCalls h]
  | .call _ _, h => by simp only [Code.noCalls] at h; cases h
  | .frame .., h => by simp only [Code.noCalls] at h; cases h
  | .icall .., h => by simp only [Code.noCalls] at h; cases h

/-- Code whose calls can be inlined uses at most their return addresses. -/
theorem depth_inlineOk : ∀ {c : Prog isa}, c.InlineOk = true → c.x86_64Depth ≤ 8
  | .block _, _ => Nat.zero_le _
  | .seq a b, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, Nat.max_le]
    exact ⟨depth_inlineOk h.1, depth_inlineOk h.2⟩
  | .ite _ t e, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, Nat.max_le]
    exact ⟨depth_inlineOk h.1, depth_inlineOk h.2⟩
  | .loop b _, h => by
    simp only [Code.InlineOk] at h
    simp only [Code.x86_64Depth]
    exact depth_inlineOk h
  | .call _ b, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, Nat.zero_add, Nat.le_refl]
  | .frame .., h => by simp only [Code.InlineOk] at h; cases h
  | .icall .., h => by simp only [Code.InlineOk] at h; cases h

theorem attemptCode_depth (v : RoundImpl) : (attemptCode v).x86_64Depth ≤ 8 :=
  depth_inlineOk (attemptCode_inlineOk v)

theorem attemptCall_depth (v : RoundImpl) : (attemptCall v).x86_64Depth ≤ 16 := by
  change (attemptCode v).x86_64Depth + 8 ≤ 16
  exact Nat.add_le_add_right (attemptCode_depth v) 8

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
