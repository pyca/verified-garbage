module

public import VerifiedGarbage.Spec.Gcm.Prepared16

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import Mathlib.Data.List.Basic
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! # Sixteen prepared powers: Prepared-context StreamCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem encSpecPrepared16_pre {s : State} (h : encCallPre CtxMode.prepared16 s) :
    (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  all_goals with_reducible assumption

theorem encSpecPrepared16_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, Spec.Gcm.streamEncryptPost] at h
  sig_reduce [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecPrepared16_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPrepared16Contract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def EncFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptPrepared16Contract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.prepared16 where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecPrepared16_pre h)
    exact ⟨t, s', he, ha, encSpecPrepared16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecPrepared16_pre h₁) (encSpecPrepared16_pre h₂)
    (encSpecPrepared16_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

end VG.Proof.AesGcm.X86_64.StreamTo
