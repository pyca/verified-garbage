import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo

/-! # Prepared-context StreamCallee contracts -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem encSpecPrepared_pre {s : State} (h : encCallPre CtxMode.prepared s) :
    (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂⟩ := h
  sig_pre [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared] at *
  all_goals with_reducible assumption

theorem encSpecPrepared_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamCryptPreparedPre, X86_64.abi, X86_64.argRegs, Spec.Gcm.streamEncryptPost] at h
  sig_reduce [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecPrepared_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPreparedContract, Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def EncFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.prepared where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecPrepared_pre h)
    exact ⟨t, s', he, ha, encSpecPrepared_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecPrepared_pre h₁) (encSpecPrepared_pre h₂)
    (encSpecPrepared_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

end VG.Proof.AesGcm.X86_64.StreamTo
