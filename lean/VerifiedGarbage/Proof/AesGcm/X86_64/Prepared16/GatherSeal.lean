module

public import VerifiedGarbage.Spec.Gcm.Prepared16

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SealCallee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Data.List.Basic
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies a short text to the output and encrypts it there by a call of
`vg_aes_gcm_seal_prepared`, by its shared contract, as
`Gather/SealCallee.lean` does for the other key contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem sealSpecR16_pre {s : State} (h : sealPreK CtxMode.prepared16 s) :
    (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  sig_pre [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  all_goals with_reducible assumption

theorem sealSpecR16_post {s s' : State} (hR : rounds s)
    (h : (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624).post s s') :
    Proof.AesGcm.sealX86_64.post s s' := by
  sig_post [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, Spec.Gcm.sealPrepared16Pre,
    X86_64.abi, X86_64.argRegs, Spec.Gcm.sealPost] at h
  sig_reduce [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem sealSpecR16_pub {s₁ s₂ : State} (h : sealPubK s₁ s₂) :
    (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealPrepared16Contract, Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_prepared` from its shared contract. -/
def SealFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2624)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SealFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => sealSpecR16_pre h)
    (fun _ _ h h' => sealSpecR16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => sealSpecR16_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
