module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCallee
public import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_split_prepared` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
copies the slices after the first of a short text to the output and
encrypts the text by a call of `vg_aes_gcm_seal_split_prepared`, by its
shared contract, as `Gather/SplitCallee.lean` does for the other key
contexts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

theorem splitSpecR_pre {s : State} (h : splitPreK CtxMode.prepared s) :
    (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    Spec.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    Spec.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared,
    BitVec.setWidth_eq] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpecR_post {M : CtxMode} {s s' : State}
    (h : (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672).post s s') (hR : rounds s) :
    (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    Spec.Gcm.sealSplitPreparedPre, X86_64.abi, X86_64.argRegs, Spec.Gcm.sealSplitPost] at h
  sig_reduce [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecR_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂⟩ := h
  sig_pub [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.sealSplitPreparedContract, Spec.Gcm.sealSplitPreparedSig, Spec.Gcm.sealSplitPrecomputedSig,
    X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- `vg_aes_gcm_seal_split_prepared` from its shared contract. -/
def SplitFn.ofPrepared (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.prepared :=
  CallFn.ofSpec f hv (fun _ h => splitSpecR_pre h)
    (fun _ _ h h' => splitSpecR_post (M := CtxMode.prepared) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecR_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
