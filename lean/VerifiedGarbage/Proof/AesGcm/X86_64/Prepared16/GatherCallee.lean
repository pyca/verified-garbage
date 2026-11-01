module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Data.List.Basic
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! # Sixteen prepared powers: Prepared-context GatherCallee contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)

theorem toSpecPrepared16_pre {s : State} (h : toPre CtxMode.prepared16 s) :
    (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
  have a₂₈ := h
  clear h
  sig_pre [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr] at *
  all_goals first
    | with_reducible assumption
    | omega
    | exact congrArg (BitVec.setWidth 64) a₃

theorem toSpecPrepared16_post {s s' : State} (hR : rounds s)
    (h : (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPrepared16Pre, X86_64.abi, X86_64.argRegs, Proof.Gcm.streamEncryptToPost] at h
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpecPrepared16_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.Gcm.streamEncryptToPrepared16Contract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

def ToFn.ofPrepared16 (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.streamEncryptToPrepared16Contract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.prepared16 :=
  CallFn.ofSpec f hv (fun _ h => toSpecPrepared16_pre h)
    (fun _ _ h h' => toSpecPrepared16_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpecPrepared16_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
