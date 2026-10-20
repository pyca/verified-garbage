module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! The canonical dynamic context remains readonly throughout a search. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Spec.Ffdh

def rContext (p : KeyPublic sampling) : Region := ⟨State.addr p.context, 8 * p.contextWords⟩

theorem KeyInput.cached_held {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    CachedHeld p s.mem := by
  cases sampling with
  | full | vetted => simp [CachedHeld, GenerationPolicy.cachedContext]
  | cached =>
    intro _
    have pre := h.1
    cases h.2.1
    have strip : stripConsts [] s = s := by simp [stripConsts, State.withRegions]
    change (cachedKeySearchContract abi (stackUse .cached)).pre (stripConsts [] s) at pre
    rw [strip] at pre
    sig_pre [cachedKeySearchContract, cachedKeySearchSig,
      keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    sig_split pre
    change generationContextAt s.mem (State.addr (stackArg s 9)) (stackArg s 10).toNat
      (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
    simp only [generationContextAt, State.addr]
    constructor <;> sig_close

theorem KeyInput.context_fit {p : KeyPublic sampling} {s : State} (h : KeyInput p s)
    (cached : sampling.cachedContext = true) : p.context.toNat + 8 * p.contextWords ≤ 2 ^ 32 := by
  cases sampling with
  | full | vetted => simp [GenerationPolicy.cachedContext] at cached
  | cached =>
    have pre := h.1
    cases h.2.1
    have strip : stripConsts [] s = s := by simp [stripConsts, State.withRegions]
    change (cachedKeySearchContract abi (stackUse .cached)).pre (stripConsts [] s) at pre
    rw [strip] at pre
    sig_pre [cachedKeySearchContract, cachedKeySearchSig,
      keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    sig_split pre
    change (stackArg s 9).toNat + 8 * (stackArg s 10).toNat ≤ 2 ^ 32
    simp only [Nat.mul_comm] at *
    sig_close

theorem CachedHeld.after_frame {p : KeyPublic sampling} {m m' : Mem} {changes : List Region}
    (h : CachedHeld p m) (frame : Frame changes m m')
    (fit : sampling.cachedContext = true → 8 * p.contextWords < 2 ^ 64)
    (sep : sampling.cachedContext = true → ∀ r ∈ changes, (rContext p).Disjoint r) : CachedHeld p m' := by
  intro cached
  obtain ⟨size, canonical⟩ := h cached
  refine ⟨size, ?_⟩
  rw [VG.Proof.Rsa.wordsAt_frame frame (fit cached) (sep cached)]
  exact canonical

end VG.Proof.Ffdh.Arm.KeySearch
