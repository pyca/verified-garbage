module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Start
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Loop
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Finish
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Framework.Block

/-! The full native ARMv7 key search satisfies the shared result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration

def searchResult (p : KeyPublic) (s : State) : KeySearchResult :=
  keySearch p.a p.len ⟨p.keys, p.scalars⟩ (keyRand p s)

theorem function_ok (backend : VG.Proof.Ffdh.Arm.Backend) {p : KeyPublic} {s : State}
    (h : KeyInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.code (.call backend.keyName backend.generateKey)) s fun t =>
      abiPreserved s t ∧ ResultPost p (searchResult p s) t := by
  have fit : 24 ≤ s.sp.toNat := by
    have fits := h.bounds.stackFits
    rw [← h.2] at fits
    change 184 ≤ s.sp.toNat at fits
    omega
  unfold VG.Impl.Ffdh.Arm.KeySearch.code
  refine WP.frame (by decide) fit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (start_ok h) ?_
  intro u live
  rw [WP.seq_iff]
  have inv : KeyInvariant p s (searchResult p s) (128 * p.keys + p.scalars + 1) u := by
    refine ⟨0, p.keys, p.scalars, rfl, live, ?_, ?_⟩
    all_goals simp only [searchResult, KeyPublic.tail, keyTail, after, List.drop_zero, Nat.zero_add]
  refine WP.mono (loop backend (attemptRun_ok backend) inv) ?_
  intro t finished
  exact finish_ok finished

theorem correct (backend : VG.Proof.Ffdh.Arm.Backend) (s : State)
    (pre : (keySearchContract abi stackUse).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.KeySearch.code (.call backend.keyName backend.generateKey)) s tr t ∧
      abiPreserved s t ∧ (keySearchContract abi stackUse).post s t := by
  let p := keyOfState s
  have input : KeyInput p s := ⟨pre, rfl⟩
  obtain ⟨tr, t, run, abiOk, result⟩ := function_ok backend input
  refine ⟨tr, t, run, abiOk, ?_⟩
  have statusFits : (searchResult p s).status < 2 ^ 32 := by
    cases outcome : (searchResult p s).outcome <;> simp [KeySearchResult.status, outcome]
  sig_post [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change (t.gpr .r0).toNat = (searchResult p s).status ∧
    KeyOutput p (searchResult p s) t.mem ∧
    Spec.Rsa.wordsAt t.mem (State.addr p.control) 4 =
      [BitVec.ofNat 64 (searchResult p s).retries.keys, BitVec.ofNat 64 (searchResult p s).retries.scalars,
        BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if (searchResult p s).status = 0 then p.len else 0)] ∧
    Spec.Rsa.wordsAt t.mem (State.addr p.up) 1 = [BitVec.ofNat 64 (searchResult p s).used]
  refine ⟨?_, result.output, result.policy, result.used⟩
  rw [result.status, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusFits]

end VG.Proof.Ffdh.Arm.KeySearch
