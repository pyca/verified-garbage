module

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Finish
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Loop

/-! # The key-generation controller's correctness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.KeyGeneration
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem initial_key_result {p : KeyPublic} {s : State} (h : KeyInput p s) :
    keyResult s = p.tail (keyRand s) 0 p.keys p.scalars := by
  cases h.2
  simp only [keyResult, KeyPublic.tail, keyTail, after, keyOfState, KeyPublic.a, List.drop_zero,
    Nat.zero_add]

theorem returned_post {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hr : KeyReturned p (keyResult s) t) : keyPost s t := by
  cases h.2
  exact hr

theorem key_correct_ok (v : RoundImpl) {s : State} (h : keyPre s) :
    WP isa (code (attemptCall v)) s fun t => keyPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let p := keyOfState s
  have hp : KeyInput p s := ⟨h, rfl⟩
  unfold code
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (key_start hp) fun u hu => ?_)
  have hinv : KeyInvariant p s (keyResult s) (128 * p.keys + p.scalars + 1) u :=
    ⟨0, p.keys, p.scalars, rfl, hu, by rw [initial_key_result hp], by rw [initial_key_result hp]⟩
  refine WP.seq (WP.mono (key_loop v hinv) fun t ht => ?_)
  refine WP.mono (key_finish ht) fun q ⟨hr, hg, hrd, hwr⟩ => ?_
  exact ⟨returned_post hp hr, hg, hrd, hwr⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
