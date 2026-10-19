module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitnessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitnessCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample

/-! The forced-witness transformation uses only public buffer addresses. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem forceSampleArgs_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (.block [ldh .x1 kOut]) s (fun t => t.gpr .x1 = p.prime.p) := by
  have hw := h.ready.ws
  brun [hw.x0, hdr_enc (show kOut < 32 by decide), h.ptr,
    hw.scr.ld (show 8 * kOut + 8 ≤ p.prime.Z by have := hw.h256; simp only [kOut, sFn]; omega)]

theorem forceStoredWitness_ct (len : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x1])
      (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc).isSome = true) :
    RelCT isa (Two SampleBefore) (Impl.Dsa.AArch64.Generation.forceStoredWitness len) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.forceStoredWitness
  apply RelCT.block_append
  refine RelCT.seq (two_post (two_taint [.x0] ?_ (by taint_decide))
    (fun _ _ h => forceSampleArgs_state h)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.ready.ws.x0.trans ht.ready.ws.x0.symm
  · exact two_taint [.x1] (fun _ _ _ hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hs.trans ht.symm) ht

def SamplePublic.forced (p : SamplePublic) : SamplePublic :=
  ⟨p.prime, VG.Proof.Dsa.Generation.forcedWitnessBytes p.bytes,
    (VG.Proof.Dsa.Generation.forcedWitnessBytes_length
      (by rw [p.length]; exact p.prime.len2)).trans p.length⟩

theorem forceSample_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.AArch64.Generation.forceStoredWitness p.bytes.length) s (SampleBefore p.forced) :=
  WP.mono (forceSample_ok h p.prime.exponentRoom
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega))
    (fun _ ⟨ht, _, _, _⟩ => ht)

end VG.Proof.Dsa.AArch64.Generation
