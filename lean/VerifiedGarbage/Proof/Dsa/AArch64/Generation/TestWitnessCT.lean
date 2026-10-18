module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TestWitness
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw

/-! Loading and classifying a stored witness has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MlKem.AArch64

structure SamplePublic where
  prime : PrimeParams
  bytes : List Byte
  length : bytes.length = prime.len

def SampleBefore (p : SamplePublic) (s : State) : Prop :=
  SampleState p.prime.B p.prime.p p.prime.Z p.prime.w p.prime.N p.bytes s

def SampleLoaded (p : SamplePublic) (s : State) : Prop :=
  ModulusReady s p.prime.B p.prime.Z p.prime.w p.prime.N ∧
    wv s.mem p.prime.B (slot p.prime.w aX) p.prime.w = Spec.Rsa.os2ip p.bytes

theorem sampleLoad_ct : RelCT isa (Two SampleBefore) Impl.Dsa.AArch64.Generation.loadWitness (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.loadWitness
  exact loadA_ct0 (fun p : SamplePublic => p.prime.B) (fun p => p.prime.Z) (fun p => p.prime.w)
    (by decide) (by decide) (by decide) (fun p => p.prime.p) (fun p => p.bytes.length)
    (fun _ _ h => ⟨h.ready.ws, h.ptr, h.len⟩) (by taint_decide) (by taint_decide) (by taint_decide)

theorem sampleLoad_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa Impl.Dsa.AArch64.Generation.loadWitness s (SampleLoaded p) :=
  WP.mono (loadWitness_ok h.ready p.prime.exponentRoom h.ptr h.len h.source
    (by rw [p.length]; have := p.prime.len2; omega) (by rw [p.length]; exact p.prime.lenWords))
    (fun _ ⟨hr, hx, _, _⟩ => ⟨hr, hx⟩)

theorem witnessRange_ct : RelCT isa (Two PrimeGood) Impl.Dsa.AArch64.Generation.witnessRange (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.witnessRange
  refine two_map (Φ' := fun (q : WPub) s => VG.Proof.Rsa.AArch64.Ws s q.L.B q.L.Z q.L.w)
    (fun p : PrimeParams => (⟨⟨p.B, p.Z, p.w⟩, p.rp, 0⟩ : WPub)) (fun _ _ h => h) ?_
  have e : ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa)) =
      [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] ++
      ([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop] ++
      [.block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) := rfl
  rw [e]
  exact ct_app' (by simp) (by simp) witLow_ct (ct_app' (by simp) (by simp) witCmp_ct
    (two_taint _ (pins_of _ (fun p : WPub => wsVal p.L.B p.L.w) fun _ _ h => h) (by taint_decide)))


theorem witnessRange_good {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa Impl.Dsa.AArch64.Generation.witnessRange s (PrimeGood p) := by
  refine WP.mono (drawRange_ok h (X := wv s.mem p.B (slot p.w aX) p.w) rfl)
    fun t ⟨_, hm, hk⟩ => ?_
  exact h.congr' (rs := []) (by intro a _; rw [hm]) (by simp) hk (by decide)

theorem testRange_ct : RelCT isa (Two PrimeGood) Impl.Dsa.AArch64.Generation.testRange (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.testRange
  exact RelCT.seq (two_post witnessRange_ct (fun _ _ h => witnessRange_good h))
    (two_taint [.x0] (fun _ _ _ hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hs.x0.trans ht.x0.symm) (by taint_decide))

theorem testWitness_ct : RelCT isa (Two SampleBefore) Impl.Dsa.AArch64.Generation.testWitness (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.testWitness
  exact RelCT.seq (two_post sampleLoad_ct (fun _ _ h => sampleLoad_state h))
    (two_map SamplePublic.prime (fun _ _ h => h.1.ws) testRange_ct)

end VG.Proof.Dsa.AArch64.Generation
