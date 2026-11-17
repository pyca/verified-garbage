module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuildCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSeed
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT

/-! ### `Dsa.AArch64.Generation.SubgroupCTState`, which only this module used -/

section

/-! # Public subgroup-generation data excludes unused frame contents -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

structure SubgroupPublic where
  plan : SubgroupPlan
  used : Nat

def SubgroupPlan.withWords (p : SubgroupPlan) (W : Nat → BitVec 64)
    (hw : ∀ i ∈ [0, 5, 14, 15], W i = p.W i) : SubgroupPlan :=
  { p with W := W
           base := by rw [hw 5 (by simp)]; exact p.base
           outputPtr := by rw [hw 5 (by simp)]; exact p.outputPtr
           outputSlot := (hw 0 (by simp)).trans p.outputSlot
           witnessPtr := by rw [hw 5 (by simp)]; exact p.witnessPtr
           tapePtr := (hw 14 (by simp)).trans p.tapePtr
           tapeLength := (hw 15 (by simp)).trans p.tapeLength
           geometry := by rw [hw 5 (by simp)]; exact p.geometry }

def SubgroupBefore (p : SubgroupPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i ∈ [0, 5, 14, 15], W i = p.plan.W i,
    SubgroupState (p.plan.withWords W hw) p.used s

def SubgroupPublic.hash (p : SubgroupPublic) : QHashPlan :=
  ⟨p.plan.F, p.plan.hash, p.plan.seedPtr, p.plan.prime.len, p.plan.output, p.plan.width⟩

theorem subgroup_hash {p : SubgroupPublic} {s : State} (h : SubgroupBefore p s) : QHashState p.hash s := by
  obtain ⟨W, hw, hs⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact ⟨hs.layout, V, W, R, hs.label, (p.plan.withWords W hw).outputSlot⟩

def SubgroupPublic.primeCall (p : SubgroupPublic) : PrimeTestPublic (8 * p.plan.prime.len) where
  F := p.plan.F
  S := p.plan.hash
  A := p.plan.W 5
  rp := p.plan.prime.rp
  rand := p.plan.prime.rand
  N := p.plan.prime.N
  used := p.used
  geometry := p.plan.geometry

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SubgroupReadyCT`, which only this module used -/

section

/-! # Hash and shape the subgroup candidate before the native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem subgroup_candidate_ready (H : GenerationHashes)
    {p : SubgroupPublic} {s : State} (h : SubgroupBefore p s) :
    WP isa (qCandidate H.sha1 H.sha256) s fun t =>
      PrimeTestBefore (8 * p.plan.prime.len) p.primeCall t := by
  obtain ⟨W, hw, hs⟩ := h
  let q := p.plan.withWords W hw
  have plen : p.plan.prime.len ≤ 32 := by rcases p.plan.width with h | h <;> omega_using [h]
  obtain ⟨V, R⟩ := hs.rep
  have candidate := qBuild_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
    H.width1 H.width256 p.plan.width hs.layout R hs.label q.outputSlot hs.outputWrite
    p.plan.outputFrame.symm p.plan.outputScratch
  dsimp only [q, SubgroupPlan.withWords] at candidate
  refine WP.mono candidate fun t ⟨tq, step, ff, L, V', R'⟩ => ?_
  have bt : Spec.Rsa.bytesAt t.mem p.plan.output p.plan.prime.len =
      Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N := by
    have se : Spec.Rsa.bytesAt s.mem p.plan.seedPtr p.plan.prime.len = p.plan.seed := hs.seed
    rw [tq, se]
    exact congrArg (Spec.Dsa.encodeBE p.plan.prime.len) p.plan.modulus.symm
  have hc : Impl.Dsa.AArch64.ProbablePrime.candidate (8 * p.plan.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.AArch64.ProbablePrime.candidate
    rcases p.plan.width with hh | hh <;> rw [hh] <;> decide
  have h5 := hw 5 (by simp)
  exact ⟨W, V', {
    layout := L
    rep := R'
    arena := h5
    arenaWrite := by have := hs.arena.congr step.wr; rwa [show q.W 5 = p.plan.W 5 from h5] at this
    tapePtr := q.tapePtr
    tapeLength := q.tapeLength
    usedSlot := hs.usedSlot
    usedBound := hs.usedBound
    tapeSize := p.plan.prime.randMax
    tapeCover := by rw [step.rd, step.wr]; exact hs.tapeCover
    tapeBytes := bytes_of_src (source_of_frame hs.tape ff p.plan.tapeHash p.plan.prime.randMax step.rd step.wr)
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem
        (p.plan.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q) p.plan.prime.len) = p.plan.prime.N
      rw [p.plan.outputPtr, bt, VG.Proof.Dsa.decodeBE_os2ip]
      exact p.plan.encoding
    odd := by
      change p.plan.prime.N % 2 = 1
      rw [p.plan.modulus]
      exact (VG.Proof.Dsa.Generation.qCandidate_shape
        (show 2 ≤ 8 * p.plan.prime.len by rcases p.plan.width with hh | hh <;> omega_using [hh]) p.plan.seed).1
    bitLen := p.plan.bits }⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Public seed-attempt inputs exclude unused frame words -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SubgroupCT.lean`, which only this module imported.
section

/-! # Constant time of subgroup hashing, shaping and native primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

def SubgroupSized (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  SubgroupBefore p s ∧ p.plan.prime.len = len

def SubgroupCall (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  PrimeTestBefore (8 * p.plan.prime.len) p.primeCall s ∧ p.plan.prime.len = len

theorem subgroupCandidate_ct (H : GenerationHashes) (len : Nat) :
    RelCT isa (Two (SubgroupSized len)) (qCandidate H.sha1 H.sha256) (Two (SubgroupCall len)) := by
  refine two_post (two_map SubgroupPublic.hash (fun _ _ h => subgroup_hash h.1)
    (qCandidate_ct H)) ?_
  intro p s h
  exact WP.mono (subgroup_candidate_ready H h.1) fun _ ht => ⟨ht, h.2⟩

theorem subgroup_ct (H : GenerationHashes) (T : PrimeTest)
    (len : Nat) (hlen : len = 20 ∨ len = 32) :
    RelCT isa (Two (SubgroupSized len)) (subgroup H.sha1 H.sha256 T.run len)
      (fun _ _ => True) := by
  unfold subgroup
  refine RelCT.seq (subgroupCandidate_ct H len) ?_
  refine (primeCall_ct T (bits := 8 * len) ?_).mono (fun s t ⟨p, ⟨hs, hl⟩, ⟨ht, _⟩, hsp⟩ => ?_) fun _ _ h => h
  · rcases hlen with rfl | rfl <;> unfold ProbablePrime.Supported <;> decide
  · subst hl
    exact ⟨p.primeCall, hs, ht, hsp⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SeedPublic where
  context : GenerationContext
  seed : GenerationTape context.geo
  length : seed.bytes.length = context.geo.qLen
  used : Nat
  seedCursor : BitVec 64
  bound : used ≤ context.rand.bytes.length

def SeedPublic.subgroup (p : SeedPublic) : SubgroupPublic where
  plan := p.context.geo.subgroupPlan p.context.rand p.seed p.length
    (upd p.context.saved 0 (VG.Proof.Bignum.off p.context.geo.B q))
    (by simpa [upd] using p.context.baseSlot) (by simp [upd])
    (by simpa [upd] using p.context.randSlot) (by simpa [upd] using p.context.randLengthSlot)
  used := p.used
def SeedBefore (qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 1 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ p.context.geo.qLen = qLen

def SeedPrepared (qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 0 = VG.Proof.Bignum.off p.context.geo.B q ∧
    W 25 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ p.context.geo.qLen = qLen

theorem seedPrepared_subgroup {qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrepared qLen p s) : SubgroupSized qLen p.subgroup s := by
  obtain ⟨⟨W, hm, h0, h25, h16, _⟩, seed, he⟩ := h
  have matchWords : ∀ i ∈ [0, 5, 14, 15], W i = p.subgroup.plan.W i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact hm.slots 5 (by simp [generationSlots])
    · exact hm.slots 14 (by simp [generationSlots])
    · exact hm.slots 15 (by simp [generationSlots])
  have state := hm.subgroupState p.seed p.length seed h0 h25 h16 p.bound
  exact ⟨⟨W, matchWords, state⟩, he⟩

theorem seedArguments_ready {qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore qLen p s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments qLen)) s (SeedPrepared qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, he⟩ := h
  have hb := (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot
  have step := prepareSeed_ok hm
  rw [he] at step
  refine WP.mono step fun t ⟨ht, ff, hk⟩ => ?_
  exact ⟨⟨seedWords W qLen, ht,
    by simp [seedWords, upd, hb], by simp [seedWords, upd, h1], by simpa [seedWords, upd] using h16, by simpa [seedWords, upd] using h10⟩,
    seed.frame ff hk.rd hk.wr, he⟩

end VG.Proof.Dsa.AArch64.Generation
