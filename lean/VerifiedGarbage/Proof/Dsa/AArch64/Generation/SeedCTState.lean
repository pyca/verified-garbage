module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT

/-! ### `Dsa.AArch64.Generation.QBuildCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.HashCT`, which only this module used -/

section

/-! # Seed hashing's trace depends only on its public location and width -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem seedHash_ct {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    {F S rp : Addr} {len : Nat} (hlen : len < 2 ^ 64) :
    RelCT isa (LR F S (fun W s => LabAt s F S W rp len))
      (Impl.Dsa.AArch64.Generation.seedHash G1 G256) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.seedHash
  refine (lr_wp (X' := fun W s => LabAt s F S W rp len ∧ s.gpr .x0 = BitVec.ofNat 64 len - 20)
    (lr_taint [] (by taint_decide) nopin) ?_).seq ?_
  · intro s V W L R A
    exact WP.mono (hashTest_ok L R A.hll) fun t ⟨hx, hm, hk⟩ =>
      ⟨V, W, L.congr hk.sp hk.wr (by rw [hm]), hm ▸ R,
        A.congr hk.rd hk.wr rfl rfl, hx⟩
  · refine RelCT.ite ?_ ?_ ?_
    · intro a b h
      obtain ⟨⟨_, _, _, _, _, ha⟩, ⟨_, _, _, _, _, hb⟩⟩ := h
      simp only [eval, State.read, ha, hb]
    · apply (hashLabel_tr h1 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial
    · apply (hashLabel_tr h256 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Subgroup hashing and byte shaping have public traces. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

structure QHashPlan where
  F : Addr
  S : Addr
  label : Addr
  len : Nat
  output : Addr
  width : len = 20 ∨ len = 32

structure QHashState (p : QHashPlan) (s : State) : Prop where
  layout : Lay s p.F p.S
  rep : ∃ V W, Rep s.mem p.F p.S V W ∧ LabAt s p.F p.S W p.label p.len ∧ W 0 = p.output

theorem qHash_ct (H : GenerationHashes) : RelCT isa (Two QHashState)
    (Impl.Dsa.AArch64.Generation.seedHash H.sha1 H.sha256) (Two QHashState) := by
  refine two_post ?_ ?_
  · intro s t tr1 tr2 u v hp e1 e2
    obtain ⟨p, hs, ht, _⟩ := hp
    obtain ⟨Vs, Ws, Rs, As, _⟩ := hs.rep
    obtain ⟨Vt, Wt, Rt, At, _⟩ := ht.rep
    exact seedHash_ct H.h1 H.h256 (by rcases p.width with h | h <;> omega_using [h]) s t tr1 tr2 u v
      ⟨⟨Vs, Ws, hs.layout, Rs, As⟩, ⟨Vt, Wt, ht.layout, Rt, At⟩⟩ e1 e2
  · intro p s h
    obtain ⟨V, W, R, A, hop⟩ := h.rep
    exact WP.mono (seedHash_frame_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
      H.width1 H.width256 p.width h.layout R A)
      fun t ⟨Lt, step, _, V', Rt, _, _⟩ => ⟨Lt, V', W, Rt, A.congr step.rd step.wr rfl rfl, hop⟩

def QShapeState (p : QHashPlan) (s : State) : Prop :=
  s.gpr .x2 = p.output ∧ s.gpr .x12 = VG.Proof.Bignum.off p.S oDig ∧ s.gpr .x9 = BitVec.ofNat 64 p.len

theorem qArgs_ct : RelCT isa (Two QHashState) (.block Impl.Dsa.AArch64.Generation.qArgs) (Two QShapeState) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_
  intro p s h
  obtain ⟨V, W, R, A, hop⟩ := h.rep
  exact WP.mono (qArgs_ok h.layout R hop A.hll) fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem qCandidate_ct (H : GenerationHashes) : RelCT isa (Two QHashState)
    (Impl.Dsa.AArch64.Generation.qCandidate H.sha1 H.sha256) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.qCandidate
  refine RelCT.seq (qHash_ct H) (RelCT.seq qArgs_ct (qShape_ct ?_))
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Dsa.AArch64.Generation

end

end

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
