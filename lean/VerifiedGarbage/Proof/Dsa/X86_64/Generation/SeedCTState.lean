module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash

/-! ### `Dsa.X86_64.Generation.QBuildCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.HashCT`, which only this module used -/

section

/-! # Seed-hash selection and streaming calls have public traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem seedHashAt_ct {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) :
    RelCT isa (Two (LW n)) (Impl.Dsa.X86_64.Generation.seedHashAt G1 G256 len)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.seedHashAt
  split
  · exact hashLabel_ct h1 n hn (Or.inl rfl)
  · exact hashLabel_ct h256 n hn (Or.inl rfl)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Subgroup-candidate hashing and shaping have public traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure QHashPlan where
  hash : LQ
  output : Addr
  width : hash.labLen = 20 ∨ hash.labLen = 32

structure QHashState (n : Nat) (p : QHashPlan) (s : State) : Prop where
  frame : FrV n p.hash.F p.hash.ws s
  layout : Lay s p.hash.F p.hash.S
  rep : ∃ V W, Rep s.mem p.hash.F p.hash.S V W ∧
    LabAt s p.hash.F p.hash.S W p.hash.lab p.hash.labLen ∧ W 0 = p.output

theorem QHashState.label {n : Nat} {p : QHashPlan} {s : State} (h : QHashState n p s) : LW n p.hash s := by
  obtain ⟨V, W, R, A, _⟩ := h.rep
  exact ⟨h.frame, h.layout, V, W, R, A⟩

theorem qHash_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) :
    RelCT isa (Two (QHashState n)) (Impl.Dsa.X86_64.Generation.seedHashAt H.sha1 H.sha256 len)
      (Two (QHashState n)) := by
  refine two_post (two_map QHashPlan.hash (fun _ _ h => h.label) (seedHashAt_ct H.h1 H.h256 n hn len)) ?_
  intro p s h
  obtain ⟨V, W, R, A, hop⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.seedHashAt
  split
  · exact WP.mono (hash_bytes_frame H.h1 H.hash1 H.size1 h.layout R A)
      fun t ⟨L, rd, wr, _, _, V', R', _, _⟩ =>
        ⟨h.frame.congr (L.rsp.trans h.layout.rsp.symm) wr, L,
          V', W, R', A.congr rd wr rfl rfl, hop⟩
  · exact WP.mono (hash_bytes_frame H.h256 H.hash256 H.size256 h.layout R A)
      fun t ⟨L, rd, wr, _, _, V', R', _, _⟩ =>
        ⟨h.frame.congr (L.rsp.trans h.layout.rsp.symm) wr, L,
          V', W, R', A.congr rd wr rfl rfl, hop⟩

def QShapeState (p : QHashPlan) (s : State) : Prop :=
  s.gpr .rdi = p.output ∧ s.gpr .rsi = off p.hash.S oDig ∧
    s.gpr .rcx = BitVec.ofNat 64 p.hash.labLen ∧
    s.gpr .rdx = BitVec.ofNat 64 (8 * p.hash.labLen)

theorem qArgs_ct (n : Nat) :
    RelCT isa (Two (QHashState n)) (.block Impl.Dsa.X86_64.Generation.qArgs) (Two QShapeState) := by
  refine two_post (two_taint [.rsp] ?_ (by taint_decide)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    obtain ⟨V, W, R, A, hop⟩ := h.rep
    exact WP.mono (qArgs_ok h.layout R hop A.hll) fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩

theorem qCandidate_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) :
    RelCT isa (Two (QHashState n)) (Impl.Dsa.X86_64.Generation.qCandidate H.sha1 H.sha256 len)
      (fun _ _ => True) := by
  refine RelCT.seq (qHash_ct H n hn len) (RelCT.seq (qArgs_ct n) ?_)
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.SubgroupCTState`, which only this module used -/

section

/-! # Public subgroup-generation data excludes unused frame contents -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

structure SubgroupPublic where
  plan : SubgroupPlan
  used : Nat
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout (plan.W 5) wr

def SubgroupPlan.withWords (p : SubgroupPlan) (W : Nat → BitVec 64)
    (hw : ∀ i ∈ [0, 5, 13, 15], W i = p.W i) : SubgroupPlan :=
  { p with W := W
           base := by rw [hw 5 (by simp)]; exact p.base
           outputPtr := by rw [hw 5 (by simp)]; exact p.outputPtr
           outputSlot := (hw 0 (by simp)).trans p.outputSlot
           witnessPtr := by rw [hw 5 (by simp)]; exact p.witnessPtr
           tapePtr := (hw 13 (by simp)).trans p.tapePtr
           tapeLength := (hw 15 (by simp)).trans p.tapeLength
           geometry := by rw [hw 5 (by simp)]; exact p.geometry }

def SubgroupBefore (n : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i ∈ [0, 5, 13, 15], W i = p.plan.W i,
    SubgroupState (p.plan.withWords W hw) p.used s ∧
      FrV n p.plan.prime.sp p.ws s ∧ s.wr = p.wr

def SubgroupPublic.hash (p : SubgroupPublic) : QHashPlan :=
  ⟨⟨p.plan.prime.sp, p.plan.hash, p.ws, p.plan.seedPtr, p.plan.prime.len⟩,
    p.plan.output, p.plan.width⟩

theorem subgroup_hash {n : Nat} {p : SubgroupPublic} {s : State}
    (h : SubgroupBefore n p s) : QHashState n p.hash s := by
  obtain ⟨W, hw, hs, hf, _⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact ⟨hf, hs.layout, V, W, R, hs.label, (p.plan.withWords W hw).outputSlot⟩

def SubgroupPublic.primeCall (p : SubgroupPublic) : PrimeTestPublic (8 * p.plan.prime.len) where
  F := p.plan.prime.sp
  S := p.plan.hash
  A := p.plan.W 5
  rp := p.plan.prime.rp
  rand := p.plan.prime.rand
  N := p.plan.prime.N
  used := p.used
  geometry := p.plan.geometry

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public seed-attempt inputs exclude unused frame words -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SubgroupReadyCT.lean`, which only this module imported.
section

/-! # Hash and shape the subgroup candidate before the native primality call -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem subgroup_candidate_ready (H : GenerationHashes) {n : Nat}
    {p : SubgroupPublic} {s : State} (h : SubgroupBefore n p s) :
    WP isa (qCandidate H.sha1 H.sha256 p.plan.prime.len) s fun t =>
      PrimeTestBefore (8 * p.plan.prime.len) p.primeCall t := by
  obtain ⟨W, hw, hs, _, hwr⟩ := h
  let q := p.plan.withWords W hw
  have plen : p.plan.prime.len ≤ 32 := by rcases p.plan.width with h | h <;> omega
  obtain ⟨V, R⟩ := hs.rep
  have candidate := qCandidate_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
    H.width1 H.width256 p.plan.width hs.layout R hs.label q.outputSlot hs.outputWrite
    (fun i hi j hj => ?_) p.plan.outputHash
  case refine_1 =>
    have he := p.plan.outputHash.scratch j hj (oDig + i) (by unfold oDig oRsa; omega)
    simpa only [off_off, SubgroupPlan.withWords, q] using Ne.symm he
  dsimp only [q, SubgroupPlan.withWords] at candidate
  refine WP.mono candidate fun t ⟨tq, rd, wr, _, ff, L, V', R'⟩ => ?_
  have bt : Spec.Rsa.bytesAt t.mem p.plan.output p.plan.prime.len =
      Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N := by
    have se : Spec.Rsa.bytesAt s.mem p.plan.seedPtr p.plan.prime.len = p.plan.seed := hs.seed
    rw [tq, se]
    exact congrArg (Spec.Dsa.encodeBE p.plan.prime.len) p.plan.modulus.symm
  have hc : Impl.Dsa.X86_64.ProbablePrime.candidate (8 * p.plan.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.X86_64.ProbablePrime.candidate
    rcases p.plan.width with hh | hh <;> rw [hh] <;> decide
  have h5 := hw 5 (by simp)
  exact ⟨W, V', {
    layout := L
    rep := R'
    arena := h5
    arenaWrite := by have := hs.arena.congr wr; rwa [show q.W 5 = p.plan.W 5 from h5] at this
    tapePtr := q.tapePtr
    tapeLength := q.tapeLength
    usedSlot := hs.usedSlot
    usedBound := hs.usedBound
    tapeSize := p.plan.prime.randMax
    tapeCover := by rw [rd, wr]; exact hs.tapeCover
    tapeBytes := bytes_of_src (source_of_frame hs.tape ff p.plan.tapeHash p.plan.prime.randMax rd wr)
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
        (show 2 ≤ 8 * p.plan.prime.len by rcases p.plan.width with hh | hh <;> omega) p.plan.seed).1
    bitLen := p.plan.bits }⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SubgroupCT.lean`, which only this module imported.
section

/-! # Constant time of subgroup hashing, shaping and native primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.X86_64.Generation

def SubgroupSized (n len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  SubgroupBefore n p s ∧ p.plan.prime.len = len

def SubgroupCall (len : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  PrimeTestBefore (8 * p.plan.prime.len) p.primeCall s ∧ p.plan.prime.len = len

theorem subgroupCandidate_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) :
    RelCT isa (Two (SubgroupSized n len)) (qCandidate H.sha1 H.sha256 len) (Two (SubgroupCall len)) := by
  refine two_post (two_map SubgroupPublic.hash (fun _ _ h => subgroup_hash h.1)
    (qCandidate_ct H n hn len)) ?_
  intro p s ⟨h, hl⟩
  subst hl
  exact WP.mono (subgroup_candidate_ready H h) fun _ ht => ⟨ht, rfl⟩

theorem subgroup_ct (H : GenerationHashes) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (len : Nat) (hlen : len = 20 ∨ len = 32) :
    RelCT isa (Two (SubgroupSized n len)) (subgroup H.sha1 H.sha256 T.run len)
      (fun _ _ => True) := by
  unfold subgroup
  refine RelCT.seq (subgroupCandidate_ct H n hn len) ?_
  refine (primeCall_ct T (bits := 8 * len) ?_).mono (fun s t ⟨p, ⟨hs, hl⟩, ⟨ht, _⟩⟩ => ?_) fun _ _ h => h
  · rcases hlen with rfl | rfl <;> unfold ProbablePrime.Supported <;> decide
  · subst hl
    exact ⟨p.primeCall, hs, ht⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure SeedPublic where
  context : GenerationContext
  seed : GenerationTape context.geo
  length : seed.bytes.length = context.geo.qLen
  used : Nat
  seedCursor : BitVec 64
  bound : used ≤ context.rand.bytes.length
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout context.geo.B wr

def SeedPublic.subgroup (p : SeedPublic) : SubgroupPublic where
  plan := p.context.geo.subgroupPlan p.context.rand p.seed p.length
    (upd p.context.saved 0 (off p.context.geo.B q))
    (by simpa [upd] using p.context.baseSlot) (by simp [upd])
    (by simpa [upd] using p.context.randSlot) (by simpa [upd] using p.context.randLengthSlot)
  used := p.used
  ws := p.ws
  wr := p.wr
  header := by
    change PrimeHeaderLayout (p.context.saved 5) p.wr
    rw [p.context.baseSlot]
    exact p.header

def SeedBefore (n qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 1 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.qLen = qLen

def SeedPrepared (n qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 0 = off p.context.geo.B q ∧
    W 27 = p.seed.ptr ∧ W 16 = BitVec.ofNat 64 p.used ∧ W 10 = p.seedCursor) ∧
  GenerationTapeMemory p.seed s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.qLen = qLen

theorem seedPrepared_subgroup {n qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrepared n qLen p s) : SubgroupSized n qLen p.subgroup s := by
  obtain ⟨⟨W, hm, h0, h27, h16, _⟩, seed, hf, hw, he⟩ := h
  have matchWords : ∀ i ∈ [0, 5, 13, 15], W i = p.subgroup.plan.W i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact hm.slots 5 (by simp [generationSlots])
    · exact hm.slots 13 (by simp [generationSlots])
    · exact hm.slots 15 (by simp [generationSlots])
  have state := hm.subgroupState p.seed p.length seed h0 h27 h16 p.bound
  exact ⟨⟨W, matchWords, state, hf, hw⟩, he⟩

theorem seedArguments_ready {n qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore n qLen p s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments qLen)) s (SeedPrepared n qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, he⟩ := h
  have hb := (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot
  have step := prepareSeed_ok hm
  rw [he] at step
  refine WP.mono step fun t ⟨ht, ff, hk⟩ => ?_
  exact ⟨⟨seedWords W qLen, ht,
    by simp [seedWords, upd, hb], by simp [seedWords, upd, h1], by simpa [seedWords, upd] using h16, by simpa [seedWords, upd] using h10⟩,
    seed.frame ff hk.2.1 hk.2.2, hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, he⟩

end VG.Proof.Dsa.X86_64.Generation
