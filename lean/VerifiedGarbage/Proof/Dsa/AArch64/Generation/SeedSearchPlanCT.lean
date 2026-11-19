module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSearch
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QCandidate
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! ### `Dsa.AArch64.Generation.SeedCTState`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.PrimeCallCT`, which this module and modules that import it used -/

section

/-! # Calling the probable-prime test in constant time

The test's arguments are the generation's pointers and lengths, and its
leak, the candidate and the unread tape, is public: so is its status, which
the result then branches on. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout

/-- What two runs of a call agree on. -/
structure PrimeTestPublic (bits : Nat) where
  F : Addr
  S : Addr
  A : Addr
  rp : Addr
  rand : List Byte
  N : Nat
  used : Nat
  geometry : PrimeCallGeometry bits F S A rp rand.length

def PrimeTestBefore (bits : Nat) (a : PrimeTestPublic bits) (s : State) : Prop :=
  ∃ W V, PrimeCallInputs bits a.F a.S a.A a.rp a.rand a.N a.used W V s

theorem PrimeCallInputs.congr {bits : Nat} {F S A rp : Addr} {rand : List Byte} {N used : Nat}
    {W : Nat → BitVec 64} {V : Nat → Byte} {s t : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s)
    (hm : t.mem = s.mem) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    PrimeCallInputs bits F S A rp rand N used W V t where
  layout := h.layout.congr hsp hwr (by rw [hm])
  rep := hm ▸ h.rep
  arena := h.arena
  arenaWrite := h.arenaWrite.congr hwr
  tapePtr := h.tapePtr
  tapeLength := h.tapeLength
  usedSlot := h.usedSlot
  usedBound := h.usedBound
  tapeSize := h.tapeSize
  tapeCover := by rw [hrd, hwr]; exact h.tapeCover
  tapeBytes := by rw [hm]; exact h.tapeBytes
  candidate := by rw [hm]; exact h.candidate
  odd := h.odd
  bitLen := h.bitLen

/-- The arguments in their registers. -/
def PrimeTestReady (bits : Nat) (a : PrimeTestPublic bits) (u : State) : Prop :=
  ∃ s W V, PrimeCallInputs bits a.F a.S a.A a.rp a.rand a.N a.used W V s ∧
    u.gpr .x0 = a.A ∧ u.gpr .x1 = BitVec.ofNat 64 (domainCheck / 8) ∧
    u.gpr .x2 = a.rp + BitVec.ofNat 64 a.used ∧ u.gpr .x3 = BitVec.ofNat 64 (a.rand.length - a.used) ∧
    u.gpr .x4 = off a.F 152 ∧ u.mem = s.mem ∧ u.sp = a.F ∧ u.rd = s.rd ∧ u.wr = s.wr

/-- The test's status. -/
def PrimeTestPublic.status {bits : Nat} (a : PrimeTestPublic bits) : Nat :=
  Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime a.N (a.rand.drop a.used))

theorem PrimeTestPublic.status_lt {bits : Nat} (a : PrimeTestPublic bits) : a.status < 3 := by
  unfold PrimeTestPublic.status
  rcases Spec.Dsa.probablePrime a.N (a.rand.drop a.used) with _ | ⟨_ | _, _⟩ <;>
    simp only [Proof.Dsa.ProbablePrime.status] <;> decide

def PrimeTestDone (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.sp = a.F ∧ (t.gpr .x0).setWidth 32 = BitVec.ofNat 32 a.status

def PrimeTestStatus (bits : Nat) (a : PrimeTestPublic bits) (t : State) : Prop :=
  t.sp = a.F ∧ t.gpr .x0 = BitVec.ofNat 64 a.status

theorem primeCallArgs_ct (bits : Nat) :
    RelCT isa (Two (PrimeTestBefore bits)) (.block Impl.Dsa.AArch64.Generation.primeCallArgs)
      (Two (PrimeTestReady bits)) := by
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide) fun a s ⟨W, V, h⟩ => ?_
  exact WP.mono (primeCallArgs_ok h) fun u ⟨h0, h1, h2, h3, h4, hm, ku⟩ =>
    ⟨s, W, V, h, h0, h1, h2, h3, h4, hm, ku.sp.trans h.layout.sp, ku.rd, ku.wr⟩

theorem primeCallTest_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestReady bits)) (T.run bits) (Two (PrimeTestDone bits)) := by
  refine two_post ?_ fun a u ⟨s, W, V, h, h0, h1, h2, h3, h4, hm, hsp, hrd, hwr⟩ =>
    WP.mono (primeCall_call_ok T hb h a.geometry h0 h1 h2 h3 h4 hm hsp hrd hwr) fun t C => ⟨C.sp, C.status⟩
  refine RelCT.callExDit (T.verified bits hb).1 (T.verified bits hb).2.1 (T.noDit bits hb) (fun _ _ h => h)
    fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => ?_
  obtain ⟨_, _, _, i₁, h0₁, h1₁, h2₁, h3₁, h4₁, hm₁, hsp₁, hrd₁, hwr₁⟩ := h₁
  obtain ⟨_, _, _, i₂, h0₂, h1₂, h2₂, h3₂, h4₂, hm₂, hsp₂, hrd₂, hwr₂⟩ := h₂
  have E₁ := primeCall_entry i₁ a.geometry h0₁ h1₁ h2₁ h3₁ h4₁ hm₁ hsp₁ hrd₁ hwr₁
  have E₂ := primeCall_entry i₂ a.geometry h0₂ h1₂ h2₂ h3₂ h4₂ hm₂ hsp₂ hrd₂ hwr₂
  refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes⟩
  sig_pub [ProbablePrime.contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  have hl : (BitVec.ofNat 64 (a.rand.length - a.used)).toNat = a.rand.length - a.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i₁.tapeSize; omega_using [this])]
  rw [hsp₁, hsp₂, h0₁, h0₂, h2₁, h2₂, h3₁, h3₂, h1₁, h1₂, h4₁, h4₂, hl, E₁.candidate, E₂.candidate,
    E₁.tape, E₂.tape]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem primeCallStatus_ct (bits : Nat) :
    RelCT isa (Two (PrimeTestDone bits)) Impl.Dsa.AArch64.Generation.primeCallStatus fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.primeCallStatus
  refine RelCT.seq (two_piece (Ψ := PrimeTestStatus bits) [] (fun _ _ _ _ _ _ hr => nomatch hr)
    (by taint_decide) fun a t ⟨hsp, hx0⟩ => ?_) ?_
  · have hk := a.status_lt
    have hz : (BitVec.ofNat 32 a.status).setWidth 64 = BitVec.ofNat 64 a.status := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hk]
    have run0 : WP isa (.block [.addImm .w .x0 .x0 0]) t fun u => u.gpr .x0 = BitVec.ofNat 64 a.status := by
      brun [exec_addImm_w_zero, State.write, hx0, hz]
    exact WP.mono (WP.keep [.x0] run0 (by decide)) fun u ⟨hu, ku⟩ => ⟨ku.sp.trans hsp, hu⟩
  · exact two_taint [.x0] (fun a s₁ s₂ h₁ h₂ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact h₁.2.trans h₂.2.symm) (by taint_decide)

theorem primeCall_ct (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits) :
    RelCT isa (Two (PrimeTestBefore bits)) (Impl.Dsa.AArch64.Generation.primeCall T.run bits)
      fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.primeCall
  exact RelCT.seq (primeCallArgs_ct bits) (RelCT.seq (primeCallTest_ct T hb) (primeCallStatus_ct bits))

end VG.Proof.Dsa.AArch64.Generation

end

end

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

end

end

/-! ### `Dsa.AArch64.Generation.SearchCTState`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.AttemptBlocksCT`, which this module and modules that import it used -/

section

/-! # Public addressing on p-attempt entry and return to the search controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

structure AttemptReturnPublic where
  F : Addr
  S : Addr
  arena : Addr

def AttemptReturnBefore (p : AttemptReturnPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.arena

def AttemptReturnReady (p : AttemptReturnPublic) (s : State) : Prop :=
  s.gpr .x0 = VG.Proof.Bignum.off p.arena Impl.Dsa.Generation.Layout.control ∧ s.sp = p.F

theorem controlBase_ready {p : AttemptReturnPublic} {s : State} (h : AttemptReturnBefore p s) :
    WP isa (.block controlBase) s (AttemptReturnReady p) := by
  obtain ⟨V, W, R, hw⟩ := h.2
  exact WP.mono (controlBase_ok h.1 R (by rw [hw])) fun _ ⟨hb, _, hk⟩ =>
    ⟨hb, hk.sp.trans h.1.sp⟩

theorem controlBase_ct : RelCT isa (Two AttemptReturnBefore) (.block controlBase) (Two AttemptReturnReady) := by
  exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => controlBase_ready h)

theorem searchReturn_ct : RelCT isa (Two AttemptReturnBefore) (.block searchReturn) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := controlBase)
    (l₂ := [.ldrSp .x3 152, VG.Impl.Bignum.AArch64.sth .x3 2])
  refine RelCT.seq controlBase_ct (two_taint [.x0] ?_ (by taint_decide))
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.1.trans ht.1.symm

structure AttemptPointers where
  B : Addr
  F : Addr

def AttemptRegisters (p : AttemptPointers) (s : State) : Prop := s.gpr .x0 = p.B ∧ s.sp = p.F

theorem pAttemptArgs_ct : RelCT isa (Two AttemptRegisters) (.block pAttemptArgs) (fun _ _ => True) :=
  two_taint [.x0] (fun _ _ _ hs ht r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.trans ht.1.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PPrimalityCTState`, which this module and modules that import it used -/

section

/-! # Public p-search data and the live frame words used by primality -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def PPrimalityWords (p : PPrimalityPlan) (W : Nat → BitVec 64) : Prop :=
  (∀ i < 6, W i = p.construct.hash.W i) ∧ W 14 = p.rp ∧ W 15 = BitVec.ofNat 64 p.rand.length

def PPrimalityPlan.withWords (p : PPrimalityPlan) (W : Nat → BitVec 64)
    (hw : PPrimalityWords p W) : PPrimalityPlan :=
  { p with
    construct := p.construct.withWords W hw.1
    tapePtr := hw.2.1
    tapeLength := hw.2.2
    bufferSeparate := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.bufferSeparate
    bufferOutside := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.bufferOutside
    tapeBuffer := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.tapeBuffer
    framePrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.framePrime
    hashPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.hashPrime
    pPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.pPrime
    exponentPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.exponentPrime
    hashStack := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.hashStack
    arenaBound := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaBound
    tapeArena := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.tapeArena
    arenaFrame := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaFrame
    arenaStack := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaStack
    tapeConstruct := by
      simpa only [PConstructPlan.withWords, HashPlan.withWords, PConstructPlan.changed, HashPlan.changed,
        hw.1 5 (by decide)] using p.tapeConstruct }

structure PPrimalityPublic where
  plan : PPrimalityPlan
  used : Nat

def PPrimalityPublic.construct (p : PPrimalityPublic) : PConstructPublic := ⟨p.plan.construct⟩

def PPrimalityBefore (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PPrimalityPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : PPrimalityWords p.plan W,
    PConstructState (p.plan.construct.withWords W hw.1) H s ∧
      W 16 = BitVec.ofNat 64 p.used) ∧
    p.used ≤ p.plan.rand.length ∧
    Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand ∧
    (Scr s (p.plan.construct.hash.W 5) domainCheck ∧
      Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)) ∧
    p.plan.construct.len = pLen ∧ p.plan.construct.hash.len = qLen

theorem pPrimality_construct {pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore H pLen qLen p s) : PConstructBefore H pLen qLen p.construct s := by
  obtain ⟨W, hw, hs, _⟩ := h.1
  exact ⟨⟨W, hw.1, hs⟩, h.2.2.2.2⟩

structure PPrimalityAfter (p : PPrimalityPublic) (s : State) : Prop where
  layout : Lay s p.plan.construct.hash.F p.plan.construct.hash.S
  frame : ∃ V W, Rep s.mem p.plan.construct.hash.F p.plan.construct.hash.S V W ∧
    PPrimalityWords p.plan W ∧ W 16 = BitVec.ofNat 64 p.used
  ws : VG.Proof.Rsa.AArch64.Ws s p.plan.construct.B p.plan.construct.Z (p.plan.construct.len / 8)
  pointer : VG.Proof.Bignum.word s.mem p.plan.construct.B 160 = VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len =
    Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value
  odd : p.plan.construct.value % 2 = 1
  fits : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)
  source : Src s p.plan.construct.B p.plan.construct.Z
    (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
    (Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value)
  tape : Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand
  arena : Scr s (p.plan.construct.hash.W 5) domainCheck
  tapeCover : Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)
  usedBound : p.used ≤ p.plan.rand.length

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The p-search counter and entropy cursor determine each public attempt -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SearchPublic where
  plan : SearchPlan
  counter : Nat
  used : Nat
  bound : counter < 32 * plan.attempt.construct.len

def SearchPublic.offset (p : SearchPublic) : Nat :=
  1 + p.counter * (p.plan.attempt.construct.hash.count + 1)

theorem SearchPublic.carry (p : SearchPublic) : p.offset + p.plan.attempt.construct.hash.count < 2 ^ 32 := by
  have hc : p.counter < 12288 := by
    rcases p.plan.attempt.construct.width with h | h | h <;> omega_using [p.bound, h]
  have hm := Nat.mul_le_mul_left p.counter (show p.plan.attempt.construct.hash.count + 1 ≤ 12 by
    have := p.plan.attempt.construct.hash.count_le; omega_using [this])
  dsimp only [SearchPublic.offset]
  omega_using [p.plan.attempt.construct.hash.count_le, hc, hm]

def SearchPublic.attemptPlan (p : SearchPublic) : PPrimalityPlan :=
  p.plan.attempt.reframe (attemptWords p.plan.attempt.construct.hash.W p.offset) p.offset
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (by simp [attemptWords, VG.Proof.RsaOaep.AArch64.upd])
    (by simp [attemptWords, VG.Proof.RsaOaep.AArch64.upd]) p.carry

def SearchPublic.attempt (p : SearchPublic) : PPrimalityPublic where
  plan := p.attemptPlan
  used := p.used
def SearchBefore (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  (∃ W, SearchMemory p.plan W s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    SearchControl p.plan.C p.counter (p.plan.attempt.construct.hash.count + 1) s ∧
    p.used ≤ p.plan.attempt.rand.length ∧ p.plan.attempt.construct.len = pLen ∧
    p.plan.attempt.construct.hash.len = qLen

def SearchPublic.pointers (p : SearchPublic) : AttemptPointers :=
  ⟨p.plan.C, p.plan.attempt.construct.hash.F⟩

theorem searchBefore_pointers {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBefore pLen qLen p s) : AttemptRegisters p.pointers s := by
  obtain ⟨W, hs, _⟩ := h.1
  exact ⟨h.2.1.x0, hs.layout.sp⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Public seed inputs instantiate the bounded prime-search plan -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def SeedPublic.words (p : SeedPublic) : Nat → BitVec 64 :=
  upd (upd p.context.saved 1 p.seed.ptr) 10 p.seedCursor

def SeedPublic.searchPlan (p : SeedPublic) : SearchPlan :=
  p.context.geo.searchPlan p.seed p.context.rand p.length (searchWords p.context.geo.B p.words) 0
    (by have := p.context.geo.hashSizes.1; omega_using [this])
    (by simp [searchWords, words, upd])
    (by simpa [searchWords, words, upd] using p.context.wrappedSlot)
    (by simpa [searchWords, words, upd] using p.context.hashesSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, words, upd] using p.context.baseSlot)
    (by simp [searchWords, upd])
    (by simpa [searchWords, words, upd] using p.context.randSlot)
    (by simpa [searchWords, words, upd] using p.context.randLengthSlot)

def SeedPublic.search (p : SeedPublic) : SearchPublic where
  plan := p.searchPlan
  counter := 0
  used := p.used
  bound := by
    change 0 < 32 * p.context.geo.pLen
    rcases p.context.geo.width with h | h | h <;> omega_using [h]

def SeedPrimeBefore (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore qLen p s ∧ p.context.geo.pLen = pLen ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.context.geo.B q) p.context.geo.qLen =
    Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)

theorem seedPrime_words {p : SeedPublic} {s : State}
    {W : Nat → BitVec 64} (h : GenerationMemory p.context W s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor) :
    ∀ k ∈ searchSlots, W k = p.searchPlan.attempt.construct.hash.W k := by
  intro k hk
  change W k = searchWords p.context.geo.B p.words k
  by_cases hk1 : k = 1
  · subst k; simpa [searchWords, SeedPublic.words, upd] using h1
  by_cases hk10 : k = 10
  · subst k; simpa [searchWords, SeedPublic.words, upd] using h10
  have member : k ∈ generationSlots := by
    simp only [searchSlots, generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega_using [hk1, hk10, hk]
  have neq : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 25 := by
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    omega_using [hk]
  simpa [searchWords, SeedPublic.words, upd, hk1, hk10, neq.1, neq.2.1, neq.2.2] using h.slots k member

end VG.Proof.Dsa.AArch64.Generation
