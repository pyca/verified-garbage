module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of one seed of the refillable-tape search on AArch64

The seed's subgroup and prime search are the finite search's
(`SeedSubgroupCT.lean`, `SeedPrimeCT.lean`). After `p`, the generator stage
reads its `h` candidates from the window of `rand` after the octets
consumed, a function of public data (`StagePublic`); the stage's leak is
public as for the finite search, and its result, which the seed's status
branches on, a function of its public inputs. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

/-! ## The generator stage -/

/-- The generator stage's public inputs: its context, whose `h` tape is the
window, `p`, `q` and the octets of `rand` consumed before it. -/
structure StagePublic where
  ctx : GenerationContext
  value : Nat
  qval : Nat
  used : Nat
  domain : VG.Proof.Dsa.Generation.PDomain ctx.geo.pLen value
  qfit : qval < 256 ^ ctx.geo.qLen
  qpos : 0 < qval
  short : ctx.hs.bytes.length ≤ 128 * ctx.geo.pLen

def StagePublic.cands (a : StagePublic) : List Nat :=
  (Spec.Dsa.generationChunks a.ctx.geo.pLen a.ctx.hs.bytes).map Spec.Dsa.decodeBE

def StagePublic.code (a : StagePublic) : Nat := Proof.Dsa.GeneratorStage.code a.value a.qval a.cands

def StagePublic.count (a : StagePublic) : Nat :=
  a.ctx.geo.pLen * VG.Proof.Dsa.Generation.generatorCount a.value a.qval a.cands

theorem StagePublic.count_lt (a : StagePublic) : a.count < 2 ^ 32 := by
  have pn : a.ctx.geo.pLen ≤ 384 := by rcases a.ctx.geo.width with hh | hh | hh <;> omega
  have hc : VG.Proof.Dsa.Generation.generatorCount a.value a.qval a.cands ≤ a.ctx.hs.bytes.length / a.ctx.geo.pLen := by
    refine Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _) (Nat.le_of_eq ?_)
    simp only [StagePublic.cands, Spec.Dsa.generationChunks, List.length_map, List.length_range]
  have hm := Nat.mul_le_mul_left a.ctx.geo.pLen hc
  have hd : a.ctx.geo.pLen * (a.ctx.hs.bytes.length / a.ctx.geo.pLen) ≤ a.ctx.hs.bytes.length := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have := a.short
  unfold StagePublic.count
  omega

/-- The stage's inputs in memory. -/
def StageInputs (a : StagePublic) (s : State) : Prop :=
  ∃ W, GenerationMemory a.ctx W s ∧ W 16 = BitVec.ofNat 64 a.used ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B VG.Impl.Dsa.Generation.Layout.p) a.ctx.geo.pLen =
      Spec.Dsa.encodeBE a.ctx.geo.pLen a.value ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B exponent) a.ctx.geo.pLen =
      Spec.Dsa.encodeBE a.ctx.geo.pLen ((a.value - 1) / a.qval) ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B q) a.ctx.geo.qLen = Spec.Dsa.encodeBE a.ctx.geo.qLen a.qval

def StageBefore (pLen : Nat) (a : StagePublic) (s : State) : Prop :=
  a.ctx.geo.pLen = pLen ∧ StageInputs a s

/-- The stage's arguments in their registers. -/
def StageArgs (pLen : Nat) (a : StagePublic) (u : State) : Prop :=
  a.ctx.geo.pLen = pLen ∧ ∃ s, StageInputs a s ∧ u.gpr .x0 = a.ctx.geo.B ∧
    u.gpr .x1 = BitVec.ofNat 64 (usedBytes a.ctx.geo.pLen / 8) ∧
    u.gpr .x2 = a.ctx.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 a.ctx.hs.bytes.length ∧
    u.mem = s.mem ∧ u.sp = a.ctx.geo.F ∧ u.rd = s.rd ∧ u.wr = s.wr

/-- After the stage: its result in `x0`. -/
def StageCalled (a : StagePublic) (t : State) : Prop :=
  ∃ V W, Lay t a.ctx.geo.F a.ctx.geo.hash ∧ Rep t.mem a.ctx.geo.F a.ctx.geo.hash V W ∧
    W 16 = BitVec.ofNat 64 a.used ∧ W 13 = BitVec.ofNat 64 a.ctx.hs.bytes.length ∧
    t.gpr .x0 = BitVec.ofNat 64 (a.code + 4 * a.count)

theorem stageArgs_ct (pLen : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) hc).isSome = true) :
    RelCT isa (Two (StageBefore pLen)) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen))
      (Two (StageArgs pLen)) := by
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) ht fun a s ⟨hp, W, hm, h16, bp, be, bq⟩ => ?_
  subst hp
  exact WP.mono (generatorCallArgs_ok hm) fun u ⟨h0, h1, h2, h3, hmem, ku⟩ =>
    ⟨rfl, s, ⟨W, hm, h16, bp, be, bq⟩, h0, h1, h2, h3, hmem, ku.sp.trans hm.layout.sp, ku.rd, ku.wr⟩

theorem stageCall_ct (G : GeneratorStage) (pLen : Nat) (hb : Generator.Supported pLen) :
    RelCT isa (Two (StageArgs pLen)) (G.run pLen) (Two StageCalled) := by
  refine two_post ?_ fun a u h => ?_
  · refine RelCT.callEx (G.verified pLen hb).1 (G.verified pLen hb).2.1 fun u₁ u₂ ⟨a, h₁, h₂, _⟩ => ?_
    obtain ⟨hp, s₁, ⟨W₁, m₁, _, bp₁, be₁, bq₁⟩, h0₁, h1₁, h2₁, h3₁, hm₁, hsp₁, hr₁, hw₁⟩ := h₁
    obtain ⟨_, s₂, ⟨W₂, m₂, _, bp₂, be₂, bq₂⟩, h0₂, h1₂, h2₂, h3₂, hm₂, hsp₂, hr₂, hw₂⟩ := h₂
    have E₁ := generatorCall_entry m₁ a.value a.qval a.domain a.qfit a.qpos bp₁ be₁ bq₁ h0₁ h1₁ h2₁ h3₁ hm₁ hsp₁
      hr₁ hw₁
    have E₂ := generatorCall_entry m₂ a.value a.qval a.domain a.qfit a.qpos bp₂ be₂ bq₂ h0₂ h1₂ h2₂ h3₂ hm₂ hsp₂
      hr₂ hw₂
    subst hp
    refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes⟩
    sig_pub [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    rw [hsp₁, hsp₂, h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂]
    have hl : (BitVec.ofNat 64 a.ctx.hs.bytes.length).toNat = a.ctx.hs.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.ctx.hs.size]
    rw [hl, E₁.pv, E₂.pv, E₁.qv, E₂.qv, E₁.tape, E₂.tape]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hp, s, ⟨W, hm, h16, bp, be, bq⟩, h0, h1, h2, h3, hmem, hsp, hrd, hwr⟩ := h
    subst hp
    refine WP.mono (generatorCall_call_ok G hm a.value a.qval a.domain a.qfit a.qpos bp be bq h0 h1 h2 h3 hmem hsp
      hrd hwr) fun t C => ?_
    obtain ⟨V, Lt, Rt, -, -, -⟩ := generatorCalled_memory hm C hwr hrd
    exact ⟨V, W, Lt, Rt, h16, (hm.slots 13 (by decide)).trans a.ctx.hLengthSlot, C.status⟩

theorem stageStatus_ct (pLen : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) hc₁).isSome =
      true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) hc₂).isSome = true) :
    RelCT isa (Two StageCalled) (Impl.Dsa.AArch64.Generation.Refill.stageStatus pLen) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.stageStatus
  refine RelCT.seq (two_piece (Ψ := fun a t => t.gpr .x4 = BitVec.ofNat 64 a.code - 3) [.x0] ?_ (by taint_decide)
    ?_) (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₁)
      (two_taint [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₂))
  · intro a s t ⟨_, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.trans ht.symm
  · intro a s ⟨V, W, L, R, h16, _, hx⟩
    have hc : a.code < 4 := by
      rcases stage_code_cases a.value a.qval a.cands with h | h | h <;> simp only [StagePublic.code, h] <;> decide
    exact WP.mono (consumed_run L R hc a.count_lt hx h16) fun t ⟨⟨_, _, h4⟩, _⟩ => h4
  · intro a s t hs ht
    simp only [eval, State.read, hs, ht]

/-- The window, the stage and its status. -/
theorem refillGenerator_ct_of (G : GeneratorStage) (pLen : Nat) (hb : Generator.Supported pLen)
    {hc₀ hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₀ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) hc₀).isSome = true)
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) hc₁).isSome =
      true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) hc₂).isSome =
      true)
    (ht₃ : (taint.check (Taint.ofRegs []) (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) hc₃).isSome = true)
    {α : Type} {Φ : α → State → Prop} (stage : α → StagePublic)
    (window : ∀ a s, Φ a s → WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s
      (StageBefore pLen (stage a))) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen) (fun _ _ => True) := by
  simp only [Impl.Dsa.AArch64.Generation.Refill.refillGenerator, VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_map stage (Φ' := fun b s => ∃ a, stage a = b ∧ Φ a s) (fun a s h => ⟨a, rfl, h⟩) ?_)
    (RelCT.seq (stageArgs_ct pLen ht₁) (RelCT.seq (stageCall_ct G pLen hb) (stageStatus_ct pLen ht₂ ht₃)))
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₀ fun b s ⟨a, e, h⟩ => ?_
  subst e
  exact window a s h

/-! ## The window -/

/-- The window of `rand` after the octets `p`'s search consumed. -/
def SeedGeneratorPublic.window (a : SeedGeneratorPublic) : GenerationTape a.seed.context.geo :=
  a.seed.context.rand.slice a.seed.used (min (a.seed.context.rand.bytes.length - a.seed.used) (128 * a.seed.context.geo.pLen))
    (by have := a.seed.bound; omega)

def SeedGeneratorPublic.stage (a : SeedGeneratorPublic) : StagePublic where
  ctx := a.seed.context.withHs a.window
  value := a.value
  qval := a.qValue
  used := a.seed.used
  domain := a.domain
  qfit := a.q_bounds.2
  qpos := a.q_bounds.1
  short := by
    show (a.window).bytes.length ≤ 128 * a.seed.context.geo.pLen
    rw [SeedGeneratorPublic.window, slice_length]
    omega

theorem seedGenerator_window {pLen qLen : Nat} {a : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore pLen qLen a s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s (StageBefore pLen a.stage) := by
  obtain ⟨⟨⟨⟨W, hm, _, h16, _⟩, _, _⟩, hp, bq⟩, bp, be⟩ := h
  subst hp
  have pn : a.seed.context.geo.pLen ≤ 384 := by rcases a.seed.context.geo.width with hh | hh | hh <;> omega
  have qn : a.seed.context.geo.qLen ≤ 32 := by rcases a.seed.context.geo.qWidth with hh | hh <;> omega
  have hp_b : VG.Impl.Dsa.Generation.Layout.p + a.seed.context.geo.pLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have he_b : exponent + a.seed.context.geo.pLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have hq_b : q + a.seed.context.geo.qLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  refine WP.mono (refillWindow_ok hm h16 a.seed.bound rfl) fun t ⟨mt, ft, _, _⟩ => ⟨rfl, _, mt, ?_,
    (a.seed.context.geo.frame_bytes ft hp_b).trans bp, (a.seed.context.geo.frame_bytes ft he_b).trans be,
    (a.seed.context.geo.frame_bytes ft hq_b).trans bq⟩
  show upd (upd W 11 _) 13 _ 16 = BitVec.ofNat 64 a.seed.used
  simp [upd, h16]

theorem refillGenerator_ct (G : GeneratorStage) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen) (fun _ _ => True) := by
  have hb : Generator.Supported pLen := by rcases sizes with h | h | h <;> simp [h.1, Generator.Supported]
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact refillGenerator_ct_of G _ hb (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
      SeedGeneratorPublic.stage fun _ _ h => seedGenerator_window h

/-! ## The seed -/

theorem refillPrimeFinish_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (.seq (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (Impl.Dsa.AArch64.Generation.onSuccess (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (refillGenerator_ct G pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

/-- A seed's attempt from its public inputs. -/
def RefillAttemptBefore (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore qLen p s ∧ p.context.geo.pLen = pLen

theorem refillAttempt_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (RefillAttemptBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pLen qLen)
      (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold Impl.Dsa.AArch64.Generation.Refill.refillAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2) (refillPrimeFinish_ct H G T pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
