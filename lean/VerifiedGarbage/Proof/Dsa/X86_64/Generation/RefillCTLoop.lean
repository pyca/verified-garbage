module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
meta import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import Mathlib.Tactic.Set

/-! ### `Dsa.X86_64.Generation.RefillCTSeed`, which only this module used -/

section

/-! # One seed of the refillable-tape search, with its `h` tape public

`refillAttempt_ok` (`RefillAttempt.lean`) with the `h` tape the attempt
leaves named: `refillHs`, the window after the seed's `p` search, or the
tape it had if the seed has no `p`. Its constant-time proof needs it, since
the next seed's public inputs include it. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

theorem GenerationTape.window_congr {g : GenerationGeometry} (t : GenerationTape g) {d d' n n' : Nat}
    (hd : d = d') (hn : n = n') (h : d + n ≤ t.bytes.length) (h' : d' + n' ≤ t.bytes.length) :
    t.window d n h = t.window d' n' h' := by
  subst hd; subst hn; rfl

/-- The `h` tape a seed's attempt leaves, from the seed and the witness
tape after it. -/
def refillHs (p : GenerationContext) (seed rest : List Byte) : GenerationTape p.geo :=
  match Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed) rest with
  | some (true, r) =>
    match Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen) (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed)
        seed r with
    | some (some _, r') => p.rand.window (p.rand.bytes.length - r'.length)
        (min (p.rand.bytes.length - (p.rand.bytes.length - r'.length)) (128 * p.geo.pLen)) (by omega_using [])
    | _ => p.hs
  | _ => p.hs

/-- `RefillFinished` with the `h` tape `hs`. -/
def CtFinished (p : GenerationContext) (initial : Nat → BitVec 64)
    (res : Option (Option Spec.Dsa.Params × List Byte)) (hs : GenerationTape p.geo) (s t : State) : Prop :=
  ∃ (W : Nat → BitVec 64) (used : Nat), GenerationMemory (p.withHs hs) W t ∧
    used ≤ p.rand.bytes.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (∀ k ∈ refillSlots, W k = initial k) ∧ SeedOutcome p res W used t ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CtFinished.prepend {p : GenerationContext} {Wi Wm : Nat → BitVec 64}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {hs : GenerationTape p.geo} {s u t : State}
    (h : CtFinished p Wm res hs u t) (slots : ∀ k ∈ searchSlots, Wm k = Wi k)
    (hf : Frame p.changed s.mem u.mem) (hr : u.rd = s.rd) (hw : u.wr = s.wr) :
    CtFinished p Wi res hs s t := by
  obtain ⟨W, used, mt, hu, h16, hsl, outcome, ft, rt, wt⟩ := h
  exact ⟨W, used, mt, hu, h16, fun k hk => (hsl k hk).trans (slots k (refillSlots_search hk)), outcome,
    hf.trans ft, rt.trans hr, wt.trans hw⟩

theorem CtFinished.hs {p : GenerationContext} {W : Nat → BitVec 64}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {hs hs' : GenerationTape p.geo} {s t : State}
    (h : CtFinished p W res hs s t) (e : hs = hs') : CtFinished p W res hs' s t := e ▸ h

theorem ctFinished_of {p : GenerationContext} {W Wt : Nat → BitVec 64} {used : Nat}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {hs : GenerationTape p.geo} {s t : State}
    (h : GenerationMemory p Wt t) (hhs : hs = p.hs) (hu : used ≤ p.rand.bytes.length)
    (h16 : Wt 16 = BitVec.ofNat 64 used)
    (slots : ∀ k ∈ searchSlots, Wt k = W k) (outcome : SeedOutcome p res Wt used t)
    (hf : Frame p.changed s.mem t.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    CtFinished p W res hs s t := by
  subst hhs
  exact ⟨Wt, used, h.withHs_self, hu, h16, fun k hk => slots k (refillSlots_search hk), outcome, hf, hr, hw⟩

theorem ctGeneratorFinish_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length)
    {res : Option (Option Spec.Dsa.Params × List Byte)}
    (hnone : Spec.Dsa.generator value qval (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen
        Spec.Dsa.generatorAttempts (p.rand.bytes.drop used)) = none →
      res = if Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length then
        some (none, (p.rand.bytes.drop used).drop (Spec.Dsa.generatorAttempts * p.geo.pLen)) else none)
    (hsome : ∀ gv, Spec.Dsa.generator value qval (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen
        Spec.Dsa.generatorAttempts (p.rand.bytes.drop used)) = some gv →
      res = some (if Spec.Dsa.parametersValid ⟨value, qval, gv⟩ then some ⟨value, qval, gv⟩ else none,
        (p.rand.bytes.drop used).drop (p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
          (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used))))) :
    WP isa (VG.Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.Refill.window p.geo.pLen,
      Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen,
      .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
      Impl.Dsa.X86_64.Generation.Refill.windowShort p.geo.pLen,
      Impl.Dsa.X86_64.Generation.onSuccess
        (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen)]) s
      (CtFinished p W res (p.rand.window used (min (p.rand.bytes.length - used) (128 * p.geo.pLen)) (by omega_using [hu])) s) := by
  obtain pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  obtain p0 : 0 < p.geo.pLen := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  obtain qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  obtain pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  obtain hp_b : VG.Impl.Dsa.Generation.Layout.p + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  obtain he_b : exponent + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  obtain hq_b : q + p.geo.qLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [qn])
  obtain hg_b : g + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  set n := min (p.rand.bytes.length - used) (128 * p.geo.pLen) with hn
  have rlen : (p.rand.bytes.drop used).length = p.rand.bytes.length - used := List.length_drop
  obtain hwin : used + n ≤ p.rand.bytes.length := by omega_using [hu]
  obtain hsub : Region.Sub ⟨(p.rand.window used n hwin).ptr, (p.rand.window used n hwin).bytes.length⟩
      ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
    rw [GenerationTape.window_length]
    exact Offset.sub_base p.rand.ptr hwin
  -- The window's candidates.
  obtain hlen : (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
      (p.rand.bytes.drop used)).length = n / p.geo.pLen := by
    simp only [VG.Proof.Dsa.Generation.windowCandidates, List.length_map, Spec.Dsa.generationChunks,
      List.length_range, List.length_take, rlen, Spec.Dsa.generatorAttempts]
    rw [hn, Nat.min_comm]
  unfold VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
    VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
  refine WP.seq (WP.mono (refillWindow_ok h h16 hu hn) fun u ⟨mu, fu, ru, wu⟩ => ?_)
  obtain hcand : (Spec.Dsa.generationChunks p.geo.pLen
      (p.withHs (p.rand.window used n hwin)).hs.bytes).map Spec.Dsa.decodeBE =
      VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used) := by
    show (Spec.Dsa.generationChunks p.geo.pLen ((p.rand.bytes.drop used).take n)).map Spec.Dsa.decodeBE = _
    obtain ht : (p.rand.bytes.drop used).take n =
        (p.rand.bytes.drop used).take (Spec.Dsa.generatorAttempts * p.geo.pLen) :=
      List.take_eq_take_iff.mpr (by rw [rlen]; unfold Spec.Dsa.generatorAttempts; omega_using [])
    unfold VG.Proof.Dsa.Generation.windowCandidates
    rw [ht]
  refine WP.seq (WP.mono (seedGenerator_ok M Sq mu value qval domain
      ((p.geo.frame_bytes fu hp_b).trans bp) ((p.geo.frame_bytes fu he_b).trans be)
      ((p.geo.frame_bytes fu hq_b).trans bq))
    fun v ⟨Wv, mv, slots, h20, bpv, bqv, result, fv, rv, wv⟩ => ?_)
  simp only [GenerationContext.withHs_geo, GenerationContext.withHs_changed] at h20 bpv bqv result fv
  rw [hcand] at h20 result
  generalize hhs : VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
    (p.rand.bytes.drop used) = hs at h20 result hnone hsome hlen
  obtain hc : p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤ n :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _) (Nat.le_of_eq hlen)))
      (Nat.mul_div_le n _)
  obtain v16 : Wv 16 = BitVec.ofNat 64 used := by
    rw [slots 16 (by simp [generatorSlots])]; simpa [upd] using h16
  obtain v12 : Wv 12 = BitVec.ofNat 64 n := by
    rw [slots 12 (by simp [generatorSlots])]; simp [upd]
  refine WP.seq (WP.mono (refillConsumed_ok mv) fun w ⟨mw, fw, rw', ww⟩ => ?_)
  obtain w16 : upd Wv 16 (Wv 16 + Wv 20) 16 =
      BitVec.ofNat 64 (used + p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs) := by
    simp only [upd, ite_true, v16, h20, BitVec.ofNat_add]
  obtain w12 : upd Wv 16 (Wv 16 + Wv 20) 12 = BitVec.ofNat 64 n := by simp [upd, v12]
  obtain w19 : upd Wv 16 (Wv 16 + Wv 20) 19 = Wv 19 := by simp [upd]
  obtain wslots : ∀ k ∈ refillSlots, upd Wv 16 (Wv 16 + Wv 20) k = W k := by
    intro k hk
    obtain ⟨hg, n11, n12, n16, _⟩ := refillSlots_cases hk
    simp only [upd, n16, ite_false]
    rw [slots k hg]
    simp [upd, n11, n12]
  refine WP.seq (WP.mono (refillShort_ok mw w12 (by omega_using [pn])) fun x ⟨mx, fx, rx, wx⟩ => ?_)
  obtain hbound : used + p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤
      p.rand.bytes.length := by omega_using [hu, hc]
  obtain fsx : Frame p.changed s.mem x.mem :=
    (((GenerationContext.frame_single fu).trans fv).trans (GenerationContext.frame_single fw)).trans
      (GenerationContext.frame_single fx)
  obtain rsx : x.rd = s.rd := rx.trans (rw'.trans (rv.trans ru))
  obtain wsx : x.wr = s.wr := wx.trans (ww.trans (wv.trans wu))
  obtain hdrop : ∀ k, (p.rand.bytes.drop used).drop k = p.rand.bytes.drop (used + k) := fun _ => List.drop_drop
  rw [w19] at mx
  rcases result with ⟨h19, hr⟩ | ⟨gv, h19, hr, _, upper, bgv⟩
  · have hcount := generatorCount_of_none hr
    by_cases short : n < 128 * p.geo.pLen
    · rw [ite_eq_left ⟨by rw [h19]; decide, short⟩] at mx
      apply onSuccess_generation_ok mx
      · intro _ _ _ _ hs1
        exact absurd hs1 (by simp [upd])
      · intro t mt hm kt _
        obtain hnot : ¬ (Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length) := by
          simp only [rlen, Spec.Dsa.generatorAttempts]; omega_using [short]
        refine ⟨_, _, mt, hbound, by simpa [upd] using w16, fun k hk => ?_,
          Or.inl ⟨by simp [upd], by rw [hnone hr, ite_eq_right hnot]⟩,
          by rw [hm]; exact fsx, kt.2.1.trans rsx, kt.2.2.trans wsx⟩
        simpa [upd, (refillSlots_cases hk).2.2.2.2] using wslots k hk
    · rw [ite_eq_right (fun hh => short hh.2)] at mx
      obtain hn128 : n = 128 * p.geo.pLen := by omega_using [short]
      obtain hc128 : VG.Proof.Dsa.Generation.generatorCount value qval hs = 128 := by
        rw [hcount, hlen, hn128, Nat.mul_div_cancel _ p0]
      apply onSuccess_generation_ok mx
      · intro _ _ _ _ hs1
        obtain impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs1
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        obtain hyes : Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length := by
          simp only [rlen, Spec.Dsa.generatorAttempts]; omega_using [short]
        refine ⟨_, _, mt, hbound, w16, wslots, Or.inr (Or.inl ⟨h19, ?_⟩),
          by rw [hm]; exact fsx, kt.2.1.trans rsx, kt.2.2.trans wsx⟩
        rw [hnone hr, ite_eq_left hyes, hdrop, hc128, Nat.mul_comm]
        rfl
  · rw [ite_eq_right (fun hh => hh.1 h19)] at mx
    apply onSuccess_generation_ok mx
    · intro y my hm ky _
      obtain pbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := by
        rw [hm, p.geo.frame_bytes fx hp_b, p.geo.frame_bytes fw hp_b]; exact bpv
      obtain qbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval := by
        rw [hm, p.geo.frame_bytes fx hq_b, p.geo.frame_bytes fw hq_b]; exact bqv
      obtain gbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv := by
        rw [hm, p.geo.frame_bytes fx hg_b, p.geo.frame_bytes fw hg_b]; exact bgv
      refine WP.mono (finishDomain_ok (checkName := checkName) M Sq my ⟨value, qval, gv⟩ pfit qfit
        (Nat.lt_trans upper pfit) pbytes qbytes gbytes) fun t ⟨mt, bytes, ft, rt, wt⟩ => ?_
      refine ⟨_, _, mt, hbound, by simpa [upd] using w16, fun k hk => ?_, ?_,
        (show Frame p.changed s.mem y.mem by rw [hm]; exact fsx).trans ft,
        rt.trans (ky.2.1.trans rsx), wt.trans (ky.2.2.trans wsx)⟩
      · simpa [upd, (refillSlots_cases hk).2.2.2.2] using wslots k hk
      · rw [hsome gv hr, hdrop]
        by_cases valid : Spec.Dsa.parametersValid ⟨value, qval, gv⟩
        · exact Or.inr (Or.inr ⟨by simp [upd, valid], ⟨value, qval, gv⟩, by simp only [valid, ite_true], bytes⟩)
        · exact Or.inr (Or.inl ⟨by simp [upd, valid], by simp only [valid, ite_false]⟩)
    · intro _ _ _ _ hn1
      exact False.elim (hn1 (by rw [w19]; exact h19))

/-! ## The seed -/

theorem ctPrimeFinish_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length)
    {rest : List Byte}
    (hprime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) rest =
      some (true, p.rand.bytes.drop used)) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen)
      (Impl.Dsa.X86_64.Generation.onSuccess (VG.Impl.Bignum.X86_64.seqs [
        Impl.Dsa.X86_64.Generation.Refill.window p.geo.pLen,
        Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen,
        .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
        Impl.Dsa.X86_64.Generation.Refill.windowShort p.geo.pLen,
        Impl.Dsa.X86_64.Generation.onSuccess
          (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen)]))) s
      (CtFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest)
        (refillHs p seed.bytes rest) s) := by
  obtain qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    have shape := VG.Proof.Dsa.Generation.qCandidate_shape
      (by rcases p.geo.qWidth with hh | hh <;> omega_using [hh] : 2 ≤ 8 * p.geo.qLen) seed.bytes
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  refine WP.seq (WP.mono (seedPrime_ok H T h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      obtain impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ctFinished_of mt (by simp only [refillHs, hprime, hr]) huu u16 slots (Or.inl ⟨h19, ?_⟩) (by rw [hm]; exact fu)
        (kt.2.1.trans ru) (kt.2.2.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      obtain bv : Spec.Rsa.bytesAt v.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      obtain ev : Spec.Rsa.bytesAt v.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      obtain qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      obtain call := ctGeneratorFinish_ok (checkName := checkName) M Sq mv value
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) domain qfit bv ev qv u16 huu
        (res := VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest)
        (fun hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
        (fun gv hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
      exact WP.mono call fun t ht => (ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)).hs (by
        simp only [refillHs, hprime, hr]
        exact GenerationTape.window_congr _ (by rw [List.length_drop]; omega_using [huu]) (by rw [List.length_drop]; omega_using []) _ _)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      obtain impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ctFinished_of mt (by simp only [refillHs, hprime, hr]) huu u16 slots (Or.inr (Or.inl ⟨h19, ?_⟩)) (by rw [hm]; exact fu)
        (kt.2.1.trans ru) (kt.2.2.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]

/-- One seed of the refillable-tape search, at `W 1`, with its witnesses
and its generator's candidates read from `rand` after its first `used`
octets. -/
theorem ctAttempt_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm
        T.run p.geo.pLen p.geo.qLen) s
      (CtFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes
        (p.rand.bytes.drop used)) (refillHs p seed.bytes (p.rand.bytes.drop used)) s) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.refillAttempt
  refine WP.seq (WP.mono (seedSubgroup_ok H T h seed hlen hseed h1 h16 hu)
    fun u ⟨usedu, status, huu, mu, bqu, fail, result, fu, ru, wu⟩ => ?_)
  let Wu := upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 usedu)) 19 status
  obtain u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  obtain u19 : Wu 19 = status := by simp [Wu, upd]
  obtain slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm
  obtain u1 : Wu 1 = seed.ptr := (slots 1 (by simp [searchSlots])).trans h1
  obtain seedu := hseed.frame fu ru wu
  cases qr : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used) with
  | none =>
    obtain hs : Wu 19 = 0 := u19.trans (fail qr)
    apply onSuccess_generation_ok mu
    · intro _ _ _ _ accepted
      obtain impossible : (0 : BitVec 64) = 1 := hs.symm.trans accepted
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ctFinished_of mt (by simp only [refillHs, qr]) huu u16 slots (Or.inl ⟨hs, ?_⟩) (by rw [hm]; exact fu)
        (kt.2.1.trans ru) (kt.2.2.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, qr]
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    obtain ⟨hs, cursor⟩ := result accepted rest qr
    obtain suffix : p.rand.bytes.drop usedu = rest := by
      rw [cursor]
      exact VG.Proof.Dsa.Generation.probablePrime_cursor qr
    cases accepted with
    | false =>
      obtain hstatus : Wu 19 = 3 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro _ _ _ _ accepted
        obtain impossible : (3 : BitVec 64) = 1 := hstatus.symm.trans accepted
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        refine ctFinished_of mt (by simp only [refillHs, qr]) huu u16 slots (Or.inr (Or.inl ⟨hstatus, ?_⟩)) (by rw [hm]; exact fu)
          (kt.2.1.trans ru) (kt.2.2.trans wu)
        simp only [VG.Proof.Dsa.Generation.refillAttempt, qr, suffix]
    | true =>
      obtain hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        obtain seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.2.1 kv.2.2
        obtain qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        obtain call := ctPrimeFinish_ok (checkName := checkName) H M Sq T mv seed hlen seedv u1 qv u16 huu
          (by rw [qr, suffix])
        exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.RefillCTAttempt`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.RefillCTWindow`, which only this module used -/

section

/-! # Timing of the refillable-tape search's `h` window

Before its generator search, a seed of the refillable-tape search points
its `h` tape (frame words 11 and 12) at the window of the witness tape after
its witnesses (`Refill.window`). The window's start and length are public:
the witness tape's octets consumed and its length. `SeedGeneratorPublic.windowed`
is the generator search's public input over that window. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-- The window's length from the witness tape's `u`-th octet. -/
def GenerationContext.ctWindowLen (c : GenerationContext) (u : Nat) : Nat :=
  min (c.rand.bytes.length - u) (Impl.Dsa.X86_64.Generation.Refill.windowBytes c.geo.pLen)

theorem GenerationContext.ctWindow_fit (c : GenerationContext) {u : Nat} (hu : u ≤ c.rand.bytes.length) :
    u + c.ctWindowLen u ≤ c.rand.bytes.length := by
  unfold ctWindowLen; omega_using [hu]

/-- The window from the witness tape's `u`-th octet. -/
def GenerationContext.ctWindow (c : GenerationContext) (u : Nat) (hu : u ≤ c.rand.bytes.length) :
    GenerationTape c.geo :=
  c.rand.window u (c.ctWindowLen u) (c.ctWindow_fit hu)

/-- The generator search's public input over the window after the seed's witnesses. -/
def SeedGeneratorPublic.windowed (g : SeedGeneratorPublic) : SeedGeneratorPublic where
  seed :=
    { context := g.seed.context.withHs (g.seed.context.ctWindow g.seed.used g.seed.bound)
      seed := g.seed.seed
      length := g.seed.length
      used := g.seed.used
      seedCursor := g.seed.seedCursor
      bound := g.seed.bound
      ws := g.seed.ws
      wr := g.seed.wr
      header := g.seed.header }
  value := g.value
  domain := g.domain

theorem ctFrame_bytes {g : GenerationGeometry} {m m' : Mem}
    (hf : Frame [⟨g.F, frameBytes⟩] m m') {d n : Nat} (hd : d + n ≤ usedBytes g.pLen) :
    Spec.Rsa.bytesAt m' (off g.B d) n = Spec.Rsa.bytesAt m (off g.B d) n := by
  have pn : g.pLen ≤ 384 := by rcases g.width with hh | hh | hh <;> omega_using [hh]
  apply VG.Proof.Dsa.Generation.frame_bytesAt hf
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (g.frame_part hd).symm
  · unfold usedBytes domainCheck at hd; omega_using [hd, pn]

/-- Two word stores to the frame change only the frame. -/
theorem ctFrame_two (F : Addr) {j k : Nat} (hj : j < nW) (hk : k < nW) (m : Mem) (a b : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m ((m.writeW (off F (8 * j)) a).writeW (off F (8 * k)) b) :=
  ((Frame.refl _ m).writeW (List.mem_singleton_self _) a (cF F hj)).writeW
    (List.mem_singleton_self _) b (cF F hk)

theorem ctWindowHead_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total width : Nat}
    (h13 : W 13 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hw : width < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 width))]) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used) ∧ Keep [.rax, .rcx] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax)] using hle)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax), Nat.mod_eq_of_lt (by omega_using [hmax] : total - used < 2 ^ 64)]
  have R1 := R.wf L.geo (k := 11) (by decide) (off base used)
  have r120 : (s.mem.writeW (off F 88) (off base used)).readW (off F 120) 64 = BitVec.ofNat 64 total :=
    R1.slot (d := 120) (k := 15) rfl (by decide) (by simp [upd, h15])
  have r128 : (s.mem.writeW (off F 88) (off base used)).readW (off F 128) 64 = BitVec.ofNat 64 used :=
    R1.slot (d := 128) (k := 16) rfl (by decide) (by simp [upd, h16])
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used)) (by
    xrun [ea_sp, L.rsp, L.ld (d := 104) (by decide), L.ld (d := 128) (by decide), L.st (d := 88) (by decide),
      L.ld (d := 120) (by decide),
      R.slot (d := 104) (k := 13) rfl (by decide) h13, R.slot (d := 128) (k := 16) rfl (by decide) h16,
      r120, r128, sx_ofNat hw, hsub]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hmax] : total - used < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hw] : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hr, hm⟩, hk⟩ => ⟨hc, hr, hm, hk⟩

/-- The window's two words written: the generator search's input over the window. -/
theorem seedGeneratorBefore_windowed {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen g s)
    (hm : t.mem = (s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used)).writeW
        (off g.seed.context.geo.F 96) (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used)))
    (hsp : t.gpr .rsp = s.gpr .rsp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    SeedGeneratorBefore n pLen qLen g.windowed t ∧ Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem t.mem := by
  obtain ⟨⟨⟨⟨W, hm0, h1, h16, h10⟩, seed, hf, hw, hq⟩, hp, bq⟩, bp, be⟩ := h
  obtain ⟨V, R⟩ := hm0.rep
  have L := hm0.layout
  have fr : Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem t.mem := by
    rw [hm]; exact ctFrame_two _ (j := 11) (k := 12) (by decide) (by decide) _ _ _
  have ff : Frame g.seed.context.changed s.mem t.mem := GenerationContext.frame_single fr
  have Rt : Rep t.mem g.seed.context.geo.F g.seed.context.geo.hash V
      (upd (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) 12
        (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used))) := by
    rw [hm]
    exact (R.wf L.geo (k := 11) (by decide) _).wf L.geo (k := 12) (by decide) _
  have Lt := lay_of_rep L R Rt (by simp [upd]) hsp hwr
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : g.seed.context.geo.qLen ≤ 32 := by rcases g.seed.context.geo.qWidth with hh | hh <;> omega_using [hh]
  have rt := hm0.rand.frame ff hrd hwr
  have mt : GenerationMemory g.windowed.seed.context
      (upd (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) 12
        (BitVec.ofNat 64 (g.seed.context.ctWindowLen g.seed.used))) t :=
    { layout := Lt
      rep := ⟨V, Rt⟩
      slots := by
        intro k hk
        by_cases e11 : k = 11
        · subst e11
          simp [upd, SeedGeneratorPublic.windowed, GenerationContext.withHs, GenerationContext.ctWindow,
            GenerationTape.window]
        · by_cases e12 : k = 12
          · subst e12
            simp [upd, SeedGeneratorPublic.windowed, GenerationContext.withHs, GenerationContext.ctWindow,
              GenerationTape.window_length]
          · simp only [upd, e11, e12, ite_false, SeedGeneratorPublic.windowed, GenerationContext.withHs]
            exact hm0.slots k hk
      scratch := hm0.scratch.congr hwr
      seeds := hm0.seeds.frame ff hrd hwr
      hs := rt.window (g.seed.context.ctWindow_fit g.seed.bound)
      rand := rt }
  refine ⟨⟨⟨⟨⟨_, mt, ?_, ?_, ?_⟩, seed.frame ff hrd hwr, hf.congr hsp hwr, hwr.trans hw, hq⟩, hp, ?_⟩, ?_, ?_⟩, fr⟩
  · simpa [upd, SeedGeneratorPublic.windowed] using h1
  · simpa [upd, SeedGeneratorPublic.windowed] using h16
  · simpa [upd, SeedGeneratorPublic.windowed] using h10
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B q) g.seed.context.geo.qLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [qn]))]
    exact bq
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) g.seed.context.geo.pLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn]))]
    exact bp
  · change Spec.Rsa.bytesAt t.mem (off g.seed.context.geo.B exponent) g.seed.context.geo.pLen = _
    rw [ctFrame_bytes fr (g.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn]))]
    exact be


theorem ctStoreRcx96_ok {t : State} {F S : Addr} (L : Lay t F S) :
    WP isa (.block [.store (sp 96) .rcx]) t fun u =>
      u.mem = t.mem.writeW (off F 96) (t.gpr .rcx) ∧ Keep [] t u := by
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off F 96) (t.gpr .rcx)) (by
    xrun [ea_sp, L.rsp, L.st (d := 96) (by decide)]) rfl) fun _ h => h

theorem ctStoreImm96_ok {t : State} {F S : Addr} (L : Lay t F S) {w : Nat} (hw : w < 2 ^ 32) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 w)), .store (sp 96) .rax]) t fun u =>
      u.mem = t.mem.writeW (off F 96) (BitVec.ofNat 64 w) ∧ Keep [.rax] t u := by
  have hv : (BitVec.ofNat 32 w).setWidth 64 = BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hw] : w < 4294967296)]
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off F 96) (BitVec.ofNat 64 w)) (by
    xrun [ea_sp, L.rsp, L.st (d := 96) (by decide), hv]) rfl) fun _ h => h

/-- After the window's comparison: its start written, its length in `rcx`
and compared with `windowBytes`. -/
def WindowCheckedFrom (n pLen qLen : Nat) (g : SeedGeneratorPublic) (s t : State) : Prop :=
  SeedGeneratorBefore n pLen qLen g s ∧
    t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) ∧
    t.gpr .rcx = BitVec.ofNat 64 (g.seed.context.rand.bytes.length - g.seed.used) ∧
    t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used) ∧
    Keep [.rax, .rcx] s t

def WindowChecked (n pLen qLen : Nat) (g : SeedGeneratorPublic) (t : State) : Prop :=
  ∃ s, WindowCheckedFrom n pLen qLen g s t

theorem windowBytes_lt (pLen : Nat) (hp : pLen ≤ 384) :
    Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen < 2 ^ 31 := by
  unfold Impl.Dsa.X86_64.Generation.Refill.windowBytes; omega_using [hp]

theorem windowHead_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen g s) :
    WP isa (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes
        g.seed.context.geo.pLen)))]) s (WindowCheckedFrom n pLen qLen g s) := by
  obtain ⟨⟨⟨⟨W, hm, _, h16, _⟩, _⟩, _⟩, _⟩ := id h
  obtain ⟨V, R⟩ := hm.rep
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega_using [hh]
  refine WP.mono (ctWindowHead_ok hm.layout R
    ((hm.slots 13 (by simp [generationSlots])).trans g.seed.context.randSlot) h16
    ((hm.slots 15 (by simp [generationSlots])).trans g.seed.context.randLengthSlot)
    g.seed.bound g.seed.context.rand.size (windowBytes_lt _ pn)) fun t ⟨hc, hr, hmem, hk⟩ => ?_
  exact ⟨h, hc, hr, hmem, hk⟩

theorem windowChecked_lay {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen g s)
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) : Lay t g.seed.context.geo.F g.seed.context.geo.hash := by
  obtain ⟨⟨⟨⟨W, hm0, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨V, R⟩ := hm0.rep
  have Rt : Rep t.mem g.seed.context.geo.F g.seed.context.geo.hash V
      (upd W 11 (off g.seed.context.rand.ptr g.seed.used)) := by
    rw [hm]; exact R.wf hm0.layout.geo (k := 11) (by decide) _
  exact lay_of_rep hm0.layout R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2

theorem windowTaken_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (hs : SeedGeneratorBefore n pLen qLen g s)
    (hc : t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))
    (hr : t.gpr .rcx = BitVec.ofNat 64 (g.seed.context.rand.bytes.length - g.seed.used))
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) (hb : isa.eval .b t = some true) :
    WP isa (.block [.store (sp 96) .rcx]) t fun u =>
      SeedGeneratorBefore n pLen qLen g.windowed u ∧
        Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have short : g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have e : isa.eval .b t = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
        Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) := by simp only [eval, hc]
    have := hb.symm.trans e
    simpa using this
  refine WP.mono (ctStoreRcx96_ok (windowChecked_lay hs hm hk)) fun u ⟨hu, ku⟩ => ?_
  have len : g.seed.context.ctWindowLen g.seed.used = g.seed.context.rand.bytes.length - g.seed.used := by
    unfold GenerationContext.ctWindowLen; omega_using [short]
  have hw := seedGeneratorBefore_windowed hs (t := u) (by rw [hu, hm, hr, len])
    ((ku.gpr (by decide)).trans (hk.gpr (by decide))) (ku.2.1.trans hk.2.1) (ku.2.2.trans hk.2.2)
  exact ⟨hw.1, hw.2, ku.2.1.trans hk.2.1, ku.2.2.trans hk.2.2⟩

theorem windowFull_ready {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (hs : SeedGeneratorBefore n pLen qLen g s)
    (hc : t.cf = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))
    (hm : t.mem = s.mem.writeW (off g.seed.context.geo.F 88) (off g.seed.context.rand.ptr g.seed.used))
    (hk : Keep [.rax, .rcx] s t) (hb : isa.eval .b t = some false) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes
        g.seed.context.geo.pLen))), .store (sp 96) .rax]) t fun u =>
      SeedGeneratorBefore n pLen qLen g.windowed u ∧
        Frame [⟨g.seed.context.geo.F, frameBytes⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have full : ¬ g.seed.context.rand.bytes.length - g.seed.used <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have e : isa.eval .b t = some (decide (g.seed.context.rand.bytes.length - g.seed.used <
        Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)) := by simp only [eval, hc]
    have := hb.symm.trans e
    simpa using this
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega_using [hh]
  refine WP.mono (ctStoreImm96_ok (windowChecked_lay hs hm hk)
    (by have := windowBytes_lt _ pn; omega_using [this])) fun u ⟨hu, ku⟩ => ?_
  have len : g.seed.context.ctWindowLen g.seed.used =
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    unfold GenerationContext.ctWindowLen; omega_using [full]
  have hw := seedGeneratorBefore_windowed hs (t := u) (by rw [hu, hm, len])
    ((ku.gpr (by decide)).trans (hk.gpr (by decide))) (ku.2.1.trans hk.2.1) (ku.2.2.trans hk.2.2)
  exact ⟨hw.1, hw.2, ku.2.1.trans hk.2.1, ku.2.2.trans hk.2.2⟩

theorem seedGeneratorBefore_pLen {n pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen g s) : g.seed.context.geo.pLen = pLen := h.1.2.1

theorem windowChecked_pins (n pLen qLen : Nat) : Pins (WindowChecked n pLen qLen) [.rsp] := by
  intro g s t ⟨s₀, ⟨⟨⟨⟨_, hs, _⟩, _⟩, _⟩, _⟩, _, _, _, hks⟩ ⟨t₀, ⟨⟨⟨⟨_, ht, _⟩, _⟩, _⟩, _⟩, _, _, _, hkt⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [hks.gpr (by decide), hkt.gpr (by decide)]
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem seedGeneratorBefore_pins (n pLen qLen : Nat) : Pins (SeedGeneratorBefore n pLen qLen) [.rsp] := by
  intro g s t ⟨⟨⟨⟨_, hs, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨_, ht, _⟩, _⟩, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem window_ct_of (n pLen qLen : Nat)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)),
      .store (sp 88) .rax, .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen)))]) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rsp]) (.block [.store (sp 96) .rcx]) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .rax (.imm (BitVec.ofNat 32
      (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen))), .store (sp 96) .rax]) h₃).isSome = true) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.window pLen)
      (Two fun (g : SeedGeneratorPublic) s => SeedGeneratorBefore n pLen qLen g.windowed s) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.window
  refine RelCT.seq (two_piece (Ψ := WindowChecked n pLen qLen) [.rsp] (seedGeneratorBefore_pins n pLen qLen) t₁
    fun g s h => ?_) ?_
  · have hp := seedGeneratorBefore_pLen h
    subst pLen
    exact WP.mono (windowHead_ready h) fun t ht => ⟨s, ht⟩
  refine two_ite (fun g s t ⟨_, hs, hcs, _⟩ ⟨_, ht, hct, _⟩ => by simp only [eval, hcs, hct]) ?_ ?_
  · refine two_piece [.rsp] (fun g s t hs ht => windowChecked_pins n pLen qLen g s t hs.1 ht.1) t₂
      fun g t ⟨⟨s, hs, hc, hr, hm, hk⟩, hb⟩ => WP.mono (windowTaken_ready hs hc hr hm hk hb) fun _ h => h.1
  · refine two_piece [.rsp] (fun g s t hs ht => windowChecked_pins n pLen qLen g s t hs.1 ht.1) t₃
      fun g t ⟨⟨s, hs, hc, hr, hm, hk⟩, hb⟩ => ?_
    have hp := seedGeneratorBefore_pLen hs
    subst pLen
    exact WP.mono (windowFull_ready hs hc hm hk hb) fun _ h => h.1

theorem window_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.window pLen)
      (Two fun (g : SeedGeneratorPublic) s => SeedGeneratorBefore n pLen qLen g.windowed s) := by
  rcases hp with rfl | rfl | rfl
  all_goals exact window_ct_of n _ qLen (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of one seed of the refillable-tape search

A seed's attempt (`Refill.refillAttempt`) is the finite search's
(`seedAttempt_ct`) with the window around its generator search: the window
(`window_ct`), the candidates' octets counted as consumed, and the status of
a window cut short. Each branches only on the status word and the window's
length, which the seed's public inputs fix. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

theorem domainFinishBefore_frame {pLen qLen : Nat} {d : DomainFinishPublic} {s t : State}
    (h : DomainFinishBefore pLen qLen d s) {W : Nat → BitVec 64} (hm : GenerationMemory d.context W t)
    (hf : Frame [⟨d.context.geo.F, frameBytes⟩] s.mem t.mem) : DomainFinishBefore pLen qLen d t := by
  obtain ⟨_, bp, bq, bg, hp, hq⟩ := h
  have pn : d.context.geo.pLen ≤ 384 := by rcases d.context.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : d.context.geo.qLen ≤ 32 := by rcases d.context.geo.qWidth with hh | hh <;> omega_using [hh]
  refine ⟨⟨W, hm⟩, ?_, ?_, ?_, hp, hq⟩
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn]))]; exact bp
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [qn]))]; exact bq
  · rw [ctFrame_bytes hf (d.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn]))]; exact bg

theorem seedGeneratorAfter_pins (pLen qLen : Nat) : Pins (SeedGeneratorAfter pLen qLen) [.rsp] := by
  intro g s t ⟨⟨_, hs, _⟩, _⟩ ⟨⟨_, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

/-! ## The candidates' octets consumed -/

theorem consumed_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorAfter pLen qLen g s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.windowConsumed) s (SeedGeneratorAfter pLen qLen g) := by
  obtain ⟨⟨W, hm, h19⟩, next⟩ := h
  refine WP.mono (refillConsumed_ok hm) fun t ⟨mt, ft, _, _⟩ => ?_
  exact ⟨⟨_, mt, by simpa [upd] using h19⟩, fun hs => domainFinishBefore_frame (next hs) mt ft⟩

/-! ## A window cut short -/

/-- The status after `windowShort`: a window shorter than `windowBytes`
without a generator ran out. -/
def SeedGeneratorPublic.shortStatus (g : SeedGeneratorPublic) : BitVec 64 :=
  if g.status = 1 then 1 else
    if g.seed.context.hs.bytes.length < Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen
    then 0 else g.status

def ShortAfter (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory g.seed.context W s ∧ W 19 = g.shortStatus) ∧
  (g.shortStatus = 1 → DomainFinishBefore pLen qLen g.finish s)

def ShortChecked (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  SeedGeneratorAfter pLen qLen g s ∧ isa.eval .e s = some (g.status == 1)

def ShortCompared (pLen qLen : Nat) (g : SeedGeneratorPublic) (s : State) : Prop :=
  SeedGeneratorAfter pLen qLen g s ∧ g.status ≠ 1 ∧
  isa.eval .b s = some (decide (g.seed.context.hs.bytes.length <
    Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen))

theorem seedGeneratorAfter_keep {pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorAfter pLen qLen g s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedGeneratorAfter pLen qLen g t :=
  seedGeneratorAfter_congr h hm hk

theorem shortStatus_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorAfter pLen qLen g s) :
    WP isa (.block successStatus) s (ShortChecked pLen qLen g) := by
  obtain ⟨⟨W, hm, h19⟩, _⟩ := id h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
  exact ⟨seedGeneratorAfter_keep h he hk, by simp only [eval, hz, h19]⟩

theorem shortLength_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortChecked pLen qLen g s) (he : isa.eval .e s = some false) :
    WP isa (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax (.imm (BitVec.ofNat 32
        (Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen)))]) s
      (ShortCompared pLen qLen g) := by
  obtain ⟨hg, hs⟩ := h
  obtain ⟨⟨W, hm, _⟩, _⟩ := id hg
  obtain ⟨V, R⟩ := hm.rep
  have pn : g.seed.context.geo.pLen ≤ 384 := by rcases g.seed.context.geo.width with hh | hh | hh <;> omega_using [hh]
  have h12 : W 12 = BitVec.ofNat 64 g.seed.context.hs.bytes.length :=
    (hm.slots 12 (by simp [generationSlots])).trans g.seed.context.hLengthSlot
  have ne : g.status ≠ 1 := by
    intro e; have := hs.symm.trans he; simp [e] at this
  refine WP.mono (shortCheck_ok hm.layout R h12 g.seed.context.hs.size (windowBytes_lt _ pn))
    fun t ⟨hc, hmt, kt⟩ => ?_
  exact ⟨seedGeneratorAfter_keep hg hmt kt, ne, by simp only [eval, hc]⟩

theorem shortAccepted_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortChecked pLen qLen g s) (he : isa.eval .e s = some true) :
    WP isa (.block []) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, next⟩, hs⟩ := h
  have e : g.status = 1 := by
    have := hs.symm.trans he; simpa using this
  have sh : g.shortStatus = 1 := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_left e]
  exact WP.block_nil ⟨⟨W, hm, h19.trans (e.trans sh.symm)⟩, fun _ => next e⟩

theorem shortRanOut_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortCompared pLen qLen g s) (hb : isa.eval .b s = some true) :
    WP isa (.block (stackStatus 0)) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, _⟩, ne, hc⟩ := h
  have short : g.seed.context.hs.bytes.length <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have := hc.symm.trans hb; simpa using this
  have sh : g.shortStatus = 0 := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_right ne, ite_eq_left short]
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (stackStatus_ok hm.layout R 0 (by decide)) fun t ⟨Lt, Rt, ot, kt⟩ => ?_
  have mt := hm.frame Lt ⟨V, Rt⟩ (fun k hk => by
    have : k ≠ 19 := by rintro rfl; exact absurd hk (by decide)
    simp [upd, this]) (GenerationContext.status_frame ot) kt.2.1 kt.2.2
  exact ⟨⟨_, mt, by simp [upd, sh]⟩, fun h1 => by rw [sh] at h1; exact absurd h1 (by decide)⟩

theorem shortFull_ready {pLen qLen : Nat} {g : SeedGeneratorPublic} {s : State}
    (h : ShortCompared pLen qLen g s) (hb : isa.eval .b s = some false) :
    WP isa (.block []) s (ShortAfter pLen qLen g) := by
  obtain ⟨⟨⟨W, hm, h19⟩, _⟩, ne, hc⟩ := h
  have full : ¬ g.seed.context.hs.bytes.length <
      Impl.Dsa.X86_64.Generation.Refill.windowBytes g.seed.context.geo.pLen := by
    have := hc.symm.trans hb; simpa using this
  have sh : g.shortStatus = g.status := by
    unfold SeedGeneratorPublic.shortStatus; rw [ite_eq_right ne, ite_eq_right full]
  exact WP.block_nil ⟨⟨W, hm, h19.trans sh.symm⟩, fun h1 => absurd (sh.symm.trans h1) ne⟩

theorem shortChecked_pins (pLen qLen : Nat) : Pins (ShortChecked pLen qLen) [.rsp] :=
  fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1

theorem shortCompared_pins (pLen qLen : Nat) : Pins (ShortCompared pLen qLen) [.rsp] :=
  fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1

theorem windowShort_ct (pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
      (Impl.Dsa.X86_64.Generation.Refill.windowShort pLen)
      (Two fun g s => ShortAfter pLen qLen g s) := by
  have tc : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax
      (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.windowBytes pLen)))]) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold Impl.Dsa.X86_64.Generation.Refill.windowShort
  refine RelCT.seq (two_piece (Ψ := fun g s => ShortChecked pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    [.rsp] (fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
    fun g s h => WP.mono (shortStatus_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine two_ite (fun g s t hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_
  · exact two_post (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun g s h => shortAccepted_ready h.1.1 h.2
  refine RelCT.seq (two_piece (Ψ := ShortCompared pLen qLen) [.rsp]
    (fun g s t hs ht => shortChecked_pins pLen qLen g s t hs.1.1 ht.1.1) tc.choose_spec fun g s h => ?_) ?_
  · obtain ⟨⟨hc, hp⟩, he⟩ := h
    subst pLen
    exact shortLength_ready hc he
  refine two_ite (fun g s t hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_
  · exact two_piece [.rsp] (fun g s t hs ht => shortCompared_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
      fun g s h => shortRanOut_ready h.1 h.2
  · exact two_post (two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide))
      fun g s h => shortFull_ready h.1 h.2

/-! ## After the seed's `p`: the window, the generator and the parameters -/

theorem shortAfter_congr {pLen qLen : Nat} {g : SeedGeneratorPublic} {s t : State}
    (h : ShortAfter pLen qLen g s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) : ShortAfter pLen qLen g t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨⟨Wt, ht⟩, bp, bq, bg, hp, hq⟩ := next ha
  exact ⟨⟨Wt, ht.congr hm hk⟩, hm ▸ bp, hm ▸ bq, hm ▸ bg, hp, hq⟩

theorem refillTail_ct (M : Mont) (Sq : MontS) (n pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen))
      (VG.Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.Refill.window pLen,
        generatorSearch Sq.mm M.mm pLen, .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
        Impl.Dsa.X86_64.Generation.Refill.windowShort pLen,
        onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)]) (fun _ _ => True) := by
  have width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384 := by
    rcases sizes with h | h | h <;> simp [h.1]
  unfold VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
    VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
  refine RelCT.seq (window_ct n pLen qLen width) (two_map SeedGeneratorPublic.windowed (fun _ _ h => h) ?_)
  refine RelCT.seq (two_post (Ψ := fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    (seedGenerator_ct M Sq n pLen qLen width)
    (fun g s h => WP.mono (seedGenerator_after M Sq h) fun _ ht => ⟨ht, seedGeneratorBefore_pLen h⟩)) ?_
  refine RelCT.seq (two_piece (Ψ := fun g s => SeedGeneratorAfter pLen qLen g s ∧ g.seed.context.geo.pLen = pLen)
    [.rsp] (fun g s t hs ht => seedGeneratorAfter_pins pLen qLen g s t hs.1 ht.1) (by taint_decide)
    fun g s h => WP.mono (consumed_ready h.1) fun _ ht => ⟨ht, h.2⟩) ?_
  refine RelCT.seq (windowShort_ct pLen qLen width) ?_
  apply onSuccess_ct (Φ := ShortAfter pLen qLen) (fun g : SeedGeneratorPublic => g.seed.context)
    SeedGeneratorPublic.shortStatus (fun _ _ h => h.1) (fun _ _ _ h hm hk => shortAfter_congr h hm hk)
  exact two_map SeedGeneratorPublic.finish (fun _ _ h => h.1.2 h.2)
    (finishDomain_ct (checkName := checkName) M Sq pLen qLen sizes)

/-! ## The seed -/

theorem refillPrimeFinish_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore n pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (onSuccess (VG.Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.Refill.window pLen,
          generatorSearch Sq.mm M.mm pLen, .block Impl.Dsa.X86_64.Generation.Refill.windowConsumed,
          Impl.Dsa.X86_64.Generation.Refill.windowShort pLen,
          onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)])))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T n hn pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter n pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (refillTail_ct (checkName := checkName) M Sq n pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

theorem refillAttempt_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3 ∨ n = 6) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedAttemptBefore n pLen qLen))
      (Impl.Dsa.X86_64.Generation.Refill.refillAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
        pLen qLen) (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold Impl.Dsa.X86_64.Generation.Refill.refillAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T n hn qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter n pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2)
    (refillPrimeFinish_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of the refillable-tape search's controller

The controller's public state between seeds (`LoopPublic`): the search's
context and its current `h` tape, the octets of the witness tape consumed,
the seeds it may still reject and the pointers to `used` and `state`. Each
seed's attempt leaves a public `h` tape (`refillHs`), status and cursor, all
functions of the tape's octets (`LoopPublic.res`), so two runs of the
controller with the same public state take the same branches and leave the
same public state (`DonePublic` when it stops). -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-- Where the controller's words and the pointers it holds are, apart from
the search's other memory. -/
structure CtlOK (c : GenerationContext) (c0 c1 : BitVec 64) : Prop where
  changed : ∀ r ∈ c.changed, (Refill.ctlRegion c.geo.F).Disjoint r
  rand : (⟨c.rand.ptr, c.rand.bytes.length⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  seeds : (⟨c.seeds.ptr, c.seeds.bytes.length⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  hash : (Refill.ctlRegion c.geo.F).Disjoint ⟨c.geo.hash, oRsa⟩
  bound : c.geo.F.toNat + 328 ≤ 2 ^ 64

theorem CtlOK.gm {c : GenerationContext} {c0 c1 : BitVec 64} (ok : CtlOK c c0 c1) {hs : GenerationTape c.geo}
    (hin : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨c.rand.ptr, c.rand.bytes.length⟩)
    {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory (c.withHs hs) W s)
    (hf : Frame [Refill.ctlRegion c.geo.F] s.mem t.mem) (hsp : t.gpr .rsp = s.gpr .rsp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : GenerationMemory (c.withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem c.geo.F c.geo.hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (Refill.ctl_frame _).symm)
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ok.hash.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    Refill.tapeMemory_ctl hm.seeds hf ok.seeds hr hw, Refill.tapeMemory_ctl hm.hs hf (ok.rand.sub_left hin) hr hw,
    Refill.tapeMemory_ctl hm.rand hf ok.rand hr hw⟩

theorem CtlOK.word {c : GenerationContext} {c0 c1 : BitVec 64} (ok : CtlOK c c0 c1) {m m' : Mem}
    (hf : Frame c.changed m m') {k : Nat} (hk : k < 4) :
    Refill.ctlWord m' c.geo.F k = Refill.ctlWord m c.geo.F k :=
  Refill.ctlWord_frame hf ok.changed hk

theorem refillHs_sub (p : GenerationContext) (seed rest : List Byte)
    (hin : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩) :
    Region.Sub ⟨(refillHs p seed rest).ptr, (refillHs p seed rest).bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
  unfold refillHs
  split
  · split
    · rw [GenerationTape.window_length]
      exact Offset.sub_base p.rand.ptr (by omega_using [])
    · exact hin
  · exact hin

/-- Where the buffers the search's end writes are, apart from its other memory. -/
structure EndOK (c : GenerationContext) (c0 c1 : BitVec 64) (wr : List Region) : Prop where
  stIn : (⟨c1, 32⟩ : Region) ∈ wr
  usIn : (⟨c0, 8⟩ : Region) ∈ wr
  stBound : c1.toNat + 32 ≤ 2 ^ 64
  usBound : c0.toNat + 8 ≤ 2 ^ 64
  stChanged : ∀ r ∈ c.changed, (⟨c1, 32⟩ : Region).Disjoint r
  usChanged : ∀ r ∈ c.changed, (⟨c0, 8⟩ : Region).Disjoint r
  stRand : (⟨c1, 32⟩ : Region).Disjoint ⟨c.rand.ptr, c.rand.bytes.length⟩
  usRand : (⟨c0, 8⟩ : Region).Disjoint ⟨c.rand.ptr, c.rand.bytes.length⟩
  stSeeds : (⟨c1, 32⟩ : Region).Disjoint ⟨c.seeds.ptr, c.seeds.bytes.length⟩
  usSeeds : (⟨c0, 8⟩ : Region).Disjoint ⟨c.seeds.ptr, c.seeds.bytes.length⟩
  stHash : (⟨c1, 32⟩ : Region).Disjoint ⟨c.geo.hash, oRsa⟩
  usHash : (⟨c0, 8⟩ : Region).Disjoint ⟨c.geo.hash, oRsa⟩
  stCtl : (⟨c1, 32⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  usCtl : (⟨c0, 8⟩ : Region).Disjoint (Refill.ctlRegion c.geo.F)
  out : OutputPlan c
  outIn : (⟨c.saved 6, 2 * c.geo.pLen + c.geo.qLen⟩ : Region) ∈ wr
  lenBound : c.rand.bytes.length < 2 ^ 32

/-! ## The public state -/

structure LoopPublic where
  ctx : GenerationContext
  hs : GenerationTape ctx.geo
  start : Nat
  left : Nat
  c0 : BitVec 64
  c1 : BitVec 64
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout ctx.geo.B wr
  startBound : start ≤ ctx.rand.bytes.length
  leftBound : left ≤ Spec.Dsa.parameterSeeds
  hsIn : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨ctx.rand.ptr, ctx.rand.bytes.length⟩
  ok : CtlOK ctx c0 c1
  ends : EndOK ctx c0 c1 wr

def LoopPublic.context (P : LoopPublic) : GenerationContext := P.ctx.withHs P.hs

/-- The seed's octets and the witness tape after them. -/
def LoopPublic.seedBytes (P : LoopPublic) : List Byte :=
  (P.ctx.rand.bytes.drop P.start).take P.ctx.geo.qLen

def LoopPublic.rest (P : LoopPublic) : List Byte := P.ctx.rand.bytes.drop (P.start + P.ctx.geo.qLen)

/-- The seed's result. -/
def LoopPublic.res (P : LoopPublic) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.refillAttempt P.ctx.geo.pLen P.ctx.geo.qLen P.seedBytes P.rest

def LoopPublic.hsNext (P : LoopPublic) : GenerationTape P.ctx.geo := refillHs P.context P.seedBytes P.rest

def LoopPublic.after (P : LoopPublic) : Nat :=
  match P.res with
  | some (_, r) => P.ctx.rand.bytes.length - r.length
  | none => P.start

def LoopPublic.status (P : LoopPublic) : BitVec 64 :=
  match P.res with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def LoopPublic.next (P : LoopPublic) : LoopPublic where
  ctx := P.ctx
  hs := P.hsNext
  start := P.after
  left := P.left - 1
  c0 := P.c0
  c1 := P.c1
  ws := P.ws
  wr := P.wr
  header := P.header
  startBound := by
    unfold LoopPublic.after; split
    · exact Nat.sub_le _ _
    · exact P.startBound
  leftBound := by have := P.leftBound; omega_using [this]
  hsIn := refillHs_sub P.context _ _ P.hsIn
  ok := P.ok
  ends := P.ends

/-- The controller's state when it stops. -/
structure DonePublic where
  ctx : GenerationContext
  hs : GenerationTape ctx.geo
  status : BitVec 64
  cursor : Nat
  left : Nat
  used : Nat
  c0 : BitVec 64
  c1 : BitVec 64
  ws : List Region
  wr : List Region
  cursorBound : cursor ≤ ctx.rand.bytes.length
  hsIn : Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨ctx.rand.ptr, ctx.rand.bytes.length⟩
  ok : CtlOK ctx c0 c1
  ends : EndOK ctx c0 c1 wr

def LoopPublic.stop (P : LoopPublic) (status : BitVec 64) : DonePublic :=
  ⟨P.ctx, P.hs, status, P.start, P.left, 0, P.c0, P.c1, P.ws, P.wr, P.startBound, P.hsIn, P.ok, P.ends⟩

def LoopPublic.done (P : LoopPublic) : DonePublic :=
  ⟨P.ctx, P.hsNext, P.status, P.start, P.left, P.after, P.c0, P.c1, P.ws, P.wr, P.startBound,
    refillHs_sub P.context _ _ P.hsIn, P.ok, P.ends⟩

/-! ## The predicates -/

def CtlAt (F : Addr) (c0 c1 : BitVec 64) (left : Nat) (t : State) : Prop :=
  Refill.ctlWord t.mem F 0 = c0 ∧ Refill.ctlWord t.mem F 1 = c1 ∧
  Refill.ctlWord t.mem F 2 = BitVec.ofNat 64 left ∧ Refill.ctlRegion F ∈ t.wr

def RefillLoopBefore (n pLen qLen : Nat) (P : LoopPublic) (t : State) : Prop :=
  (∃ W, GenerationMemory P.context W t ∧ W 16 = BitVec.ofNat 64 P.start ∧ W 10 = 0) ∧
  CtlAt P.ctx.geo.F P.c0 P.c1 P.left t ∧ FrV n P.ctx.geo.F P.ws t ∧ t.wr = P.wr ∧
  P.ctx.geo.pLen = pLen ∧ P.ctx.geo.qLen = qLen

def DoneAt (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  (∃ W, GenerationMemory (D.ctx.withHs D.hs) W t ∧ W 19 = D.status ∧
    (D.status = 1 → W 16 = BitVec.ofNat 64 D.used)) ∧
  CtlAt D.ctx.geo.F D.c0 D.c1 D.left t ∧ Refill.ctlWord t.mem D.ctx.geo.F 3 = BitVec.ofNat 64 D.cursor ∧
  FrV n D.ctx.geo.F D.ws t ∧ t.wr = D.wr ∧ (D.status = 0 ∨ D.status = 1 ∨ D.status = 2) ∧
  D.ctx.geo.pLen = pLen ∧ D.ctx.geo.qLen = qLen

/-- Before the iteration's last status test. -/
def LoopMid (n pLen qLen m : Nat) : LoopPublic ⊕ DonePublic → State → Prop
  | .inl P, t => RefillLoopBefore n pLen qLen P t ∧ (∃ W, GenerationMemory P.context W t ∧ W 19 = 3) ∧ P.left < m
  | .inr D, t => DoneAt n pLen qLen D t

def LoopPost (n pLen qLen m : Nat) : LoopPublic ⊕ DonePublic → State → Prop
  | .inl P, t => isa.eval .e t = some true ∧ RefillLoopBefore n pLen qLen P t ∧ P.left < m
  | .inr D, t => isa.eval .e t = some false ∧ DoneAt n pLen qLen D t

theorem two_image {α β : Type} {Φ : β → State → Prop} (f : α → β) {s t : State}
    (h : Two (fun a s => Φ (f a) s) s t) : Two Φ s t :=
  let ⟨a, h₁, h₂⟩ := h; ⟨f a, h₁, h₂⟩

theorem loopBefore_rsp {n pLen qLen : Nat} {P : LoopPublic} {t : State} (h : RefillLoopBefore n pLen qLen P t) :
    t.gpr .rsp = P.ctx.geo.F := h.2.2.1.rsp

/-- `RefillLoopBefore` across a step that keeps the memory but `rax` and `rcx`. -/
theorem loopBefore_keep {n pLen qLen : Nat} {P : LoopPublic} {s t : State} (h : RefillLoopBefore n pLen qLen P s)
    (hm : t.mem = s.mem) (hk : Keep [.rax, .rcx] s t) : RefillLoopBefore n pLen qLen P t := by
  obtain ⟨⟨W, hW, h16, h10⟩, ⟨c0, c1, c2, cw⟩, hf, hw, hp, hq⟩ := h
  refine ⟨⟨W, hW.congr2 hm hk, h16, h10⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, hf.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans hw, hp, hq⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2

end VG.Proof.Dsa.X86_64.Generation
