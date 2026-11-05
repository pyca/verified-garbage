module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Set

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
        (min (p.rand.bytes.length - (p.rand.bytes.length - r'.length)) (128 * p.geo.pLen)) (by omega)
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
      (CtFinished p W res (p.rand.window used (min (p.rand.bytes.length - used) (128 * p.geo.pLen)) (by omega)) s) := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have p0 : 0 < p.geo.pLen := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  have hp_b : VG.Impl.Dsa.Generation.Layout.p + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have he_b : exponent + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have hq_b : q + p.geo.qLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have hg_b : g + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  set n := min (p.rand.bytes.length - used) (128 * p.geo.pLen) with hn
  have rlen : (p.rand.bytes.drop used).length = p.rand.bytes.length - used := List.length_drop
  have hwin : used + n ≤ p.rand.bytes.length := by omega
  have hsub : Region.Sub ⟨(p.rand.window used n hwin).ptr, (p.rand.window used n hwin).bytes.length⟩
      ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
    rw [GenerationTape.window_length]
    exact Offset.sub_base p.rand.ptr hwin
  -- The window's candidates.
  have hlen : (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
      (p.rand.bytes.drop used)).length = n / p.geo.pLen := by
    simp only [VG.Proof.Dsa.Generation.windowCandidates, List.length_map, Spec.Dsa.generationChunks,
      List.length_range, List.length_take, rlen, Spec.Dsa.generatorAttempts]
    rw [hn, Nat.min_comm]
  unfold VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
    VG.Impl.Bignum.X86_64.seqs VG.Impl.Bignum.X86_64.seqs
  refine WP.seq (WP.mono (refillWindow_ok h h16 hu hn) fun u ⟨mu, fu, ru, wu⟩ => ?_)
  have hcand : (Spec.Dsa.generationChunks p.geo.pLen
      (p.withHs (p.rand.window used n hwin)).hs.bytes).map Spec.Dsa.decodeBE =
      VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used) := by
    show (Spec.Dsa.generationChunks p.geo.pLen ((p.rand.bytes.drop used).take n)).map Spec.Dsa.decodeBE = _
    have ht : (p.rand.bytes.drop used).take n =
        (p.rand.bytes.drop used).take (Spec.Dsa.generatorAttempts * p.geo.pLen) :=
      List.take_eq_take_iff.mpr (by rw [rlen]; unfold Spec.Dsa.generatorAttempts; omega)
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
  have hc : p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤ n :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _) (Nat.le_of_eq hlen)))
      (Nat.mul_div_le n _)
  have v16 : Wv 16 = BitVec.ofNat 64 used := by
    rw [slots 16 (by simp [generatorSlots])]; simpa [upd] using h16
  have v12 : Wv 12 = BitVec.ofNat 64 n := by
    rw [slots 12 (by simp [generatorSlots])]; simp [upd]
  refine WP.seq (WP.mono (refillConsumed_ok mv) fun w ⟨mw, fw, rw', ww⟩ => ?_)
  have w16 : upd Wv 16 (Wv 16 + Wv 20) 16 =
      BitVec.ofNat 64 (used + p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs) := by
    simp only [upd, ite_true, v16, h20, BitVec.ofNat_add]
  have w12 : upd Wv 16 (Wv 16 + Wv 20) 12 = BitVec.ofNat 64 n := by simp [upd, v12]
  have w19 : upd Wv 16 (Wv 16 + Wv 20) 19 = Wv 19 := by simp [upd]
  have wslots : ∀ k ∈ refillSlots, upd Wv 16 (Wv 16 + Wv 20) k = W k := by
    intro k hk
    obtain ⟨hg, n11, n12, n16, _⟩ := refillSlots_cases hk
    simp only [upd, n16, ite_false]
    rw [slots k hg]
    simp [upd, n11, n12]
  refine WP.seq (WP.mono (refillShort_ok mw w12 (by omega)) fun x ⟨mx, fx, rx, wx⟩ => ?_)
  have hbound : used + p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤
      p.rand.bytes.length := by omega
  have fsx : Frame p.changed s.mem x.mem :=
    (((GenerationContext.frame_single fu).trans fv).trans (GenerationContext.frame_single fw)).trans
      (GenerationContext.frame_single fx)
  have rsx : x.rd = s.rd := rx.trans (rw'.trans (rv.trans ru))
  have wsx : x.wr = s.wr := wx.trans (ww.trans (wv.trans wu))
  have hdrop : ∀ k, (p.rand.bytes.drop used).drop k = p.rand.bytes.drop (used + k) := fun _ => List.drop_drop
  rw [w19] at mx
  rcases result with ⟨h19, hr⟩ | ⟨gv, h19, hr, _, upper, bgv⟩
  · have hcount := generatorCount_of_none hr
    by_cases short : n < 128 * p.geo.pLen
    · rw [ite_eq_left ⟨by rw [h19]; decide, short⟩] at mx
      apply onSuccess_generation_ok mx
      · intro _ _ _ _ hs1
        exact absurd hs1 (by simp [upd])
      · intro t mt hm kt _
        have hnot : ¬ (Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length) := by
          simp only [rlen, Spec.Dsa.generatorAttempts]; omega
        refine ⟨_, _, mt, hbound, by simpa [upd] using w16, fun k hk => ?_,
          Or.inl ⟨by simp [upd], by rw [hnone hr, ite_eq_right hnot]⟩,
          by rw [hm]; exact fsx, kt.2.1.trans rsx, kt.2.2.trans wsx⟩
        simpa [upd, (refillSlots_cases hk).2.2.2.2] using wslots k hk
    · rw [ite_eq_right (fun hh => short hh.2)] at mx
      have hn128 : n = 128 * p.geo.pLen := by omega
      have hc128 : VG.Proof.Dsa.Generation.generatorCount value qval hs = 128 := by
        rw [hcount, hlen, hn128, Nat.mul_div_cancel _ p0]
      apply onSuccess_generation_ok mx
      · intro _ _ _ _ hs1
        have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs1
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        have hyes : Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length := by
          simp only [rlen, Spec.Dsa.generatorAttempts]; omega
        refine ⟨_, _, mt, hbound, w16, wslots, Or.inr (Or.inl ⟨h19, ?_⟩),
          by rw [hm]; exact fsx, kt.2.1.trans rsx, kt.2.2.trans wsx⟩
        rw [hnone hr, ite_eq_left hyes, hdrop, hc128, Nat.mul_comm]
        rfl
  · rw [ite_eq_right (fun hh => hh.1 h19)] at mx
    apply onSuccess_generation_ok mx
    · intro y my hm ky _
      have pbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := by
        rw [hm, p.geo.frame_bytes fx hp_b, p.geo.frame_bytes fw hp_b]; exact bpv
      have qbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval := by
        rw [hm, p.geo.frame_bytes fx hq_b, p.geo.frame_bytes fw hq_b]; exact bqv
      have gbytes : Spec.Rsa.bytesAt y.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv := by
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
  have qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    have shape := VG.Proof.Dsa.Generation.qCandidate_shape
      (by rcases p.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * p.geo.qLen) seed.bytes
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  refine WP.seq (WP.mono (seedPrime_ok H T h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ctFinished_of mt (by simp only [refillHs, hprime, hr]) huu u16 slots (Or.inl ⟨h19, ?_⟩) (by rw [hm]; exact fu)
        (kt.2.1.trans ru) (kt.2.2.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have bv : Spec.Rsa.bytesAt v.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      have ev : Spec.Rsa.bytesAt v.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      have call := ctGeneratorFinish_ok (checkName := checkName) M Sq mv value
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) domain qfit bv ev qv u16 huu
        (res := VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest)
        (fun hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
        (fun gv hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
      exact WP.mono call fun t ht => (ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)).hs (by
        simp only [refillHs, hprime, hr]
        exact GenerationTape.window_congr _ (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega) _ _)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
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
  have u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  have u19 : Wu 19 = status := by simp [Wu, upd]
  have slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm
  have u1 : Wu 1 = seed.ptr := (slots 1 (by simp [searchSlots])).trans h1
  have seedu := hseed.frame fu ru wu
  cases qr : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used) with
  | none =>
    have hs : Wu 19 = 0 := u19.trans (fail qr)
    apply onSuccess_generation_ok mu
    · intro _ _ _ _ accepted
      have impossible : (0 : BitVec 64) = 1 := hs.symm.trans accepted
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine ctFinished_of mt (by simp only [refillHs, qr]) huu u16 slots (Or.inl ⟨hs, ?_⟩) (by rw [hm]; exact fu)
        (kt.2.1.trans ru) (kt.2.2.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, qr]
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    obtain ⟨hs, cursor⟩ := result accepted rest qr
    have suffix : p.rand.bytes.drop usedu = rest := by
      rw [cursor]
      exact VG.Proof.Dsa.Generation.probablePrime_cursor qr
    cases accepted with
    | false =>
      have hstatus : Wu 19 = 3 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro _ _ _ _ accepted
        have impossible : (3 : BitVec 64) = 1 := hstatus.symm.trans accepted
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        refine ctFinished_of mt (by simp only [refillHs, qr]) huu u16 slots (Or.inr (Or.inl ⟨hstatus, ?_⟩)) (by rw [hm]; exact fu)
          (kt.2.1.trans ru) (kt.2.2.trans wu)
        simp only [VG.Proof.Dsa.Generation.refillAttempt, qr, suffix]
    | true =>
      have hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        have seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.2.1 kv.2.2
        have qv : Spec.Rsa.bytesAt v.mem (off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        have call := ctPrimeFinish_ok (checkName := checkName) H M Sq T mv seed hlen seedv u1 qv u16 huu
          (by rw [qr, suffix])
        exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.2.1.trans ru) (kv.2.2.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.X86_64.Generation
