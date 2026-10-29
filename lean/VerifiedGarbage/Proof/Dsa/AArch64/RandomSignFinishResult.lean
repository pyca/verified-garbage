module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
/-! Convert a completed retry loop into the public signature and consumption outputs. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomSignLoop.lean`, which only this module imported.
section

/-! Functional correctness and termination of the outer signing retry loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Dsa.Random
open VG.Proof.Dsa (RandomSignResultRel randomSignRemaining randomSignDraw)

def RandomSignLoopPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop :=
  (∃ fuel, RandomSignRunning h hq (start + result.used) fuel t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status ∧
  (result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0))

def RandomSignLoopInv {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult)
    (fuel : Nat) (t : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning h hq used fuel t ∧
    RandomSignResultRel (randomInput s) start result used fuel

private theorem sample_none_status {draw : VG.Spec.Dsa.Random.Sample} (h : draw.scalar = none) :
    sampleStatus draw ≠ 1 ∧ (BitVec.ofNat 64 (sampleStatus draw) : BitVec 64) ≠ 4 := by
  simp only [sampleStatus, h]
  split <;> decide

private theorem attempt_progress (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {start fuel : Nat} {result : Spec.Dsa.RandomSignResult}
    (hi : RandomSignLoopInv h hq start result fuel t) :
    WP isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) t fun u =>
      Scr u (randomBase s) Random.frameBytes ∧ u.sp = randomBase s ∧
      ((word u.mem (randomBase s) Random.oStatus ≠ 4 ∧ RandomSignLoopPost h hq start result u) ∨
        (word u.mem (randomBase s) Random.oStatus = 4 ∧ ∃ k < fuel, RandomSignLoopInv h hq start result k u)) := by
  obtain ⟨hpos, hbound, used, hr, hrel⟩ := hi
  cases fuel with
  | zero => omega
  | succ fuel =>
    refine WP.mono (random_sign_attempt v hr hpos (by omega)) fun u hu => ?_
    cases hc : (randomSignDraw (randomInput s) used).scalar with
    | none =>
      simp only [RandomSignAttemptPost, hc] at hu
      obtain ⟨hr', hs⟩ := hu
      obtain ⟨_, _, hready⟩ := hr'.ready
      obtain ⟨_, hstatus, hused⟩ := hrel.sample_none hc
      have hne := sample_none_status hc
      refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hs]; exact hne.2,
        ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hs, hstatus], ?_⟩⟩
      intro he
      exact False.elim (hne.1 (hstatus.symm.trans he))
    | some k =>
      simp only [RandomSignAttemptPost, hc] at hu
      cases hs : randomSingleResult s k with
      | some sig =>
        simp only [hs, Option.isSome_some, ite_true] at hu
        obtain ⟨hr', hword, hout⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        obtain ⟨hsig, hstatus, hused⟩ := hrel.success hc hs
        refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
          ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl,
          fun _ => ?_⟩⟩
        rw [hsig]
        exact hout
      | none =>
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_sub_cancel] at hu
        obtain ⟨hr', hword, _⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        have hrel' := hrel.retry hc hs
        by_cases hz : fuel = 0
        · subst fuel
          obtain ⟨_, hstatus, hused⟩ := hrel'.exhausted
          refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
            ⟨0, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl, ?_⟩⟩
          intro he
          omega
        · have hn : fuel + 1 ≠ 1 := by omega
          refine ⟨hready.scr, hready.sp, Or.inr ⟨by rw [hword, ite_eq_right hn], fuel,
            by omega, by omega, by omega, used + (randomSignDraw (randomInput s) used).used, hr', hrel'⟩⟩

theorem random_sign_loop_correct (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel ≤ 8) :
    WP isa (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul))
      (.block (Random.statusTest 4))) (.zero .x .x4)) t
      (RandomSignLoopPost h hq used (randomSignRemaining (randomInput s) used fuel)) := by
  apply random_statusLoop_rule _ (randomBase s) (RandomSignLoopInv h hq used (randomSignRemaining (randomInput s) used fuel))
  · intro n a b ⟨hp, hb, k, hk, hrel⟩ hm hkeep
    exact ⟨hp, hb, k, hk.congr hm hkeep, hrel⟩
  · intro a b ⟨⟨n, hn⟩, hs, hout⟩ hm hkeep
    exact ⟨⟨n, hn.congr hm hkeep⟩, by rw [hm]; exact hs, fun h => by rw [hm]; exact hout h⟩
  · intro n a ha
    exact attempt_progress v ha
  · exact ⟨hpos, hbound, used, hr, RandomSignResultRel.refl _ _ _⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomSignFinishPre (s : State) (used : Nat) (t : State) : Prop where
  scr : Scr t (randomBase s) Random.frameBytes
  sp : t.sp = randomBase s
  saved : RandomSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

structure RandomSignBodyPost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  sp : t.sp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

private theorem bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem random_finish_ready_result {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    {result : Spec.Dsa.RandomSignResult} (hr : RandomSignFinishPre s result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
      result.signature.getD (List.replicate (s.gpr .x1).toNat 0))
    (hbound : result.status ≤ 2) (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  have houtlen : 0 < (s.gpr .x1).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .x2 :=
    hr.saved (56, s.gpr .x2) (by simp [randomSavedValues])
  have hframeOut := h.stackOut.sub_left (random_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (random_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .x0) (s.gpr .x1).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .x2, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono (random_finish_ok (B := randomBase s) (op := s.gpr .x0) (k := (s.gpr .x1).toNat) hr.scr hr.sp
    (hr.saved (40, s.gpr .x0) (by simp [randomSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [randomSavedValues]))
    houtlen (s.gpr .x1).isLt
    (fun j hj => ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .x2 := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hk.sp.trans hr.sp, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc => (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc),
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .x1).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega
      rw [hsig hs]
      exact bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem random_finish_result {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {result : Spec.Dsa.RandomSignResult}
    (hp : RandomSignLoopPost h hq 0 result t) (hbound : result.status ≤ 2)
    (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  obtain ⟨⟨fuel, hr⟩, hstatus, houtput⟩ := hp
  obtain ⟨cm, draws, hready⟩ := hr.ready
  exact random_finish_ready_result h
    ⟨hready.scr, hready.sp, hr.saved, (by simpa only [randomContextOf, Nat.zero_add] using hready.usedWord), hr.rd, hr.wr, hr.callee, hr.vectors⟩
    hstatus houtput hbound hsig

end VG.Proof.Dsa.AArch64
