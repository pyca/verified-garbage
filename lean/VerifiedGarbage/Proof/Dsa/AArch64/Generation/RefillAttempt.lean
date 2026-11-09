module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # One seed of the refillable-tape search on AArch64

`refillAttempt_ok`: the seed attempt of the refillable-tape search
(`Impl.Dsa.AArch64.Generation.Refill.refillAttempt`) computes
`Proof.Dsa.Generation.refillAttempt`. Once `p` is found, the generator
stage's `h` tape is the window of the witness tape after `p`'s witnesses
(`window`); the octets of the candidates it read count as consumed, and a
window cut short without a generator ran out (`stageStatus`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

/-- Without a generator, `generator` reads every candidate. -/
theorem generatorCount_of_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none →
      VG.Proof.Dsa.Generation.generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, hn => by
    rw [VG.Proof.Dsa.Generation.generator_cons'] at hn
    cases hit : VG.Proof.Dsa.Generation.generatorHit p q h
    · simp only [hit, Bool.false_eq_true, ite_false] at hn
      simp only [VG.Proof.Dsa.Generation.generatorCount, hit, Bool.false_eq_true, ite_false,
        List.length_cons, generatorCount_of_none hn]
    · simp [hit] at hn

/-- `subs` of two numbers: the carry is set iff there is no borrow. -/
theorem refill_subs_ge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~BitVec.ofNat 64 b).toNat + (true).toNat) = decide (b ≤ a) := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega_arith)

theorem movi_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

/-! ## The window -/

theorem window_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total pLen : Nat}
    (h14 : W 14 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hp : 128 * pLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.off F 88) (VG.Proof.Bignum.off base used)).writeW (VG.Proof.Bignum.off F 104)
        (BitVec.ofNat 64 (min (total - used) (128 * pLen))) := by
  have w14 : s.mem.readW (s.sp + BitVec.ofNat 64 112) 64 = base := by
    rw [L.sp]; exact (R.fr 14 (by decide)).trans h14
  have w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 used := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  have w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 total := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  have l112 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 112) 8 := by rw [L.sp]; exact L.ld (d := 112) (by decide)
  have l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  have l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  have s88 : InRegions s.wr (s.sp + BitVec.ofNat 64 88) 8 := by rw [L.sp]; exact L.st (d := 88) (by decide)
  have s104 : InRegions s.wr (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.st (d := 104) (by decide)
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) :=
    Offset.ofNat_sub_ofNat hle
  have hm := movi_ofNat hp
  unfold Impl.Dsa.AArch64.Generation.Refill.window Impl.Dsa.AArch64.Generation.Refill.windowBytes
  brun [State.write, exec_ldrSp (off := 112) (by decide), exec_ldrSp (off := 128) (by decide),
    exec_ldrSp (off := 120) (by decide), exec_storeSp (off := 88) (by decide),
    exec_storeSp (off := 104) (by decide), w14, w16, w15, l112, l128, l120, s88, s104, hsub, hm,
    refill_subs_ge (show total - used < 2 ^ 64 by omega) (show 128 * pLen < 2 ^ 64 by omega)]
  rw [L.sp]
  by_cases hc : 128 * pLen ≤ total - used
  · simp only [hc, decide_true, ite_true, Nat.min_eq_right hc]
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, Nat.min_eq_left (by omega : total - used ≤ 128 * pLen)]

theorem slice_length {g : GenerationGeometry} (t : GenerationTape g) {d n : Nat}
    (h : d + n ≤ t.bytes.length) : (t.slice d n h).bytes.length = n := by
  simp only [GenerationTape.slice, List.length_take, List.length_drop]; omega

/-- `window`: the `h` tape is the window of `rand` after its first `used`
octets. -/
theorem refillWindow_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) {used n : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) (hn : n = min (p.rand.bytes.length - used) (128 * p.geo.pLen)) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window p.geo.pLen)) s fun t =>
      GenerationMemory (p.withHs (p.rand.slice used n (by omega)))
        (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) t ∧
      Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have L := h.layout
  have h14 : W 14 = p.rand.ptr := (h.slots 14 (by simp [generationSlots])).trans p.randSlot
  have h15 : W 15 = BitVec.ofNat 64 p.rand.bytes.length :=
    (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6]
    (window_run L R h14 h16 h15 hu p.rand.size (by omega))
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide) rfl
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  rw [← hn] at hm
  have Rt : Rep t.mem p.geo.F p.geo.hash V (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) := by
    rw [hm]; exact (R.wf L.geo (k := 11) (by decide) _).wf L.geo (k := 13) (by decide) _
  have ft : Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cF p.geo.F (d := 88) (by decide))).writeW
      List.mem_cons_self _ (cF p.geo.F (d := 104) (by decide))
  have fc : Frame p.changed s.mem t.mem := GenerationContext.frame_single ft
  have room : used + n ≤ p.rand.bytes.length := by omega
  refine ⟨⟨lay_of_rep L R Rt (by simp [upd]) kt.sp kt.wr, ⟨V, Rt⟩, ?_, h.scratch.congr kt.wr,
    h.seeds.frame fc kt.rd kt.wr, (h.rand.frame fc kt.rd kt.wr).slice room, h.rand.frame fc kt.rd kt.wr⟩,
    ft, kt.rd, kt.wr⟩
  intro k hk
  by_cases e11 : k = 11
  · subst e11; simp [upd, GenerationContext.withHs, GenerationTape.slice]
  by_cases e13 : k = 13
  · subst e13; simp [upd, GenerationContext.withHs, slice_length]
  simp only [upd, GenerationContext.withHs, e11, e13, ite_false]
  exact h.slots k hk

/-! ## The stage's result -/

theorem shr2_ofNat {c b : Nat} (hc : c < 4) (h : c + 4 * b < 2 ^ 64) :
    BitVec.ofNat 64 (c + 4 * b) >>> 2 = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h]
  omega

theorem shl2_ofNat (b : Nat) : BitVec.ofNat 64 b <<< 2 = BitVec.ofNat 64 (4 * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The seed's status from the stage's end `c` (`Proof.Dsa.GeneratorStage.code`)
and the window's length `n`. -/
def refillStatus (c n pLen : Nat) : Nat := if c = 3 then (if n < 128 * pLen then 0 else 3) else 2 * c - 1

theorem consumed_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c b u : Nat} (hc : c < 4) (hb : b < 2 ^ 32)
    (hx : s.gpr .x0 = BitVec.ofNat 64 (c + 4 * b)) (h16 : W 16 = BitVec.ofNat 64 u) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.consumed) s fun t =>
      (t.mem = s.mem.writeW (VG.Proof.Bignum.off F 128) (BitVec.ofNat 64 (u + b)) ∧ t.gpr .x3 = BitVec.ofNat 64 c ∧
        t.gpr .x4 = BitVec.ofNat 64 c - 3) ∧ Keep [.x3, .x4, .x5] s t := by
  have w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 u := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  have l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  have s128 : InRegions s.wr (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.st (d := 128) (by decide)
  have e1 := shr2_ofNat hc (by omega : c + 4 * b < 2 ^ 64)
  have e2 := shl2_ofNat b
  have e3 : BitVec.ofNat 64 (c + 4 * b) - BitVec.ofNat 64 (4 * b) = BitVec.ofNat 64 c := by
    rw [Offset.ofNat_sub_ofNat (by omega)]; congr 1; omega
  refine WP.keep [.x3, .x4, .x5] ?_ (by decide)
  unfold Impl.Dsa.AArch64.Generation.Refill.consumed
  brun [State.write, exec_lsr_x' (by decide : 2 < 64), exec_lsl_x (by decide : 2 < 64),
    exec_ldrSp (off := 128) (by decide), exec_storeSp (off := 128) (by decide), w16, l128, s128, hx, e1, e2, e3]
  refine ⟨?_, rfl⟩
  rw [L.sp, ← BitVec.ofNat_add]

theorem shortStatus_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {n pLen : Nat} (h13 : W 13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hp : 128 * pLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 (if n < 128 * pLen then 0 else 3)) ∧
        t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w13 : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 n := by
    rw [L.sp]; exact (R.fr 13 (by decide)).trans h13
  have l104 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.ld (d := 104) (by decide)
  have s152 : InRegions s.wr (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.st (d := 152) (by decide)
  have hm := movi_ofNat hp
  unfold Impl.Dsa.AArch64.Generation.Refill.shortStatus Impl.Dsa.AArch64.Generation.Refill.windowBytes
  brun [State.write, exec_ldrSp (off := 104) (by decide), exec_storeSp (off := 152) (by decide), w13, l104, s152, hm,
    refill_subs_ge hn (show 128 * pLen < 2 ^ 64 by omega)]
  rw [L.sp]
  by_cases hc : 128 * pLen ≤ n
  · simp only [hc, decide_true, ite_true, show ¬ n < 128 * pLen by omega, ite_false]; rfl
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, show n < 128 * pLen by omega, ite_true]; rfl

theorem foundStatus_run {s : State} {F S : Addr} (L : Lay s F S) {c : Nat} (hc : 1 ≤ c ∧ c < 4) (hx : s.gpr .x3 = BitVec.ofNat 64 c) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 (2 * c - 1)) := by
  have s152 : InRegions s.wr (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.st (d := 152) (by decide)
  have e : BitVec.ofNat 64 c + BitVec.ofNat 64 c - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 * c - 1) := by
    rw [← BitVec.ofNat_add, Offset.ofNat_sub_ofNat (by omega)]; congr 1; omega
  unfold Impl.Dsa.AArch64.Generation.Refill.foundStatus
  brun [State.write, exec_subImm_x' (by decide : 1 < 4096), exec_storeSp (off := 152) (by decide), s152, hx, e]
  rw [L.sp]

/-- The stage's result as the seed's status, and its candidates' octets
consumed. -/
theorem stageStatus_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c b u n pLen : Nat} (hc : c = 1 ∨ c = 2 ∨ c = 3)
    (hb : b < 2 ^ 32) (hx : s.gpr .x0 = BitVec.ofNat 64 (c + 4 * b))
    (h16 : W 16 = BitVec.ofNat 64 u) (h13 : W 13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) (hp : 128 * pLen < 2 ^ 16) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.stageStatus pLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.Refill.stageStatus
  refine WP.seq (WP.mono (consumed_run L R (by omega) hb hx h16) fun u₁ ⟨⟨hm₁, h3, h4⟩, k₁⟩ => ?_)
  have R₁ : Rep u₁.mem F S V (upd W 16 (BitVec.ofNat 64 (u + b))) := by
    rw [hm₁]; exact R.wf L.geo (k := 16) (by decide) _
  have L₁ := lay_of_rep L R R₁ (by simp [upd]) k₁.sp k₁.wr
  have f₁ : Frame [⟨F, frameBytes⟩] s.mem u₁.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (cF F (d := 128) (by decide))
  have done : ∀ (v : Nat) (t : State), t.mem = u₁.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 v) →
      t.sp = u₁.sp → t.rd = u₁.rd → t.wr = u₁.wr → v = refillStatus c n pLen →
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    intro v t hm hsp hrd hwr hv
    subst hv
    have Rt : Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) := by
      rw [hm]; exact R₁.wf L₁.geo (k := 19) (by decide) _
    refine ⟨lay_of_rep L₁ R₁ Rt (by simp [upd]) hsp hwr, Rt, ?_, hrd.trans k₁.rd, hwr.trans k₁.wr⟩
    rw [hm]
    exact f₁.writeW List.mem_cons_self _ (cF F (d := 152) (by decide))
  by_cases h3c : c = 3
  · subst h3c
    refine WP.ite true (by simp [eval, State.read, h4]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    have h13' : upd W 16 (BitVec.ofNat 64 (u + b)) 13 = BitVec.ofNat 64 n := by simp [upd, h13]
    refine WP.mono (shortStatus_run L₁ R₁ h13' hn hp) fun t ⟨hm, hsp, hrd, hwr⟩ =>
      done _ t hm hsp hrd hwr (by simp [refillStatus])
  · have hc' : c = 1 ∨ c = 2 := by omega
    refine WP.ite false (by
      simp only [eval, State.read, h4, BitVec.setWidth_eq, Option.some.injEq, beq_eq_false_iff_ne]
      rcases hc' with rfl | rfl <;> decide) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.mono (WP.keep [.x3] (foundStatus_run L₁ (by omega) h3) (by decide)) fun t ⟨hm, kt⟩ =>
      done _ t hm kt.sp kt.rd kt.wr (by simp [refillStatus, h3c])

/-! ## After `p`: the window, the stage and the status -/

theorem GenerationGeometry.frame_bytes {g : GenerationGeometry} {m m' : Mem}
    (hf : Frame [⟨g.F, frameBytes⟩] m m') {d n : Nat} (hd : d + n ≤ usedBytes g.pLen) :
    Spec.Rsa.bytesAt m' (VG.Proof.Bignum.off g.B d) n = Spec.Rsa.bytesAt m (VG.Proof.Bignum.off g.B d) n := by
  have pn : g.pLen ≤ 384 := by rcases g.width with hh | hh | hh <;> omega
  apply VG.Proof.Dsa.Generation.frame_bytesAt hf
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (g.frame_part hd).symm
  · unfold usedBytes domainCheck at hd; omega

/-- The generation's memory after the stage's call: the frame and the hash
workspace are as they were. -/
theorem generatorCalled_memory {p : GenerationContext} {W : Nat → BitVec 64} {s u t : State}
    {value qval : Nat} (h : GenerationMemory p W s) (C : GeneratorCalled p value qval s u t)
    (hu : u.wr = s.wr) (hr : u.rd = s.rd) :
    ∃ V, Lay t p.geo.F p.geo.hash ∧ Rep t.mem p.geo.F p.geo.hash V W ∧ Frame p.changed s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have L := h.layout
  obtain ⟨V, R⟩ := h.rep
  have hashKept : ∀ o < oRsa, t.mem (VG.Proof.Bignum.off p.geo.hash o) = s.mem (VG.Proof.Bignum.off p.geo.hash o) := by
    intro o ho
    have c8 : VG.Impl.Dsa.Generation.Layout.hash = 16384 := rfl
    have c9 : oRsa = 8192 := rfl
    have hw8 : 8 * (usedBytes p.geo.pLen / 8) = usedBytes p.geo.pLen := by
      rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide
    have hhb : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.geo.pLen :=
      p.geo.small_bound (by decide) (by decide)
    have k := C.keeps (VG.Impl.Dsa.Generation.Layout.hash + o) (by omega) (by
      intro r hr
      have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hw | hw | hw <;> omega
      have qn : Impl.Dsa.AArch64.Generator.qLen p.geo.pLen ≤ 32 := by
        unfold Impl.Dsa.AArch64.Generator.qLen; split <;> omega
      simp only [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [parent, g, packed, Impl.Dsa.AArch64.Generator.spill,
          VG.Impl.Dsa.Generation.Layout.control, arithmetic, domainCheck, Impl.Dsa.Layout.activeBytes,
          Impl.Dsa.AArch64.Generator.spillBytes, Impl.Dsa.Layout.usedBytes, arithmeticBytes] <;> omega)
    simpa only [GenerationGeometry.hash, VG.Proof.Bignum.off, BitVec.add_assoc, BitVec.ofNat_add] using k
  have frameKept : ∀ k < nW, VG.Proof.Bignum.word t.mem p.geo.F (8 * k) = W k := by
    intro k hk
    rw [← R.fr k hk]
    refine C.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    have hf : Region.Sub ⟨VG.Proof.Bignum.off p.geo.F (8 * k), 8⟩ ⟨p.geo.F, frameBytes⟩ :=
      Offset.sub_base _ (by have : nW = 34 := rfl; have : frameBytes = 272 := rfl; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.geo.frameArena.sub_left hf
    · exact p.geo.frame_below.sub_left hf
  have Rt : Rep t.mem p.geo.F p.geo.hash V W :=
    ⟨fun o ho => (hashKept o ho).trans (R.scr o ho), frameKept⟩
  have Lt : Lay t p.geo.F p.geo.hash := lay_of_rep L R Rt rfl (C.sp.trans L.sp.symm) (C.wr.trans hu)
  refine ⟨V, Lt, Rt, Frame.sub C.frame fun r hr => ?_, C.rd.trans hr, C.wr.trans hu⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩

theorem stage_code_cases (p q : Nat) (hs : List Nat) :
    Proof.Dsa.GeneratorStage.code p q hs = 1 ∨ Proof.Dsa.GeneratorStage.code p q hs = 2 ∨
      Proof.Dsa.GeneratorStage.code p q hs = 3 := by
  unfold Proof.Dsa.GeneratorStage.code
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem refillGenerator_ok (G : GeneratorStage) {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
      Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen =
      Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
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
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run p.geo.pLen) s (RefillFinished p W res s) := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have p0 : 0 < p.geo.pLen := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have hp_b : VG.Impl.Dsa.Generation.Layout.p + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have he_b : exponent + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have hq_b : q + p.geo.qLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  have hpk_b : packed + (2 * p.geo.pLen + p.geo.qLen) ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega)
  obtain ⟨n, hn⟩ : ∃ n, n = min (p.rand.bytes.length - used) (128 * p.geo.pLen) := ⟨_, rfl⟩
  have rlen : (p.rand.bytes.drop used).length = p.rand.bytes.length - used := List.length_drop
  have hwin : used + n ≤ p.rand.bytes.length := by omega
  let win := p.rand.slice used n hwin
  have hsub : Region.Sub ⟨win.ptr, win.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
    rw [slice_length]
    exact Offset.sub_base p.rand.ptr hwin
  have hlen : (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
      (p.rand.bytes.drop used)).length = n / p.geo.pLen := by
    simp only [VG.Proof.Dsa.Generation.windowCandidates, List.length_map, Spec.Dsa.generationChunks,
      List.length_range, List.length_take, rlen, Spec.Dsa.generatorAttempts]
    rw [hn, Nat.min_comm]
  have hcand : (Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE =
      VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used) := by
    show (Spec.Dsa.generationChunks p.geo.pLen ((p.rand.bytes.drop used).take n)).map Spec.Dsa.decodeBE = _
    have ht : (p.rand.bytes.drop used).take n =
        (p.rand.bytes.drop used).take (Spec.Dsa.generatorAttempts * p.geo.pLen) :=
      List.take_eq_take_iff.mpr (by rw [rlen]; unfold Spec.Dsa.generatorAttempts; omega)
    unfold VG.Proof.Dsa.Generation.windowCandidates
    rw [ht]
  simp only [Impl.Dsa.AArch64.Generation.Refill.refillGenerator, VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (refillWindow_ok h h16 hu hn) fun u ⟨mu, fu, ru, wu⟩ => ?_)
  refine WP.seq (WP.mono (generatorCallArgs_ok (p := p.withHs win) mu) fun v ⟨h0, h1, h2, h3, hmv, kv⟩ => ?_)
  have hsp : v.sp = p.geo.F := kv.sp.trans mu.layout.sp
  refine WP.seq (WP.mono (generatorCall_call_ok (p := p.withHs win) G mu value qval domain qfit qpos
    ((p.geo.frame_bytes fu hp_b).trans bp) ((p.geo.frame_bytes fu he_b).trans be)
    ((p.geo.frame_bytes fu hq_b).trans bq) h0 h1 h2 h3 hmv hsp kv.rd kv.wr) fun t C => ?_)
  obtain ⟨V, Lt, Rt, ft, rt, wt⟩ := generatorCalled_memory mu C kv.wr kv.rd
  have hx0 : t.gpr .x0 = BitVec.ofNat 64 (Proof.Dsa.GeneratorStage.result p.geo.pLen value qval
      ((Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE)) := C.status
  have hpk : ∀ a, Proof.Dsa.GeneratorStage.stage value qval
      ((Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE) = some a →
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := C.packed
  rw [hcand] at hx0 hpk
  generalize hhs : VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
    (p.rand.bytes.drop used) = hs at hx0 hpk hnone hsome hlen
  have hc : p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤ n :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _)
      (Nat.le_of_eq hlen))) (Nat.mul_div_le n _)
  let c := Proof.Dsa.GeneratorStage.code value qval hs
  let b := p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs
  have hx : t.gpr .x0 = BitVec.ofNat 64 (c + 4 * b) := hx0
  have t16 : upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n) 16 = BitVec.ofNat 64 used := by
    simp [upd, h16]
  have t13 : upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n) 13 = BitVec.ofNat 64 n := by
    simp [upd]
  refine WP.mono (stageStatus_run Lt Rt (stage_code_cases value qval hs) (by omega) hx t16 t13 (by omega) (by omega))
    fun t' ⟨Lt', Rt', ft', rt', wt'⟩ => ?_
  have fut : Frame p.changed u.mem t'.mem := ft.trans (GenerationContext.frame_single ft')
  have fsx : Frame p.changed s.mem t'.mem := (GenerationContext.frame_single fu).trans fut
  have rsx : t'.rd = s.rd := rt'.trans (rt.trans ru)
  have wsx : t'.wr = s.wr := wt'.trans (wt.trans wu)
  let Wt := upd (upd (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) 16
    (BitVec.ofNat 64 (used + b))) 19 (BitVec.ofNat 64 (refillStatus c n p.geo.pLen))
  have mt : GenerationMemory (p.withHs win) Wt t' := by
    refine mu.frame Lt' ⟨V, Rt'⟩ (fun k hk => ?_) fut (rt'.trans rt) (wt'.trans wt)
    have : k ≠ 16 ∧ k ≠ 19 := by simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [Wt, upd, this.1, this.2]
  have hbound : used + b ≤ p.rand.bytes.length := by omega
  have wslots : ∀ k ∈ refillSlots, Wt k = W k := by
    intro k hk
    have : k ≠ 11 ∧ k ≠ 13 ∧ k ≠ 16 ∧ k ≠ 19 := by
      simp only [refillSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp [Wt, upd, this.1, this.2.1, this.2.2.1, this.2.2.2]
  have w16 : Wt 16 = BitVec.ofNat 64 (used + b) := by simp [Wt, upd]
  have w19 : Wt 19 = BitVec.ofNat 64 (refillStatus c n p.geo.pLen) := by simp [Wt, upd]
  have hdrop : ∀ k, (p.rand.bytes.drop used).drop k = p.rand.bytes.drop (used + k) := fun _ => List.drop_drop
  refine ⟨win, Wt, used + b, hsub, mt, hbound, w16, wslots, ?_, fsx, rsx, wsx⟩
  cases hg : Spec.Dsa.generator value qval hs with
  | none =>
    have hcode : c = 3 := by simp [c, Proof.Dsa.GeneratorStage.code, hg]
    have hcount := generatorCount_of_none hg
    by_cases short : n < 128 * p.geo.pLen
    · have hnot : ¬ (Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length) := by
        simp only [rlen, Spec.Dsa.generatorAttempts]; omega
      refine Or.inl ⟨by rw [w19, hcode]; simp [refillStatus, short], by rw [hnone hg, ite_eq_right hnot]⟩
    · have hn128 : n = 128 * p.geo.pLen := by omega
      have hc128 : VG.Proof.Dsa.Generation.generatorCount value qval hs = 128 := by
        rw [hcount, hlen, hn128, Nat.mul_div_cancel _ p0]
      have hyes : Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length := by
        simp only [rlen, Spec.Dsa.generatorAttempts]; omega
      refine Or.inr (Or.inl ⟨by rw [w19, hcode]; simp [refillStatus, short], ?_⟩)
      rw [hnone hg, ite_eq_left hyes, hdrop]
      congr 3
      simp only [b, hc128, Spec.Dsa.generatorAttempts, Nat.mul_comm]
  | some gv =>
    rw [hsome gv hg, hdrop]
    by_cases valid : Spec.Dsa.parametersValid ⟨value, qval, gv⟩
    · have hcode : c = 1 := by simp [c, Proof.Dsa.GeneratorStage.code, hg, valid]
      refine Or.inr (Or.inr ⟨by rw [w19, hcode]; rfl, ⟨value, qval, gv⟩, by simp only [valid, ite_true]; rfl, ?_⟩)
      have hst : Proof.Dsa.GeneratorStage.stage value qval hs = some ⟨value, qval, gv⟩ := by
        simp [Proof.Dsa.GeneratorStage.stage, hg, valid]
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft' (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact (p.geo.frame_part hpk_b).symm) (by omega)]
      exact hpk _ hst
    · have hcode : c = 2 := by simp [c, Proof.Dsa.GeneratorStage.code, hg, valid]
      exact Or.inr (Or.inl ⟨by rw [w19, hcode]; rfl, by simp only [valid, ite_false]; rfl⟩)

/-! ## The seed -/

theorem refillPrimeFinish_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (hhs : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length)
    {rest : List Byte}
    (hprime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) rest =
      some (true, p.rand.bytes.drop used)) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen)
      (Impl.Dsa.AArch64.Generation.onSuccess
        (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run p.geo.pLen))) s
      (RefillFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest) s) := by
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases p.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * p.geo.qLen) seed.bytes
  have qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  have qpos : 0 < Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1
  refine WP.seq (WP.mono (seedPrime_ok H T h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine refillFinished_of mt hhs huu u16 slots (Or.inl ⟨h19, ?_⟩) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have bv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      have ev : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      have qv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      have call := refillGenerator_ok G mv value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) domain qfit qpos
        bv ev qv u16 huu
        (res := VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest)
        (fun hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
        (fun gv hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
      exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.rd.trans ru) (kv.wr.trans wu)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine refillFinished_of mt hhs huu u16 slots (Or.inr (Or.inl ⟨h19, ?_⟩)) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]

/-- One seed of the refillable-tape search, at `W 1`, with its witnesses
and its generator's candidates read from `rand` after its first `used`
octets. -/
theorem refillAttempt_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (hhs : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run p.geo.pLen p.geo.qLen) s
      (RefillFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes
        (p.rand.bytes.drop used)) s) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.refillAttempt
  refine WP.seq (WP.mono (seedSubgroup_ok H T h seed hlen hseed h1 h16 hu)
    fun u ⟨usedu, status, huu, mu, bqu, fail, result, fu, ru, wu⟩ => ?_)
  let Wu := upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 usedu)) 19 status
  have u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  have u19 : Wu 19 = status := by simp [Wu, upd]
  have slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot).symm
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
      refine refillFinished_of mt hhs huu u16 slots (Or.inl ⟨hs, ?_⟩) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
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
        refine refillFinished_of mt hhs huu u16 slots (Or.inr (Or.inl ⟨hstatus, ?_⟩)) (by rw [hm]; exact fu)
          (kt.rd.trans ru) (kt.wr.trans wu)
        simp only [VG.Proof.Dsa.Generation.refillAttempt, qr, suffix]
    | true =>
      have hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        have seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.rd kv.wr
        have qv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        have call := refillPrimeFinish_ok H G T mv hhs seed hlen seedv u1 qv u16 huu (by rw [qr, suffix])
        exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.rd.trans ru) (kv.wr.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.AArch64.Generation
