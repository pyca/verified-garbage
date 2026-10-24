module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Finish
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Spec
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Draw
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Call

/-!
# Randomized DSA signing on PPC64LE: the attempts

`attempts_ok`: from `AttInv` (the specification's remaining attempts from
`u` octets consumed, with `a` attempts left, give the result `resOf`), the
loop of attempts ends in `AttOut`: the result's status and consumption in
`r31` and `r25`, and its signature in `out` when the status is 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-- The result, on entry. -/
abbrev resOf (s₀ : State) : Spec.Dsa.RandomSignResult := randomSignRemaining (inpOf (rlOf s₀) s₀.mem) 0 8

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (rlOf s₀) (qbOf (rlOf s₀) s₀.mem)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (rlOf s₀) s₀.mem)

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (rlOf s₀).ql - (eOf s₀).W, m (off (rlOf s₀).F (oNonce + j)) = 0

/-- At the head of the attempts' loop, with `a` attempts left and `u` octets consumed. -/
structure AttInv (s₀ : State) (a u : Nat) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 u
  hu : u ≤ (rlOf s₀).rl
  r26 : t.gpr .r26 = BitVec.ofNat 64 a
  ha1 : 1 ≤ a
  ha8 : a ≤ 8
  zero : NZero s₀ t.mem
  rel : RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) u a

/-- After the attempts. -/
structure AttOut (s₀ : State) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used
  r31 : t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 →
    Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)

theorem sub1_beq : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 1 == 0) = decide (st = 1) := by decide

theorem sub4_beq : ∀ st < 5, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = decide (st = 4) := by decide

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} : sampleStatus S = 1 ↔ S.scalar.isSome := by
  unfold sampleStatus
  split
  · simp_all
  · rename_i h; simp only [h, Option.isSome_none, Bool.false_eq_true, iff_false]; split <;> decide

/-- The registers of `Scanned` other than `Ctx`'s. -/
theorem Scanned.step {s₀ t t' : State} (hs : Scanned (rlOf s₀) s₀ t) (hc : Ctx (rlOf s₀) s₀ t')
    (h27 : t'.gpr .r27 = t.gpr .r27) (h28 : t'.gpr .r28 = t.gpr .r28) (h29 : t'.gpr .r29 = t.gpr .r29) :
    Scanned (rlOf s₀) s₀ t' :=
  ⟨hc, h27.trans hs.r27, h28.trans hs.r28, fun hq => h29.trans (hs.r29 hq)⟩

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : RL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  have hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega)] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 120 + (x - L.F).toNat = (x - L.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)] at hn
  omega

/-- The sampler's run keeps `Scanned` and the nonce's zeros. -/
theorem sampled {s₀ t t₁ : State} {u : Nat} {S : Spec.Dsa.Random.Sample} (h : rsContract.pre s₀)
    (hs : Scanned (rlOf s₀) s₀ t) (hz : NZero s₀ t.mem) (so : SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S t t₁)
    (hq : 1 < qOf s₀) : Scanned (rlOf s₀) s₀ t₁ ∧ NZero s₀ t₁.mem := by
  have hL := rlOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
  have hql : (eOf s₀).ql ≤ 32 := hE.ql
  have hql' := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide
  refine ⟨hs.step (hs.ctx.step hL so.keep.sp so.keep.rd so.keep.wr (fun r hr => so.keep.gpr r (hdis r hr))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out))
    (so.keep.gpr _ (by decide)) (so.keep.gpr _ (by decide)) (so.keep.gpr _ (by decide)), fun j hj => ?_⟩
  have hF := hL.fnw
  have e : ofs (eOf s₀).F (off (rlOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
  have hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    simp only [SE.o]; omega
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact hz j hj

theorem ctx_r3 : ∀ r ∈ ctxRegs, r ∉ ([.r3] : List Reg) := by decide

theorem ctx_r26 : ∀ r ∈ ctxRegs, r ∉ ([.r26, .r31] : List Reg) := by decide

/-- After `[subi r3 r31 4]`, the loop goes on exactly when the status is 4. -/
theorem tail_ok {t : State} {st : Nat} (h31 : t.gpr .r31 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [.subi .r3 .r31 4]) t fun t' =>
      (isa.eval (.zero .d .r3) t' = some (decide (st = 4)) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
  refine WP.keep (c := .block [.subi .r3 .r31 4]) [.r3] ?_ (by decide)
  prun [h31]
  rw [show VG.PPC64LE.eval (.zero .d .r3) (t.write .r3 (BitVec.ofNat 64 st - BitVec.ofNat 64 4)) =
    some ((t.write .r3 (BitVec.ofNat 64 st - BitVec.ofNat 64 4)).gpr .r3 == 0) from eval_zero _ _]
  gsimp; rw [sub4_beq st hst]

/-- A frame's octet is kept by the call, which writes `out` and `scratch` only. -/
theorem frame_byte {L : RL} (hL : L.Ok) {m m' : Mem} (hf : Frame (signWr L) m m') {d : Nat} (hd : d < frameBytes) :
    m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  have hin : L.frR.Contains (off L.F d) 1 := VG.Offset.contains_base _ (by omega) (by simp only [frameBytes] at hd; omega)
  simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.dFO _ hin hc
  · exact hL.dFS _ hin hc

/-- One attempt. -/
theorem attempt_ok {s₀ t : State} {a u : Nat} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) (hi : AttInv s₀ a u t) :
    WP isa (.seq attempt (.block [.subi .r3 .r31 4])) t fun t' =>
      isa.eval (.zero .d .r3) t' = some (decide (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4)) ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a ≠ 4 → AttOut s₀ t') ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4 → 1 < a ∧
          AttInv s₀ (a - 1) (u + (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).used) t') := by
  have hL := rlOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hQ := seOf_Q (L := rlOf s₀) s₀.mem hq
  have henv := hi.sc.env h hq
  have hql := hL.ql
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := hi.ha1; omega⟩
  generalize hD : randomSignDraw (inpOf (rlOf s₀) s₀.mem) u = D
  have hD' : Spec.Dsa.Random.sample (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u) = D := by
    rw [← hD, draw_eq hL]
  have hDu : u + D.used ≤ (rlOf s₀).rl := by
    have := Dsa.Random.sample_used_le (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u)
    rw [hD', List.length_drop, VG.Proof.Bignum.bytesAt_length] at this
    have := hi.hu; omega
  unfold attempt
  refine WP.seq (WP.seq (WP.mono (sample_ok hE hQ henv hi.r25 hi.hu) fun t₁ so => ?_))
  rw [hD'] at so
  obtain ⟨sc₁, z₁⟩ := sampled h hi.sc hi.zero so hq
  have hst := sampleStatus_le D
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_)
  have sc₂ : Scanned (rlOf s₀) s₀ t₂ := sc₁.step (sc₁.ctx.step hL k2.sp k2.rd k2.wr
    (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _))
    (k2.gpr _ (by decide)) (k2.gpr _ (by decide)) (k2.gpr _ (by decide))
  have b31 : t₂.gpr .r31 = BitVec.ofNat 64 (sampleStatus D) := (k2.gpr _ (by decide)).trans so.r31
  have b25 : t₂.gpr .r25 = BitVec.ofNat 64 (u + D.used) := (k2.gpr _ (by decide)).trans so.r25
  have b26 : t₂.gpr .r26 = BitVec.ofNat 64 (a' + 1) :=
    (k2.gpr _ (by decide)).trans ((so.keep.gpr _ (by decide)).trans hi.r26)
  refine WP.ite (decide (sampleStatus D = 1)) (by rw [eval_zero, a3, so.r31, sub1_beq _ (by omega)])
    (fun hs => ?_) (fun hs => ?_)
  · -- A nonce: the call.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    have hdk : randomSignDraw (inpOf (rlOf s₀) s₀.mem) u = D := hD
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq z₁ (so.cand k hk)
    refine WP.seq (WP.mono (callArgs_ok hL sc₂.ctx) fun t₃ ⟨ha3, m3, k3⟩ => ?_)
    refine WP.seq (WP.mono (sign_ok h ha3) fun t₄ sg => ?_)
    have es : sresOf (rlOf s₀) t₃.mem = Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql
        (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest := by
      simp only [sresOf, inpOf]; rw [m3, sc₂.ctx.key, sc₂.ctx.dig, hnonce]
    have b26' : t₄.gpr .r26 = BitVec.ofNat 64 (a' + 1) :=
      (sg.pres _ (by decide)).trans ((k3.gpr _ (by decide)).trans b26)
    have sc₄ : Scanned (rlOf s₀) s₀ t₄ := sc₂.step sg.ctx ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide)))
      ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide))) ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide)))
    have b25' : t₄.gpr .r25 = BitVec.ofNat 64 (u + D.used) :=
      (sg.pres _ (by decide)).trans ((k3.gpr _ (by decide)).trans b25)
    have z₄ : NZero s₀ t₄.mem := fun j hj => by
      rw [frame_byte hL sg.frame (by simp only [oNonce, frameBytes]; omega), m3, m2]; exact z₁ j hj
    have hr3 := sg.r3
    rw [es] at hr3
    refine WP.mono (callFinish_ok b26' (by omega) hi.ha8 hr3) fun t₅ ⟨m5, k5, hs1, hs0⟩ => ?_
    have sc₅ : Scanned (rlOf s₀) s₀ t₅ := sc₄.step (sc₄.ctx.step hL k5.sp k5.rd k5.wr
      (fun r hr => k5.gpr r (ctx_r26 r hr)) (by rw [m5]; exact Frame.refl _ _))
      (k5.gpr _ (by decide)) (k5.gpr _ (by decide)) (k5.gpr _ (by decide))
    have b25'' : t₅.gpr .r25 = BitVec.ofNat 64 (u + D.used) := (k5.gpr _ (by decide)).trans b25'
    have hdk' : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).scalar = some k := by rw [hD]; exact hk
    cases hsr : Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql (inpOf (rlOf s₀) s₀.mem).key
        (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest with
    | some sig =>
      obtain ⟨c31, -⟩ := hs1 (by rw [hsr]; exact Nat.one_ne_zero)
      obtain ⟨rsig, rst, ru⟩ := hi.rel.success hdk' hsr
      rw [hD] at ru
      have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 1 := by
        simp only [randomSignAttemptStatus, hdk']
        simp only [inpOf] at hsr ⊢
        simp [hsr]
      refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
        ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
      refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
        (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
        ?_, ?_, fun _ => ?_⟩
      · rw [k6.gpr _ (by decide), b25'', ← ru, Nat.zero_add]
      · rw [k6.gpr _ (by decide), c31, rst]
      · rw [m6, m5, sg.out, es, hsr, rsig]
    | none =>
      obtain ⟨c26, c31⟩ := hs0 (by rw [hsr]; rfl)
      have rel' := hi.rel.retry hdk' hsr
      rw [hD] at rel'
      by_cases ha0 : a' = 0
      · subst ha0
        rw [ite_eq_left rfl] at c31
        obtain ⟨-, rst, ru⟩ := rel'.exhausted
        have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (0 + 1) = 0 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr]
        refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
          ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
        refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
          (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
          ?_, ?_, fun h1 => absurd (rst ▸ h1) (by decide)⟩
        · rw [k6.gpr _ (by decide), b25'', ← ru, Nat.zero_add]
        · rw [k6.gpr _ (by decide), c31, rst]
      · rw [Nat.add_sub_cancel, ite_eq_right ha0] at c31
        have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 4 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr, ha0]
        refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
          ⟨by rw [ev, hAS], fun h => absurd hAS h, fun _ => ⟨by omega, ?_⟩⟩
        rw [Nat.add_sub_cancel]
        refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
          (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
          (k6.gpr _ (by decide)).trans b25'', hDu, (k6.gpr _ (by decide)).trans (c26.trans (by rw [Nat.add_sub_cancel])), by omega, by have := hi.ha8; omega, ?_, rel'⟩
        intro j hj
        rw [m6, m5]; exact z₄ j hj
  · -- No nonce: the sampler's status.
    simp only [decide_eq_false_iff_not] at hs
    have hk : D.scalar = none := by
      cases hc : D.scalar with
      | none => rfl
      | some k => exact absurd (sampleStatus_some.mpr (by rw [hc]; rfl)) hs
    obtain ⟨rs, rst, ru⟩ := hi.rel.sample_none (hD ▸ hk)
    rw [hD] at rst ru
    have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = sampleStatus D := by
      unfold randomSignAttemptStatus
      rw [hD]
      simp only [hk]
    refine WP.mono (WP.block_nil rfl) fun t₃ e₃ => ?_
    subst e₃
    refine WP.mono (tail_ok b31 (by omega)) fun t₄ ⟨⟨ev, m4⟩, k4⟩ =>
      ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; omega⟩
    · refine ⟨sc₂.step (sc₂.ctx.step hL k4.sp k4.rd k4.wr (fun r hr => k4.gpr r (ctx_r3 r hr))
        (by rw [m4]; exact Frame.refl _ _)) (k4.gpr _ (by decide)) (k4.gpr _ (by decide)) (k4.gpr _ (by decide)),
        ?_, ?_, fun h1 => absurd (rst ▸ h1) hs⟩
      · rw [k4.gpr _ (by decide), b25, ← ru, Nat.zero_add]
      · rw [k4.gpr _ (by decide), b31, rst]

end VG.Proof.Dsa.PPC64LE.RS
