module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSFinish
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSSpec
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCall
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on RISC-V: the attempts

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Attempt.lean`). `attempt_ok`:
from `AttInv` (the specification's remaining attempts from `u` octets
consumed, with `a` attempts left, give the result `resOf`), an attempt
either ends the loop in `AttOut` (the result's status and consumption in
`s10` and `s5`, and its signature in `out` when the status is 1) or leaves
`AttInv` with one attempt fewer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
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
  s5 : t.gpr .s5 = BitVec.ofNat 64 u
  hu : u ≤ (rlOf s₀).rl
  s6 : t.gpr .s6 = BitVec.ofNat 64 a
  ha1 : 1 ≤ a
  ha8 : a ≤ 8
  zero : NZero s₀ t.mem
  rel : RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) u a

/-- After the attempts. -/
structure AttOut (s₀ : State) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used
  s10 : t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status
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
    (h7 : t'.gpr .s7 = t.gpr .s7) (h8 : t'.gpr .s8 = t.gpr .s8) (h9 : t'.gpr .s9 = t.gpr .s9) :
    Scanned (rlOf s₀) s₀ t' :=
  ⟨hc, h7.trans hs.s7, h8.trans hs.s8, fun hq => h9.trans (hs.s9 hq)⟩

/-- `Scanned` across a change that keeps `Ctx`'s and the scan's registers, the
stack pointer, the regions and the memory. -/
theorem Scanned.keep {s₀ t t' : State} {rs : List Reg} (hL : (rlOf s₀).Ok) (hs : Scanned (rlOf s₀) s₀ t)
    (k : Keep rs t t') (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hd : ∀ r ∈ ctxRegs ++ [.s7, .s8, .s9], r ∉ rs := by decide) : Scanned (rlOf s₀) s₀ t' :=
  hs.step (hs.ctx.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hd r (List.mem_append_left _ hr)))
    (by rw [hm]; exact Frame.refl _ _))
    (k.1 _ (hd _ (by decide))) (k.1 _ (hd _ (by decide))) (k.1 _ (hd _ (by decide)))

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
  rw [show 2 ^ 64 - 32 + (x - L.F).toNat = (x - L.F).toNat - 32 + 2 ^ 64 by omega, Nat.add_mod_right,
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
  refine ⟨hs.step (hs.ctx.step hL (so.env.sp.trans hs.ctx.sp.symm) so.keep.2.1 so.keep.2.2
    (fun r hr => so.keep.1 r (hdis r hr))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out))
    (so.keep.1 _ (by decide)) (so.keep.1 _ (by decide)) (so.keep.1 _ (by decide)), fun j hj => ?_⟩
  have hF := hL.fnw
  have e : ofs (eOf s₀).F (off (rlOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
  have hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    simp only [SE.o]; omega
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact hz j hj

/-- After `[addi a0 s10 -4]`, the loop goes on exactly when the status is 4. -/
theorem tail_ok {t : State} {st : Nat} (h10 : t.gpr .s10 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [.addi .a0 .s10 (-4)]) t fun t' =>
      ((isa.eval (.zero .a0) t' = some (decide (st = 4)) ∧ t'.mem = t.mem) ∧ Keep [.a0] t t') ∧
        t'.sp = t.sp := by
  refine wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-4)]) [.a0] ?_ (by decide) (by rfl))
  brun [h10]
  show some ((t.write .a0 (BitVec.ofNat 64 st - 4#64)).gpr .a0 == 0) = _
  gsimp
  rw [sub4_beq st hst]

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
    WP isa (.seq attempt (.block [.addi .a0 .s10 (-4)])) t fun t' =>
      isa.eval (.zero .a0) t' = some (decide (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4)) ∧
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
  refine WP.seq (WP.seq (WP.mono (sample_ok hE hQ henv hi.s5 hi.hu) fun t₁ so => ?_))
  rw [hD'] at so
  obtain ⟨sc₁, z₁⟩ := sampled h hi.sc hi.zero so hq
  have hst := sampleStatus_le D
  refine WP.seq (WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .a0 = t₁.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a3⟩, k2⟩, sp2⟩ => ?_)
  have sc₂ : Scanned (rlOf s₀) s₀ t₂ := sc₁.keep hL k2 sp2 m2
  have b10 : t₂.gpr .s10 = BitVec.ofNat 64 (sampleStatus D) := (k2.1 _ (by decide)).trans so.s10
  have b5 : t₂.gpr .s5 = BitVec.ofNat 64 (u + D.used) := (k2.1 _ (by decide)).trans so.s5
  have b6 : t₂.gpr .s6 = BitVec.ofNat 64 (a' + 1) :=
    (k2.1 _ (by decide)).trans ((so.keep.1 _ (by decide)).trans hi.s6)
  refine WP.ite (decide (sampleStatus D = 1)) (by rw [Steps.eval_zero, a3, so.s10, sub1_beq _ (by omega)])
    (fun hs => ?_) (fun hs => ?_)
  · -- A nonce: the call.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq z₁ (so.cand k hk)
    refine WP.seq (WP.mono (callArgs_ok hL rfl sc₂.ctx) fun t₃ ⟨⟨ha3, m3, k3⟩, sp3⟩ => ?_)
    refine WP.seq (WP.mono (sign_ok h ha3) fun t₄ sg => ?_)
    have es : sresOf (rlOf s₀) t₃.mem = Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql
        (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest := by
      simp only [sresOf, inpOf]; rw [m3, sc₂.ctx.key, sc₂.ctx.digB, hnonce]
    have b6' : t₄.gpr .s6 = BitVec.ofNat 64 (a' + 1) :=
      (sg.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b6)
    have sc₄ : Scanned (rlOf s₀) s₀ t₄ := sc₂.step sg.ctx ((sg.pres _ (by decide)).trans (k3.1 _ (by decide)))
      ((sg.pres _ (by decide)).trans (k3.1 _ (by decide))) ((sg.pres _ (by decide)).trans (k3.1 _ (by decide)))
    have b5' : t₄.gpr .s5 = BitVec.ofNat 64 (u + D.used) :=
      (sg.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b5)
    have z₄ : NZero s₀ t₄.mem := fun j hj => by
      rw [frame_byte hL sg.frame (by simp only [oNonce, frameBytes]; omega), m3, m2]; exact z₁ j hj
    have hr0 := sg.a0
    rw [es] at hr0
    refine WP.mono (wp_sp (callFinish_ok b6' (by omega) hi.ha8 hr0)) fun t₅ ⟨⟨m5, k5, hs1, hs0⟩, sp5⟩ => ?_
    have sc₅ : Scanned (rlOf s₀) s₀ t₅ := sc₄.keep hL k5 sp5 m5
    have b5'' : t₅.gpr .s5 = BitVec.ofNat 64 (u + D.used) := (k5.1 _ (by decide)).trans b5'
    have hdk' : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).scalar = some k := by rw [hD]; exact hk
    cases hsr : Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql (inpOf (rlOf s₀) s₀.mem).key
        (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest with
    | some sig =>
      obtain ⟨c10, -⟩ := hs1 (by rw [hsr]; exact Nat.one_ne_zero)
      obtain ⟨rsig, rst, ru⟩ := hi.rel.success hdk' hsr
      rw [hD] at ru
      have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 1 := by
        simp only [randomSignAttemptStatus, hdk']
        simp only [inpOf] at hsr ⊢
        simp [hsr]
      refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
        ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
      refine ⟨sc₅.keep hL k6 sp6 m6, ?_, ?_, fun _ => ?_⟩
      · rw [k6.1 _ (by decide), b5'', ← ru, Nat.zero_add]
      · rw [k6.1 _ (by decide), c10, rst]
      · rw [m6, m5, sg.out, es, hsr, rsig]
    | none =>
      obtain ⟨c6, c10⟩ := hs0 (by rw [hsr]; rfl)
      have rel' := hi.rel.retry hdk' hsr
      rw [hD] at rel'
      by_cases ha0 : a' = 0
      · subst ha0
        rw [ite_eq_left rfl] at c10
        obtain ⟨-, rst, ru⟩ := rel'.exhausted
        have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (0 + 1) = 0 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr]
        refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
          ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
        refine ⟨sc₅.keep hL k6 sp6 m6, ?_, ?_, fun h1 => absurd (rst ▸ h1) (by decide)⟩
        · rw [k6.1 _ (by decide), b5'', ← ru, Nat.zero_add]
        · rw [k6.1 _ (by decide), c10, rst]
      · rw [Nat.add_sub_cancel, ite_eq_right ha0] at c10
        have hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 4 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr, ha0]
        refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
          ⟨by rw [ev, hAS], fun h => absurd hAS h, fun _ => ⟨by omega, ?_⟩⟩
        rw [Nat.add_sub_cancel]
        refine ⟨sc₅.keep hL k6 sp6 m6, (k6.1 _ (by decide)).trans b5'', hDu,
          (k6.1 _ (by decide)).trans (c6.trans (by rw [Nat.add_sub_cancel])), by omega,
          by have := hi.ha8; omega, ?_, rel'⟩
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
    refine WP.mono (tail_ok b10 (by omega)) fun t₄ ⟨⟨⟨ev, m4⟩, k4⟩, sp4⟩ =>
      ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; omega⟩
    · refine ⟨sc₂.keep hL k4 sp4 m4, ?_, ?_, fun h1 => absurd (rst ▸ h1) hs⟩
      · rw [k4.1 _ (by decide), b5, ← ru, Nat.zero_add]
      · rw [k4.1 _ (by decide), b10, rst]

end VG.Proof.Dsa.RISCV64.RS
