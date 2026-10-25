module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Checks
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# ML-DSA signing on PPC64LE: the rejection sampling loop

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseL.lean`). An iteration
(`iter_ok`) either continues, with the next iteration's head (`IL`), or ends
the loop (`XS`): with `r24 = 1` when it passed, as `signIteration` does
within `maxBounds` after the iterations before were rejected; with
`r24 = 0` when `signLoop` returns nothing within `minBounds` (its
`SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (passF zF amat Rej ParamsOk signIteration_eqF signLoop_min_none signCommit_eq)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem eval_nonzero_w (s : State) (r : Reg) : isa.eval (.nonzero .w r) s = some ((s.gpr r).setWidth 32 != 0) := by
  change VG.PPC64LE.eval (.nonzero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

/-! ## The loop of the specification -/

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1v p σ) (rppOf p σ) κ c),
          (List.range p.k).map (Proof.MlDsa.Sign.hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (CTv p σ κ) = some (cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : ¬ PassV p σ κ) : iterF p σ maxBounds κ = some (CTv p σ κ, none) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : PassV p σ κ) : iterF p σ maxBounds κ =
      some (CTv p σ κ, some ((List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (CTv p σ κ) = none) : iterF p σ minBounds κ = none := by
  rw [iterF, Proof.MlDsa.Sign.signIteration_eq, signCommit_eq, h]; rfl

end

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICd p STK t σ s
  r01 : (s.gpr .r3).setWidth 32 = 0 ∨ (s.gpr .r3).setWidth 32 = 1
  ok : (s.gpr .r3).setWidth 32 = 1 → PolyIs s.mem (SL p STK σ 0) (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .r3).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} : KeyGen.BallOk (slay2 p STK σ) sWb2 (sc oCT) (cLen p) p.τ cP (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  exact ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
    ⟨sptr_ok rfl (by decide), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide,
    by csep hF, by csep hF, by csep hF, hF.bp, ⟨hc.1, by omega_arith, hF.tau⟩⟩

theorem ball_ok {t : Nat} {σ s : State} (h : ICd p STK t σ s) :
    WP isa (ballAt P (cLen p) p.τ cP) s (IB p STK σ t) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hb := h.1.w1b
  unfold ballAt
  refine ball_okX hP h.1.l.k.sc.site hS (ball_m hF) fun s' k' hred hout hmax => ?_
  have hct : bytesAt s.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) := h.2
  rw [hct] at hout hmax
  refine ⟨⟨h.1.keep k' (by csep hF) (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide)), ?_⟩, ?_,
    fun h1 => ⟨⟨hred h1, ball_val hout h1 (hmax h1)⟩, hmax h1⟩, fun h0 => ?_⟩
  · rw [bytes_keepW h.1.l.k.sc.site.ok k'.frame (by csep hF) (by decide) (by omega_arith)]; exact h.2
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

end

/-! ## The end of an iteration -/

theorem SC2.of_regs {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s)
    (hg : ∀ r, r ∉ [.r3, .r24, .r25, .r26, .r27] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨hs.ok, hs.len, hs.w0, hs.w1, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s48, by rw [hsp]; exact hs.spk,
    by rw [hg .r31 (by decide)]; exact hs.r31, by rw [hg .r30 (by decide)]; exact hs.r30,
    by rw [hg .r29 (by decide)]; exact hs.r29, by rw [hg .r28 (by decide)]; exact hs.r28,
    by rw [hwr]; exact hs.cw, by rw [hwr, hrd]; exact hs.cr⟩, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hs' => ?_, by rw [hm]; exact h.sav, by rw [hm]; exact h.sk, by rw [hm]; exact h.mu⟩
  have : r ∉ [.r3, .r24, .r25, .r26, .r27] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl)
    · simp [preserved] at hr
    all_goals simp [savedTop] at hs'
  rw [hg r this]; exact h.pres r hr hs'

theorem IK.of_regs {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s)
    (hg : ∀ r, r ∉ [.r3, .r24, .r25, .r26, .r27] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : IK p STK σ s' :=
  ⟨h.sc.of_regs hg hm hrd hwr hsp, h.ok, by rw [hm]; exact h.A, by rw [hm]; exact h.rpp, by rw [hm]; exact h.s1,
    by rw [hm]; exact h.s2, by rw [hm]; exact h.t0⟩

/-- A block that writes one register `d` (one of `r3`, `r24`–`r27`) with `v`. -/
abbrev W1 (d : Reg) (v : BitVec 64) (s s' : State) : Prop :=
  s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem W1.of_regs {d : Reg} (hd : d ∈ [.r3, .r24, .r25, .r26, .r27]) {v : BitVec 64} {s s' : State}
    (h : W1 d v s s') : ∀ r, r ∉ [.r3, .r24, .r25, .r26, .r27] → s'.gpr r = s.gpr r :=
  fun r hr => h.2.1 r fun e => hr (e ▸ hd)

theorem li_ok (d : Reg) {v : Nat} (hv : v < 2 ^ 15) (s : State) :
    WP isa (.block [.li d v]) s (W1 d (BitVec.ofNat 64 v) s) := by
  crun [hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem addi_ok {d : Reg} (hd : d ≠ .r0) {v : Nat} (hv : v < 2 ^ 15) (s : State) :
    WP isa (.block [.addi d d v]) s (W1 d (s.gpr d + BitVec.ofNat 64 v) s) := by
  crun [hd, hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem subi_ok {d : Reg} (hd : d ≠ .r0) {v : Nat} (hv : v ≤ 2 ^ 15) (s : State) :
    WP isa (.block [.subi d d v]) s (W1 d (s.gpr d - BitVec.ofNat 64 v) s) := by
  crun [hd, hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem bit_pos {a : Prop} [Decidable a] (h : a) : bit a = 1 := ifp h _ _
theorem bit_neg {a : Prop} [Decidable a] (h : ¬ a) : bit a = 0 := ifn h _ _

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `r25 = 1`. -/
structure EP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  ct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t)
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  h : ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  pass : PassV p σ (p.ℓ * t)
  r24 : s.gpr .r24 = 1
  r25 : s.gpr .r25 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `r25 = 814 - t`. -/
structure EF (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  r27 : s.gpr .r27 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  r25 : s.gpr .r25 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  fail : ¬ PassV p σ (p.ℓ * t)
  r24 : s.gpr .r24 = 0
  t_lt : t < 814
  rej : RejT p σ t

/-- `SampleInBall` did not finish within `minBounds`: `r24 = 0`, `r25 = 1`. -/
structure EB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  r24 : s.gpr .r24 = 0
  r25 : s.gpr .r25 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- The loop ended: in `r24`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (STK : Nat) (σ : State) (s : State) : Prop where
  k : IK p STK σ s
  r01 : s.gpr .r24 = 0 ∨ s.gpr .r24 = 1
  pass : s.gpr .r24 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t) ∧
    (∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)) ∧
    ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  fail : s.gpr .r24 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .r25 ≠ 0 ∧ IL p STK σ (t + 1) s) ∨ (s.gpr .r25 = 0 ∧ XS p STK σ s)

theorem kthen_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : KO p STK σ t s)
    (hb : s.gpr .r24 ≠ 0) : WP isa (.block [.li .r25 1]) s (EP p STK σ t) := by
  refine WP.mono (li_ok .r25 (by decide) s) fun s' w => ?_
  have hpass : PassV p σ (p.ℓ * t) := by
    by_contra hc
    rw [h.r24, bit_neg hc] at hb; exact hb rfl
  have e24 : s.gpr .r24 = 1 := by rw [h.r24, bit_pos hpass]
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.2.2.1]; exact h.b.ct, fun r hr => by rw [w.2.2.1]; exact h.z r hr,
    fun i hi => by rw [w.2.2.1]; exact h.h i hi, h.b.some, hpass,
    by rw [w.2.1 .r24 (by decide)]; exact e24, w.1, h.b.l.t_lt, h.b.l.rej⟩

theorem kelse_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2 ^ 15) (h : KO p STK σ t s)
    (hb : s.gpr .r24 = 0) : WP isa (.block [.addi .r27 .r27 p.ℓ]) s (EF p STK σ t) := by
  refine WP.mono (addi_ok (by decide) hl s) fun s' w => ?_
  have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => by
    rw [h.r24, bit_pos hp] at hb; exact absurd hb (by decide)
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.1, h.b.l.r27, ← BitVec.ofNat_add, Nat.mul_succ], by rw [w.2.1 .r25 (by decide)]; exact h.b.l.r25,
    h.b.some, hfail, by rw [w.2.1 .r24 (by decide), h.r24, bit_neg hfail], h.b.l.t_lt, h.b.l.rej⟩

theorem kbranch_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2 ^ 15)
    (h : KO p STK σ t s) :
    WP isa (ifOkElse (.block [.li .r25 1]) (.block [.addi .r27 .r27 p.ℓ])) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' :=
  WP.ite _ (eval_nonzero s .r24) (fun hb => WP.mono (kthen_ok h (by simpa using hb)) fun _ h => .inl h)
    fun hb => WP.mono (kelse_ok hl h (by simpa using hb)) fun _ h => .inr h

theorem eb_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IB p STK σ t s)
    (h0 : (s.gpr .r3).setWidth 32 = 0) : WP isa (.block [.li .r24 0, .li .r25 1]) s (EB p STK σ t) := by
  rw [show ([.li .r24 0, .li .r25 1] : List Instr) = [.li .r24 0] ++ [.li .r25 1] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .r24 (by decide) s) fun s1 w1 => WP.mono (li_ok .r25 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.c.1.l.k.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2, h.bad h0,
    by rw [w2.2.1 .r24 (by decide)]; exact w1.1, w2.1, h.c.1.l.t_lt, h.c.1.l.rej⟩

theorem dec_end {p : Params} {STK : Nat} (hp : ParamsOk p) {σ : State} {t : Nat} {s : State}
    (h : EP p STK σ t s ∨ EF p STK σ t s ∨ EB p STK σ t s) :
    WP isa (.block [.subi .r25 .r25 1]) s (LP p STK σ t) := by
  refine WP.mono (subi_ok (by decide) (by decide) s) fun s' w => ?_
  have hk : IK p STK σ s := by rcases h with h | h | h <;> exact h.k
  have K := hk.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2
  have e24 : s'.gpr .r24 = s.gpr .r24 := w.2.1 .r24 (by decide)
  have em : s'.mem = s.mem := w.2.2.1
  rcases h with h | h | h
  · -- passed
    have z : s'.gpr .r25 = 0 := by rw [w.1, h.r25]; decide
    refine .inr ⟨z, K, .inr (e24.trans h.r24), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [em]; exact h.ct, fun r hr => by rw [em]; exact h.z r hr, fun i hi => by rw [em]; exact h.h i hi⟩,
      fun h0 => absurd (h0.symm.trans (e24.trans h.r24)) (by decide)⟩
  · -- rejected
    have ht := h.t_lt
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    have e25 : s'.gpr .r25 = BitVec.ofNat 64 (814 - (t + 1)) := by
      rw [w.1, h.r25, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
    by_cases ht' : t = 813
    · subst ht'
      refine .inr ⟨by rw [e25]; decide, K, .inl (e24.trans h.r24),
        fun h1 => absurd (h1.symm.trans (e24.trans h.r24)) (by decide), fun _ => loop_none_exh hr⟩
    · refine .inl ⟨by rw [e25]; intro e; have := congrArg BitVec.toNat e; simp at this; omega_arith,
        ⟨K, by rw [w.2.1 .r27 (by decide)]; exact h.r27, e25, by omega_arith, hr⟩⟩
  · -- `SampleInBall` failed
    have z : s'.gpr .r25 = 0 := by rw [w.1, h.r25]; decide
    exact .inr ⟨z, K, .inl (e24.trans h.r24), fun h1 => absurd (h1.symm.trans (e24.trans h.r24)) (by decide),
      fun _ => loop_none_ball h.rej h.none⟩

/-! ## An iteration, and the loop -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem checks_ok {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : KA p STK t σ s) :
    WP isa (checks P p) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' := by
  unfold checks
  refine WP.seq (WP.mono ((cntt_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (kinit_piece.ok σ s1 hpre h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono ((zs_piece hP hF hS).ok σ s2 hpre h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono ((r0s_piece hP hF hS).ok σ s3 hpre h3) fun s4 h4 => ?_)
  refine WP.seq (WP.mono ((hs_piece hP hF hS).ok σ s4 hpre h4) fun s5 h5 => ?_)
  exact WP.seq (WP.mono ((onesOk_piece hF).ok σ s5 hpre h5) fun s6 h6 => kbranch_ok (by have := hF.l; omega_arith) h6)

theorem iter_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : IL p STK σ t s) :
    WP isa (iter P p) s (LP p STK σ t) := by
  unfold iter
  refine WP.seq (WP.mono ((commit_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hF hS h1) fun s2 h2 => ?_)
  refine WP.seq (WP.ite _ (eval_nonzero_w s2 .r3) (fun hb => ?_) fun hb => ?_)
  · have h1' : (s2.gpr .r3).setWidth 32 = 1 := by
      rcases h2.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hF hS hpre ⟨h2.c, (h2.ok h1').1, (h2.ok h1').2⟩) fun s' h' =>
      dec_end hp (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (eb_ok h2 (by simpa using hb)) fun s' h' => dec_end hp (.inr (.inr h'))

omit hP hF hS in
theorem loopInit_ok {σ s : State} (h : IK p STK σ s) :
    WP isa (.block [.li .r27 0, .li .r25 814]) s (IL p STK σ 0) := by
  rw [show ([.li .r27 0, .li .r25 814] : List Instr) = [.li .r27 0] ++ [.li .r25 814] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .r27 (by decide) s) fun s1 w1 => WP.mono (li_ok .r25 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2,
    by rw [w2.2.1 .r27 (by decide), w1.1, Nat.mul_zero], w2.1, by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {s : State} (h : IK p STK σ s) :
    WP isa (Impl.MlDsa.PPC64LE.Sign.signLoop P p) s (XS p STK σ) := by
  unfold Impl.MlDsa.PPC64LE.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p STK σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hF hS hp hpre hs) fun s' h' => ?_
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [eval_nonzero]; exact congrArg some (bne_iff_ne.mpr hz), 814 - (t + 1), by have := hs.t_lt; omega_arith, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [eval_nonzero, hz]; rfl, hX⟩

end

end VG.Proof.MlDsa.PPC64LE.Sign
