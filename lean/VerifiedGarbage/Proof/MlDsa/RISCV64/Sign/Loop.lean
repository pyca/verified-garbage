module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Checks
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA signing on RISC-V: the rejection sampling loop

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseL.lean`). An iteration
(`iter_ok`) either continues, with the next iteration's head (`IL`), or ends
the loop (`XS`): with `s4 = 1` when it passed, as `signIteration` does
within `maxBounds` after the iterations before were rejected; with
`s4 = 0` when `signLoop` returns nothing within `minBounds` (its
`SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (passF zF amat Rej ParamsOk signIteration_eqF signLoop_min_none signCommit_eq)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem zx_set32 (x : BitVec 64) : (zx x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [zx, BitVec.toNat_setWidth]
  omega

/-- The result of a call, the low word of `a0`, zero-extended. -/
theorem zxBlk_ok (s : State) :
    WP isa (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32]) s fun s' =>
      s'.gpr .a0 = zx (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  mrun []
  exact ⟨KeyGen.zx_shift _, fun r hr => by simp only [hr, ite_false]⟩

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
  r01 : (s.gpr .a0).setWidth 32 = 0 ∨ (s.gpr .a0).setWidth 32 = 1
  ok : (s.gpr .a0).setWidth 32 = 1 → PolyIs s.mem (SL p STK σ 0) (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .a0).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

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
    ⟨sptr_ok rfl (by decide), by csep hF⟩, show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide,
    by csep hF, by csep hF, by csep hF, hF.bp, ⟨hc.1, by omega_arith, hF.tau⟩, by salsep, by salsep⟩

theorem ball_ok {t : Nat} {σ s : State} (h : ICd p STK t σ s) :
    WP isa (ballAt P (cLen p) p.τ cP) s (IB p STK σ t) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hb := h.1.w1b
  unfold ballAt
  refine ball_okX hP h.1.l.k.sc.site hS (ball_m hF) fun s' k' hred hout hmax => ?_
  have hct : bytesAt s.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) := h.2
  rw [hct] at hout hmax
  refine ⟨⟨h.1.keep k' (by csep hF) (k'.cs .s5 (by decide)) (k'.cs .s7 (by decide)), ?_⟩, ?_,
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
    (hg : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨hs.ok, hs.len, hs.w0, hs.w1, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s1168, by rw [hsp]; exact hs.spk, by rw [hsp]; exact hs.al, hs.al0,
    by rw [hg .s11 (by decide)]; exact hs.s11, by rw [hg .s10 (by decide)]; exact hs.s10,
    by rw [hg .s9 (by decide)]; exact hs.s9, by rw [hg .s8 (by decide)]; exact hs.s8,
    by rw [hwr]; exact hs.cw, by rw [hwr, hrd]; exact hs.cr⟩, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hs' => ?_, by rw [hm]; exact h.sav, by rw [hm]; exact h.sk, by rw [hm]; exact h.mu, h.pre,
    by rw [hg .s3 (by decide)]; exact h.s3, by rw [hm]; exact h.cache⟩
  have : r ∉ [.a0, .s4, .s5, .s6, .s7] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl)
    · simp [preserved] at hr
    all_goals simp [savedTop] at hs'
  rw [hg r this]; exact h.pres r hr hs'

theorem IK.of_regs {p : Params} {STK : Nat} {σ s s' : State} (h : IK p STK σ s)
    (hg : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : IK p STK σ s' :=
  ⟨h.sc.of_regs hg hm hrd hwr hsp, h.ok, by rw [hm]; exact h.A, by rw [hm]; exact h.rpp, by rw [hm]; exact h.s1,
    by rw [hm]; exact h.s2, by rw [hm]; exact h.t0⟩

/-- A block that writes one register `d` (one of `a0`, `s4`–`s7`) with `v`. -/
abbrev W1 (d : Reg) (v : BitVec 64) (s s' : State) : Prop :=
  s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem W1.of_regs {d : Reg} (hd : d ∈ [.a0, .s4, .s5, .s6, .s7]) {v : BitVec 64} {s s' : State}
    (h : W1 d v s s') : ∀ r, r ∉ [.a0, .s4, .s5, .s6, .s7] → s'.gpr r = s.gpr r :=
  fun r hr => h.2.1 r fun e => hr (e ▸ hd)

theorem li_ok (d : Reg) {v : Nat} (hv : v < 2048) (s : State) :
    WP isa (.block [.li d v]) s (W1 d (BitVec.ofNat 64 v) s) := by
  mrun [hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem addi_ok {d : Reg} {v : Nat} (hv : v < 2048) (s : State) :
    WP isa (.block [.addi d d v]) s (W1 d (s.gpr d + BitVec.ofNat 64 v) s) := by
  mrun [hv]
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem subi_ok {d : Reg} (s : State) :
    WP isa (.block [.addi d d (-1)]) s (W1 d (s.gpr d - BitVec.ofNat 64 1) s) := by
  mrun []
  exact ⟨by simp, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩

theorem bit_pos {a : Prop} [Decidable a] (h : a) : bit a = 1 := ifp h _ _
theorem bit_neg {a : Prop} [Decidable a] (h : ¬ a) : bit a = 0 := ifn h _ _

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `s5 = 1`. -/
structure EP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  ct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t)
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)
  h : ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  pass : PassV p σ (p.ℓ * t)
  s4 : s.gpr .s4 = 1
  s5 : s.gpr .s5 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `s5 = 814 - t`. -/
structure EF (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  s7 : s.gpr .s7 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  fail : ¬ PassV p σ (p.ℓ * t)
  s4 : s.gpr .s4 = 0
  t_lt : t < 814
  rej : RejT p σ t

/-- `SampleInBall` did not finish within `minBounds`: `s4 = 0`, `s5 = 1`. -/
structure EB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p STK σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  s4 : s.gpr .s4 = 0
  s5 : s.gpr .s5 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- The loop ended: in `s4`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (STK : Nat) (σ : State) (s : State) : Prop where
  k : IK p STK σ s
  r01 : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1
  pass : s.gpr .s4 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ (p.ℓ * t) ∧
    (∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ (p.ℓ * t) r)) ∧
    ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ (p.ℓ * t) i]
  fail : s.gpr .s4 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .s5 ≠ 0 ∧ IL p STK σ (t + 1) s) ∨ (s.gpr .s5 = 0 ∧ XS p STK σ s)

theorem kthen_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : KO p STK σ t s)
    (hb : s.gpr .s4 ≠ 0) : WP isa (.block [.li .s5 1]) s (EP p STK σ t) := by
  refine WP.mono (li_ok .s5 (by decide) s) fun s' w => ?_
  have hpass : PassV p σ (p.ℓ * t) := by
    by_contra hc
    rw [h.s4, bit_neg hc] at hb; exact hb rfl
  have e24 : s.gpr .s4 = 1 := by rw [h.s4, bit_pos hpass]
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.2.2.1]; exact h.b.ct, fun r hr => by rw [w.2.2.1]; exact h.z hpass r hr,
    fun i hi => by rw [w.2.2.1]; exact h.h hpass i hi, h.b.some, hpass,
    by rw [w.2.1 .s4 (by decide)]; exact e24, w.1, h.b.l.t_lt, h.b.l.rej⟩

theorem kelse_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2048) (h : KO p STK σ t s)
    (hb : s.gpr .s4 = 0) : WP isa (.block [.addi .s7 .s7 p.ℓ]) s (EF p STK σ t) := by
  refine WP.mono (addi_ok hl s) fun s' w => ?_
  have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => by
    rw [h.s4, bit_pos hp] at hb; exact absurd hb (by decide)
  exact ⟨h.b.l.k.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2,
    by rw [w.1, h.b.l.s7, ← BitVec.ofNat_add, Nat.mul_succ], by rw [w.2.1 .s5 (by decide)]; exact h.b.l.s5,
    h.b.some, hfail, by rw [w.2.1 .s4 (by decide), h.s4, bit_neg hfail], h.b.l.t_lt, h.b.l.rej⟩

theorem kbranch_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (hl : p.ℓ < 2048)
    (h : KO p STK σ t s) :
    WP isa (ifOkElse (.block [.li .s5 1]) (.block [.addi .s7 .s7 p.ℓ])) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' :=
  WP.ite _ (Steps.eval_nonzero s .s4) (fun hb => WP.mono (kthen_ok h (by simpa using hb)) fun _ h => .inl h)
    fun hb => WP.mono (kelse_ok hl h (by simpa using hb)) fun _ h => .inr h

/-- `IB` after the result is zero-extended. -/
theorem IB.zx {p : Params} {STK : Nat} {σ : State} {t : Nat} {s s' : State} (h : IB p STK σ t s)
    (w : s'.gpr .a0 = zx (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp) : IB p STK σ t s' := by
  obtain ⟨g3, go, m3, rd3, wr3, sp3⟩ := w
  have k3 : Kept ((slay2 p STK σ).RL []) s s' :=
    ⟨fun r hr => go r (by rintro rfl; simp [preserved] at hr), sp3, rd3, wr3, by rw [m3]; exact Frame.refl _ _⟩
  have e32 : (s'.gpr .a0).setWidth 32 = (s.gpr .a0).setWidth 32 := by rw [g3, zx_set32]
  exact ⟨⟨h.c.1.keep k3 rfl (go _ (by decide)) (go _ (by decide)), by rw [m3]; exact h.c.2⟩,
    by rw [e32]; exact h.r01, fun h1 => by rw [m3]; exact h.ok (by rw [← e32]; exact h1),
    fun h0 => h.bad (by rw [← e32]; exact h0)⟩

theorem zx_zero {x : BitVec 64} (h : x.setWidth 32 = 0) : zx x = 0 := by rw [zx, h]; rfl

theorem eb_ok {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : IB p STK σ t s)
    (h0 : (s.gpr .a0).setWidth 32 = 0) : WP isa (.block [.li .s4 0, .li .s5 1]) s (EB p STK σ t) := by
  rw [show ([.li .s4 0, .li .s5 1] : List Instr) = [.li .s4 0] ++ [.li .s5 1] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .s4 (by decide) s) fun s1 w1 => WP.mono (li_ok .s5 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.c.1.l.k.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2, h.bad h0,
    by rw [w2.2.1 .s4 (by decide)]; exact w1.1, w2.1, h.c.1.l.t_lt, h.c.1.l.rej⟩

theorem dec_end {p : Params} {STK : Nat} (hp : ParamsOk p) {σ : State} {t : Nat} {s : State}
    (h : EP p STK σ t s ∨ EF p STK σ t s ∨ EB p STK σ t s) :
    WP isa (.block [.addi .s5 .s5 (-1)]) s (LP p STK σ t) := by
  refine WP.mono (subi_ok s) fun s' w => ?_
  have hk : IK p STK σ s := by rcases h with h | h | h <;> exact h.k
  have K := hk.of_regs (W1.of_regs (by decide) w) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2
  have e24 : s'.gpr .s4 = s.gpr .s4 := w.2.1 .s4 (by decide)
  have em : s'.mem = s.mem := w.2.2.1
  rcases h with h | h | h
  · -- passed
    have z : s'.gpr .s5 = 0 := by rw [w.1, h.s5]; decide
    refine .inr ⟨z, K, .inr (e24.trans h.s4), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [em]; exact h.ct, fun r hr => by rw [em]; exact h.z r hr, fun i hi => by rw [em]; exact h.h i hi⟩,
      fun h0 => absurd (h0.symm.trans (e24.trans h.s4)) (by decide)⟩
  · -- rejected
    have ht := h.t_lt
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    have e25 : s'.gpr .s5 = BitVec.ofNat 64 (814 - (t + 1)) := by
      rw [w.1, h.s5, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
    by_cases ht' : t = 813
    · subst ht'
      refine .inr ⟨by rw [e25]; decide, K, .inl (e24.trans h.s4),
        fun h1 => absurd (h1.symm.trans (e24.trans h.s4)) (by decide), fun _ => loop_none_exh hr⟩
    · refine .inl ⟨by rw [e25]; intro e; have := congrArg BitVec.toNat e; simp at this; omega_arith,
        ⟨K, by rw [w.2.1 .s7 (by decide)]; exact h.s7, e25, by omega_arith, hr⟩⟩
  · -- `SampleInBall` failed
    have z : s'.gpr .s5 = 0 := by rw [w.1, h.s5]; decide
    exact .inr ⟨z, K, .inl (e24.trans h.s4), fun h1 => absurd (h1.symm.trans (e24.trans h.s4)) (by decide),
      fun _ => loop_none_ball h.rej h.none⟩

/-! ## An iteration, and the loop -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem checksR0_ok {σ : State} (hpre:SPre p STK σ) {t : Nat} {s : State} (h:IQ p STK σ t 0 0 s) :
    WP isa (checksR0 P p) s (KO p STK σ t) := by
  unfold checksR0
  refine WP.seq (WP.mono (seqOk_ok (I:=fun i=>IQ p STK σ t i i) p.k 0
    (fun i _ hi s hs=>(r0R_piece hP hF hS (by omega)).ok σ s hpre hs) s h) fun s₁ ⟨k,_,hk,hi,hd⟩=>?_)
  rw [Nat.zero_add] at hk hd
  apply WP.ite _ (Steps.eval_nonzero s₁ .s4)
  · intro hb
    have hn:s₁.gpr .s4≠0:=by simpa using hb
    have he:k=p.k:=hd.resolve_right hn
    subst he
    exact WP.seq (WP.mono ((hs_piece hP hF hS).ok σ s₁ hpre hi.ih) fun s₂ h₂=>(onesOk_piece hF).ok σ s₂ hpre h₂)
  · intro hb
    have hz:s₁.gpr .s4=0:=by simpa using hb
    have hn:¬PassV p σ (p.ℓ*t):=fun hp=>(bit_ne.mpr ⟨hp.1,hp.2.1⟩) ((IQ.done hk hi hd).symm.trans hz)
    exact WP.block_nil (rejected_ko hi.b hn hz)

theorem zchecks_ok {σ : State} (hpre:SPre p STK σ) {t : Nat} {s : State} (h:IZ p STK σ t 0 0 s) :
    WP isa (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p))) s (KO p STK σ t) := by
  refine WP.seq (WP.mono (seqOk_ok (I:=fun i=>IZ p STK σ t i i) p.ℓ 0
    (fun i _ hi s hs=>(zR_piece hP hF hS (by omega)).ok σ s hpre hs) s h) fun s₁ ⟨k,_,hk,hi,hd⟩=>?_)
  rw [Nat.zero_add] at hk hd
  apply WP.ite _ (Steps.eval_nonzero s₁ .s4)
  · intro hb
    have hn:s₁.gpr .s4≠0:=by simpa using hb
    have he:k=p.ℓ:=hd.resolve_right hn
    subst he
    exact checksR0_ok hP hF hS hpre hi.iq
  · intro hb
    have hz:s₁.gpr .s4=0:=by simpa using hb
    have hn:¬PassV p σ (p.ℓ*t):=fun hp=>(bit_ne.mpr hp.1) ((IZ.done hk hi hd).symm.trans hz)
    exact WP.block_nil (rejected_ko hi.b hn hz)

theorem checks_ok {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : KA p STK t σ s) :
    WP isa (checks P p) s fun s' => EP p STK σ t s' ∨ EF p STK σ t s' := by
  unfold checks
  refine WP.seq (WP.mono ((cntt_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (kinit_piece.ok σ s1 hpre h1) fun s2 h2 => ?_)
  exact WP.seq (WP.mono (zchecks_ok hP hF hS hpre h2) fun s₃ h₃=>kbranch_ok (by have := hF.l; omega) h₃)

theorem iter_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {t : Nat} {s : State} (h : IL p STK σ t s) :
    WP isa (iter P p) s (LP p STK σ t) := by
  unfold iter
  refine WP.seq (WP.mono ((commit_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hF hS h1) fun s2 h2 => ?_)
  refine WP.seq (WP.seq (WP.mono (zxBlk_ok s2) fun s3 ⟨g3, go, m3, rd3, wr3, sp3⟩ => ?_))
  have h3 : IB p STK σ t s3 := h2.zx ⟨g3, go, m3, rd3, wr3, sp3⟩
  refine WP.ite _ (Steps.eval_nonzero s3 .a0) (fun hb => ?_) fun hb => ?_
  · have h1' : (s3.gpr .a0).setWidth 32 = 1 := by
      rcases h3.r01 with e | e
      · have : s3.gpr .a0 = 0 := by rw [g3, zx, ← zx_set32, ← g3, e]; rfl
        rw [this] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hF hS hpre ⟨h3.c, (h3.ok h1').1, (h3.ok h1').2⟩) fun s' h' =>
      dec_end hp (h'.elim .inl (fun h => .inr (.inl h)))
  · have z : s3.gpr .a0 = 0 := by simpa using hb
    have z32 : (s3.gpr .a0).setWidth 32 = 0 := by rw [z]; rfl
    exact WP.mono (eb_ok h3 z32) fun s' h' => dec_end hp (.inr (.inr h'))

omit hP hF hS in
theorem loopInit_ok {σ s : State} (h : IK p STK σ s) :
    WP isa (.block [.li .s7 0, .li .s5 814]) s (IL p STK σ 0) := by
  rw [show ([.li .s7 0, .li .s5 814] : List Instr) = [.li .s7 0] ++ [.li .s5 814] from rfl, WP.block_append_iff]
  refine WP.mono (li_ok .s7 (by decide) s) fun s1 w1 => WP.mono (li_ok .s5 (by decide) s1) fun s2 w2 => ?_
  have k1 := h.of_regs (W1.of_regs (by decide) w1) w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.1 w1.2.2.2.2.2
  exact ⟨k1.of_regs (W1.of_regs (by decide) w2) w2.2.2.1 w2.2.2.2.1 w2.2.2.2.2.1 w2.2.2.2.2.2,
    by rw [w2.2.1 .s7 (by decide), w1.1, Nat.mul_zero], w2.1, by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok (hp : ParamsOk p) {σ : State} (hpre : SPre p STK σ) {s : State} (h : IK p STK σ s) :
    WP isa (Impl.MlDsa.RISCV64.Sign.signLoop P p) s (XS p STK σ) := by
  unfold Impl.MlDsa.RISCV64.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p STK σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hF hS hp hpre hs) fun s' h' => ?_
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [Steps.eval_nonzero]; exact congrArg some (bne_iff_ne.mpr hz), 814 - (t + 1), by have := hs.t_lt; omega_arith, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [Steps.eval_nonzero, hz]; rfl, hX⟩

end

end VG.Proof.MlDsa.RISCV64.Sign
