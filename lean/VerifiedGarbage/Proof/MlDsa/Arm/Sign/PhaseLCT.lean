module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-! ### `MlDsa.Arm.Sign.PhaseL`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on ARMv7: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `r11 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `r11 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

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
          (List.range p.k).map (hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
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
  rw [iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

/-- The loop ended: in `r11`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : IK p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  pass : s.gpr .r11 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) ∧ Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) ∧
    HFam s 5 p.k (Hv p σ (p.ℓ * t))
  fail : s.gpr .r11 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `r11 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  r11 : s.gpr .r11 = 0
  cnt : s.mem.readW (pa s (sc oCNT)) 32 = 1
  t_lt : t < 814
  rej : RejT p σ t

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.z = false ∧ IL p D σ (t + 1) s) ∨ (s.z = true ∧ XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  inB (sgW p) (sc oCNT) 4 && inB (sgB p) (sc oCNT) 4 && ikChk p [(sc oCNT, 4)] && keepB (sgB p) [(sc oCNT, 4)] (sc oKAP) 4 &&
    keepB (sgB p) [(sc oCNT, 4)] (sc oCT) (cLen p) && famChk (sgB p) [(sc oCNT, 4)] (yBase p) p.ℓ &&
    famChk (sgB p) [(sc oCNT, 4)] 5 p.k && icwChk p [] p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    keepB (sgB p) [] cP 1024 && ikChk p [] &&
    keepB (sgB p) [(sc oKAP, 4)] (sc oCNT) 4 && inB (sgW p) (sc oKAP) 4 && ikChk p [(sc oKAP, 4)]

theorem lChk_ok {p : Params} (h : Ok3 p) : lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem ofNat32_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 32) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- `CNT ← CNT - 1`, setting Z when it reaches 0. -/
abbrev decCnt : List Instr := [.ldr .r0 .r7 oCNT, .subs .r0 .r0 (.imm 1), .str .r0 .r7 oCNT]

/-- `decW_ok` in the layout. -/
theorem decCnt_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
    (w1 : inB wbs (sc oCNT) 4 = true) :
    WP isa (.block decCnt) s fun s' => (s'.mem = s.mem.writeW (pa s (sc oCNT)) (s.mem.readW (pa s (sc oCNT)) 32 - 1) ∧
      s'.z = (s.mem.readW (pa s (sc oCNT)) 32 - 1 == 0)) ∧ PPostB D s s' [(sc oCNT, 4)] ∧ CS s s' := by
  have ac : State.addr (s.gpr .r7 + BitVec.ofNat 32 oCNT) = pa s (sc oCNT) := L.pa32W (p := sc oCNT) w1 (by decide)
  refine WP.mono (decW_ok (sc oCNT) (by decide) (by decide) s (by rw [ac]; exact L.iW w1))
    fun s' ⟨⟨hm, hz⟩, hg, hrd, hwr, hsp⟩ => ?_
  rw [ac] at hm hz
  have hf : Frame [⟨pa s (sc oCNT), 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcs : CS s s' := fun r hr _ => hg r fun h => by
    simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
  exact ⟨⟨hm, hz⟩, PostB.of_cs hcs hrd hwr hsp hf, hcs⟩

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : EP p D σ t s ∨ EF p D σ t s ∨ EB p D σ t s) :
    WP isa (.block decCnt) s (LP p D σ t) := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (decCnt_okB L w1) fun s' ⟨⟨hm, hz⟩, hP, hcs⟩ => ?_
  have K := hk.step hP k1
  have e15 : s'.gpr .r11 = s.gpr .r11 := hcs _ (by decide) (by decide)
  rcases h with h | h | h
  · -- passed
    rw [h.cnt] at hz
    refine .inr ⟨by rw [hz]; rfl, K, .inr (e15.trans h.r11), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.r11)) (by decide)⟩
  · -- rejected
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    rw [h.cnt, ofNat32_sub_one (by have := h.t_lt; omega_using [this]) (by have := h.t_lt; omega_using []),
      ofNat32_beq_zero (by have := h.t_lt; omega_using [])] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
        fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => loop_none_exh hr⟩
    · have hne : decide (814 - t - 1 = 0) = false := by have := h.t_lt; simp only [decide_eq_false_iff_not]; omega_using [ht, this]
      refine .inl ⟨by rw [hz, hne], K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega_using [ht, this], hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self32, h.cnt,
        ofNat32_sub_one (by have := h.t_lt; omega_using [this]) (by have := h.t_lt; omega_using []), Nat.sub_sub]
  · -- `SampleInBall` failed
    rw [h.cnt] at hz
    exact .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
      fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => loop_none_ball h.rej h.none⟩

theorem cmp0_ok (s : State) : WP isa (.block [.cmp .r0 (.imm 0)]) s fun s₁ =>
    s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r0 == 0) := by
  run_block []
  simp

theorem IB.step0 {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : IB p D σ t s) (hc : lChk p = true)
    (hP : PPostB D s s' []) (hax : s'.gpr .r0 = s.gpr .r0) : IB p D σ t s' := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := h.c.l.st.lay
  refine ⟨h.c.step hP c1, by rw [L.keepBytes hP c2, h.ct], hax ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (hax ▸ h0)⟩
  obtain ⟨hc', hs⟩ := h.ok (hax ▸ h1)
  exact ⟨L.keepPoly hP c3 hc', hs⟩

theorem test_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s fun s' =>
      (IB p D σ t s' ∧ s'.z = (s'.gpr .r0 == 0)) ∧ s'.gpr .r0 = s.gpr .r0 := by
  refine WP.mono (cmp0_ok s) fun s3 ⟨g3, hm3, hrd, hwr, hsp, hz3⟩ => ?_
  have hcs : CS s s3 := fun r _ _ => by rw [g3]
  have hP3 : PPostB D s s3 [] := PostB.of_cs hcs hrd hwr hsp (by rw [hm3]; exact Frame.refl _ _)
  have hax3 : s3.gpr .r0 = s.gpr .r0 := by rw [g3]
  exact ⟨⟨h.step0 hc4 hP3 hax3, by rw [hz3, hax3]⟩, hax3⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h1 : s.gpr .r0 = 1) : KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem mov0_ok (s : State) : WP isa (.block [.mov .r11 (.imm 0)]) s fun s' => s'.gpr .r11 = 0 ∧ Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem else_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h0 : s.gpr .r0 = 0) :
    WP isa (.block (([.mov .r11 (.imm 0)] : List Instr) ++ setW (sc oCNT) 1)) s (EB p D σ t) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s4 ⟨h154, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB11 k4 _).1
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (setW_okB L4 (by decide) (by decide) w1) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5 _ (by decide) (by decide), h154],
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self32]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : lChk p = true) {σ : State} {s : State} (hk : IK p D σ s) :
    WP isa (.block decCnt) s fun s' =>
      s'.z = (s.mem.readW (pa s (sc oCNT)) 32 - 1 == 0) ∧ s'.gpr .r11 = s.gpr .r11 ∧
      bytesAt s'.mem (pa s' (sc oCT)) (cLen p) = bytesAt s.mem (pa s (sc oCT)) (cLen p) ∧
      ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (decCnt_okB L w1) fun s' ⟨⟨_, hz⟩, hP, hcs⟩ => ?_
  exact ⟨hz, hcs _ (by decide) (by decide), L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem iter_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : IL p D σ t s) : WP isa (iter P p) s (LP p D σ t) := by
  unfold iter
  refine WP.seq (WP.mono (commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hc2 h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (test_ok hc4 h2) fun s3 ⟨⟨I3, hz3⟩, _⟩ => ?_)
  refine WP.seq (WP.ite (M := isa) (!(s3.gpr .r0 == 0)) (show some (!s3.z) = _ by rw [hz3])
    (fun hb => ?_) fun hb => ?_)
  · have h1 : s3.gpr .r0 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hc3 (I3.ka h1)) fun s' h' => dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (else_ok hc4 I3 (by simpa using hb)) fun s' h' => dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {s : State} (h : IK p D σ s) :
    WP isa (.block (setW (sc oKAP) 0 ++ setW (sc oCNT) 814)) s (IL p D σ 0) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (setW_okB L (by decide) (by decide) wk) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (setW_okB K1.d.im.st.lay (by decide) (by decide) w1) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self32]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self32], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {s : State}
    (h : IK p D σ s) : WP isa (Impl.MlDsa.Arm.Sign.signLoop P p) s (XS p D σ) := by
  unfold Impl.MlDsa.Arm.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [hev, hz]; rfl, 814 - (t + 1), by have := hs.t_lt; omega_using [hn, this], t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [hev, hz]; rfl, hX⟩

end VG.Proof.MlDsa.Arm.Sign

end

end

/-!
# ML-DSA signing on ARMv7: the loop leaks what `signLeak` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoop p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := leakL p σ₁ (1000 - t) (p.ℓ * t) = leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (map_toNat_inj h1), hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoop p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1v p σ₁)) ((List.range p.k).map (S2v p σ₁))
      ((List.range p.k).map (T0v p σ₁)) (muOf σ₁) (rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoop p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1v p σ₂)) ((List.range p.k).map (S2v p σ₂))
      ((List.range p.k).map (T0v p σ₂)) (muOf σ₂) (rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega_using [ht]]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakF_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakF_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega_using [], Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    outTag (iterF p σ maxBounds κ) = if PassV p σ κ then
      1 :: ((List.range p.k).map (Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [iterF_eq hp, cV_eq hs, Option.map_some]
  by_cases hv : PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) :
    PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t) := by
  have e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

/-- `signRejectTag`'s value: which check failed, and for those of `z` and
`r₀` the first polynomial that failed it. -/
def tagFn (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (x y : Nat) : Nat :=
  if ¬ a then 5 * x else if ¬ b then 2 + 5 * y else if ¬ c then 3 else 4

theorem tagFn_eq {a b c a' b' c' : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable a'] [Decidable b']
    [Decidable c'] {x y x' y' : Nat} (h : tagFn a b c x y = tagFn a' b' c' x' y') :
    (a ↔ a') ∧ (¬ a → x = x') ∧ (a ∧ b ↔ a' ∧ b') ∧ (a → ¬ b → y = y') := by
  unfold tagFn at h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    by_cases hc' : c' <;> simp only [ha, hb, hc, ha', hb', hc', not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega_using [h])

/-- The first polynomial of `z` that fails its check, or `ℓ`. -/
abbrev zFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.ℓ).findIdx fun r => decide (normRq [Zv p σ κ r] ≥ p.γ₁ - p.β)

/-- The first polynomial of `r₀` that fails its check, or `k`. -/
abbrev rFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.k).findIdx fun i => decide (normRq [R0v p σ κ i] ≥ p.γ₂ - p.β)

theorem tag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    signRejectTag p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
      ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ =
      tagFn (ZOk p σ κ) (R0Ok p σ κ) (∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) (zFirst p σ κ) (rFirst p σ κ) := by
  rw [signRejectTag_eqF hp, show ctF p (Am p σ) (muOf σ) (rppOf p σ) κ = CTv p σ κ from rfl, cV_eq hs]
  rfl

/-- The first `r ≤ n` polynomials pass a check exactly when the first that
fails it comes at `r` or later. -/
theorem prefix_ok {n B : Nat} (f : Nat → Poly) {r : Nat} (hr : r ≤ n) :
    (∀ j < r, normRq [f j] < B) ↔ r ≤ (List.range n).findIdx fun j => decide (normRq [f j] ≥ B) := by
  rw [← prefix_findIdx n _ hr]
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]

/-- Two runs that agree on what the iterations from `t` leak agree on the
checks of iteration `t` that pass, polynomial by polynomial. -/
theorem leq_agree (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) : ChecksAgree p t σ₁ σ₂ := by
  have hpass := leq_pass hp h ht hs₁ hs₂
  by_cases h1 : PassV p σ₁ (p.ℓ * t)
  · have h2 := hpass.mp h1
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega_using [hr, hj])) (fun j hj => h2.1 j (by omega_using [hr, hj])),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega_using [hi, hj])⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega_using [hi, hj])⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    have e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [tag_eq hp hs₁, tag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := tagFn_eq e
    refine ⟨fun r hr => ?_, fun i hi => ?_, hpass⟩
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · exact iff_of_true (fun j hj => hz j (by omega_using [hr, hj])) (fun j hj => ea.mp hz j (by omega_using [hr, hj]))
      · rw [prefix_ok _ hr, prefix_ok _ hr]; exact iff_of_eq (congrArg (r ≤ ·) (ex hz))
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · have hz' := ea.mp hz
        by_cases hr0 : R0Ok p σ₁ (p.ℓ * t)
        · have hr0' := (eab.mp ⟨hz, hr0⟩).2
          exact iff_of_true ⟨hz, fun j hj => hr0 j (by omega_using [hi, hj])⟩ ⟨hz', fun j hj => hr0' j (by omega_using [hi, hj])⟩
        · rw [and_iff_right hz, and_iff_right hz', prefix_ok _ hi, prefix_ok _ hi]
          exact iff_of_eq (congrArg (i ≤ ·) (ey hz hr0))
      · exact iff_of_false (fun h => hz h.1) (fun h => hz (ea.mpr h.1))

theorem leq_hints (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : PassV p σ₁ (p.ℓ * t)) (h2 : PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact hints_inj (by simp) (List.cons.inj e).2

end

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (signK p D).pre σ₁ → (signK p D).pre σ₂ → (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

theorem z_of_eval {s : State} {b : Bool} (h : isa.eval .ne s = some b) : s.z = !b := by
  have e : some (!s.z) = some b := h
  cases hz : s.z <;> cases b <;> simp_all

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.z = false) :
    IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · rw [hz] at h; cases h

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.z = true) :
    XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · rw [hz] at h; cases h
  · exact h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  RS p D (fun _ _ => True) (XS p D) x y ∧ x.gpr .r11 = y.gpr .r11 ∧
    (x.gpr .r11 = 1 → bytesAt x.mem (pa x (sc oCT)) (cLen p) = bytesAt y.mem (pa y (sc oCT)) (cLen p) ∧
      ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.z = y.z ∧ (x.z = false → RS p D (LeakEq p (t + 1)) (fun σ s => IL p D σ (t + 1) s) x y) ∧
    (x.z = true → OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True)
      (.block decCnt) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (decF hc (h.elim (·.k) (·.k))))
    (RelCT.mono (block_tr (rs := [.r7]) rfl (P := fun x y => LRel D (sgR p) (sgW p) x y) fun x y h => lrel_r7 h)
      (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.z = true := by rw [z₁, e₁.cnt]; rfl
    have zy : y'.z = true := by rw [z₂, e₂.cnt]; rfl
    refine ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r11, e₂.r11], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact leq_ct he e₁.t_lt,
      Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.z = y'.z := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.r11, f₂.r11], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.r11)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True)
      (.block decCnt) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (.inr (.inr h))) (decF hc h.k))
    (RelCT.mono (block_tr (rs := [.r7]) rfl (P := fun x y => LRel D (sgR p) (sgW p) x y) fun x y h => lrel_r7 h)
      (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.z = true := by rw [z₁, e₁.cnt]; rfl
  have zy : y'.z = true := by rw [z₂, e₂.cnt]; rfl
  exact ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r11, e₂.r11],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.r11)) (by decide)⟩⟩

theorem ax_one {s : State} (hz : s.z = (s.gpr .r0 == 0))
    (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) (hb : isa.eval .ne s = some true) : s.gpr .r0 = 1 := by
  have e := z_of_eval hb
  rcases hr with h | h
  · rw [hz, h] at e; cases e
  · exact h

theorem ax_zero {s : State} (hz : s.z = (s.gpr .r0 == 0)) (hb : isa.eval .ne s = some false) : s.gpr .r0 = 0 := by
  have e := z_of_eval hb
  rw [hz] at e
  simpa using e

theorem iter_tr {P : Prims} (hP : PrimsOk P D) (hp : ParamsOk p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc4 : lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (RS p D (LeakEq p t) fun σ s => IL p D σ t s) (iter P p) (IX p D t) := by
  have hc2' := hc2
  simp only [bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iter
  refine RelCT.seq (commit_tr hP hc1) ?_
  refine RelCT.seq (R := fun (x y : State) => RS p D (LeakEq p t) (fun σ s => IB p D σ t s) x y ∧
      x.gpr .r0 = y.gpr .r0)
    (RelCT.mono (liftQ (G := fun _ _ => True) (J := fun σ s => IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun (x y : State) => RS p D (LeakEq p t)
      (fun σ s => IB p D σ t s ∧ s.z = (s.gpr .r0 == 0)) x y ∧
      x.gpr .r0 = y.gpr .r0)
    (liftQ (F := fun s s' => s'.gpr .r0 = s.gpr .r0)
      (fun _ _ _ h => test_ok hc4 h)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hg j₁ j₂ f₁ f₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, by rw [f₁, f₂, hg]⟩) ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  refine RelCT.seq (R := fun (x y : State) => (RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True) ∨
      (RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (relOr (endPF_tr hp hc4) (endB_tr hp hc4))
  · rintro x y ⟨⟨σ₁, σ₂, _, _, _, _, ⟨_, z₁⟩, ⟨_, z₂⟩⟩, hg⟩
    rw [hev, hev, z₁, z₂, hg]
  · refine RelCT.mono (checks_tr hP hc3 fun σ₁ σ₂ he s₁ s₂ => leq_agree hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := ax_one z₁ i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (liftT (I := fun σ s => IB p D σ t s ∧ s.gpr .r0 = 0)
      (J := fun σ s => EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => else_ok hc4 h.1 h.2)
      (block_tr rfl fun x y h => lrel_r7 h))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := ax_zero z₁ hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : PrimsOk P D) (hp : ParamsOk p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc4 : lChk p = true) :
    RelCT isa (RS p D (LeakEq p 0) fun σ s => IK p D σ s) (Impl.MlDsa.Arm.Sign.signLoop P p) (OX p D) := by
  unfold Impl.MlDsa.Arm.Sign.signLoop
  refine RelCT.seq (liftT (J := fun σ s => IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => loopInit_ok hc4 h)
    (block_tr rfl fun x y h => lrel_r7 h)) ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ RS p D (LeakEq p t) (fun σ s => IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := iter_tr hP hp hc1 hc2 hc3 hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [hev, hev, hz], fun h => ho (z_of_eval h), fun h =>
    ⟨814 - (t + 1), by omega_using [hn, ht], t + 1, rfl, hc (z_of_eval h)⟩⟩

end

end VG.Proof.MlDsa.Arm.Sign
