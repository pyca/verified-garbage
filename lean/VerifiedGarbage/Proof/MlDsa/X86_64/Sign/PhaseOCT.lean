module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly

/-! ### `MlDsa.X86_64.Sign.PhaseL`, which only this module used -/

section

/-!
# ML-DSA signing on x86-64: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `r15 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `r15 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
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

/-- The loop ended: in `r15`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : IK p D σ s
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  pass : s.gpr .r15 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) ∧ Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) ∧
    HFam s 5 p.k (Hv p σ (p.ℓ * t))
  fail : s.gpr .r15 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `r15 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  r15 : s.gpr .r15 = 0
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = 1
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
  (s.zf = some false ∧ IL p D σ (t + 1) s) ∨ (s.zf = some true ∧ XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  inB (sgW p) (sc oCNT) 8 && inB (sgB p) (sc oCNT) 8 && ikChk p [(sc oCNT, 8)] && keepB (sgB p) [(sc oCNT, 8)] (sc oKAP) 8 &&
    keepB (sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) && famChk (sgB p) [(sc oCNT, 8)] (yBase p) p.ℓ &&
    famChk (sgB p) [(sc oCNT, 8)] 5 p.k && icwChk p [] p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    keepB (sgB p) [] cP 1024 && ikChk p [] &&
    keepB (sgB p) [(sc oKAP, 8)] (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 && ikChk p [(sc oKAP, 8)]

theorem lChk_ok {p : Params} (h : Ok3 p) : lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem ofNat64_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  VG.Proof.MlKem.X86_64.ofNat64_pred h hk

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : EP p D σ t s ∨ EF p D σ t s ∨ EB p D σ t s) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) s (LP p D σ t) := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (decQ_ok (sc oCNT) (by decide) s (L.iW w1) (L.iR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP', hcs⟩ := postB_of_keep (D := D) k (by decide) hf
  have hP : PPostB D s s' [(sc oCNT, 8)] := hP'
  have K := hk.step hP k1
  have e15 : s'.gpr .r15 = s.gpr .r15 := hcs _ (by decide)
  rcases h with h | h | h
  · -- passed
    rw [h.cnt] at hz
    refine .inr ⟨by rw [hz]; rfl, K, .inr (e15.trans h.r15), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.r15)) (by decide)⟩
  · -- rejected
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    rw [h.cnt, ofNat64_sub_one (by have := h.t_lt; omega_using [this]) (by have := h.t_lt; omega_using []),
      VG.Proof.MlKem.X86_64.ofNat64_beq_zero (by have := h.t_lt; omega_using [])] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r15),
        fun h1 => absurd (h1.symm.trans (e15.trans h.r15)) (by decide), fun _ => loop_none_exh hr⟩
    · have hne : decide (814 - t - 1 = 0) = false := by have := h.t_lt; simp only [decide_eq_false_iff_not]; omega_using [ht, this]
      refine .inl ⟨by rw [hz, hne], K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega_using [ht, this], hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self64, h.cnt,
        ofNat64_sub_one (by have := h.t_lt; omega_using [this]) (by have := h.t_lt; omega_using []), Nat.sub_sub]
  · -- `SampleInBall` failed
    rw [h.cnt] at hz
    exact .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r15),
      fun h1 => absurd (h1.symm.trans (e15.trans h.r15)) (by decide), fun _ => loop_none_ball h.rej h.none⟩

theorem testRax_ok (s : State) : WP isa (.block [.alu32 .test .rax (.reg .rax)]) s fun s₁ =>
    (s₁.mem = s.mem ∧ s₁.gpr .rax = s.gpr .rax ∧
      s₁.zf = some (((s.gpr .rax).setWidth 32 &&& (s.gpr .rax).setWidth 32) == 0)) ∧ Keep [.rax] s s₁ :=
  WP.keep [.rax] (by xrun) (Proof.MlKem.X86_64.writesOnly_of (by decide))

theorem IB.step0 {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : IB p D σ t s) (hc : lChk p = true)
    (hP : PPostB D s s' []) (hax : s'.gpr .rax = s.gpr .rax) : IB p D σ t s' := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := h.c.l.st.lay
  refine ⟨h.c.step hP c1, by rw [L.keepBytes hP c2, h.ct], hax ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (hax ▸ h0)⟩
  obtain ⟨hc', hs⟩ := h.ok (hax ▸ h1)
  exact ⟨L.keepPoly hP c3 hc', hs⟩

theorem test_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s) :
    WP isa (.block [.alu32 .test .rax (.reg .rax)]) s fun s' =>
      (IB p D σ t s' ∧ s'.zf = some ((s'.gpr .rax).setWidth 32 == 0)) ∧
        (s'.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32 := by
  refine WP.mono (testRax_ok s) fun s3 ⟨⟨hm3, hax3, hz3⟩, k3⟩ => ?_
  have hf3 : Frame [] s.mem s3.mem := by rw [hm3]; exact Frame.refl _ _
  obtain ⟨hP3', _⟩ := postB_of_keep (D := D) k3 (by decide) hf3
  have hP3 : PPostB D s s3 [] := hP3'
  rw [BitVec.and_self] at hz3
  exact ⟨⟨h.step0 hc4 hP3 hax3, by rw [hz3, hax3]⟩, by rw [hax3]⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h1 : (s.gpr .rax).setWidth 32 = 1) : KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem else_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h0 : (s.gpr .rax).setWidth 32 = 0) :
    WP isa (.block (([.mov32 .r15 (.imm 0)] : List Instr) ++ setQ (sc oCNT) 1)) s (EB p D σ t) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r15 = 0) (by xrun) (Proof.MlKem.X86_64.writesOnly_of (by decide)))
    fun s4 ⟨⟨hm4, h154⟩, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB15 k4 hm4 _).1
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (setQ_okB L4 (by decide) (by decide) w1) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5 _ (by decide), h154],
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self64]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : lChk p = true) {σ : State} {s : State} (hk : IK p D σ s) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) s fun s' =>
      s'.zf = some (s.mem.readW (pa s (sc oCNT)) 64 - 1 == 0) ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s' (sc oCT)) (cLen p) = bytesAt s.mem (pa s (sc oCT)) (cLen p) ∧
      ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (decQ_ok (sc oCNT) (by decide) s (L.iW w1) (L.iR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP', hcs⟩ := postB_of_keep (D := D) k (by decide) hf
  have hP : PPostB D s s' [(sc oCNT, 8)] := hP'
  exact ⟨hz, hcs _ (by decide), L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem iter_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc3' : ksChk2 p = true) (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : IL p D σ t s) : WP isa (iter P p) s (LP p D σ t) := by
  unfold iter
  refine WP.seq (WP.mono (commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hc2 h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (test_ok hc4 h2) fun s3 ⟨⟨I3, hz3⟩, _⟩ => ?_)
  refine WP.seq (WP.ite (!((s3.gpr .rax).setWidth 32 == 0)) (show s3.zf.map (!·) = _ by rw [hz3]; rfl)
    (fun hb => ?_) fun hb => ?_)
  · have h1 : (s3.gpr .rax).setWidth 32 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hc3 hc3' (I3.ka h1)) fun s' h' => dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (else_ok hc4 I3 (by simpa using hb)) fun s' h' => dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {s : State} (h : IK p D σ s) :
    WP isa (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) s (IL p D σ 0) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (setQ_okB L (by decide) (by decide) wk) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (setQ_okB K1.d.im.st.lay (by decide) (by decide) w1) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self64]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self64], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc3' : ksChk2 p = true) (hc4 : lChk p = true) {σ : State} {s : State}
    (h : IK p D σ s) : WP isa (Impl.MlDsa.X86_64.Sign.signLoop P p) s (XS p D σ) := by
  unfold Impl.MlDsa.X86_64.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hp hc1 hc2 hc3 hc3' hc4 hs) fun s' h' => ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [hev, hz]; rfl, 814 - (t + 1), by have := hs.t_lt; omega_using [hn, this], t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [hev, hz]; rfl, hX⟩

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-! ### `MlDsa.X86_64.Sign.PhaseLCT`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: the loop leaks what `signLeak` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
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

theorem zf_of_eval {s : State} {b : Bool} (h : s.zf.map (!·) = some b) : s.zf = some (!b) := by
  cases hz : s.zf with
  | none => rw [hz] at h; cases h
  | some c => rw [hz] at h; cases c <;> cases b <;> simp_all

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.zf = some false) :
    IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · rw [hz] at h; cases h

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.zf = some true) :
    XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · rw [hz] at h; cases h
  · exact h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  RS p D (fun _ _ => True) (XS p D) x y ∧ x.gpr .r15 = y.gpr .r15 ∧
    (x.gpr .r15 = 1 → bytesAt x.mem (pa x (sc oCT)) (cLen p) = bytesAt y.mem (pa y (sc oCT)) (cLen p) ∧
      ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.zf = y.zf ∧ (x.zf = some false → RS p D (LeakEq p (t + 1)) (fun σ s => IL p D σ (t + 1) s) x y) ∧
    (x.zf = some true → OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True)
      (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
        .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (decF hc (h.elim (·.k) (·.k))))
    (RelCT.mono (block_tr (rs := [.rbx]) rfl (P := fun x y => LRel D (sgR p) (sgW p) x y) fun x y h => lrel_rbx h)
      (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.zf = some true := by rw [z₁, e₁.cnt]; rfl
    have zy : y'.zf = some true := by rw [z₂, e₂.cnt]; rfl
    refine ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r15, e₂.r15], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact leq_ct he e₁.t_lt,
      Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.zf = y'.zf := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.r15, f₂.r15], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.r15)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True)
      (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
        .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (.inr (.inr h))) (decF hc h.k))
    (RelCT.mono (block_tr (rs := [.rbx]) rfl (P := fun x y => LRel D (sgR p) (sgW p) x y) fun x y h => lrel_rbx h)
      (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.zf = some true := by rw [z₁, e₁.cnt]; rfl
  have zy : y'.zf = some true := by rw [z₂, e₂.cnt]; rfl
  exact ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r15, e₂.r15],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.r15)) (by decide)⟩⟩

theorem ax_one {s : State} (hz : s.zf = some ((s.gpr .rax).setWidth 32 == 0))
    (hr : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1) (hb : isa.eval .ne s = some true) :
    (s.gpr .rax).setWidth 32 = 1 := by
  have e := zf_of_eval hb
  rcases hr with h | h
  · rw [hz, h] at e; cases e
  · exact h

theorem ax_zero {s : State} (hz : s.zf = some ((s.gpr .rax).setWidth 32 == 0)) (hb : isa.eval .ne s = some false) :
    (s.gpr .rax).setWidth 32 = 0 := by
  have e := zf_of_eval hb
  rw [hz] at e
  simpa using e

theorem iter_tr {P : Prims} (hP : PrimsOk P D) (hp : ParamsOk p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc3' : ksChk2 p = true) (hc4 : lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (RS p D (LeakEq p t) fun σ s => IL p D σ t s) (iter P p) (IX p D t) := by
  have hc2' := hc2
  simp only [bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iter
  refine RelCT.seq (commit_tr hP hc1) ?_
  refine RelCT.seq (R := fun x y => RS p D (LeakEq p t) (fun σ s => IB p D σ t s) x y ∧
      (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32)
    (RelCT.mono (liftQ (G := fun _ _ => True) (J := fun σ s => IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun x y => RS p D (LeakEq p t)
      (fun σ s => IB p D σ t s ∧ s.zf = some ((s.gpr .rax).setWidth 32 == 0)) x y ∧
      (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32)
    (liftQ (F := fun s s' => (s'.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32)
      (fun _ _ _ h => test_ok hc4 h)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hg j₁ j₂ f₁ f₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, by rw [f₁, f₂, hg]⟩) ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  refine RelCT.seq (R := fun x y => (RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True) ∨
      (RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (relOr (endPF_tr hp hc4) (endB_tr hp hc4))
  · rintro x y ⟨⟨σ₁, σ₂, _, _, _, _, ⟨_, z₁⟩, ⟨_, z₂⟩⟩, hg⟩
    rw [hev, hev, z₁, z₂, hg]
  · refine RelCT.mono (checks_tr hP hc3 hc3' fun σ₁ σ₂ he s₁ s₂ => leq_agree hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := ax_one z₁ i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (liftT (I := fun σ s => IB p D σ t s ∧ (s.gpr .rax).setWidth 32 = 0)
      (J := fun σ s => EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => else_ok hc4 h.1 h.2)
      (block_tr rfl fun x y h => lrel_rbx h))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := ax_zero z₁ hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : PrimsOk P D) (hp : ParamsOk p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc3' : ksChk2 p = true) (hc4 : lChk p = true) :
    RelCT isa (RS p D (LeakEq p 0) fun σ s => IK p D σ s) (Impl.MlDsa.X86_64.Sign.signLoop P p) (OX p D) := by
  unfold Impl.MlDsa.X86_64.Sign.signLoop
  refine RelCT.seq (liftT (J := fun σ s => IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => loopInit_ok hc4 h)
    (block_tr rfl fun x y h => lrel_rbx h)) ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ RS p D (LeakEq p t) (fun σ s => IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := iter_tr hP hp hc1 hc2 hc3 hc3' hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [hev, hev, hz], fun h => ho (zf_of_eval h), fun h =>
    ⟨814 - (t + 1), by omega_using [hn, ht], t + 1, rfl, hc (zf_of_eval h)⟩⟩

end

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-! ### `MlDsa.X86_64.Sign.Correct`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Sign.PhaseO`, which only this module used -/

section

/-!
# ML-DSA signing on x86-64: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`output_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega_using [hB, this]

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [VG.Proof.MlKem.X86_64.off_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_using []]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    pa s (pS (5 + i)) = pa s (Impl.MlDsa.X86_64.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show s.gpr .rbx + BitVec.ofNat 64 (oP (5 + i)) = s.gpr .rbx + BitVec.ofNat 64 (oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [VG.Proof.MlKem.X86_64.off_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega_using []]

theorem r14_bases (o : Nat) : ((.r14, o) : Ptr).1 ∈ bases := by
  show Reg.r14 ∈ bases; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : IK p D σ s
  z : Fam s (yBase p) p.ℓ (Zv p σ κ)
  h : HFam s 5 p.k (Hv p σ κ)
  sig : bytesAt s.mem (pa s (.r14, 0)) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r
  r15 : s.gpr .r15 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && famChk (sgB p) ws (yBase p) p.ℓ && famChk (sgB p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : ofam p ws = true)
    (hs : keepB (sgB p) ws (.r14, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .r15 = s.gpr .r15) :
    OS p D σ κ r s' := by
  simp only [ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.r15⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  copyChk (sgB p) (sgW p) (.r14, 0) (sc oCT) (cLen p) && ofam p [((.r14, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (sgB p) (sgW p) (yP p r) 1024 (.r14, sigZ p r) (zLen p) &&
      ofam p [((.r14, sigZ p r), zLen p)] && keepB (sgB p) [((.r14, sigZ p r), zLen p)] (.r14, 0) (cLen p + zLen p * r)) &&
    rwChk (sgB p) (sgW p) (hP 0) (256 * p.k * 4) (.r14, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    ikChk p [((.r14, sigH p), p.ω + p.k)] &&
    keepB (sgB p) [((.r14, sigH p), p.ω + p.k)] (.r14, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : Ok3 p) : oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : PrimsOk P D) {p : Params} (hc : oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : IK p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (h15 : s.gpr .r15 = 1) :
    WP isa (copy (.r14, 0) (sc oCT) (cLen p)) s fun s1 =>
      OS p D σ κ 0 s1 ∧ ∀ f, HFam s 5 p.k f → HFam s1 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (copy_okB L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1 _ (by decide), h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p D σ κ r s) (hpass : PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => OS p D σ κ (r + 1) s' ∧ ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.d.im.st.lay
  have hzr := h.z r hr
  refine WP.mono (bpAt_ok hPO Lh hbp hzl c1 hzr.1 (inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs' _ (by decide))
  have c2' := c2
  simp only [ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.r15⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, pa_add, Nat.zero_add,
    hP'.pa (r14_bases _), hb', hzr.2, zEnc, zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    hintOnes (hintAt s.mem (pa s (Impl.MlDsa.X86_64.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [hintAt_of (f := Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [pS_hint] at this,
    hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.X86_64.Sign.hP 0) (256 * p.k) p.ω (.r14, sigH p) (p.ω + p.k)) s fun s' =>
      IK p D σ s' ∧ bytesAt s'.mem (pa s' (.r14, 0)) p.sigLen = sigV p σ κ ∧ s'.gpr .r15 = 1 := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.d.im.st.lay
  refine WP.mono (hbpAt_ok hPO L2 hhp ch (hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3 _ (by decide), h2.r15]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, hintAt_of (f := Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [pS_hint] at this]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : IK p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (hpass : PassV p σ κ)
    (h15 : s.gpr .r15 = 1) :
    WP isa (output P p) s fun s' => IK p D σ s' ∧ bytesAt s'.mem (pa s' (.r14, 0)) p.sigLen = sigV p σ κ ∧
      s'.gpr .r15 = 1 := by
  unfold output
  refine WP.seq (WP.mono (outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (packZ_ok hPO hc (by omega_using [hr]) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.X86_64.Sign

end

end


/-!
# ML-DSA signing on x86-64: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega_using [hj]
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega_using [hj, this]

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega_using [ht]) (iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `r15`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  ok : s.gpr .r15 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (pa s (.r14, 0)) p.sigLen)
  bad : s.gpr .r15 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  stChk p [] && famChk (sgB p) [] (aBase p) (p.k * p.ℓ) && ikChk p [] && famChk (sgB p) [] (yBase p) p.ℓ &&
    famChk (sgB p) [] 5 p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    (List.range 6).all (fun k => inB (sgB p) (sc (oSV + 8 * k)) 8) &&
    decide (scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32)

theorem fChk_ok {p : Params} (h : Ok3 p) : fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  aChk p && dChk p && cChk p && bChk p && ksChk p && lChk p && oChk p && fChk p

theorem allChk_ok {p : Params} (h : Ok3 p) : allChk p = true := by
  simp only [allChk, aChk_ok h, dChk_ok h, cChk_ok h, bChk_ok h, ksChk_ok h, lChk_ok h, oChk_ok h, fChk_ok h,
    Bool.and_self]

theorem r15_one {s : State} (h : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1) (hne : (s.gpr .r15).setWidth 32 ≠ 0) :
    s.gpr .r15 = 1 := by
  rcases h with e | e
  · rw [e] at hne; exact absurd rfl hne
  · exact e

theorem r15_zero {s : State} (h : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1) (he : (s.gpr .r15).setWidth 32 = 0) :
    s.gpr .r15 = 0 := by
  rcases h with e | e
  · exact e
  · rw [e] at he; exact absurd he (by decide)

theorem rest_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (h : IM p D σ s) :
    WP isa (rest P p) s (FS p D σ) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf'
  have hp := paramsOk h3
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono (decodeOrCopy_ok hP hd (pkChk_ok h3) hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hp hc1 hb hks (ksChk2_ok h3) hl h1) fun s2 h2 => ?_)
  have L2 := h2.k.d.im.st.lay
  unfold ifOk
  refine ifOkElse_ok (D := D) (fun s3 hP3 hcs3 hm3 hne => ?_) fun s3 hP3 hcs3 hm3 he => ?_
  · have h15 := r15_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (output_ok hP ho (h2.k.step hP3 ik) (by rw [L2.keepBytes hP3 kct, hct])
      (Fam.keep L2 hP3 fy hz) (HFam.keep L2 hP3 f5 hh) hpass (by rw [hcs3 _ (by decide), h15]))
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := r15_zero h2.r01 he
    have e15 : s3.gpr .r15 = 0 := by rw [hcs3 _ (by decide), h15]
    exact WP.block_nil ⟨(h2.k.step hP3 ik).d.im.st, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
      fun _ => signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨σ.gpr r, len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (pa s (b, 0)) len = bytesAt σ.mem (σ.gpr r) len := by
  rw [pa, hb, VG.Proof.MlKem.X86_64.add_ofNat_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (ht : Top σ s) (hf : Frame [⟨σ.gpr .r8, scrLen p⟩] σ.mem s.mem) : St p D σ s := by
  have hc := fChk_ok h3
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hsz := hc.2
  have hpre' := hpre
  obtain ⟨_, hwr, d1, d2, d3, d4, d5, d6, d7, _, _, _, _, _, _, _, _, _, _, n1, n2, n3, n4, n5, _⟩ := hpre'
  have hsk := skLen_le_skL p σ
  exact ⟨ht, sgLay hpre hP.hD' hsz ht,
    entry_bytes hf (d2.sub_left (Region.sub_prefix hsk)) (by omega_using [hsz]) (ht.regs (.rbp, .rdi) (by decide)),
    entry_bytes hf d4 (by omega_using []) (ht.regs (.r12, .rsi) (by decide)),
    entry_bytes hf d6 (by omega_using []) (ht.regs (.r13, .rdx) (by decide)),
    Frame.sub hf fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (by rw [hwr]; simp), fun _ h => h⟩⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p)
    (hmx : ctlOk (Impl.MlDsa.X86_64.Sign.sign P p) = true) (σ : State)
    (hpre : (signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.X86_64.Sign.sign P p) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, hsv⟩, hsz⟩ := hf'
  have main : WP isa (Impl.MlDsa.X86_64.Sign.sign P p) σ fun s₅ => gprPreserved σ s₅ ∧
      ∃ s₄, FS p D σ s₄ ∧ (s₅.gpr .rax).setWidth 32 = (s₄.gpr .r15).setWidth 32 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.X86_64.Sign.sign
    refine WP.seq (WP.mono (pro_ok hpre hsz.1) fun s₁ ⟨h₁, _, hf₁, h15⟩ => ?_)
    have S1 := entry_st hP h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (expandA_ok hP ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (D := D) (fun s₃ hP₃ hcs₃ hm₃ hne => ?_) fun s₃ hP₃ hcs₃ hm₃ he => ?_
      · have h1 := r15_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact rest_ok hP h3 hpre ⟨h₂.st.step hP₃ st0, ok, Fam.keep h₂.st.lay hP₃ fa0 fam⟩
      · have h0 := r15_zero h₂.r01 he
        have e15 : s₃.gpr .r15 = 0 := by rw [hcs₃ _ (by decide), h0]
        exact WP.block_nil ⟨h₂.st.step hP₃ st0, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
          fun _ => signMu_min_A (h₂.bad h0)⟩
    · exact WP.mono (topEpi_ok h₄.st.top fun k hk => h₄.st.lay.iR (hsv k hk)) fun s₅ ⟨hr, hg, hm⟩ =>
        ⟨hg, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, abiPreserved_of_ctl hmx he hg, ?_⟩
  have e14 : pa s₄ (.r14, 0) = σ.gpr .rcx := by
    rw [pa, h₄.st.top.regs (.r14, .rcx) (by decide), VG.Proof.MlKem.X86_64.add_ofNat_zero]
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0]; rfl, h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1]; rfl, maxBounds, by rw [hm, ← e14]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: the signature leaks only the hint

Writing the signature leaks its pointers and the hint (`output_tr`), on which
two runs whose loops leaked the same agree (`OX`); so all but `Â` leaks what
`signLeak` says (`rest_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : HFam x 5 k f) (hy : HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x (Impl.MlDsa.X86_64.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (pa y (Impl.MlDsa.X86_64.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (pa s (Impl.MlDsa.X86_64.Sign.hP 0)) i =
      coeffAt s.mem (pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [pS_hint s (i / 256)]
    simp only [coeffAt]
    rw [VG.Proof.MlKem.X86_64.off_add (pa s _) (1024 * (i / 256)), show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega_using []]
  have hq : i / 256 < k := by omega_using [hi]
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, IK p D σ s ∧ bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ ∧ Fam s (yBase p) p.ℓ (Zv p σ κ) ∧
    HFam s 5 p.k (Hv p σ κ) ∧ PassV p σ κ ∧ s.gpr .r15 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, OS p D σ κ r s ∧ PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (pa s (yP p r)) ∧ InRange s.mem (pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : PrimsOk P D) (hc : oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => RS p D E (IOi p D) x y ∧ HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  have hcc := copyChk_spec cc
  unfold output
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D 0) x y ∧ HJ p x y) (liftQ
    (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
        (P := fun x y => LRel D (sgR p) (sgW p) x y)
        fun x y h => ⟨h.regs (.r14, p.sigLen) (by simp [sgR, sgW]), lrel_rbx h _ (List.mem_singleton_self _)⟩)
      (fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk.d.im.st) fun _ _ h => h)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D p.ℓ) x y ∧ HJ p x y) (RelCT.mono (seqR_tr
    (R := fun r x y => RS p D E (IOr p D r) x y ∧ HJ p x y) p.ℓ 0 fun r _ hr => liftQ
      (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (packZ_ok hP hc (by omega_using [hr]) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (bpAt_tr hP hbp hzl (cz r (by omega_using [hr])).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega_using [hr]), i₂.zr (by omega_using [hr])⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨hones_ok o₁ a₁, hones_ok o₂ a₂, hint_coeffs hx hy⟩

theorem XS.io (hf : fChk p = true) {σ x₀ x : State} (h : XS p D σ x₀) (h15 : x₀.gpr .r15 = 1)
    (hP : PPostB D x₀ x []) (hcs : ∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) : IOi p D σ x := by
  simp only [fChk, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf
  have L := h.k.d.im.st.lay
  obtain ⟨t, _, _, _, hpass, hct, hz, hh⟩ := h.pass h15
  exact ⟨p.ℓ * t, h.k.step hP ik, by rw [L.keepBytes hP kct, hct], Fam.keep L hP fy hz, HFam.keep L hP f5 hh, hpass,
    by rw [hcs _ (by decide), h15]⟩

theorem rest_tr {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) :
    RelCT isa (RS p D (LeakEq p 0) (IM p D)) (rest P p) (RS p D (LeakEq p 0) (FS p D)) := by
  refine liftR (fun σ s hpre h => rest_ok hP h3 hpre h) ?_
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, f5⟩, -⟩, -⟩, -⟩ := hf'
  have hp := paramsOk h3
  unfold rest
  refine RelCT.seq (decodeOrCopy_tr hP hd (pkChk_ok h3)) (RelCT.seq (signLoop_tr hP hp hc1 hb hks (ksChk2_ok h3) hl) ?_)
  unfold ifOk
  refine ifOkElse_tr (D := D) (fun x y h => by rw [h.2.1]) (RelCT.mono (output_tr hP ho (E := fun _ _ => True))
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, _, s₁, s₂⟩, h15, hj⟩, ⟨hPx, hcx, _⟩, ⟨hPy, hcy, _⟩, hne⟩ => ?_)
    fun _ _ h => h) (RelCT.mono nil_tr (fun _ _ h => h) fun _ _ _ => trivial)
  have e₁ := r15_one s₁.r01 hne
  have e₂ : y₀.gpr .r15 = 1 := h15 ▸ e₁
  obtain ⟨_, f, hx, hy⟩ := hj e₁
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, s₁.io hf e₁ hPx hcx, s₂.io hf e₂ hPy hcy⟩, f,
    HFam.keep s₁.k.d.im.st.lay hPx f5 hx, HFam.keep s₂.k.d.im.st.lay hPy f5 hy⟩

end

end VG.Proof.MlDsa.X86_64.Sign
