module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTMr
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTMr
meta import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# A candidate on PPC64LE: the test in constant time

`test_ct`: two runs of the test (trial division, then Miller–Rabin), with
the same public data, leak the same trace: trial division by its own
constant time (`DivOk.ct`), from candidates its table divides alike
(`div_agree`); whether it found a divisor, and the test's result, are the
same in both runs (`comp_agree`, `shape_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat hUsed)
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (test testResult trialDiv finish finNone finPrime hOut hOutLen testArgs
  hTrial)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)

/-- What two runs share once the candidate passed `gcd(c − 1, e) = 1`. -/
structure GOk (a : CD) (s0 : State) : Prop where
  krel : KRel a s0
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1

theorem GOk.candS {a : CD} {s0 : State} (h : GOk a s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 :=
  candS_eq h.krel.1 hav

theorem comp_agree' {a : CD} {s0 s0' : State} (h : GOk a s0) (h' : GOk a s0') (hav : oL s0 ≤ rL s0) :
    Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) =
      Spec.RsaKeyGen.obviouslyComposite (64 * cw s0') (candOf s0') := by
  have hav' : oL s0' ≤ rL s0' := by rw [← h.krel.oL_eq h'.krel, ← h.krel.rL_eq h'.krel]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts h.krel.1
  obtain ⟨hw', -, -⟩ := cw_facts h'.krel.1
  have e := comp_agree h.krel h'.krel hav
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact h.ncl)
  rwa [h.candS hav, h'.candS hav', hw, hw', show 8 * (8 * cw s0) = 64 * cw s0 by omega,
    show 8 * (8 * cw s0') = 64 * cw s0' by omega] at e

theorem comp_same' {a : CD} {s0 s0' : State} (h : GOk a s0) (h' : GOk a s0') (hav : oL s0 ≤ rL s0)
    (ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = true) : candOf s0 = candOf s0' := by
  have hav' : oL s0' ≤ rL s0' := by rw [← h.krel.oL_eq h'.krel, ← h.krel.rL_eq h'.krel]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts h.krel.1
  have e := comp_same h.krel h'.krel hav
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact h.ncl)
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact ho)
  rwa [h.candS hav, h'.candS hav'] at e

/-! ## Trial division -/

/-- After the test's arguments. -/
def TA (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ T1 s0 (cw s0) (candOf s0) s

/-- Trial division's start: `out` and `out_len` saved. -/
def TD (a : CD) (s : State) : Prop :=
  ∃ s0 s1, GOk a s0 ∧ T1 s0 (cw s0) (candOf s0) s1 ∧
    s = { s1 with mem := (s1.mem.writeW (off (sB s0) 24) (s1.gpr .r23)).writeW (off (sB s0) 40) (s1.gpr .r24) }

/-- After trial division. -/
def TD' (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ s.gpr .r31 = sB s0

/-- After it. -/
def TB (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ T2 s0 (cw s0) (candOf s0) s

theorem pins_TIn : Pins (fun a s => ∃ s0, GOk a s0 ∧ TIn s0 s (cw s0) (candOf s0)) [.r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree g.krel g'.krel h.env h'.env _ (by simp)

theorem pins_TA : Pins TA [.r23, .r24, .r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.ctx.r23, h'.ctx.r23]; exact g.krel.reg g'.krel (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact g.krel.reg g'.krel (by decide)
  · exact env_agree g.krel g'.krel h.env h'.env _ (by simp)

theorem pins_TD' : Pins TD' [.r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h, h']; exact g.krel.arg g'.krel (i := 1) (by decide)

theorem TD.divIn {a : CD} {s : State} (h : TD a s) :
    ∃ s0, GOk a s0 ∧ DivIn s (sB s0) (8 * sL s0) (cw s0) (nTrial (cw s0)) ∧ arr s.mem (sB s0) (cw s0) 0 = candOf s0 ∧
      s.syms = s0.syms ∧ oL s0 ≤ rL s0 := by
  obtain ⟨s0, s1, g, h1, rfl⟩ := h
  have e := h1.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  rw [slot_lin] at hZ
  have d1 := h1.divIn.write (s1.gpr .r23) (d := 24) (by omega) (by simp only [hTrial]; omega) h1.tabDj
  have d2 := d1.write (s1.gpr .r24) (d := 40) (by omega) (by simp only [hTrial]; omega) h1.tabDj
  refine ⟨s0, g, d2, ?_, h1.syms, by rw [h1.tc.hw]; exact h1.tc.h8⟩
  have o := ((writeW_outside s1.mem (sB s0) (d := 24) (s1.gpr .r23) (by omega)).mono (o' := 24) (n' := 24) (by omega)
    (by omega)).trans ((writeW_outside (s1.mem.writeW (off (sB s0) 24) (s1.gpr .r23)) (sB s0) (d := 40)
      (s1.gpr .r24) (by omega)).mono (o' := 24) (n' := 24) (by omega) (by omega))
  rw [← h1.arr0]
  exact o.val32 (by rw [slot_lin]; omega) (by rw [slot_lin]; omega)

/-- Candidates the table divides alike. -/
theorem div_agree {a : CD} {s₁ s₂ : State} (h₁ : TD a s₁) (h₂ : TD a s₂) (hsp : s₁.sp = s₂.sp) : DivRel s₁ s₂ := by
  obtain ⟨s0, g, d, a0, sy, hav⟩ := h₁.divIn
  obtain ⟨s0', g', d', a0', sy', -⟩ := h₂.divIn
  have hw4 := d'.env.hw
  have hB : sB s0 = sB s0' := g.krel.arg g'.krel (i := 1) (by decide)
  have hL : sL s0 = sL s0' := by simp only [sL, g.krel.arg g'.krel (i := 2) (by decide)]
  have hw : cw s0 = cw s0' := by simp only [cw, g.krel.oL_eq g'.krel]
  rw [hB, hL, hw] at d
  rw [hB, hw] at a0
  refine ⟨sB s0', 8 * sL s0', cw s0', nTrial (cw s0'), d, d', hsp,
    by rw [sy, sy']; exact g.krel.sym g'.krel, fun i hi => ?_⟩
  rw [a0, a0']
  have c8 : ∀ {t : State}, GOk a t → 4 ≤ cw t → 8161 < candOf t := fun {t} gt h4 => by
    have := (VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * cw t) (by omega)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .r10) (8 * cw t)))).2.1
    have : 2 ^ 14 ≤ 2 ^ (64 * cw t - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    show 8161 < Spec.RsaKeyGen.candidate (64 * cw t) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .r10) (8 * cw t)))
    omega
  cases ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0)
  · have ho' := (comp_agree' g g' hav).symm.trans ho
    have none : ∀ {t : State}, GOk a t → 4 ≤ cw t →
        Spec.RsaKeyGen.obviouslyComposite (64 * cw t) (candOf t) = false →
        ∀ j < nTrial (cw t), VG.Proof.RsaKeyGen.entryDivides (candOf t) j = false := by
      intro t gt h4 hc j hj
      have hp := VG.Proof.RsaKeyGen.trialPrefix_spec (w := cw t) (c8 gt h4)
      rw [hc] at hp
      cases he : VG.Proof.RsaKeyGen.entryDivides (candOf t) j
      · rfl
      · rw [VG.Proof.RsaKeyGen.trialPrefix_hit hj he] at hp; cases hp
    rw [none g (by rw [hw]; exact hw4) ho i (by rw [hw]; exact hi), none g' hw4 ho' i hi]
  · rw [comp_same' g g' hav ho]

theorem pins_TD_r31 {a : CD} {s : State} (h : TD a s) : ∃ s0, GOk a s0 ∧ s.gpr .r31 = sB s0 := by
  obtain ⟨s0, s1, g, h1, rfl⟩ := h
  exact ⟨s0, g, h1.env.h31⟩

theorem trialDiv_ct {trial : Prog isa} (D : DivOk trial) :
    RelCT isa (Two TA) (trialDiv trial) fun _ _ => True := by
  unfold trialDiv
  refine RelCT.seq (two_post (Ψ := TD) (two_taint _ pins_TA (by taint_decide)) fun a s ⟨s0, g, h⟩ => ?_)
    (RelCT.seq (two_post (Ψ := TD') (D.ct (P := Two TD) fun s₁ s₂ ⟨a, h₁, h₂, hsp⟩ => div_agree h₁ h₂ hsp)
      fun a s hd => ?_) (two_taint _ pins_TD' (by taint_decide)))
  · have e := h.env
    have hs := e.hs
    have hnw := hs.nowrap
    have hZ := e.hZ
    rw [slot_lin] at hZ
    have hst : WP isa (.block [sth .r23 hOut, sth .r24 hOutLen]) s fun u =>
        u = { s with mem := (s.mem.writeW (off (sB s0) 24) (s.gpr .r23)).writeW (off (sB s0) 40) (s.gpr .r24) } := by
      simp only [sth, hOut, hOutLen]
      prun [e.h31, hs.st (d := 24) (n := 8) (by omega), hs.st (d := 40) (n := 8) (by omega)]
    exact WP.mono hst fun u hu => ⟨s0, s, g, h, hu⟩
  · obtain ⟨s0, g, d, -, -, -⟩ := hd.divIn
    obtain ⟨s0', g', h31⟩ := pins_TD_r31 hd
    exact WP.mono (D.ok d) fun t ⟨_, _, hk, _⟩ => ⟨s0', g', (hk .r31 (by decide)).trans h31⟩

/-! ## The result -/

/-- The test's status, from what became of the candidate. -/
def stOf (s0 : State) : Nat :=
  match Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem stOf_shape (s0 : State) : stOf s0 = (VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0)
    ((rB s0).drop (8 * cw s0)))).elim 0 fun x => if x.1 then 1 else 2 := by
  unfold stOf VG.Proof.RsaKeyGen.shapeOf
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩ <;> rfl

theorem stOf_eq {a : CD} {s0 s0' q q' : State} (C : LCtx a s0 q) (C' : LCtx a s0' q') : stOf s0 = stOf s0' := by
  rw [stOf_shape, stOf_shape, shape_eq C C']

theorem T4.stat {s0 s : State} (h : T4 s0 (cw s0) (candOf s0) s) :
    word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (stOf s0) := by
  have r := h.res
  unfold stOf
  revert r
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩
  · exact id
  · exact fun r => r.1

/-- After the witnesses. -/
def TR (a : CD) (s : State) : Prop := ∃ s0, (∃ q, LCtx a s0 q) ∧ T4 s0 (cw s0) (candOf s0) s

/-- The status in `r3`. -/
def R1 (a : CD) (t : State) : Prop :=
  ∃ s0, (∃ q, LCtx a s0 q) ∧ Ctx s0 t ∧ t.gpr .r31 = sB s0 ∧ t.gpr .r3 = BitVec.ofNat 64 (stOf s0)

/-- The status less one in `r3`. -/
def R2 (a : CD) (t : State) : Prop :=
  ∃ s0, (∃ q, LCtx a s0 q) ∧ Ctx s0 t ∧ t.gpr .r31 = sB s0 ∧
    t.gpr .r3 = BitVec.ofNat 64 (stOf s0) - BitVec.ofNat 64 1

theorem pins_TR : Pins TR [.r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, h⟩ ⟨s0', ⟨q', C'⟩, h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel h.prep.env h'.prep.env _ (by simp)

theorem ctx_pins {a : CD} {s0 s0' s s' : State} (k : KRel a s0) (k' : KRel a s0') (c : Ctx s0 s) (c' : Ctx s0' s') :
    ∀ r ∈ [Reg.r23, .r24, .r25], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [c.r23, c'.r23]; exact k.reg k' (by decide)
  · rw [c.r24, c'.r24]; exact k.reg k' (by decide)
  · rw [c.r25, c'.r25]; exact k.reg k' (by decide)

theorem pins_R1 : Pins R1 [.r23, .r24, .r25, .r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, c, h31, -⟩ ⟨s0', ⟨q', C'⟩, c', h31', -⟩ r hr
  have := ctx_pins C.krel C'.krel c c'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact this _ (by simp)
  · exact this _ (by simp)
  · exact this _ (by simp)
  · rw [h31, h31']; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem pins_R2 : Pins R2 [.r23, .r24, .r25, .r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, c, h31, -⟩ ⟨s0', ⟨q', C'⟩, c', h31', -⟩ r hr
  have := ctx_pins C.krel C'.krel c c'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact this _ (by simp)
  · exact this _ (by simp)
  · exact this _ (by simp)
  · rw [h31, h31']; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem stOf_lt (s0 : State) : stOf s0 < 3 := by
  unfold stOf
  split
  · decide
  · split <;> decide

theorem result_ct : RelCT isa (Two TR) testResult fun _ _ => True := by
  unfold testResult
  refine RelCT.seq (two_post (Ψ := R1) (two_taint _ pins_TR (by taint_decide)) fun a s ⟨s0, ⟨q, C⟩, h⟩ => ?_)
    (two_ite ?_ (two_taint _ (pins_and pins_R1) (by taint_decide))
      (RelCT.seq (two_post (Ψ := R2) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
        fun a s ⟨⟨s0, CC, c, h31, h3⟩, _⟩ => ?_)
        (two_ite ?_ (two_taint _ (pins_and pins_R2) (by taint_decide))
          (two_taint _ (pins_and pins_R2) (by taint_decide)))))
  · have e := h.prep.env
    have hs := e.hs
    have hnw := hs.nowrap
    have hZ := e.hZ
    rw [slot_lin] at hZ
    exact WP.mono (WP.keep [.r28, .r3] (Q := fun t => t.gpr .r3 = word s.mem (sB s0) (8 * hStat) ∧
      t.mem = s.mem) (by
        simp only [ldh, hUsed, hStat]
        prun [e.h31, hs.ld (d := 152) (n := 8) (by omega), hs.ld (d := 160) (n := 8) (by omega)]) (by decide))
      fun t ⟨⟨a3, m⟩, k⟩ => ⟨s0, ⟨q, C⟩, h.ctx.keep k m, (k.gpr _ (by decide)).trans e.h31, a3.trans h.stat⟩
  · rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, -, -, h3⟩ ⟨s0', ⟨q', C'⟩, -, -, h3'⟩
    have := stOf_lt s0
    have := stOf_lt s0'
    rw [eval_zero_ofNat _ _ (by omega) h3, eval_zero_ofNat _ _ (by omega) h3', stOf_eq C C']
  · exact WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (stOf s0) - BitVec.ofNat 64 1 ∧
      t.mem = s.mem) (by prun [h3]) (by decide))
      fun t ⟨⟨a3, m⟩, k⟩ => ⟨s0, CC, c.keep k m, (k.gpr _ (by decide)).trans h31, a3⟩
  · rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, -, -, h3⟩ ⟨s0', ⟨q', C'⟩, -, -, h3'⟩
    rw [eval_zero, eval_zero, h3, h3', stOf_eq C C']

/-! ## The test -/

/-- The test's start. -/
def TI (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ TIn s0 s (cw s0) (candOf s0)

theorem pins_TB : Pins TB [.r10, .r11, .r29, .r31, .r25] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  have ea := env_agree g.krel g'.krel h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · rw [h.ctx.r25, h'.ctx.r25]; exact g.krel.reg g'.krel (by decide)

theorem comp_eval : ∀ (a : CD) (s₁ s₂ : State), TB a s₁ → TB a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩
  rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f, eval_nonzero_ofNat' _ _ (by split <;> decide) h'.f,
    comp_agree' g g' (by rw [h.tc.hw]; exact h.tc.h8)]

theorem test_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two TI) (test trial R.name R.code) fun _ _ => True := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := TA) (two_taint _ pins_TIn (by taint_decide))
    fun a s ⟨s0, g, h⟩ => WP.mono (argsS h) fun t ht => ⟨s0, g, ht⟩)
    (RelCT.seq (two_post (Ψ := TB) (trialDiv_ct D) fun a s ⟨s0, g, h⟩ => WP.mono (trialS D h) fun t ht => ⟨s0, g, ht⟩)
      (two_ite comp_eval (two_taint _ (pins_and pins_TB) (by taint_decide))
        (RelCT.seq (two_post (Ψ := L3) (two_taint _ (pins_and pins_TB) (by taint_decide))
          fun a s ⟨⟨s0, g, h⟩, ev⟩ => ?_)
          (RelCT.seq (two_post (Ψ := TR) (mr_ct R) fun a s ⟨s0, C⟩ =>
            WP.mono (mrStage R C.t3) fun t ht => ⟨s0, ⟨s, C⟩, ht⟩) result_ct))))
  have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = false := by
    rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> decide
  exact WP.mono (prepS h hoc) fun t ht => ⟨s0, ⟨g.krel, ht, g.ncl, g.gcd⟩⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand
