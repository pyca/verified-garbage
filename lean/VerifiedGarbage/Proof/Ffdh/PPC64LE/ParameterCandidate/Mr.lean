module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawFn
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Witnesses

/-!
# An FFDH parameter candidate on PPC64LE: the witnesses of a modulus

`millerRabin_ok`: witnesses drawn while `hStat` is 4; at the end `hStat` is 0
when the tape ran out, else 1 or 2 by `checkWitnesses`, with `used` the
octets read.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- At the head of the loop: `i` witnesses passed, `u` octets read, and
`res` what the rest of the tape gives. -/
structure MrSt (p : PP) (mb N : Nat) (res : Option (Bool × List Byte)) (i u : Nat) (s : State) : Prop where
  m : MSt p mb N s
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  idx : word s.mem p.B 176 = BitVec.ofNat 64 i
  stat : word s.mem p.B 160 = BitVec.ofNat 64 4
  ul : u ≤ p.r.length
  ik : i < Spec.Ffdh.primeChecks mb
  rest : checkWitnesses N (Spec.Ffdh.primeChecks mb - i) (p.r.drop u) = res

/-- After the loop. -/
def MrEnd (p : PP) (mb N : Nat) (res : Option (Bool × List Byte)) (t : State) : Prop :=
  MSt p mb N t ∧ (res = none → word t.mem p.B 160 = BitVec.ofNat 64 0) ∧
    ∀ b rest, res = some (b, rest) → word t.mem p.B 160 = BitVec.ofNat 64 (if b then 1 else 2) ∧
      ∃ u, u ≤ p.r.length ∧ rest = p.r.drop u ∧ word t.mem p.B 152 = BitVec.ofNat 64 u

theorem stat_zero {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 4 == 0) = decide (n = 4) := by
  by_cases h : n = 4
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- Between the draw and the test of `hStat`. -/
def MrMid (p : PP) (mb N i u : Nat) (t : State) : Prop :=
  MSt p mb N t ∧ ((p.r.length < u + (mb + 7) / 8 ∧ word t.mem p.B 160 = BitVec.ofNat 64 0) ∨
    (u + (mb + 7) / 8 ≤ p.r.length ∧ word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N (Spec.Ffdh.primeChecks mb) i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u))))

/-- The head's block: `r5 = 1` exactly when there is room for a witness. -/
theorem mrHeadBlk_ok {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (h : MrSt p mb N res i u s) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if (mb + 7) / 8 ≤ p.r.length - u then 1 else 0) ∧ t.mem = s.mem) ∧
      Keep (([.r3, .r4] : List Reg) ++ ([.r5, .r0] : List Reg)) s t := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  have hKw := h.m.ph.kW
  have hU := h.used
  simp only [word, off, Impl.MillerRabin.PPC64LE.Search.hK, Nat.reduceMul] at hKw hU
  have hsub : BitVec.ofNat 64 p.r.length - BitVec.ofNat 64 u = BitVec.ofNat 64 (p.r.length - u) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (p.r.length - u) ∧
      t.gpr .r4 = BitVec.ofNat 64 ((mb + 7) / 8) ∧ t.mem = s.mem) ?_ (by decide)) fun s₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  · simp only [ldh, hRandLen, hUsed, Impl.MillerRabin.PPC64LE.Search.hK]
    prun [h.m.st.r31, h.m.st.ld (d := 144) (by decide), h.m.st.ld (d := 152) (by decide),
      h.m.st.ld (d := 216) (by decide), h.m.st.args.rlen', hU, hKw, hsub]
  exact WP.mono (geFlag_ok a3 a4 (by omega_arith) (by omega_arith)) fun s₂ ⟨⟨a5, m₂⟩, k₂⟩ => ⟨⟨a5, m₂.trans m₁⟩, k₁.trans k₂⟩

/-- The head: room for a witness, and the draw if there is. -/
theorem mrHead_ok (R : RoundImpl) {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (h : MrSt p mb N res i u s) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4))
      (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code))) s (MrMid p mb N i u) := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  refine WP.seq (WP.mono (mrHeadBlk_ok h) fun s₂ ⟨⟨a5, m12⟩, k12⟩ => ?_)
  refine WP.ite (decide ((if (mb + 7) / 8 ≤ p.r.length - u then 1 else 0) = 0))
    (eval_zero_ofNat s₂ .r5 (by split <;> decide) a5) (fun hb => ?_) (fun hb => ?_)
  · -- No room: `hStat := 0`.
    have hr : p.r.length < u + (mb + 7) / 8 := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega_arith)] at hb; exact absurd hb (by decide)
    have st₂ : St p s₂ := h.m.st.step (by rw [m12]; exact Frm.refl _ _ _) k12
    have l160 : InRegions s₂.wr (p.B + BitVec.ofNat 64 160) 8 := st₂.st (d := 160) (by decide)
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s₂.mem.writeW (p.B + BitVec.ofNat 64 160) (BitVec.ofNat 64 0))
      (by simp only [sth, hStat]; prun [st₂.r31, l160]) (by decide)) fun t ⟨tm, kt⟩ => ?_
    have kt' := k12.trans kt
    have hf : Frm p.B [(160, 8)] s.mem t.mem := by
      rw [tm, m12]
      exact frm_writeW (a := 160) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)
    have hfr : ∀ r ∈ [((160 : Nat), (8 : Nat))], Free (wOf mb) r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Or.inl ⟨by simp, rfl⟩
    refine ⟨h.m.frm hf hfr kt' (by decide) (kt'.gpr _ (by decide)) (kt'.gpr _ (by decide))
      (kt'.gpr _ (by decide)), Or.inl ⟨hr, ?_⟩⟩
    simp only [word, off]; rw [tm, rw_self]
  · -- A draw.
    have hr : u + (mb + 7) / 8 ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega_arith)])
    have M₂ : MSt p mb N s₂ := h.m.frm (rs := []) (by rw [m12]; exact Frm.refl _ _ _) (by simp) k12 (by decide)
      (k12.gpr _ (by decide)) (k12.gpr _ (by decide)) (k12.gpr _ (by decide))
    refine WP.mono (draw_ok R M₂ (by rw [m12]; exact h.used) hr (by rw [m12]; exact h.idx)
      (by rw [m12]; exact h.stat) (by have := h.ik; unfold Spec.Ffdh.primeChecks at this; split at this <;> omega_arith))
      fun t ⟨mt, ut, st, it⟩ => ⟨mt, Or.inr ⟨hr, ut, st, it⟩⟩

theorem wp_then {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (k : ∀ t, P t → WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  exact WP.mono h fun t ht => WP.seq (WP.mono ht k)

/-- Whether the witness loop goes on after the witness at `u`, `i` passed. -/
def mrGo (r : List Byte) (mb N i u : Nat) : Bool :=
  decide (u + (mb + 7) / 8 ≤ r.length) &&
    (!decide (2 ≤ wA mb r u ∧ wA mb r u < N - 1) ||
      (Proof.MillerRabin.Round.round N (wA mb r u) && decide (i + 1 < Spec.Ffdh.primeChecks mb)))

/-- An iteration: `hStat` tested after the head. -/
theorem mrIter_ok (R : RoundImpl) {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MrSt p mb N res i u s) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4))
      (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code))
        (.block [ldh .r3 hStat, .subi .r3 .r3 4]))) s fun t =>
      isa.eval (.zero .d .r3) t = some (mrGo p.r mb N i u) ∧ (mrGo p.r mb N i u = false → MrEnd p mb N res t) ∧
      (mrGo p.r mb N i u = true → MrSt p mb N res (dIdx N i (wA mb p.r u)) (u + (mb + 7) / 8) t) := by
  have hm1 := h.m.mb1
  have hik := h.ik
  have hN3 := h.m.prep.c3
  have hodd := h.m.prep.odd
  have hK64 : Spec.Ffdh.primeChecks mb ≤ 128 := by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  have hres := h.rest
  rw [show Spec.Ffdh.primeChecks mb - i = (Spec.Ffdh.primeChecks mb - i - 1) + 1 by omega_arith] at hres
  refine wp_then (mrHead_ok R h) fun t ⟨M, hmid⟩ => ?_
  have l160 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = word t.mem p.B 160 - BitVec.ofNat 64 4 ∧
      v.mem = t.mem) (by simp only [ldh, hStat]; prun [M.st.r31, l160]) (by decide)) fun v ⟨⟨v3, vm⟩, vk⟩ => ?_
  have M' : MSt p mb N v := M.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vk (by decide)
    (vk.gpr _ (by decide)) (vk.gpr _ (by decide)) (vk.gpr _ (by decide))
  have hw : ∀ d, word v.mem p.B d = word t.mem p.B d := fun d => by rw [vm]
  have ev : ∀ k, k < 2 ^ 60 → word t.mem p.B 160 = BitVec.ofNat 64 k →
      isa.eval (.zero .d .r3) v = some (decide (k = 4)) := fun k hk he => by
    rw [eval_zero, v3, he, stat_zero hk]
  have hm : 1 ≤ mb := by omega_arith
  rcases hmid with ⟨hr, h0⟩ | ⟨hr, hu, hs, hi⟩
  · -- No room for a witness.
    rw [cw_short hbl hm hr] at hres
    have hg : mrGo p.r mb N i u = false := by
      simp only [mrGo, Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact Or.inl (by omega_arith)
    rw [hg]
    refine ⟨(ev 0 (by decide) h0).trans (by decide), fun _ => ⟨M', fun _ => by rw [hw]; exact h0, fun b rest hb => ?_⟩,
      fun h => absurd h (by decide)⟩
    rw [← hres] at hb; cases hb
  rw [cw_step hbl hm hr] at hres
  have hround := mr_round_eq (wA mb p.r u) hN3 hodd
  simp only [dStat, dIdx, mrGo, hround, decide_eq_true hr, Bool.true_and] at hs hi ⊢
  generalize wA mb p.r u = a at hs hi hres ⊢
  by_cases hrg : 2 ≤ a ∧ a < N - 1
  · simp only [hrg.1, hrg.2, and_self, true_and, ↓reduceIte, decide_true, Bool.not_true, Bool.false_or]
      at hs hi hres ⊢
    by_cases hmr : Spec.Ffdh.mrRound N a = true
    · simp only [hmr, ↓reduceIte, Bool.true_and] at hs hi hres ⊢
      by_cases hk : i + 1 < Spec.Ffdh.primeChecks mb
      · simp only [hk, ↓reduceIte, decide_true] at hs ⊢
        refine ⟨(ev 4 (by decide) hs).trans (by decide), fun h => absurd h (by decide),
          fun _ => ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hk, ?_⟩⟩
        rw [show Spec.Ffdh.primeChecks mb - (i + 1) = Spec.Ffdh.primeChecks mb - i - 1 by omega_arith]; exact hres
      · simp only [hk, ↓reduceIte, decide_false] at hs ⊢
        rw [show Spec.Ffdh.primeChecks mb - i - 1 = 0 by omega_arith, checkWitnesses] at hres
        refine ⟨(ev 1 (by decide) hs).trans (by decide), fun _ => ⟨M', fun hn => (by rw [← hres] at hn; cases hn),
          fun b rest hb => ?_⟩, fun h => absurd h (by decide)⟩
        rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
    · simp only [hmr, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at hs hi hres ⊢
      refine ⟨(ev 2 (by decide) hs).trans (by decide), fun _ => ⟨M', fun hn => (by rw [← hres] at hn; cases hn),
        fun b rest hb => ?_⟩, fun h => absurd h (by decide)⟩
      rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
  · have hrg' : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h => hrg ⟨h.1, h.2.1⟩
    simp only [hrg, hrg', ↓reduceIte, decide_false, Bool.not_false, Bool.true_or] at hs hi hres ⊢
    refine ⟨(ev 4 (by decide) hs).trans (by decide), fun h => absurd h (by decide),
      fun _ => ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hik, ?_⟩⟩
    rw [show Spec.Ffdh.primeChecks mb - i = Spec.Ffdh.primeChecks mb - i - 1 + 1 by omega_arith]; exact hres

/-- The witness loop's start: `hIdx := 0`, `hStat := 4`. -/
theorem mrInit_ok {p : PP} {mb N u : Nat} {s : State} (h : MSt p mb N s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.block [.li .r3 0, sth .r3 hIdx, .li .r3 4, sth .r3 hStat]) s
      (MrSt p mb N (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u)) 0 u) := by
  have hm1 := h.mb1
  have l160 : InRegions s.wr (p.B + BitVec.ofNat 64 160) 8 := h.st.st (d := 160) (by decide)
  have l176 : InRegions s.wr (p.B + BitVec.ofNat 64 176) 8 := h.st.st (d := 176) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = (s.mem.writeW (p.B + BitVec.ofNat 64 176)
      (BitVec.ofNat 64 0)).writeW (p.B + BitVec.ofNat 64 160) (BitVec.ofNat 64 4))
      (by simp only [sth, hIdx, hStat]; prun [h.st.r31, l160, l176]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  have hf : Frm p.B [(176, 8), (160, 8)] s.mem t.mem := by
    rw [tm]
    exact frm_writeW (frm_writeW (Frm.refl _ _ _) _ ⟨(176, 8), by simp, by decide, by decide⟩ (by decide)) _
      ⟨(160, 8), by simp, by decide, by decide⟩ (by decide)
  have hfr : ∀ r ∈ [((176 : Nat), (8 : Nat)), (160, 8)], Free (wOf mb) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩
  have M := h.frm hf hfr kt (by decide) (kt.gpr _ (by decide)) (kt.gpr _ (by decide)) (kt.gpr _ (by decide))
  have t152 : word t.mem p.B 152 = BitVec.ofNat 64 u := by
    simp only [word, off] at hu ⊢
    rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hu
  have t160 : word t.mem p.B 160 = BitVec.ofNat 64 4 := by
    simp only [word, off]; rw [tm, rw_self]
  have t176 : word t.mem p.B 176 = BitVec.ofNat 64 0 := by
    simp only [word, off]; rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
  have hK : 0 < Spec.Ffdh.primeChecks mb := by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  exact ⟨M, t152, t176, t160, hul, hK, by rw [Nat.sub_zero]⟩

/-- The witnesses of `N`, drawn from octet `u` of the tape. -/
theorem millerRabin_ok (R : RoundImpl) {p : PP} {mb N u : Nat} {s : State}
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MSt p mb N s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (millerRabin R.name R.code) s
      (MrEnd p mb N (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u))) := by
  have hm1 := h.mb1
  refine WP.seq (WP.mono (mrInit_ok h hu hul) fun t ht => ?_)
  show WP isa (.loop _ _) t _
  refine WP.loop (fun m v => ∃ i u', m = p.r.length + 1 - u' ∧
      MrSt p mb N (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u)) i u' v) ?_ (p.r.length + 1 - u) t ?_
  · rintro m v ⟨i, u', rfl, hv⟩
    have hit := mrIter_ok R hbl hv
    refine WP.mono hit fun w ⟨he, hend, hgo⟩ => ?_
    cases hg : mrGo p.r mb N i u'
    · exact Or.inl ⟨by rw [he, hg], hend hg⟩
    · have hw := hgo hg
      have hul' := hw.ul
      have hlt : p.r.length + 1 - (u' + (mb + 7) / 8) < p.r.length + 1 - u' := by omega_using [hul', hm1]
      exact Or.inr ⟨by rw [he, hg], p.r.length + 1 - (u' + (mb + 7) / 8), hlt, _, u' + (mb + 7) / 8, rfl, hw⟩
  · exact ⟨0, u, rfl, ht⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
