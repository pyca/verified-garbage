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
    omega

/-- Between the draw and the test of `hStat`. -/
def MrMid (p : PP) (mb N i u : Nat) (t : State) : Prop :=
  MSt p mb N t ∧ ((p.r.length < u + (mb + 7) / 8 ∧ word t.mem p.B 160 = BitVec.ofNat 64 0) ∨
    (u + (mb + 7) / 8 ≤ p.r.length ∧ word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N (Spec.Ffdh.primeChecks mb) i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u))))

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
  have hKw := h.m.ph.kW
  have hU := h.used
  simp only [word, off, Impl.MillerRabin.PPC64LE.Search.hK, Nat.reduceMul] at hKw hU
  have hsub : BitVec.ofNat 64 p.r.length - BitVec.ofNat 64 u = BitVec.ofNat 64 (p.r.length - u) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (p.r.length - u) ∧
      t.gpr .r4 = BitVec.ofNat 64 ((mb + 7) / 8) ∧ t.mem = s.mem) ?_ (by decide)) fun s₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  · simp only [ldh, hRandLen, hUsed, Impl.MillerRabin.PPC64LE.Search.hK]
    prun [h.m.st.r31, h.m.st.ld (d := 144) (by decide), h.m.st.ld (d := 152) (by decide),
      h.m.st.ld (d := 216) (by decide), h.m.st.args.rlen', hU, hKw, hsub]
  refine WP.mono (geFlag_ok a3 a4 (by omega) (by omega)) fun s₂ ⟨⟨a5, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have m12 : s₂.mem = s.mem := m₂.trans m₁
  refine WP.ite (decide ((if (mb + 7) / 8 ≤ p.r.length - u then 1 else 0) = 0))
    (eval_zero_ofNat s₂ .r5 (by split <;> decide) a5) (fun hb => ?_) (fun hb => ?_)
  · -- No room: `hStat := 0`.
    have hr : p.r.length < u + (mb + 7) / 8 := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega)] at hb; exact absurd hb (by decide)
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
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])
    have M₂ : MSt p mb N s₂ := h.m.frm (rs := []) (by rw [m12]; exact Frm.refl _ _ _) (by simp) k12 (by decide)
      (k12.gpr _ (by decide)) (k12.gpr _ (by decide)) (k12.gpr _ (by decide))
    refine WP.mono (draw_ok R M₂ (by rw [m12]; exact h.used) hr (by rw [m12]; exact h.idx)
      (by rw [m12]; exact h.stat) (by have := h.ik; unfold Spec.Ffdh.primeChecks at this; split at this <;> omega))
      fun t ⟨mt, ut, st, it⟩ => ⟨mt, Or.inr ⟨hr, ut, st, it⟩⟩

theorem wp_then {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (k : ∀ t, P t → WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  exact WP.mono h fun t ht => WP.seq (WP.mono ht k)

/-- An iteration: `hStat` tested after the head. -/
theorem mrIter_ok (R : RoundImpl) {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MrSt p mb N res i u s) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] : List Instr) ++
        geFlag .r5 .r3 .r4))
      (.seq (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code))
        (.block [ldh .r3 hStat, .subi .r3 .r3 4]))) s fun t =>
      (isa.eval (.zero .d .r3) t = some false ∧ MrEnd p mb N res t) ∨
      (isa.eval (.zero .d .r3) t = some true ∧ ∃ i', MrSt p mb N res i' (u + (mb + 7) / 8) t) := by
  have hm1 := h.m.mb1
  have hik := h.ik
  have hN3 := h.m.prep.c3
  have hodd := h.m.prep.odd
  have hK64 : Spec.Ffdh.primeChecks mb ≤ 128 := by unfold Spec.Ffdh.primeChecks; split <;> omega
  have hres := h.rest
  rw [show Spec.Ffdh.primeChecks mb - i = (Spec.Ffdh.primeChecks mb - i - 1) + 1 by omega] at hres
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
  have hm : 1 ≤ mb := by omega
  rcases hmid with ⟨hr, h0⟩ | ⟨hr, hu, hs, hi⟩
  · -- No room for a witness.
    rw [cw_short hbl hm hr] at hres
    refine Or.inl ⟨by rw [ev 0 (by decide) h0]; decide, M', fun _ => by rw [hw]; exact h0, fun b rest hb => ?_⟩
    rw [← hres] at hb; cases hb
  rw [cw_step hbl hm hr] at hres
  have hround := mr_round_eq (wA mb p.r u) hN3 hodd
  simp only [dStat, dIdx, hround] at hs hi
  generalize wA mb p.r u = a at hs hi hres
  by_cases hrg : 2 ≤ a ∧ a < N - 1
  · simp only [hrg.1, hrg.2, and_self, true_and, ↓reduceIte] at hs hi hres
    by_cases hmr : Spec.Ffdh.mrRound N a = true
    · simp only [hmr, ↓reduceIte] at hs hi hres
      by_cases hk : i + 1 < Spec.Ffdh.primeChecks mb
      · simp only [hk, ↓reduceIte] at hs
        refine Or.inr ⟨by rw [ev 4 (by decide) hs]; decide, i + 1,
          ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hk, ?_⟩⟩
        rw [show Spec.Ffdh.primeChecks mb - (i + 1) = Spec.Ffdh.primeChecks mb - i - 1 by omega]; exact hres
      · simp only [hk, ↓reduceIte] at hs
        rw [show Spec.Ffdh.primeChecks mb - i - 1 = 0 by omega, checkWitnesses] at hres
        refine Or.inl ⟨by rw [ev 1 (by decide) hs]; decide, M', fun hn => (by rw [← hres] at hn; cases hn),
          fun b rest hb => ?_⟩
        rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
    · simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hs hi hres
      refine Or.inl ⟨by rw [ev 2 (by decide) hs]; decide, M', fun hn => (by rw [← hres] at hn; cases hn),
        fun b rest hb => ?_⟩
      rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
  · have hrg' : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h => hrg ⟨h.1, h.2.1⟩
    simp only [hrg, hrg', ↓reduceIte] at hs hi hres
    refine Or.inr ⟨by rw [ev 4 (by decide) hs]; decide, i,
      ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hik, ?_⟩⟩
    rw [show Spec.Ffdh.primeChecks mb - i = Spec.Ffdh.primeChecks mb - i - 1 + 1 by omega]; exact hres

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
