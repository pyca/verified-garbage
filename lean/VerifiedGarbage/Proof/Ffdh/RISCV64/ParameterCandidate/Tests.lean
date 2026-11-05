module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Draw
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Ends
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Checked
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# An FFDH parameter candidate on RISC-V: the tests

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Witnesses,Mr,Test,Tests,Result,TestsFn}.lean`):
`millerRabin_ok`, witnesses drawn while `hStat` is 4, against
`checkWitnesses`; `montPrep_mst`, a modulus's Montgomery constants;
`testQ_ok` and `testP_ok`, the tests of q (halved in place) and p (loaded
again); `pResult_ok` and `qResult_ok`, their results; `tests_ok`, against
`testsSpec`. Each is proven for a round whose call meets `RoundCall`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_nonzero eval_zero_ofNat eval_nonzero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (rw_self frm_writeW)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses drawWitness_eq testsSpec)

/-! ## The witnesses, one draw at a time -/

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

theorem cw_short {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : r.length < u + (mb + 7) / 8) : checkWitnesses N (n + 1) (r.drop u) = none := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hd : Spec.Ffdh.drawWitness N (r.drop u) = none := by
    rw [drawWitness_eq (by rw [hw]; omega_arith), hw]
    have : ¬((mb + 7) / 8 ≤ (r.drop u).length) := by rw [List.length_drop]; omega_arith
    simp only [this, ↓reduceIte]
  simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_none]

theorem cw_step {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : u + (mb + 7) / 8 ≤ r.length) :
    checkWitnesses N (n + 1) (r.drop u) =
      if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb r u) then checkWitnesses N n (r.drop (u + (mb + 7) / 8))
          else some (false, r.drop (u + (mb + 7) / 8)))
      else checkWitnesses N (n + 1) (r.drop (u + (mb + 7) / 8)) := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  have hl : (mb + 7) / 8 ≤ (r.drop u).length := by rw [List.length_drop]; omega_arith
  have hd := drawWitness_eq (w := N) (by rw [hw]; omega_arith) (r.drop u)
  rw [hw, hbl] at hd
  simp only [hl, ↓reduceIte, List.drop_drop] at hd
  have ha : Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb = wA mb r u := rfl
  rw [ha] at hd
  by_cases hr : 2 ≤ wA mb r u ∧ wA mb r u < N - 1
  · simp only [hr, and_self, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind, Option.bind_some]
  · simp only [hr, ↓reduceIte] at hd ⊢
    simp only [checkWitnesses, hd, Option.bind_eq_bind]

/-! ## The witnesses of a modulus -/

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

theorem sltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have e : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [ite_eq_left (e.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h]; rfl

/-- The head's block: `t4 = 1` exactly when the tape is short. -/
theorem mrHeadBlk_ok {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (h : MrSt p mb N res i u s) :
    WP isa (.block tapeShort) s fun t =>
      ((t.gpr .t4 = BitVec.ofNat 64 (if p.r.length - u < (mb + 7) / 8 then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t2, .t3, .t4] s t) ∧ t.sp = s.sp := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  have hKw := h.m.ph.kW
  have hU := h.used
  have st := h.m.st
  simp only [word, off, Impl.MillerRabin.RISCV64.Search.hK, Nat.reduceMul] at hKw hU
  have hsub : BitVec.ofNat 64 p.r.length - BitVec.ofNat 64 u = BitVec.ofNat 64 (p.r.length - u) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.rdwr (WP.keep [.t2, .t3, .t4] ?_ (by rfl) (by rfl)) |>.mono fun t ⟨a, _, _, b⟩ => ⟨a, b⟩
  simp only [tapeShort, ldh, hRandLen, hUsed, Impl.MillerRabin.RISCV64.Search.hK]
  brun [st.s6, st.ld (d := 144) (by decide), st.ld (d := 152) (by decide), st.ld (d := 216) (by decide),
    st.al (d := 144) (by decide) (by decide), st.al (d := 152) (by decide) (by decide),
    st.al (d := 216) (by decide) (by decide), st.args.rlen', hU, hKw, hsub,
    sltu_ofNat (show p.r.length - u < 2 ^ 64 by omega_arith) (show (mb + 7) / 8 < 2 ^ 64 by omega_arith)]

/-- The head: room for a witness, and the draw if there is. -/
theorem mrHead_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)}
    {i u : Nat} {s : State} (h : MrSt p mb N res i u s) :
    WP isa (.seq (.block tapeShort)
      (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw R.name R.code))) s (MrMid p mb N i u) := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  refine WP.seq (WP.mono (mrHeadBlk_ok h) fun s₂ ⟨⟨⟨a4, m12⟩, k12⟩, sp12⟩ => ?_)
  refine WP.ite (decide ((if p.r.length - u < (mb + 7) / 8 then 1 else 0) ≠ 0))
    (eval_nonzero_ofNat s₂ .t4 (by split <;> decide) a4) (fun hb => ?_) (fun hb => ?_)
  · -- No room: `hStat := 0`.
    have hr : p.r.length < u + (mb + 7) / 8 := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_right (by omega_arith)] at hb; exact hb rfl
    have st₂ : St p s₂ := h.m.st.step (by rw [m12]; exact Frm.refl _ _ _) k12 sp12
    have l160 : InRegions s₂.wr (p.B + BitVec.ofNat 64 160) 8 := st₂.st (d := 160) (by decide)
    have a160 := st₂.al (d := 160) (by decide) (by decide)
    refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.mem = s₂.mem.writeW (p.B + BitVec.ofNat 64 160)
      (BitVec.ofNat 64 0)) (by simp only [sth, hStat]; brun [st₂.s6, l160, a160, exec_li (show imm12 0 by decide)])
      (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
    have kt' := k12.trans kt
    have hf : Frm p.B [(160, 8)] s.mem t.mem := by
      rw [tm, m12]
      exact frm_writeW (a := 160) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)
    have hfr : ∀ r ∈ [((160 : Nat), (8 : Nat))], Free (wOf mb) r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Or.inl ⟨by simp, rfl⟩
    refine ⟨h.m.frm hf hfr kt' (tsp.trans sp12) (by decide) (kt'.gpr (by decide)) (kt'.gpr (by decide))
      (kt'.gpr (by decide)) (kt'.gpr (by decide)), Or.inl ⟨hr, ?_⟩⟩
    simp only [word, off]; rw [tm, rw_self]
  · -- A draw.
    have hr : u + (mb + 7) / 8 ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
      rw [ite_eq_left (by omega_arith)] at hb; exact absurd hb (by decide)
    have M₂ : MSt p mb N s₂ := h.m.frm (rs := []) (by rw [m12]; exact Frm.refl _ _ _) (by simp) k12 sp12 (by decide)
      (k12.gpr (by decide)) (k12.gpr (by decide)) (k12.gpr (by decide)) (k12.gpr (by decide))
    refine WP.mono (draw_ok hR M₂ (by rw [m12]; exact h.used) hr (by rw [m12]; exact h.idx)
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
theorem mrIter_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)}
    {i u : Nat} {s : State} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MrSt p mb N res i u s) :
    WP isa (.seq (.block tapeShort)
      (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw R.name R.code))
        (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) s fun t =>
      isa.eval (.zero .t2) t = some (mrGo p.r mb N i u) ∧ (mrGo p.r mb N i u = false → MrEnd p mb N res t) ∧
      (mrGo p.r mb N i u = true → MrSt p mb N res (dIdx N i (wA mb p.r u)) (u + (mb + 7) / 8) t) := by
  have hm1 := h.m.mb1
  have hik := h.ik
  have hN3 := h.m.prep.c3
  have hodd := h.m.prep.odd
  have hK64 : Spec.Ffdh.primeChecks mb ≤ 128 := by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  have hres := h.rest
  rw [show Spec.Ffdh.primeChecks mb - i = (Spec.Ffdh.primeChecks mb - i - 1) + 1 by omega_arith] at hres
  refine wp_then (mrHead_ok hR h) fun t ⟨M, hmid⟩ => ?_
  have l160 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun v => v.gpr .t2 = word t.mem p.B 160 - BitVec.ofNat 64 4 ∧
      v.mem = t.mem) (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160]) (by rfl) (by rfl)))
    fun v ⟨⟨⟨v3, vm⟩, vk⟩, _, _, vsp⟩ => ?_
  have M' : MSt p mb N v := M.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vk vsp (by decide)
    (vk.gpr (by decide)) (vk.gpr (by decide)) (vk.gpr (by decide)) (vk.gpr (by decide))
  have hw : ∀ d, word v.mem p.B d = word t.mem p.B d := fun d => by rw [vm]
  have ev : ∀ k, k < 2 ^ 60 → word t.mem p.B 160 = BitVec.ofNat 64 k →
      isa.eval (.zero .t2) v = some (decide (k = 4)) := fun k hk he => by
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
    WP isa (.block [.li .t2 0, sth .t2 hIdx, .li .t2 4, sth .t2 hStat]) s
      (MrSt p mb N (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u)) 0 u) := by
  have hm1 := h.mb1
  have st := h.st
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.mem = (s.mem.writeW (p.B + BitVec.ofNat 64 176)
      (BitVec.ofNat 64 0)).writeW (p.B + BitVec.ofNat 64 160) (BitVec.ofNat 64 4))
      (by simp only [sth, hIdx, hStat]
          brun [st.s6, st.st (d := 160) (by decide), st.st (d := 176) (by decide),
            st.al (d := 160) (by decide) (by decide), st.al (d := 176) (by decide) (by decide),
            exec_li (show imm12 0 by decide), exec_li (show imm12 4 by decide)])
      (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
  have hf : Frm p.B [(176, 8), (160, 8)] s.mem t.mem := by
    rw [tm]
    exact frm_writeW (frm_writeW (Frm.refl _ _ _) _ ⟨(176, 8), by simp, by decide, by decide⟩ (by decide)) _
      ⟨(160, 8), by simp, by decide, by decide⟩ (by decide)
  have hfr : ∀ r ∈ [((176 : Nat), (8 : Nat)), (160, 8)], Free (wOf mb) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩
  have M := h.frm hf hfr kt tsp (by decide) (kt.gpr (by decide)) (kt.gpr (by decide)) (kt.gpr (by decide))
    (kt.gpr (by decide))
  have t152 : word t.mem p.B 152 = BitVec.ofNat 64 u := by
    simp only [word, off] at hu ⊢
    rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hu
  have t160 : word t.mem p.B 160 = BitVec.ofNat 64 4 := by
    simp only [word, off]; rw [tm, rw_self]
  have t176 : word t.mem p.B 176 = BitVec.ofNat 64 0 := by
    simp only [word, off]; rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
  have hK : 0 < Spec.Ffdh.primeChecks mb := by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  exact ⟨M, t152, t176, t160, hul, hK, by rw [Nat.sub_zero]⟩

/-- The witnesses of `N`, drawn from octet `u` of the tape. -/
theorem millerRabin_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N u : Nat} {s : State}
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
    have hit := mrIter_ok hR hbl hv
    refine WP.mono hit fun w ⟨he, hend, hgo⟩ => ?_
    cases hg : mrGo p.r mb N i u'
    · exact Or.inl ⟨by rw [he, hg], hend hg⟩
    · have hw := hgo hg
      have hul' := hw.ul
      have hlt : p.r.length + 1 - (u' + (mb + 7) / 8) < p.r.length + 1 - u' := by omega_using [hul', hm1]
      exact Or.inr ⟨by rw [he, hg], p.r.length + 1 - (u' + (mb + 7) / 8), hlt, _, u' + (mb + 7) / 8, rfl, hw⟩
  · exact ⟨0, u, rfl, ht⟩

/-! ## The test of a modulus -/

/-- `montPrep`: the Montgomery constants of the modulus `N` in array 0. -/
theorem montPrep_mst {p : PP} {mb N : Nat} {s : State} (h : St p s) (hp : Ph p mb s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t => MSt p mb N t ∧ Frm p.B (mutR p.n) s.mem t.mem ∧
      word t.mem p.B 152 = word s.mem p.B 152 := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hw8 : 8 ≤ wOf mb := by simp only [wOf]; omega_arith
  have hw128 : wOf mb ≤ 128 := by simp only [wOf]; omega_arith
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have e1 := es 1; have e4 := es 4; have e6 := es 6; have e8 := es 8; have e9 := es 9; have e11 := es 11
  have e27 := es 27; have e28 := es 28
  have hZn : p.Z = 8 * p.n := rfl
  have hZ : slot (wOf mb) 28 + saveBytes ≤ p.Z := by
    have hwd : wOf mb = (mb + 63) / 64 := rfl
    have hL : p.L = (p.bits + 7) / 8 := rfl
    simp only [saveBytes, PP.Z]; omega_arith
  have env : Env s p.B (8 * p.n) (wOf mb) := ⟨h.scr, hp.a7, hp.s5, hp.t0, h.s6, by omega_arith, hw128,
    by simp only [PP.Z] at hZ; omega_arith⟩
  have harr : A s.mem p.B (wOf mb) 0 = N := by rw [A, Pre.wordsVal_eq_wv]; exact hn
  refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Search.montPrep_ok env harr hodd hN3))
    fun t ⟨⟨⟨envt, nt, inv, it1, r1, r9, r10, e, l, outs⟩, k⟩, _, _, tsp⟩ => ?_
  have fo : Frm p.B (VG.Proof.MillerRabin.RISCV64.Search.mpRanges (wOf mb)) s.mem t.mem := outs
  have hf : Frm p.B (mutR p.n) s.mem t.mem := Frm.toMut fo fun r hr => by
    simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact InMut.hdr (i := 7) (by decide)
    all_goals (try simp only [Impl.MillerRabin.RISCV64.aE]); exact InMut.arrays (by omega_arith) (by omega_arith)
  have st := h.step hf k tsp (by decide)
  have ew : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    fo.word_eq (fun r hr => by
      simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Impl.MillerRabin.RISCV64.aE] <;> omega_arith)
      (by omega_arith)
  have ph : Ph p mb t := ⟨envt.a7, envt.t0, envt.s5, (ew _ (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.RISCV64.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith)).trans hp.wW, (ew _ (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj),
    (ew _ (by simp only [hChecks]; omega_arith)).trans hp.checksW, (ew _ (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨⟨st, ph, ⟨⟨envt.hs, envt.hw, envt.hw', envt.hZ, envt.a7, envt.s5, envt.t0, it1, nt⟩, envt.s6,
    (ew 0 (by omega_arith)).trans h.args.wsLen, (ew 48 (by omega_arith)).trans hp.wW,
    (ew 224 (by omega_arith)).trans hp.strideW, fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj), hN3, hodd,
    inv, r1, r9, r10, e, l⟩, hm1, hm2⟩, hf, ew 152 (by omega_arith)⟩

/-- Before a modulus's Montgomery constants: what the test asks. -/
structure TCPre (p : PP) (mb N u : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb s
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits
  n : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  odd : N % 2 = 1
  n3 : 3 ≤ N
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  ul : u ≤ p.r.length

theorem TCPre.core {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u s) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N (checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u))) :=
  WP.seq (WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
    millerRabin_ok hR h.bl M (h152.trans h.used) h.ul)

/-- The low `k` words of a number below `2^(64 k)` are the number. -/
theorem wv_low {m : Mem} {B : Addr} {o w k v : Nat} (h : wv m B o w = v) (hk : k ≤ w)
    (hv : v < 2 ^ (64 * k)) : wv m B o k = v := by
  have e := wv_add m B o k (w - k)
  rw [show k + (w - k) = w by omega_arith, h] at e
  generalize 2 ^ (64 * k) = P at e hv
  generalize wv m B (o + 8 * k) (w - k) = hi at e
  rcases Nat.eq_zero_or_pos hi with h0 | hpos
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right P hpos; omega_arith

/-- `Ph` survives a change of memory that keeps the header. -/
theorem Ph.keepHdr {p : PP} {mb : Nat} {s t : State} (h : Ph p mb s)
    (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0) (r5 : t.gpr .s5 = s.gpr .s5)
    (hw : ∀ d, d + 8 ≤ 256 → word t.mem p.B d = word s.mem p.B d) : Ph p mb t :=
  ⟨r7.trans h.a7, r0.trans h.t0, r5.trans h.s5, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW,
    (hw 192 (by decide)).trans h.topW⟩

/-- The set-up of q's test: its working space. -/
theorem qPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq (phase true) (.block [])) s (TCPre p (p.bits - 1) ((c - 1) / 2) u) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hn' := h.dims.n'
  obtain ⟨hpo, hl, hu'⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo hl hu'
  obtain ⟨hql, hqu⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) hpo hl hu'
  have hbl := VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L)) (by rw [← hc]; exact hqo)
  rw [← hc] at hbl
  refine WP.seq (WP.mono (phase_ok h true) fun t ⟨⟨⟨st, ph, hf⟩, _⟩, _⟩ => ?_)
  simp only [mbOf, ↓reduceIte] at ph
  rw [WP.block_nil_iff]
  have hL : p.L = (p.bits + 7) / 8 := rfl
  have hwq : wOf (p.bits - 1) ≤ wOf p.bits := by simp only [wOf]; omega_arith
  refine ⟨st, ph, by omega_arith, by omega_arith, ?_, hbl, hqo, ?_, ?_, hul⟩
  · rw [slot_zero] at hq ⊢
    refine wv_low (w := wOf p.bits) ?_ hwq (Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by
      simp only [wOf]; omega_arith)))
    rw [hf.wv_eq (fun r hr => .inr (phR_low r hr)) (by simp only [wOf]; omega_arith)]
    exact hq
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 2 by omega_arith)
    omega_arith
  · rw [hf.word_eq phR_used (by decide)]; exact hu

/-- The test of q, halved in array 0 in p's width. -/
theorem testQ_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (test true R.name R.code) s
      (MrEnd p (p.bits - 1) ((c - 1) / 2)
        (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop u))) := by
  unfold test
  simp only [↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht => ht.core hR))

/-- The set-up of p's test: its working space, and p from the tape. -/
theorem pPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s (TCPre p p.bits c u) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  obtain ⟨hpo, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))).2
  rw [← hc] at hpo hl hbl
  refine WP.seq (WP.mono (phase_ok h false) fun t ⟨⟨⟨st, ph, hf⟩, _⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph
  refine WP.mono (WP.rdwr (shapeP_ok st ph hL)) fun t₂ ⟨⟨⟨hn₂, f₂⟩, k₂⟩, _, _, sp₂⟩ => ?_
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hlow : ∀ d, d + 8 ≤ 256 → word t₂.mem p.B d = word t.mem p.B d := fun d hd =>
    f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by rw [hsl]; exact hd)) (by omega_arith)
  have st₂ : St p t₂ := st.step (Frm.toMut f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact InMut.arrays (by rw [hsl]) (by rw [hsl]; simp only [saveBytes]; omega_arith)) k₂ sp₂ (by decide)
  have ph₂ : Ph p p.bits t₂ := ph.keepHdr (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide)) hlow
  refine ⟨st₂, ph₂, by omega_arith, Nat.le_refl _, by rw [hn₂, hc], hbl, hpo, ?_, ?_, hul⟩
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 1 by omega_arith)
    omega_arith
  · rw [hlow 152 (by decide), hf.word_eq phR_used (by decide)]; exact hu

/-- The test of p, loaded again from the tape. -/
theorem testP_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false R.name R.code) s
      (MrEnd p p.bits c (checkWitnesses c (Spec.Ffdh.primeChecks p.bits) (p.r.drop u))) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (pPrep_ok h hc hu hul hL) fun _ ht => ht.core hR))

/-! ## The results -/

theorem ofNat_toNat64' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `hStat` into `t3`. -/
theorem statLoad_ok {p : PP} {mb N : Nat} {s : State} (M : MSt p mb N s) :
    WP isa (.block [ldh .t3 hStat]) s fun t => MSt p mb N t ∧ t.gpr .t3 = word s.mem p.B 160 ∧ t.mem = s.mem ∧
      Keep [.t3] s t := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = word s.mem p.B 160 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp (by decide) (k.gpr (by decide))
    (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), t3, tm, k⟩

/-- `t3 - 1`, in `MSt`. -/
theorem sub1_ok {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N s) (h3 : s.gpr .t3 = BitVec.ofNat 64 v) :
    WP isa (.block [.addi .t3 .t3 (-1)]) s fun t => MSt p mb N t ∧ t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧
      t.mem = s.mem := by
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧
    t.mem = s.mem) (by brun [h3]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp (by decide) (k.gpr (by decide))
    (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), t3, tm⟩

theorem stat_one {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 == 0) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- After p's test. -/
theorem pResult_ok {p : PP} {s : State} {c : Nat} {resP : Option (Bool × List Byte)}
    (hE : MrEnd p p.bits c resP s) (hc : c < 2 ^ p.bits) :
    WP isa pResult s (CEnd p (resP.map fun x => (if x.1 then some c else none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold pResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  have h152 : word t.mem p.B 152 = word s.mem p.B 152 := by rw [tm]
  rcases resP with _ | ⟨b, rest⟩
  · have h0 := hnone rfl
    refine WP.ite true (eval_zero_ofNat t .t3 (k := 0) (by decide) (t3.trans h0)) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome b rest rfl
    have hU' : word t.mem p.B 152 = BitVec.ofNat 64 u := h152.trans hU
    cases b
    · refine WP.ite false (eval_zero_ofNat t .t3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (sub1_ok Mt (t3.trans hS)) fun v ⟨Mv, v3, vm⟩ => ?_)
      refine WP.ite false (by rw [eval_zero, v3]; decide) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine finEnd Mv.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [vm]; exact hU')
      simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · refine WP.ite false (eval_zero_ofNat t .t3 (k := 1) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (sub1_ok Mt (t3.trans hS)) fun v ⟨Mv, v3, vm⟩ => ?_)
      refine WP.ite true (by rw [eval_zero, v3]; decide) (fun _ => ?_) (fun h => absurd h (by decide))
      have hn : wv v.mem p.B 256 (wOf p.bits) = c := by
        have := Mv.prep.ctx.n
        rw [A, Pre.wordsVal_eq_wv, slot_zero] at this
        exact this
      exact pEnd Mv.st Mv.ph hn hc (by rw [vm]; exact hU') hul

/-- After a failed test of q. -/
theorem qResult_ok {p : PP} {s : State} {mb N : Nat} {resQ : Option (Bool × List Byte)}
    (hE : MrEnd p mb N resQ s) (hq : ∀ rest, resQ ≠ some (true, rest)) :
    WP isa qResult s (CEnd p (resQ.map fun x => (none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold qResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.ite true (eval_zero_ofNat t .t3 (k := 0) (by decide) (t3.trans (hnone rfl))) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · cases b
    · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome false rest rfl
      refine WP.ite false (eval_zero_ofNat t .t3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mt.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [tm]; exact hU)
      simp only [Option.map_some, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · exact absurd rfl (hq rest)

/-- `hStat` against 1. -/
theorem stat1_ok {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)]) s fun t =>
      isa.eval (.zero .t3) t = some (decide (v = 1)) ∧ MSt p mb N t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp
    (by decide) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), tm⟩

/-- The tests, once the shape passed: q in array 0 (in p's width), `used`
after p's octets. -/
theorem tests_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (testsSpec c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨_, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu
  unfold testsSpec tests
  rw [hbq, hbp]
  refine WP.seq (WP.mono (testQ_ok hR h hc hq hqo hU hL) fun t₁ e₁ => ?_)
  generalize checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop p.L) = resQ at e₁ ⊢
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    have e₂ : MrEnd p (p.bits - 1) ((c - 1) / 2) (some (b, p.r.drop u)) t₂ := by
      refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
      cases h
      exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      refine WP.seq (WP.mono (testP_ok hR M₂.st hc (by rw [hm]; exact hUu) hul hL) fun t₃ e₃ => ?_)
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
      generalize checkWitnesses c (Spec.Ffdh.primeChecks p.bits) (p.r.drop u) = resP at e₃ ⊢
      refine WP.mono (pResult_ok e₃ hcu) fun t ht => ?_
      rcases resP with _ | ⟨_ | _, _⟩ <;> exact ht

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
