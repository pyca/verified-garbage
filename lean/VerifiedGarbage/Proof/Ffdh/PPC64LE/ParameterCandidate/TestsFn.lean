module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Halve`, which this module and modules that import it used -/

section

/-! ### `Ffdh.ParameterCandidate.WordHalf`, which only this module used -/

section

/-!
# FFDH parameter candidates: halving a number of words in place

Each word shifted right by one, with the next word's low bit shifted in at
the top, is the number halved (`wv_half`). For any target whose words are 64
bits.
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen

theorem wv_half {m m' : Mem} {p : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hlo : ∀ j, j + 1 < w →
      word m' p (d + 8 * j) = (word m p (d + 8 * j) >>> 1) ||| (word m p (d + 8 * (j + 1)) <<< 63))
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) >>> 1) :
    wv m' p d w = wv m p d w / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi]
    by_cases hj : i / 64 + 1 < w
    · rw [hlo _ hj, BitVec.testBit_toNat, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
        simp only [show decide (i % 64 < 63) = true from decide_eq_true hb, Bool.not_true, Bool.and_false,
          Bool.false_and, Bool.or_false]
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 + 1 by omega,
          show (i + 1) % 64 = 0 by omega, BitVec.testBit_toNat, BitVec.getLsbD_of_ge _ _ (by omega),
          show i % 64 - 63 = 0 by omega, Nat.mul_add, Nat.mul_one]
        simp only [show decide (i % 64 < 64) = true from decide_eq_true (by omega),
          show decide (i % 64 < 63) = false from decide_eq_false hb, Bool.not_false, Bool.true_and, Bool.false_or]
    · have he : i / 64 = w - 1 := by omega
      rw [he, htop, BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = w - 1 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
      · rw [BitVec.getLsbD_of_ge _ _ (by omega), Nat.testBit_lt_two_pow]
        exact Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega)))]

end VG.Proof.Ffdh.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: q

`halveQ_ok`: array 0 halved in place (p into q = (p − 1) / 2, p being odd),
and `hBad` nonzero when q is even.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

theorem low_flag (x : BitVec 64) : (x &&& 1#64) ^^^ 1#64 = 0#64 ↔ x.toNat % 2 = 1 := by
  obtain e : x &&& 1#64 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
    omega_arith
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem wv_mod_two (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (word m p d).toNat % 2 := by
  obtain e := VG.Proof.RsaKeyGen.testBit_wv m p d w 0 (by omega_arith)
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.testBit_zero, decide_eq_decide] at e
  omega_arith

/-- The registers `halveQ` writes. -/
def hqRegs : List Reg := [.r3, .r4, .r5, .r6]

/-- Word `j` of the halved number. -/
abbrev halfW (m : Mem) (B : Addr) (a j : Nat) : BitVec 64 :=
  (word m B (a + 8 * j) >>> 1) ||| (word m B (a + 8 * (j + 1)) <<< 63)

theorem halveQ_ok {p : PP} {s : State} {w x : Nat} (hs : St p s) (h10 : s.gpr .r10 = off p.B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hx : wv s.mem p.B (slot w 0) w = x) (hw2 : 2 ≤ w)
    (hw : w < 2 ^ 31) (hZ : slot w 0 + 8 * w ≤ p.Z) :
    WP isa halveQ s fun t =>
      (wv t.mem p.B (slot w 0) w = x / 2 ∧
        (word t.mem p.B (8 * hBad) = 0#64 ↔ word s.mem p.B (8 * hBad) = 0#64 ∧ x / 2 % 2 = 1) ∧
        Frm p.B [(slot w 0, 8 * w), (8 * hBad, 8)] s.mem t.mem) ∧ Keep hqRegs s t := by
  have hnw := hs.scr.nowrap
  obtain h0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  rw [h0] at h10 hx hZ ⊢
  simp only [PP.Z] at hZ hnw
  unfold halveQ
  refine WP.seq (WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off p.B 256 ∧
      u.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u5, u6, um⟩, ku⟩ => ?_)
  · prun [h10, h11, BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = off p.B (256 + 8 * i) ∧ (∀ j < i, word t.mem p.B (256 + 8 * j) = halfW s.mem p.B 256 j) ∧
      (∀ j, i ≤ j → j < w → word t.mem p.B (256 + 8 * j) = word s.mem p.B (256 + 8 * j)) ∧
      Frm p.B [(256, 8 * w)] s.mem t.mem) ∧ Keep hqRegs s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t5, tlo, thi, tf⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [u5], fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [um],
      by rw [um]; exact Frm.refl _ _ _⟩, ku.mono (by decide)⟩ u6) fun t ht => ?_)
  · have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
    obtain l0 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * i)) 8 := hsc.ld (by omega_arith)
    obtain l1 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (i + 1))) 8 := hsc.ld (by omega_arith)
    obtain s0 : InRegions t.wr (off p.B (256 + 8 * i)) 8 := hsc.st (by omega_arith)
    obtain e8 : off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off p.B (256 + 8 * (i + 1)) := by
      rw [show off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off (off p.B (256 + 8 * i)) 8 from rfl, off_off,
        show 256 + 8 * i + 8 = 256 + 8 * (i + 1) by omega_arith]
    obtain r0 : t.mem.readW (off p.B (256 + 8 * i)) 64 = word s.mem p.B (256 + 8 * i) := thi i (by omega_arith) (by omega_arith)
    obtain r1 : t.mem.readW (off p.B (256 + 8 * (i + 1))) 64 = word s.mem p.B (256 + 8 * (i + 1)) :=
      thi (i + 1) (by omega_arith) (by omega_arith)
    refine WP.mono (WP.keep [.r3, .r4, .r5, .r6] (Q := fun u => u.gpr .r5 = off p.B (256 + 8 * (i + 1)) ∧
        u.mem = t.mem.writeW (off p.B (256 + 8 * i)) (halfW s.mem p.B 256 i) ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ?_ (by decide))
      fun u ⟨⟨u5, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, ?_, ?_⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · prun [t5, BitVec.add_zero, e8, l0, l1, s0, r0, r1]
    · intro j hj
      rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact tlo j hj
      · exact rw_self _ _ _
    · intro j hj hj'
      rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact thi j (by omega_arith) hj'
    · rw [um]
      exact frm_writeW tf _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by omega_arith)
  obtain ⟨⟨t5, tlo, thi, tf⟩, kt⟩ := ht
  obtain hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
  obtain lT : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (w - 1))) 8 := hsc.ld (by omega_arith)
  obtain sT : InRegions t.wr (off p.B (256 + 8 * (w - 1))) 8 := hsc.st (by omega_arith)
  obtain rT : t.mem.readW (off p.B (256 + 8 * (w - 1))) 64 = word s.mem p.B (256 + 8 * (w - 1)) :=
    thi (w - 1) (by omega_arith) (by omega_arith)
  obtain h31 : t.gpr .r31 = p.B := (kt.gpr .r31 (by decide)).trans hs.r31
  obtain t10 : t.gpr .r10 = off p.B 256 := (kt.gpr .r10 (by decide)).trans h10
  obtain lB : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 200) 8 := hsc.ld (d := 200) (by omega_arith)
  obtain sB : InRegions t.wr (p.B + BitVec.ofNat 64 200) 8 := hsc.st (d := 200) (by omega_arith)
  obtain l0 : InRegions (t.rd ++ t.wr) (off p.B 256) 8 := hsc.ld (by omega_arith)
  obtain rB : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (p.B + BitVec.ofNat 64 200) 64 =
      word s.mem p.B 200 := fun v => by
    rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
  obtain r0 : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (off p.B 256) 64 =
      halfW s.mem p.B 256 0 := fun v => by
    rw [show off p.B 256 = off p.B (256 + 8 * 0) from rfl, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tlo 0 (by omega_arith)
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun u => u.mem =
      (t.mem.writeW (off p.B (256 + 8 * (w - 1))) (word s.mem p.B (256 + 8 * (w - 1)) >>> 1)).writeW
        (p.B + BitVec.ofNat 64 200) (word s.mem p.B 200 ||| ((halfW s.mem p.B 256 0 &&& 1#64) ^^^ 1#64))) ?_
      (by decide)) fun u ⟨um, ku⟩ => ⟨?_, (kt.trans ku).mono (by decide)⟩
  · simp only [ldh, sth, hBad]
    prun [t5, t10, h31, BitVec.add_zero, lT, sT, rT, lB, sB, l0, rB, r0]
  obtain hv : wv u.mem p.B 256 w = x / 2 := by
    rw [← hx]
    refine Proof.Ffdh.ParameterCandidate.wv_half (by omega_arith) (fun j hj => ?_) ?_
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact tlo j (by omega_arith)
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
  refine ⟨hv, ?_, ?_⟩
  · have e := wv_mod_two u.mem p.B 256 (w := w) (by omega_arith)
    obtain t0 : t.mem.readW (p.B + BitVec.ofNat 64 256) 64 = halfW s.mem p.B 256 0 := tlo 0 (by omega_arith)
    rw [hv, um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      t0] at e
    simp only [word, off, hBad, Nat.reduceMul, um, rw_self, BitVec.or_eq_zero_iff, low_flag]
    rw [e]
  · rw [um]
    refine frm_writeW (frm_writeW (tf.mono fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) _
        ⟨_, List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by omega_arith)) _
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by omega_arith)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the tests

`tests_ok`: one witness of p, then q's if it passed, then p's others if q
passed, and their result (`Proof.Ffdh.ParameterCandidate.sievedTests`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses onPass sievedTests)

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

/-- `hStat` against 1. -/
theorem stat1_ok {C : Nat} {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N C s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 1]) s fun t =>
      isa.eval (.zero .d .r3) t = some (decide (v = 1)) ∧ MSt p mb N C t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide)), tm⟩

/-- After a test that ended with `res`: the end of the candidate when it did
not pass (`qResult`), else `cont` from octet `u` of the tape. -/
theorem stage_ok {C : Nat} {p : PP} {mb N : Nat} {t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa} (e₁ : MrEnd p mb N C res t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MSt p mb N C t₂ → t₂.mem = t₁.mem →
      word t₂.mem p.B 152 = BitVec.ofNat 64 u → WP isa cont t₂ (CEnd p (k (p.r.drop u)))) :
    WP isa (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (.ite (.zero .d .r3) cont qResult)) t₁
      (CEnd p (onPass res k)) := by
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      have e₂ : MrEnd p mb N C (some (false, p.r.drop u)) t₂ := by
        refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
        cases h
        exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      exact hcont u t₂ hul rfl M₂ hm (by rw [hm]; exact hUu)

/-- q, from p in array 0. -/
theorem halveQ_from {K : Nat} {p : PP} {s : State} {c u : Nat} (M : MSt p p.bits c K s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 u) :
    WP isa halveQ s fun t => St p t ∧ wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2 ∧
      word t.mem p.B 152 = BitVec.ofNat 64 u := by
  have hb1 := M.st.dims.b1
  have hb2 := M.st.dims.b2
  have hdn := M.st.dims.n
  obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hn₂ : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    rw [← Pre.val32_eq_wv]; exact M.prep.n
  refine WP.mono (halveQ_ok M.st M.ph.r10 M.ph.r11 hn₂ (by omega_arith) (by omega_arith)
    (by rw [hsl]; omega_arith)) fun t₃ ⟨⟨hq₃, _, f₃⟩, k₃⟩ => ⟨?_, ?_, ?_⟩
  · exact M.st.step (Frm.toMut f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact InMut.arrays (by decide) (by simp only [saveBytes]; omega_arith)
      · exact InMut.hdr (i := 25) (by decide)) k₃ (by decide) (by decide)
  · rw [hq₃]; omega_arith
  · rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact .inl (by dsimp only; omega_arith)
      · exact .inl (by decide)) (by decide)]
    exact hU

/-- The tests, once the shape passed: one witness of p, all of q's, then
p's others, `used` after p's octets. -/
theorem tests_ok (R : RoundImpl) {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (sievedTests c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨hpo, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu hpo
  unfold sievedTests tests
  rw [hbq, hbp]
  -- p's first witness.
  refine WP.seq (WP.mono (testP1_ok R h hc hU hL hL) fun t₁ e₁ => ?_)
  refine stage_ok e₁ fun u₁ t₂ hu₁ _ M₂ _ hU₂ => ?_
  -- q, from p in array 0, and its test.
  unfold testQ
  refine WP.seq (WP.mono (halveQ_from M₂ hc hU₂) fun t₃ ⟨st₃, hq₃, hU₃⟩ => ?_)
  refine WP.seq (WP.mono (testQ_ok R st₃ hc hq₃ hqo hU₃ hu₁) fun t₄ e₄ => ?_)
  refine stage_ok e₄ fun u₂ t₅ hu₂ _ M₅ _ hU₅ => ?_
  -- p's other witnesses.
  unfold testRest
  refine WP.seq (WP.mono (testPR_ok R M₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_)
  exact pResult_ok e₆ hcu

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
