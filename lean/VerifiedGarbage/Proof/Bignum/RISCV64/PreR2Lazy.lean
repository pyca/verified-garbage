module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Words
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.WordStepLazy
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: lazy steps of long division

`Precompute.step` and `Precompute.finish`, which divide by `n` (`w ≥ 4`
words, its top word not zero) 63 bits a step with the remainder kept in
`[0, 2 n)` (`Proof/Bignum/WordStepLazy.lean`), and `R² mod n` by them:

* `mulSub_ok`: `V := (V - q̂ n) 2^63 + c` modulo `2^(64 (w + 1))`, for the
  chunk `c = ⌊t₆ / 2⌋`, with the borrow of `V - q̂ n`;
* `step_ok`: a step, `q̂` from `quot_ok` and `quot3_ok` lowered by one
  (`WordStep.dec_bounds`), so that `t = V - q̂ n` is in `[0, 2 n)` and
  congruent to `V` (`WordStep.lazy_step`), for any `mid` that sets `t6`;
* `finish_ok`: `x := ⌊V / 2^63⌋ mod n`, for `⌊V / 2^63⌋ < 2 n`;
* `r2Words_ok`: `x := 2^(128 w) mod n`, by `r2Init`, the `S` steps with zero
  chunks (`r2Steps_ok`) and `finish`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot)

/-! ## `V := (V - q̂ n) 2^63 + c` -/

/-- What `mulSub` keeps after `i` words, from `s` (`q` in `s1`, `C` the chunk):
the pointers, `V`'s words from `i` on, the carry `c` (`s0`) and the borrow `b`
(`s4`), for `T`, `t`'s low `i` words, with `T + q n_{<i} = V_{<i} + 2^(64 i)
(b + c)`, and the words written so far, below `t6`, the last of `t`, shifted:
`W + 2^(64 i) ⌊t₆ / 2⌋ = T 2^63 + C`. -/
def MSInv (s : State) (B : Addr) (dV dN C : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dV + 8 * i) ∧ t.gpr .t4 = off B (dN + 8 * i) ∧ t.gpr .s1 = s.gpr .s1 ∧
    (t.gpr .s4).toNat ≤ 1 ∧ Outside B dV (8 * i) s.mem t.mem ∧
    (∃ T, T < 2 ^ (64 * i) ∧
      T + (s.gpr .s1).toNat * wordsVal s.mem B dN i =
        wordsVal s.mem B dV i + 2 ^ (64 * i) * ((t.gpr .s4).toNat + (t.gpr .s0).toNat) ∧
      wordsVal t.mem B dV i + 2 ^ (64 * i) * ((t.gpr .t6).toNat / 2) = T * 2 ^ 63 + C) ∧
    Keep [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6] s t

/-- The word stored: `⌊p / 2⌋ + 2^63 (t mod 2)`. -/
theorem shr1_or_shl63 (p t : BitVec 64) :
    ((p >>> 1) ||| (t <<< 63)).toNat = p.toNat / 2 + t.toNat % 2 * 2 ^ 63 :=
  WordStep.shr_or_shl p t (s := 1) (t := 63) rfl

theorem mulSubWord_ok {s : State} {B : Addr} {Z dV dN C w : Nat} (hs : Scr s B Z) (hV8 : dV % 8 = 0)
    (hN8 : dN % 8 = 0) (hV : dV + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z)
    (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN) {i : Nat} (hi : i < w) {t : State}
    (hI : MSInv s B dV dN C i t) :
    WP isa (.block (mulSubWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      MSInv s B dV dN C (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j1, jb, jout, ⟨T, hT, jv, jw⟩, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wX : Mont.word t.mem B (dV + 8 * i) = Mont.word s.mem B (dV + 8 * i) := jout.word (by omega) (by omega)
  have wN : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  generalize hn : Mont.word s.mem B (dN + 8 * i) = n at wN
  generalize hxv : Mont.word s.mem B (dV + 8 * i) = xv at wX
  generalize hlo : n * t.gpr .s1 + t.gpr .s0 = lo
  generalize htw : xv - lo - t.gpr .s4 = tw
  refine WP.mono (WP.keep [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6] (Q := fun t' =>
      t'.gpr .t3 = off B (dV + 8 * i + 8) ∧ t'.gpr .t4 = off B (dN + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      t'.gpr .s0 = BitVec.ofNat 64 (n.toNat * (t.gpr .s1).toNat / 2 ^ 64) + (if lo < t.gpr .s0 then 1 else 0) ∧
      t'.gpr .s4 = ((if xv < lo then (1 : BitVec 64) else 0) ||| (if xv - lo < t.gpr .s4 then 1 else 0)) ∧
      t'.gpr .t6 = tw ∧
      t'.mem = t.mem.writeW (off B (dV + 8 * i)) ((t.gpr .t6 >>> 1) ||| (tw <<< 63))) (by
    have rN : t.mem.readW (off B (dN + 8 * i)) 64 = n := wN
    have rX : t.mem.readW (off B (dV + 8 * i)) 64 = xv := wX
    unfold mulSubWord
    brun [j3, j4, rN, rX, hlo, htw, BitVec.add_zero, hs'.ld (show dN + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dN + 8 * i + 8 ≤ Z by omega) (by omega), hs'.ld (show dV + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dV + 8 * i + 8 ≤ Z by omega) (by omega), hs'.st (show dV + 8 * i + 8 ≤ Z by omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u0, u4b, u6, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_,
      Keep.trans' jk uk⟩, u5⟩
  · rw [u3, show dV + 8 * i + 8 = dV + 8 * (i + 1) by omega]
  · rw [u4, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
  · rw [uk.gpr (by decide), j1]
  · rw [u4b]; exact (sub64_arith _ _ _ jb).2
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dV + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have km := mul_arith n (t.gpr .s1) (t.gpr .s0)
    have ks := (sub64_arith xv lo (t.gpr .s4) jb).1
    rw [hlo, j1] at km
    rw [htw] at ks
    have hst := shr1_or_shl63 (t.gpr .t6) tw
    have htw2 := Nat.div_add_mod tw.toNat 2
    refine ⟨T + 2 ^ (64 * i) * tw.toNat, ?_, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show tw.toNat + 1 ≤ 2 ^ 64 from tw.isLt)
      rw [Nat.mul_succ] at this
      rw [show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      omega
    · rw [u4b, u0, wordsVal_succ_top s.mem B dN i, hn, j1, wordsVal_succ_top s.mem B dV i, hxv,
        show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      generalize 2 ^ (64 * i) = P at jv ⊢
      generalize ((if xv < lo then (1 : BitVec 64) else 0) ||| (if xv - lo < t.gpr .s4 then 1 else 0)).toNat
        = b' at ks ⊢
      generalize (BitVec.ofNat 64 (n.toNat * (s.gpr .s1).toNat / 2 ^ 64) + (if lo < t.gpr .s0 then 1 else 0)).toNat
        = c' at km ⊢
      generalize tw.toNat = tv at ks ⊢
      generalize lo.toNat = l at km ks
      generalize (s.gpr .s1).toNat = q at km jv ⊢
      generalize n.toNat = nn at km ⊢
      generalize (t.gpr .s4).toNat = b at ks jv
      generalize (t.gpr .s0).toNat = c at km jv
      generalize wordsVal s.mem B dN i = Nw at jv ⊢
      generalize wordsVal s.mem B dV i = Vw at jv ⊢
      have hin : b + c + tv + nn * q = xv.toNat + 2 ^ 64 * (b' + c') := by omega_using [km, ks]
      have := congrArg (P * ·) hin
      grind
    · rw [um, u6, fin64_wordsVal_write_top _ _ _ _ _ (by omega), hst,
        show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      generalize 2 ^ (64 * i) = P at jw ⊢
      generalize (t.gpr .t6).toNat / 2 = p at jw ⊢
      generalize tw.toNat = tv at htw2 ⊢
      generalize wordsVal t.mem B dV i = W at jw ⊢
      have e2 : tv * 2 ^ 63 = tv % 2 * 2 ^ 63 + tv / 2 * 2 ^ 64 := by
        rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]
        omega
      grind

/-- The registers `mulSub` writes. -/
def mulSubRegs : List Reg := [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6]

/-- `mulSub`, after `mulSubHead` (`V`, `w + 1` words, at `dV`, `n` at `dN`,
`q` in `s1`, the chunk shifted up a bit in `t6`): `V := T 2^63 + C` modulo
`2^(64 (w + 1))` for `C = ⌊t₆ / 2⌋` and `T + q n = V + 2^(64 (w + 1)) b`, for
the borrow `b`. -/
theorem mulSub_ok {s : State} {B : Addr} {Z dV dN w : Nat} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B dV) (h4 : s.gpr .t4 = off B dN) (h5 : s.gpr .t5 = BitVec.ofNat 64 w)
    (h0 : s.gpr .s0 = 0) (hb : s.gpr .s4 = 0)
    (hV8 : dV % 8 = 0) (hN8 : dN % 8 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hV : dV + 8 * (w + 1) ≤ Z)
    (hN : dN + 8 * w ≤ Z) (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN) :
    WP isa mulSub s fun t =>
      ((∃ b < 2, ∃ T < 2 ^ (64 * (w + 1)),
        T + (s.gpr .s1).toNat * wordsVal s.mem B dN w = wordsVal s.mem B dV (w + 1) + 2 ^ (64 * (w + 1)) * b ∧
        wordsVal t.mem B dV (w + 1) = (T * 2 ^ 63 + (s.gpr .t6).toNat / 2) % 2 ^ (64 * (w + 1))) ∧
      Outside B dV (8 * (w + 1)) s.mem t.mem) ∧ Keep mulSubRegs s t := by
  have hnw := hs.nowrap
  unfold mulSub
  have I0 : MSInv s B dV dN ((s.gpr .t6).toNat / 2) 0 s := ⟨by rw [h3]; rfl, by rw [h4]; rfl, rfl,
    by rw [hb]; decide, Outside.refl _ _ _ _, ⟨0, by decide, by simp [wordsVal, hb, h0], by simp [wordsVal]⟩,
    Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega)
    (MSInv s B dV dN ((s.gpr .t6).toNat / 2))
    (fun i hi t hI _ => mulSubWord_ok hs hV8 hN8 hV hN dNV hi hI) I0 h5)
    fun t ⟨j3, _, j1, jb, jout, ⟨T, hT, jv, jw⟩, jk⟩ => ?_)
  have hs' := hs.congr jk.2.2
  have wX : Mont.word t.mem B (dV + 8 * w) = Mont.word s.mem B (dV + 8 * w) := jout.word (by omega) (by omega)
  generalize hxv : Mont.word s.mem B (dV + 8 * w) = xv at wX
  generalize htw : xv - t.gpr .s0 - t.gpr .s4 = tw
  refine WP.mono (WP.keep [.a0, .s3, .a3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dV + 8 * w)) ((t.gpr .t6 >>> 1) ||| (tw <<< 63))) (by
    have rX : t.mem.readW (off B (dV + 8 * w)) 64 = xv := wX
    unfold mulSubTop
    brun [j3, rX, htw, hs'.ld (show dV + 8 * w + 8 ≤ Z by omega), hs'.st (show dV + 8 * w + 8 ≤ Z by omega),
      hs'.al8 (show dV + 8 * w + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t' ⟨tm, tk⟩ => ⟨⟨?_, ?_⟩, (jk.trans tk).mono (by decide)⟩
  · have ks := sub64_arith xv (t.gpr .s0) (t.gpr .s4) jb
    rw [htw] at ks
    have hst := shr1_or_shl63 (t.gpr .t6) tw
    have e1 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    refine ⟨_, Nat.lt_succ_of_le ks.2, T + 2 ^ (64 * w) * tw.toNat, ?_, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show tw.toNat + 1 ≤ 2 ^ 64 from tw.isLt)
      rw [Nat.mul_succ] at this
      rw [e1]; omega
    · rw [wordsVal_succ_top s.mem B dV w, hxv, e1]
      have ks1 := ks.1
      generalize 2 ^ (64 * w) = P at jv ⊢
      generalize (s.gpr .s1).toNat * wordsVal s.mem B dN w = qN at jv ⊢
      generalize ((if xv < t.gpr .s0 then (1 : BitVec 64) else 0) |||
        (if xv - t.gpr .s0 < t.gpr .s4 then 1 else 0)).toNat = b' at ks1 ⊢
      generalize tw.toNat = tv at ks1 ⊢
      generalize (t.gpr .s0).toNat = c at ks1 jv
      generalize (t.gpr .s4).toNat = b at ks1 jv
      generalize wordsVal s.mem B dV w = Vw at jv ⊢
      have hin : b + c + tv = xv.toNat + 2 ^ 64 * b' := by omega_using [ks1]
      have := congrArg (P * ·) hin
      grind
    · rw [tm, fin64_wordsVal_write_top _ _ _ _ _ (by omega), hst]
      have hlt := wordsVal_lt (t.mem.writeW (off B (dV + 8 * w)) ((t.gpr .t6 >>> 1) ||| (tw <<< 63))) B dV (w + 1)
      rw [fin64_wordsVal_write_top _ _ _ _ _ (by omega), hst] at hlt
      have htw2 := Nat.div_add_mod tw.toNat 2
      have e2 : tw.toNat * 2 ^ 63 = tw.toNat % 2 * 2 ^ 63 + tw.toNat / 2 * 2 ^ 64 := by
        rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]
        omega
      have key : wordsVal t.mem B dV w + 2 ^ (64 * w) * ((t.gpr .t6).toNat / 2 + tw.toNat % 2 * 2 ^ 63) +
          2 ^ (64 * (w + 1)) * (tw.toNat / 2) =
          (T + 2 ^ (64 * w) * tw.toNat) * 2 ^ 63 + (s.gpr .t6).toNat / 2 := by
        rw [e1]
        generalize 2 ^ (64 * w) = P at jw ⊢
        generalize (t.gpr .t6).toNat / 2 = p at jw ⊢
        generalize tw.toNat = tv at e2 ⊢
        generalize wordsVal t.mem B dV w = W at jw ⊢
        grind
      rw [← key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [tm]
    exact (Outside.mono (fun x hx => jout x hx) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dV + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-! ## A step -/

/-- `dec`, `a4 = 0`: `q̂ := q̂ - 1` unless it is 0. -/
theorem dec_val {s : State} (h4 : s.gpr .a4 = 0) :
    WP isa (.block dec) s fun t => ((t.gpr .s1).toNat =
      (s.gpr .s1).toNat - (if 0 < (s.gpr .s1).toNat then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.s1, .s4] s t := by
  refine WP.keep [.s1, .s4] ?_ (by rfl) (by rfl)
  unfold dec
  brun [h4]
  have hlt : ((0 : BitVec 64) < s.gpr .s1) ↔ 0 < (s.gpr .s1).toNat := Iff.rfl
  by_cases h : 0 < (s.gpr .s1).toNat
  · rw [ite_eq_left (hlt.mpr h), ite_eq_left h, BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]; show 1 ≤ (s.gpr .s1).toNat; omega)]; rfl
  · rw [ite_eq_right (fun h' => h (hlt.mp h')), ite_eq_right h, Nat.sub_zero]
    exact congrArg BitVec.toNat (BitVec.sub_zero _)

/-- The registers a step writes, but `mid`'s. -/
def stepRegs : List Reg := [.a0, .a3, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `step mid`, `n` (`w ≥ 4` words) at `dN` (`a7`), `V < n 2^64` (`w + 1`
words, and room for a word more) at `dV` (`a2`), and `P = 2^z`,
`d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63`, `v = ⌊(2^128 - 1) / d'⌋ - 2^64` and
`d'ₗ`, `(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the temporary at `dT`
(`a6`), zero in `a4`, for a `mid` that sets `t6` to `2 C` or `2 C + 1`,
keeping memory and the registers the step reads after it:
`V := t 2^63 + C` for some `t < 2 n` congruent to `V` modulo `n`, changing only
`V`'s `w + 1` words. -/
theorem step_ok {mid : List Instr} {midRegs : List Reg} {C : Nat} {Pm : State → Prop} {s : State} {B : Addr}
    {Z dV dN dT w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dV) (h6 : s.gpr .a6 = off B dT) (h7 : s.gpr .a7 = off B dN)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (hw : 4 ≤ w)
    (hw' : w < 2 ^ 31) (hV8 : dV % 8 = 0) (hN8 : dN % 8 = 0) (hT8 : dT % 8 = 0)
    (hVZ : dV + 8 * (w + 2) ≤ Z) (hNZ : dN + 8 * w ≤ Z) (hTZ : dT + 32 ≤ Z)
    (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN)
    (hP : (Mont.word s.mem B dT).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd : (Mont.word s.mem B (dT + 8)).toNat = wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (dT + 16)).toNat = (2 ^ 128 - 1) / (Mont.word s.mem B (dT + 8)).toNat - 2 ^ 64)
    (hdl : (Mont.word s.mem B (dT + 8)).toNat * 2 ^ 64 + (Mont.word s.mem B (dT + 24)).toNat =
      wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hV : wordsVal s.mem B dV (w + 1) < wordsVal s.mem B dN w * 2 ^ 64)
    (hmid : ∀ u, Keep stepRegs s u → u.mem = s.mem →
      WP isa (.block mid) u fun u' => (u'.gpr .t6).toNat / 2 = C ∧ u'.mem = u.mem ∧ Keep midRegs u u' ∧ Pm u')
    (hmidR : ∀ r ∈ [Reg.a2, .a7, .t0, .s1], r ∉ midRegs)
    (hPm : ∀ u u', Pm u → Keep stepRegs u u' → Outside B dV (8 * (w + 1)) u.mem u'.mem → Pm u') :
    WP isa (step mid) s fun t =>
      (∃ T, T < 2 * wordsVal s.mem B dN w ∧ T % wordsVal s.mem B dN w = wordsVal s.mem B dV (w + 1) % wordsVal s.mem B dN w ∧
        wordsVal t.mem B dV (w + 1) = T * 2 ^ 63 + C ∧ Outside B dV (8 * (w + 1)) s.mem t.mem) ∧
      Keep (stepRegs ++ midRegs) s t ∧ Pm t := by
  have hnw := hs.nowrap
  generalize hN : wordsVal s.mem B dN w = N at hd hd63 hdl hV ⊢
  generalize hVv : wordsVal s.mem B dV (w + 1) = Y at hV ⊢
  generalize hX : wordsVal s.mem B (dV + 8) w = X
  generalize huw : Mont.word s.mem B dV = uw
  have hu := uw.isLt
  have hY : X * 2 ^ 64 + uw.toNat = Y := by
    have e : wordsVal s.mem B dV (w + 1) = (Mont.word s.mem B dV).toNat + 2 ^ 64 * wordsVal s.mem B (dV + 8) w :=
      rfl
    rw [← hVv, ← hX, ← huw, e, Nat.mul_comm, Nat.add_comm]
  have hx : X < N := by
    rcases Nat.lt_or_ge X N with h | h
    · exact h
    · have := Nat.mul_le_mul_right (2 ^ 64) h; omega
  have hXd : wordsVal s.mem B (dV + 8) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (dT + 8)).toNat := by
    rw [hd, hX]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hx))
  -- The estimates (`WordStep.qhat3_div`), for `U = ⌊V P / 2^(64 (w - 2))⌋ = ⌊x P / 2^(64 (w - 3))⌋`
  -- (`WordStep.shift_u`) and `D = ⌊n P / 2^(64 (w - 2))⌋`.
  have hk3 : 64 * (w - 3) + 64 = 64 * (w - 2) := by omega
  have hk2 : 64 * (w - 2) + 64 = 64 * (w - 1) := by omega
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ := WordStep.qhat3_div (Y := Y) (M := N) (P := 2 ^ z) (K := 64 * (w - 3))
    (Nat.two_pow_pos z) hV (by rw [hk3, Nat.div_div_eq_div_mul, ← Nat.pow_add, hk2]; exact hd63)
  have hsh : Y * 2 ^ z / 2 ^ (64 * (w - 3) + 64) = X * 2 ^ z / 2 ^ (64 * (w - 3)) := by
    rw [← hY, show 64 * (w - 3) + 64 = 64 * (w - 4) + 128 by omega,
      WordStep.shift_u (by omega) hu, show 64 * (w - 4) + 64 = 64 * (w - 3) by omega]
  rw [hsh] at hUD hq1 hq2 hge hle
  rw [hk3] at hUD hq1 hq2 hge hle
  have hUu : X * 2 ^ z / 2 ^ (64 * (w - 3)) / 2 ^ 64 = X * 2 ^ z / 2 ^ (64 * (w - 2)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hk3]
  have hDu : N * 2 ^ z / 2 ^ (64 * (w - 2)) / 2 ^ 64 = (Mont.word s.mem B (dT + 8)).toNat := by
    rw [← hdl, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt (Mont.word s.mem B (dT + 24)).isLt, Nat.add_zero]
  rw [hUu, hDu] at hq1 hq2
  have hD0 : 0 < N * 2 ^ z / 2 ^ (64 * (w - 2)) := by
    have := Nat.mul_le_mul_right (2 ^ 64) (show 1 ≤ (Mont.word s.mem B (dT + 8)).toNat by omega)
    omega
  unfold step
  simp only [List.append_assoc]
  -- `q̂`, corrected, then lowered.
  refine WP.seq (WP.block_append (WP.mono (quot_ok (dX := dV + 8) hs (by rw [h2, Nat.add_sub_cancel]) h6 ht0 h4
    (by omega) hw' (by omega) (by omega) hT8 (by omega) hTZ hP hz (by rw [hd]; exact hd63) hv hXd)
    fun s₁ ⟨⟨q1, m1, t3, tu, ts2⟩, k1⟩ => ?_))
  rw [hX] at q1 tu
  have g1 : ∀ r ∈ [Reg.a6, .a4], s₁.gpr r = s.gpr r := fun r hr => k1.gpr (by revert r hr; decide)
  have hs₁ := hs.congr k1.2.2
  refine WP.block_append (WP.mono (quot3_ok (D := N * 2 ^ z / 2 ^ (64 * (w - 2))) hs₁ t3
    ((g1 .a6 (by decide)).trans h6) ((g1 .a4 (by decide)).trans h4) hw hw' (by omega) hT8 (by omega) hTZ
    (by rw [m1]; exact hP) hz (by rw [m1, hX]; exact tu)
    (by rw [ts2, m1]; exact hdl) hD0 (by rw [m1, hX]; exact hUD)
    (by rw [m1, hX, q1]; exact hq1) (by rw [m1, hX, q1]; exact hq2)) fun s₂ ⟨⟨q2, m2⟩, k2⟩ => ?_)
  rw [m1, hX] at q2
  rw [m1] at m2
  have k12 := k1.trans k2
  refine WP.block_append (WP.mono (dec_val ((k12.gpr (by decide)).trans h4)) fun s₃ ⟨⟨q3, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have hq3 := WordStep.dec_bounds hge hle
  rw [← q2, ← q3] at hq3
  rw [m2] at m3
  refine WP.block_append (WP.mono (hmid s₃ (k13.mono (by decide)) m3) fun s₄ ⟨c4, m4, k4, p4⟩ => ?_)
  rw [m3] at m4
  have g4 : ∀ r ∈ [Reg.a2, .a7, .t0, .s1], s₄.gpr r = s₃.gpr r := fun r hr => k4.gpr (hmidR r hr)
  have g3 : ∀ r ∈ [Reg.a2, .a7, .t0], s₃.gpr r = s.gpr r := fun r hr => k13.gpr (by revert r hr; decide)
  refine WP.mono (WP.keep [.t3, .t4, .t5, .s0, .s4] (Q := fun t =>
      t.gpr .t3 = off B dV ∧ t.gpr .t4 = off B dN ∧ t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s0 = 0 ∧
        t.gpr .s4 = 0 ∧ t.mem = s₄.mem)
    (by
      unfold mulSubHead
      brun [(g4 .a2 (by decide)).trans ((g3 .a2 (by decide)).trans h2),
        (g4 .a7 (by decide)).trans ((g3 .a7 (by decide)).trans h7),
        (g4 .t0 (by decide)).trans ((g3 .t0 (by decide)).trans ht0), exec_li_zero, BitVec.add_zero])
    (by rfl) (by rfl)) fun s₅ ⟨⟨i3, i4, i5, i0, ib, im⟩, k5⟩ => ?_
  have k45 := k4.trans k5
  rw [m4] at im
  refine WP.mono (mulSub_ok (dV := dV) (dN := dN) (hs.congr ((k13.trans k45).2.2)) i3 i4 i5 i0 ib hV8 hN8
    (by omega) hw' (by omega) hNZ dNV) fun t ⟨⟨⟨b, hb, T, hT, e1, e2⟩, o⟩, k⟩ => ?_
  have s1e : (s₅.gpr .s1).toNat = (s₃.gpr .s1).toNat := by
    rw [k5.gpr (by decide), g4 .s1 (by decide)]
  have t6e : (s₅.gpr .t6).toNat / 2 = C := by rw [k5.gpr (by decide)]; exact c4
  rw [im, hN, hVv, s1e] at e1
  rw [im] at o
  rw [t6e] at e2
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.zero_mul] at hV; omega
    · exact h
  obtain ⟨_, hT2, hTm⟩ := WordStep.lazy_step hN0 hq3.1 hq3.2 hT hb e1
  refine ⟨⟨T, hT2, hTm, ?_, o⟩, ?_, hPm _ _ p4 ((k5.trans k).mono (by decide)) (by rw [m4]; exact o)⟩
  · rw [e2, Nat.mod_eq_of_lt]
    have hN' : N < 2 ^ (64 * w) := hN ▸ wordsVal_lt _ _ _ _
    have hC : C < 2 ^ 63 := by rw [← c4]; have := (s₄.gpr .t6).isLt; omega
    rw [show 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add],
      show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]
    generalize 2 ^ (64 * w) = P at hN' ⊢
    have h1 := Nat.mul_le_mul_right (2 ^ 63) (show T + 1 ≤ 2 * P by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at h1
    omega
  · have kA : Keep stepRegs s s₃ := k13.mono (by decide)
    have kB : Keep stepRegs s₄ t := (k5.trans k).mono (by decide)
    exact ((kA.trans k4).trans kB).mono fun r hr => by
      rw [List.mem_append] at hr
      rcases hr with h | h
      · exact h
      · exact List.mem_append_left _ h

/-! ## `x := ⌊V / 2^63⌋ mod n` -/

/-- `R`'s word `i` from `V`'s words `i` and `i + 1`, for `R = ⌊V / 2^63⌋`. -/
theorem unshift_word (V i : Nat) (vi vj : BitVec 64) (hi : vi.toNat = V / 2 ^ (64 * i) % 2 ^ 64)
    (hj : vj.toNat = V / 2 ^ (64 * (i + 1)) % 2 ^ 64) :
    ((vi >>> 63) ||| (vj <<< 1)).toNat = V / 2 ^ 63 / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [WordStep.shr_or_shl vi vj (s := 63) (t := 1) rfl, hi, hj, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.add_comm 63, WordStep.shr_words V i (by decide)]

/-- The low `i + 1` words of a number, from its low `i` and word `i`. -/
theorem mod_succ_words (R i : Nat) :
    R % 2 ^ (64 * (i + 1)) = R % 2 ^ (64 * i) + 2 ^ (64 * i) * (R / 2 ^ (64 * i) % 2 ^ 64) := by
  rw [show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add], Nat.mod_mul]

/-- The registers `finish` writes. -/
def finRegs : List Reg := [.a0, .a3, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- What `finish`'s first pass keeps after `i` words, for `V` (`w + 1` words
at `dV`) and `R = ⌊V / 2^63⌋`: the pointers, `V`'s word `i` in `s2` and
`V`'s words from `i` on, `R`'s low `i` words in place of `V`'s, and the
borrow `b` (`s4`) of `R - n` over them: `D + n_{<i} = R_{<i} + 2^(64 i) b`
for some `D`. -/
def FInv (s : State) (B : Addr) (dV dN w : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dV + 8 * i) ∧ t.gpr .t4 = off B (dN + 8 * i) ∧ t.gpr .s2 = Mont.word s.mem B (dV + 8 * i) ∧
    (t.gpr .s4).toNat ≤ 1 ∧ Outside B dV (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dV i = wordsVal s.mem B dV (w + 1) / 2 ^ 63 % 2 ^ (64 * i) ∧
    (∃ D < 2 ^ (64 * i), D + wordsVal s.mem B dN i = wordsVal s.mem B dV (w + 1) / 2 ^ 63 % 2 ^ (64 * i) +
      2 ^ (64 * i) * (t.gpr .s4).toNat) ∧
    Keep finRegs s t

theorem finWord1_ok {s : State} {B : Addr} {Z dV dN w : Nat} (hs : Scr s B Z) (hV8 : dV % 8 = 0)
    (hN8 : dN % 8 = 0) (hV : dV + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z)
    (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN) {i : Nat} (hi : i < w) {t : State}
    (hI : FInv s B dV dN w i t) :
    WP isa (.block (finWord1 ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      FInv s B dV dN w (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j2, jb, jout, jv, ⟨D, hD, jd⟩, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wN : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  have wX : Mont.word t.mem B (dV + 8 * i + 8) = Mont.word s.mem B (dV + 8 * (i + 1)) := by
    rw [show dV + 8 * i + 8 = dV + 8 * (i + 1) by omega]; exact jout.word (by omega) (by omega)
  generalize hn : Mont.word s.mem B (dN + 8 * i) = n at wN
  generalize hvj : Mont.word s.mem B (dV + 8 * (i + 1)) = vj at wX
  generalize hr : (t.gpr .s2 >>> 63) ||| (vj <<< 1) = r
  refine WP.mono (WP.keep finRegs (Q := fun t' =>
      t'.gpr .t3 = off B (dV + 8 * i + 8) ∧ t'.gpr .t4 = off B (dN + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧ t'.gpr .s2 = vj ∧
      t'.gpr .s4 = ((if r < n then (1 : BitVec 64) else 0) ||| (if r - n < t.gpr .s4 then 1 else 0)) ∧
      t'.mem = t.mem.writeW (off B (dV + 8 * i)) r) (by
    have rN : (t.mem.writeW (off B (dV + 8 * i)) r).readW (off B (dN + 8 * i)) 64 = n := by
      rw [← wN]; exact (writeW_outside t.mem B (d := dV + 8 * i) r (by omega)).word (by omega) (by omega)
    have rX : t.mem.readW (off B (dV + 8 * i + 8)) 64 = vj := wX
    unfold finWord1
    brun [j3, j4, rN, rX, hr, BitVec.add_zero, hs'.ld (show dN + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dN + 8 * i + 8 ≤ Z by omega) (by omega), hs'.ld (show dV + 8 * i + 8 + 8 ≤ Z by omega),
      hs'.al8 (show dV + 8 * i + 8 + 8 ≤ Z by omega) (by omega), hs'.st (show dV + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dV + 8 * i + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u2, u4b, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (jk.trans uk).mono (by decide)⟩, u5⟩
  · rw [u3, show dV + 8 * i + 8 = dV + 8 * (i + 1) by omega]
  · rw [u4, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
  · rw [u2, hvj]
  · rw [u4b]; exact (sub64_arith _ _ _ jb).2
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dV + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have hrv : r.toNat = wordsVal s.mem B dV (w + 1) / 2 ^ 63 / 2 ^ (64 * i) % 2 ^ 64 := by
      rw [← hr, j2]
      exact unshift_word _ i _ _ (wordsVal_word (by omega)).symm (by rw [← hvj]; exact (wordsVal_word (by omega)).symm)
    rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), jv, hrv, mod_succ_words]
  · have hrv : r.toNat = wordsVal s.mem B dV (w + 1) / 2 ^ 63 / 2 ^ (64 * i) % 2 ^ 64 := by
      rw [← hr, j2]
      exact unshift_word _ i _ _ (wordsVal_word (by omega)).symm (by rw [← hvj]; exact (wordsVal_word (by omega)).symm)
    have ks := (sub64_arith r n (t.gpr .s4) jb).1
    refine ⟨D + 2 ^ (64 * i) * (r - n - t.gpr .s4).toNat, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show (r - n - t.gpr .s4).toNat + 1 ≤ 2 ^ 64 from
        (r - n - t.gpr .s4).isLt)
      rw [Nat.mul_succ] at this
      rw [show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      omega
    rw [u4b, wordsVal_succ_top s.mem B dN i, hn, mod_succ_words, ← hrv,
      show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
    generalize 2 ^ (64 * i) = P at jd ⊢
    generalize ((if r < n then (1 : BitVec 64) else 0) ||| (if r - n < t.gpr .s4 then 1 else 0)).toNat
      = b' at ks ⊢
    generalize (r - n - t.gpr .s4).toNat = dv at ks ⊢
    generalize (t.gpr .s4).toNat = b at ks jd
    generalize r.toNat = rv at ks ⊢
    generalize n.toNat = nv at ks ⊢
    have := congrArg (P * ·) ks
    grind

/-- What `finish`'s second pass keeps after `i` words, from `u` (`R`'s words
in place, the mask `0 - g` in `s1`, `g = 1` if `R ≥ n`): the pointers, `R`'s
words from `i` on, and the borrow `b`: `X_{<i} + g n_{<i} = R_{<i} + 2^(64 i) b`. -/
def GInv (u : State) (B : Addr) (dV dN g : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dV + 8 * i) ∧ t.gpr .t4 = off B (dN + 8 * i) ∧ t.gpr .s1 = u.gpr .s1 ∧
    (t.gpr .s4).toNat ≤ 1 ∧ Outside B dV (8 * i) u.mem t.mem ∧
    wordsVal t.mem B dV i + g * wordsVal u.mem B dN i = wordsVal u.mem B dV i + 2 ^ (64 * i) * (t.gpr .s4).toNat ∧
    Keep finRegs u t

theorem finWord2_ok {u : State} {B : Addr} {Z dV dN w g : Nat} (hs : Scr u B Z) (hV8 : dV % 8 = 0)
    (hN8 : dN % 8 = 0) (hV : dV + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z)
    (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN) (hg : g ≤ 1)
    (hm : u.gpr .s1 = 0 - BitVec.ofNat 64 g) {i : Nat} (hi : i < w) {t : State}
    (hI : GInv u B dV dN g i t) :
    WP isa (.block (finWord2 ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      GInv u B dV dN g (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j1, jb, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wN : Mont.word t.mem B (dN + 8 * i) = Mont.word u.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  have wX : Mont.word t.mem B (dV + 8 * i) = Mont.word u.mem B (dV + 8 * i) := jout.word (by omega) (by omega)
  generalize hn : Mont.word u.mem B (dN + 8 * i) = n at wN
  generalize hx : Mont.word u.mem B (dV + 8 * i) = x at wX
  generalize hy : n &&& u.gpr .s1 = y
  have hyv : y.toNat = g * n.toNat := by
    rw [← hy, hm]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with rfl | rfl
    · simp
    · rw [show (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, Nat.one_mul]
  refine WP.mono (WP.keep [.s0, .s2, .s3, .s4, .a3, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t3 = off B (dV + 8 * i + 8) ∧ t'.gpr .t4 = off B (dN + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      t'.gpr .s4 = ((if x < y then (1 : BitVec 64) else 0) ||| (if x - y < t.gpr .s4 then 1 else 0)) ∧
      t'.mem = t.mem.writeW (off B (dV + 8 * i)) (x - y - t.gpr .s4)) (by
    have rN : t.mem.readW (off B (dN + 8 * i)) 64 = n := wN
    have rX : t.mem.readW (off B (dV + 8 * i)) 64 = x := wX
    unfold finWord2
    brun [j3, j4, rN, rX, j1, hy, BitVec.add_zero, hs'.ld (show dN + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dN + 8 * i + 8 ≤ Z by omega) (by omega), hs'.ld (show dV + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dV + 8 * i + 8 ≤ Z by omega) (by omega), hs'.st (show dV + 8 * i + 8 ≤ Z by omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u4b, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_,
      (jk.trans uk).mono (by decide)⟩, u5⟩
  · rw [u3, show dV + 8 * i + 8 = dV + 8 * (i + 1) by omega]
  · rw [u4, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
  · rw [uk.gpr (by decide), j1]
  · rw [u4b]; exact (sub64_arith _ _ _ jb).2
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dV + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have ks := (sub64_arith x y (t.gpr .s4) jb).1
    rw [um, u4b, fin64_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top u.mem B dN i, hn,
      wordsVal_succ_top u.mem B dV i, hx,
      show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
    rw [hyv] at ks
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize ((if x < y then (1 : BitVec 64) else 0) ||| (if x - y < t.gpr .s4 then 1 else 0)).toNat
      = b' at ks ⊢
    generalize (x - y - t.gpr .s4).toNat = dv at ks ⊢
    generalize (t.gpr .s4).toNat = b at ks jv
    generalize x.toNat = xv at ks ⊢
    generalize n.toNat = nv at ks ⊢
    generalize wordsVal t.mem B dV i = Wt at jv ⊢
    generalize wordsVal u.mem B dN i = Nw at jv ⊢
    generalize wordsVal u.mem B dV i = Rw at jv ⊢
    have := congrArg (P * ·) ks
    grind

/-- `finish`, `V` (`w + 1` words) at `dV` (`a2`), `n` (`w` words) at `dN`
(`a7`), `a4` zero, for `R = ⌊V / 2^63⌋ < 2 n`: `x := R mod n` in `V`'s first
`w` words, its word `w` zero, changing only `V`'s `w + 1` words. -/
theorem finish_ok {s : State} {B : Addr} {Z dV dN w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dV) (h7 : s.gpr .a7 = off B dN) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h4 : s.gpr .a4 = 0) (hV8 : dV % 8 = 0) (hN8 : dN % 8 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hVZ : dV + 8 * (w + 1) ≤ Z) (hNZ : dN + 8 * w ≤ Z) (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN)
    (hR : wordsVal s.mem B dV (w + 1) / 2 ^ 63 < 2 * wordsVal s.mem B dN w) :
    WP isa finish s fun t =>
      (wordsVal t.mem B dV w = wordsVal s.mem B dV (w + 1) / 2 ^ 63 % wordsVal s.mem B dN w ∧
        Mont.word t.mem B (dV + 8 * w) = 0 ∧ Outside B dV (8 * (w + 1)) s.mem t.mem) ∧ Keep finRegs s t := by
  have hnw := hs.nowrap
  generalize hVv : wordsVal s.mem B dV (w + 1) = V at hR
  generalize hN : wordsVal s.mem B dN w = N at hR
  unfold finish
  -- The pointers, the borrow and `V₀`.
  refine WP.seq (WP.mono (WP.keep finRegs (Q := fun t =>
      t.gpr .t3 = off B dV ∧ t.gpr .t4 = off B dN ∧ t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s4 = 0 ∧
        t.gpr .s2 = Mont.word s.mem B dV ∧ t.mem = s.mem)
    (by brun [h2, h7, ht0, exec_li_zero, BitVec.add_zero, hs.ld (show dV + 8 ≤ Z by omega),
      hs.al8 (show dV + 8 ≤ Z by omega) hV8]) (by rfl) (by rfl))
    fun s₁ ⟨⟨i3, i4, i5, ib, i2, im⟩, k₁⟩ => ?_)
  have I0 : FInv s B dV dN w 0 s₁ := ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i2]; rfl, by rw [ib]; decide,
    by rw [im]; exact Outside.refl _ _ _ _, by rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl,
    ⟨0, by decide, by rw [ib, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩, k₁⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega) (FInv s B dV dN w)
    (fun i hi t hI _ => finWord1_ok hs hV8 hN8 hVZ hNZ dNV hi hI) I0 i5)
    fun s₂ ⟨j3, _, j2, jb, jout, jv, ⟨D, hD, jd⟩, jk⟩ => ?_)
  rw [hVv] at jv jd
  rw [hN] at jd
  have hs₂ := hs.congr jk.2.2
  -- `R`'s top word, and the mask of `R ≥ n`.
  generalize hrw : Mont.word s.mem B (dV + 8 * w) >>> 63 = rw at *
  generalize hg : (if rw < s₂.gpr .s4 then (1 : BitVec 64) else 0) ^^^ 1#64 = g
  refine WP.seq (WP.mono (WP.keep finRegs (Q := fun t =>
      t.gpr .t3 = off B dV ∧ t.gpr .t4 = off B dN ∧ t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s4 = 0 ∧
        t.gpr .s1 = 0 - g ∧ t.mem = s₂.mem.writeW (off B (dV + 8 * w)) rw)
    (by
      unfold finMid
      brun [j3, j2, hrw, hg, (jk.gpr (by decide)).trans h2, (jk.gpr (by decide)).trans h7,
        (jk.gpr (by decide)).trans ht0, (jk.gpr (by decide)).trans h4, exec_li_zero, BitVec.add_zero,
        hs₂.st (show dV + 8 * w + 8 ≤ Z by omega), hs₂.al8 (show dV + 8 * w + 8 ≤ Z by omega) (by omega)])
      (by rfl) (by rfl))
    fun u ⟨⟨u3, u4, u5, ub, u1, um⟩, uk⟩ => ?_)
  have k2 := (jk.trans uk).mono (rs' := finRegs) (by decide)
  have hsu := hs.congr k2.2.2
  -- `R`'s words and `g = [R ≥ n]`.
  have hVlt : V < 2 ^ (64 * (w + 1)) := hVv ▸ wordsVal_lt _ _ _ _
  have hVw : (Mont.word s.mem B (dV + 8 * w)).toNat = V / 2 ^ (64 * w) := by
    rw [← (wordsVal_word (m := s.mem) (base := B) (o := dV) (n := w + 1) (j := w) (by omega)), hVv,
      Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 + 64 * w = 64 * (w + 1) by omega]
    exact hVlt
  have hrw : rw.toNat = V / 2 ^ 63 / 2 ^ (64 * w) := by
    rw [← hrw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hVw, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hRs : V / 2 ^ 63 = V / 2 ^ 63 % 2 ^ (64 * w) + 2 ^ (64 * w) * rw.toNat := by
    rw [hrw, Nat.mod_add_div]
  generalize V / 2 ^ 63 = R at hR jv jd hrw hRs
  have hN0 : 0 < N := by omega
  have hNlt : N < 2 ^ (64 * w) := hN ▸ wordsVal_lt _ _ _ _
  generalize hRlo : R % 2 ^ (64 * w) = Rlo at jv jd hRs
  have hRlo' : Rlo < 2 ^ (64 * w) := hRlo ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize hb1 : (s₂.gpr .s4).toNat = b1 at jb jd
  have hgv : g.toNat = if N ≤ R then 1 else 0 := by
    rw [← hg]
    have hlt : rw < s₂.gpr .s4 ↔ rw.toNat < b1 := by rw [← hb1]; exact Iff.rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp jb with e | e
    · have hnl : ¬ rw < s₂.gpr .s4 := by rw [hlt, e]; omega
      rw [e, Nat.mul_zero, Nat.add_zero] at jd
      have : Rlo ≤ R := by rw [hRs]; exact Nat.le_add_right _ _
      rw [ite_eq_right hnl, ite_eq_left (by omega)]; rfl
    · rw [e, Nat.mul_one] at jd
      by_cases hr0 : rw.toNat = 0
      · have hl : rw < s₂.gpr .s4 := by rw [hlt, e]; omega
        rw [hr0, Nat.mul_zero, Nat.add_zero] at hRs
        rw [ite_eq_left hl, ite_eq_right (by omega)]; rfl
      · have hnl : ¬ rw < s₂.gpr .s4 := by
          rw [hlt, e]; omega
        have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * rw.toNat := Nat.le_mul_of_pos_right _ (by omega)
        rw [ite_eq_right hnl, ite_eq_left (by omega)]; rfl
  generalize hgN : (if N ≤ R then 1 else 0) = gn at hgv
  have hgn : gn ≤ 1 := by rw [← hgN]; split <;> omega
  -- `u`: `R`'s words in place.
  have o2 : Outside B (dV + 8 * w) 8 s₂.mem u.mem := by
    rw [um]; exact writeW_outside s₂.mem B (d := dV + 8 * w) rw (by omega)
  have hu0 : wordsVal u.mem B dV w = Rlo := by
    rw [Outside.wordsVal o2 (d := dV) (k := w) (by omega) (by omega), jv]
  have hu1 : Mont.word u.mem B (dV + 8 * w) = rw := by rw [um]; exact word_writeW_self _ _ _ _
  have huN : wordsVal u.mem B dN w = N := by
    rw [Outside.wordsVal o2 (d := dN) (k := w) (by omega) (by omega),
      Outside.wordsVal jout (d := dN) (k := w) (by omega) (by omega), hN]
  have hm : u.gpr .s1 = 0 - BitVec.ofNat 64 gn := by
    rw [u1]; congr 1; exact BitVec.eq_of_toNat_eq (by rw [hgv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have I1 : GInv u B dV dN gn 0 u := ⟨by rw [u3]; rfl, by rw [u4]; rfl, rfl, by rw [ub]; decide,
    Outside.refl _ _ _ _, by rw [ub]; simp [wordsVal], Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega) (GInv u B dV dN gn)
    (fun i hi t hI _ => finWord2_ok hsu hV8 hN8 hVZ hNZ dNV hgn hm hi hI) I1 u5)
    fun t₂ ⟨l3, _, _, lb, lout, lv, lk⟩ => ?_)
  rw [hu0, huN] at lv
  have hst := hsu.congr lk.2.2
  have wT : Mont.word t₂.mem B (dV + 8 * w) = rw :=
    (Outside.word lout (d := dV + 8 * w) (by omega) (by omega)).trans hu1
  generalize hb2 : t₂.gpr .s4 = b2 at lb lv
  refine WP.mono (WP.keep [.s2] (Q := fun t => t.mem = t₂.mem.writeW (off B (dV + 8 * w)) (rw - b2)) (by
    have rT : t₂.mem.readW (off B (dV + 8 * w)) 64 = rw := wT
    brun [l3, rT, hb2, hst.ld (show dV + 8 * w + 8 ≤ Z by omega), hst.st (show dV + 8 * w + 8 ≤ Z by omega),
      hst.al8 (show dV + 8 * w + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl)) fun t ⟨tm, tk⟩ => ?_
  have o3 : Outside B (dV + 8 * w) 8 t₂.mem t.mem := by
    rw [tm]; exact writeW_outside t₂.mem B (d := dV + 8 * w) _ (by omega)
  have hlo : wordsVal t.mem B dV w = wordsVal t₂.mem B dV w := Outside.wordsVal o3 (by omega) (by omega)
  have htop : Mont.word t.mem B (dV + 8 * w) = rw - b2 := by rw [tm]; exact word_writeW_self _ _ _ _
  -- `F = R - g n`, with no borrow out of the top word: `R mod n`, below `2^(64 w)`.
  have ks := (sub64_arith rw b2 0 (by decide)).1
  have e0 : rw - b2 - 0 = rw - b2 := BitVec.sub_zero _
  have e1 : (0 : BitVec 64).toNat = 0 := rfl
  rw [e0, e1, Nat.add_zero] at ks
  have hFlo := wordsVal_lt t₂.mem B dV w
  have hb3 : ((if rw < b2 then (1 : BitVec 64) else 0) ||| (if rw - b2 < 0 then 1 else 0)).toNat ≤ 1 :=
    (sub64_arith rw b2 0 (by decide)).2
  generalize ((if rw < b2 then (1 : BitVec 64) else 0) ||| (if rw - b2 < 0 then 1 else 0)).toNat = b3 at ks hb3
  generalize hxw : (rw - b2).toNat = xw at ks htop
  have hxw' : xw < 2 ^ 64 := hxw ▸ (rw - b2).isLt
  have hRg : gn * N ≤ R ∧ R - gn * N < N := by
    rw [← hgN]; split <;> omega
  have key : wordsVal t₂.mem B dV w + 2 ^ (64 * w) * xw + gn * N = R + 2 ^ (64 * w) * 2 ^ 64 * b3 := by
    rw [hRs, Nat.mul_assoc]
    generalize 2 ^ (64 * w) = P at lv ⊢
    generalize wordsVal t₂.mem B dV w = F at lv ⊢
    generalize b2.toNat = c at lv ks
    generalize rw.toNat = r at ks ⊢
    have := congrArg (P * ·) ks
    grind
  have hP : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 64 * 1 := by
    rw [Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos 64)
  have hb30 : b3 = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb3 with e | e
    · exact e
    · exfalso
      rw [e] at key
      have : 2 ^ (64 * w) * xw + 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 64 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxw'
      omega
  rw [hb30, Nat.mul_zero, Nat.add_zero] at key
  have hxw0 : xw = 0 := by
    rcases Nat.eq_zero_or_pos xw with e | e
    · exact e
    · exfalso
      have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * xw := Nat.le_mul_of_pos_right _ e
      omega
  rw [hxw0, Nat.mul_zero, Nat.add_zero] at key
  refine ⟨⟨?_, ?_, ?_⟩, (k2.trans ((lk.trans tk).mono (rs' := finRegs) (by decide))).mono (by decide)⟩
  · rw [hlo]
    rw [← hgN] at key hRg
    split at key
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [htop]; exact BitVec.eq_of_toNat_eq (by rw [hxw, hxw0]; rfl)
  · exact (((jout.mono (Nat.le_refl _) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (lout.mono (Nat.le_refl _) (by omega))).trans (o3.mono (by omega) (by omega))

/-! ## The steps -/

/-- `S` steps of `step mid`, counted by `a1`, dividing `X` by `n` (`w`
words at `dN`, the temporary at `dT` as `step_ok` needs it) 63 bits a step:
from `V = ⌊X / 2^(63 (S - 1))⌋`, with `⌊X / 2^(63 S)⌋ < 2 n`, each `mid` (in
step `j`) setting `t6` to the next chunk, `⌊X / 2^(63 (S - 2 - j))⌋ mod 2^63`
shifted up a bit, and keeping `Q`: `V = r 2^63 + c` for `c < 2^63` and some
`r < 2 n` congruent to `X` modulo `n`, changing only `V`'s `w + 1` words. -/
theorem steps_ok {mid : List Instr} {midRegs : List Reg} {Q : Nat → State → Prop} {s : State} {B : Addr}
    {Z dV dN dT w z X S : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dV) (h6 : s.gpr .a6 = off B dT) (h7 : s.gpr .a7 = off B dN)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (h1 : s.gpr .a1 = BitVec.ofNat 64 S)
    (hS : 1 ≤ S) (hS' : S < 2 ^ 31) (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hV8 : dV % 8 = 0) (hN8 : dN % 8 = 0)
    (hT8 : dT % 8 = 0) (hVZ : dV + 8 * (w + 2) ≤ Z) (hNZ : dN + 8 * w ≤ Z) (hTZ : dT + 32 ≤ Z)
    (dNV : dN + 8 * w ≤ dV ∨ dV + 8 * (w + 1) ≤ dN) (dTV : dT + 32 ≤ dV ∨ dV + 8 * (w + 1) ≤ dT)
    (hP : (Mont.word s.mem B dT).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd : (Mont.word s.mem B (dT + 8)).toNat = wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (dT + 16)).toNat = (2 ^ 128 - 1) / (Mont.word s.mem B (dT + 8)).toNat - 2 ^ 64)
    (hdl : (Mont.word s.mem B (dT + 8)).toNat * 2 ^ 64 + (Mont.word s.mem B (dT + 24)).toNat =
      wordsVal s.mem B dN w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hV0 : wordsVal s.mem B dV (w + 1) = X / 2 ^ (63 * (S - 1)))
    (hX0 : X / 2 ^ (63 * S) < 2 * wordsVal s.mem B dN w)
    (hQ0 : Q 0 s)
    (hQ : ∀ j u u', Q j u → Keep (.a1 :: stepRegs) u u' → Outside B dV (8 * (w + 1)) u.mem u'.mem → Q j u')
    (hmid : ∀ j < S, ∀ u, Q j u → WP isa (.block mid) u fun u' =>
      (u'.gpr .t6).toNat / 2 = X / 2 ^ (63 * (S - 2 - j)) % 2 ^ 63 ∧ u'.mem = u.mem ∧ Keep midRegs u u' ∧
        Q (j + 1) u')
    (hmidR : ∀ r ∈ [Reg.a2, .a7, .t0, .s1, .a1, .a6, .a4], r ∉ midRegs) :
    WP isa (.loop (.seq (step mid) (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)) s fun t =>
      (∃ r, r < 2 * wordsVal s.mem B dN w ∧ r % wordsVal s.mem B dN w = X % wordsVal s.mem B dN w ∧
        wordsVal t.mem B dV (w + 1) / 2 ^ 63 = r ∧ Outside B dV (8 * (w + 1)) s.mem t.mem) ∧
      Keep (.a1 :: (stepRegs ++ midRegs)) s t ∧ Q S t := by
  have hnw := hs.nowrap
  generalize hN : wordsVal s.mem B dN w = N at hd hd63 hdl hX0 ⊢
  let Inv : Nat → State → Prop := fun j t =>
    (∃ r, r < 2 * N ∧ r % N = X / 2 ^ (63 * (S - j)) % N ∧
      wordsVal t.mem B dV (w + 1) = r * 2 ^ 63 + X / 2 ^ (63 * (S - 1 - j)) % 2 ^ 63) ∧
    Outside B dV (8 * (w + 1)) s.mem t.mem ∧ Keep (.a1 :: (stepRegs ++ midRegs)) s t ∧ Q j t
  have I0 : Inv 0 s := by
    refine ⟨⟨X / 2 ^ (63 * S), hX0, by rw [Nat.sub_zero], ?_⟩, Outside.refl _ _ _ _, Keep.refl _ _, hQ0⟩
    rw [hV0, Nat.sub_zero]
    have e := WordStep.wordDiv_digits X 63 (S - 1)
    rwa [show S - 1 + 1 = S by omega] at e
  refine WP.mono (wp_countdown (N := S) (by omega) (by omega) Inv (fun j hj t ⟨⟨r, hr, hrm, hVt⟩, to, tk, tq⟩ _ => ?_)
    I0 h1) fun t ⟨⟨r, hr, hrm, hVt⟩, to, tk, tq⟩ => ⟨⟨r, hr, ?_, ?_, to⟩, tk, tq⟩
  rotate_left
  · rw [hrm, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  · rw [hVt]
    have : X / 2 ^ (63 * (S - 1 - S)) % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by decide)
    rw [Nat.mul_comm, Nat.mul_add_div (by decide), Nat.div_eq_of_lt this, Nat.add_zero]
  -- A step.
  have nk : ∀ q ∈ [Reg.a2, .a6, .a7, .t0, .a4], q ∉ (.a1 :: (stepRegs ++ midRegs)) := by
    intro q hq h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [stepRegs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, false_or] at h
    · exact hmidR .a2 (by decide) h
    · exact hmidR .a6 (by decide) h
    · exact hmidR .a7 (by decide) h
    · exact hmidR .t0 (by decide) h
    · exact hmidR .a4 (by decide) h
  have g : ∀ q ∈ [Reg.a2, .a6, .a7, .t0, .a4], t.gpr q = s.gpr q := fun q hq => tk.gpr (nk q hq)
  have n0 : wordsVal t.mem B dN w = N := by rw [Outside.wordsVal to (by omega) (by omega), hN]
  have wT : ∀ k, k < 4 → Mont.word t.mem B (dT + 8 * k) = Mont.word s.mem B (dT + 8 * k) := fun k hk =>
    Outside.word to (by omega) (by omega)
  have w0 := wT 0 (by decide); have w1 := wT 1 (by decide); have w2 := wT 2 (by decide); have w3 := wT 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
  rw [show 8 * 2 = 16 from rfl] at w2; rw [show 8 * 3 = 24 from rfl] at w3
  have hc : X / 2 ^ (63 * (S - 1 - j)) % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by decide)
  have hVN : wordsVal t.mem B dV (w + 1) < wordsVal t.mem B dN w * 2 ^ 64 := by
    rw [hVt, n0]
    have := Nat.mul_le_mul_right (2 ^ 63) (show r + 1 ≤ 2 * N by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at this
    rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_left_comm]
    omega
  have hsub : ∀ q ∈ [Reg.a2, .a7, .t0, .s1], q ∈ [Reg.a2, .a7, .t0, .s1, .a1, .a6, .a4] := by decide
  refine WP.seq (WP.mono (step_ok (Pm := Q (j + 1)) (C := X / 2 ^ (63 * (S - 2 - j)) % 2 ^ 63)
    (hs.congr tk.2.2) ((g .a2 (by decide)).trans h2) ((g .a6 (by decide)).trans h6)
    ((g .a7 (by decide)).trans h7) ((g .t0 (by decide)).trans ht0) ((g .a4 (by decide)).trans h4) hw hw'
    hV8 hN8 hT8 hVZ hNZ hTZ dNV (by rw [w0]; exact hP) hz (by rw [n0]; exact hd63) (by rw [w1, n0]; exact hd)
    (by rw [w2, w1]; exact hv) (by rw [w1, w3, n0]; exact hdl) hVN
    (fun u ku mu => hmid j hj u (hQ j t u tq (ku.mono (by decide)) (by rw [mu]; exact Outside.refl _ _ _ _)))
    (fun q hq => hmidR q (hsub q hq))
    (fun u u' pu ku ou => hQ (j + 1) u u' pu (ku.mono (by decide)) ou))
    fun t₁ ⟨⟨T, hT, hTm, hV1, o1⟩, k1, q1⟩ => ?_)
  refine WP.mono (dec_ok t₁ .a1) fun t₂ e2 => ?_
  subst e2
  have ka : t₁.gpr .a1 = t.gpr .a1 := k1.gpr (by
    simp only [stepRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or]
    exact hmidR .a1 (by decide))
  rw [n0] at hT hTm
  refine ⟨⟨⟨T, hT, ?_, ?_⟩, ?_, ?_, ?_⟩, by rw [gpr_write_self, ka]⟩
  · rw [hTm, hVt, show S - (j + 1) = S - 1 - j by omega]
    have e := WordStep.wordDiv_step' (X := X) (m := N) (W := 63) (n := S - 1 - j) (r := r % N)
      (u := X / 2 ^ (63 * (S - 1 - j)) % 2 ^ 63) (by rw [hrm, show S - 1 - j + 1 = S - j by omega]) rfl
    rw [← e, Nat.add_mod, Nat.mul_mod, Nat.add_mod (r % N * _), Nat.mul_mod (r % N), Nat.mod_mod, Nat.mod_mod,
      Nat.mul_mod_mod]
  · rw [mem_write, hV1, show S - 1 - (j + 1) = S - 2 - j by omega]
  · rw [mem_write]; exact to.trans o1
  · exact ((tk.trans k1).trans (Keep.write _ _ _)).mono fun q hq => by
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with ((h | h) | h) | h <;> simp_all
  · exact hQ (j + 1) t₁ _ q1 ((Keep.write _ _ _).mono (by decide)) (by rw [mem_write]; exact Outside.refl _ _ _ _)

/-! ## `R² mod n` -/

/-- `c = ⌈(w + 1) / 63⌉`, as `stepCount` computes it for `w < 189`. -/
def cOf (w : Nat) : Nat := 1 + (if 62 < w then 1 else 0) + (if 125 < w then 1 else 0)

theorem cOf_bounds {w : Nat} (hw : w ≤ 128) : w + 1 ≤ 63 * cOf w ∧ 63 * cOf w ≤ w + 63 ∧ cOf w ≤ 3 := by
  unfold cOf; split <;> split <;> omega

theorem sltu_lit {a w : Nat} (ha : a < 2 ^ 64) (hw : w < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 w then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < w then 1 else 0) := by
  have e : BitVec.ofNat 64 a < BitVec.ofNat 64 w ↔ a < w := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hw]
  by_cases h : a < w
  · rw [ite_eq_left (e.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h]; rfl

/-- `stepCount`, `w ≤ 128` in `t0`: `c` in `s0` and `S = w + 1 + c` in `a1`. -/
theorem stepCount_ok {s : State} {w : Nat} (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : w ≤ 128) :
    WP isa (.block stepCount) s fun t =>
      (t.gpr .s0 = BitVec.ofNat 64 (cOf w) ∧ t.gpr .a1 = BitVec.ofNat 64 (w + 1 + cOf w) ∧ t.mem = s.mem) ∧
        Keep [.s0, .s1, .a1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold stepCount
  brun [exec_li, ht0, sltu_lit (a := 62) (w := w) (by decide) (by omega),
    sltu_lit (a := 125) (w := w) (by decide) (by omega)]
  refine ⟨?_, ?_⟩
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp only [Mont.off, BitVec.toNat_add, BitVec.toNat_ofNat, cOf, show (1#64).toNat = 1 from rfl]
    split <;> split <;> omega

/-- A number whose words below `n` are all zero. -/
theorem wordsVal_zeros (m : Mem) (B : Addr) (d : Nat) : ∀ n,
    (∀ j < n, (Mont.word m B (d + 8 * j)).toNat = 0) → wordsVal m B d n = 0
  | 0, _ => rfl
  | n + 1, hw => by
    rw [wordsVal_succ_top, wordsVal_zeros m B d n (fun j hj => hw j (by omega)), hw n (by omega), Nat.mul_zero]

/-- A number whose words below `n` are all zero but word `k`. -/
theorem wordsVal_single (m : Mem) (B : Addr) (d k v : Nat) : ∀ n, k < n →
    (∀ j < n, (Mont.word m B (d + 8 * j)).toNat = if j = k then v else 0) → wordsVal m B d n = 2 ^ (64 * k) * v
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hw => by
    rw [wordsVal_succ_top, hw n (by omega)]
    split
    · rename_i hnk
      subst hnk
      rw [wordsVal_zeros m B d n fun j hj => by rw [hw j (by omega)]; split <;> omega, Nat.zero_add]
    · rw [wordsVal_single m B d k v n (by omega) fun j hj => hw j (by omega), Nat.mul_zero, Nat.add_zero]

/-- `e = 65 w - 63 c`, the bit of `V = ⌊2^(128 w) / 2^(63 (S - 1))⌋`. -/
def eOf (w : Nat) : Nat := 65 * w - 63 * cOf w

/-- The bit's word and position, as `r2Init` computes them. -/
theorem r2Init_vals {w : Nat} (hw : w ≤ 128) (hw4 : 4 ≤ w) (a2 : Addr) :
    (BitVec.ofNat 64 w <<< 6 + BitVec.ofNat 64 w - (BitVec.ofNat 64 (cOf w) <<< 6 - BitVec.ofNat 64 (cOf w)))
        >>> 6 <<< 3 + a2 = a2 + BitVec.ofNat 64 (8 * (eOf w / 64)) ∧
      ((BitVec.ofNat 64 w <<< 6 + BitVec.ofNat 64 w - (BitVec.ofNat 64 (cOf w) <<< 6 - BitVec.ofNat 64 (cOf w)))
        &&& BitVec.ofNat 64 63).toNat % 64 = eOf w % 64 := by
  have hc := cOf_bounds hw
  have e1 : BitVec.ofNat 64 w <<< 6 + BitVec.ofNat 64 w - (BitVec.ofNat 64 (cOf w) <<< 6 - BitVec.ofNat 64 (cOf w)) =
      BitVec.ofNat 64 (eOf w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [eOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  rw [e1]
  constructor
  · have hE : eOf w < 2 ^ 20 := by simp only [eOf]; omega
    rw [BitVec.add_comm]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show eOf w < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_comm]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [eOf]; omega

/-- `r2Init`, `V` at `dV` (`a2`, `w + 1` words), `w ≤ 128` in `t0`, `a4`
zero: `V := 2^(65 w - 63 c)` and `S = w + 1 + c` steps in `a1`. -/
theorem r2Init_ok {s : State} {B : Addr} {Z dV w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dV) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0)
    (hw : 4 ≤ w) (hw' : w ≤ 128) (hV8 : dV % 8 = 0) (hVZ : dV + 8 * (w + 1) ≤ Z) :
    WP isa r2Init s fun t =>
      (wordsVal t.mem B dV (w + 1) = 2 ^ eOf w ∧ t.gpr .a1 = BitVec.ofNat 64 (w + 1 + cOf w) ∧
        Outside B dV (8 * (w + 1)) s.mem t.mem) ∧ Keep [.s0, .s1, .s2, .s3, .t3, .t5, .a1] s t := by
  have hnw := hs.nowrap
  have hc := cOf_bounds hw'
  unfold r2Init
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B dV ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) (by omega)
    (by omega) hV8 (by omega)) fun s₂ ⟨⟨t3, hz, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hs₂ := hs.congr k12.2.2
  have g : ∀ q ∈ [Reg.a2, .t0, .a4], s₂.gpr q = s.gpr q := fun q hq => k12.gpr (by revert q hq; decide)
  generalize hm3 : s₂.mem.writeW (off B (dV + 8 * w)) 0 = m3
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [] (Q := fun t => t.mem = m3)
    (by brun [t3, (g .a4 (by decide)).trans h4, hs₂.st (show dV + 8 * w + 8 ≤ Z by omega),
      hs₂.al8 (show dV + 8 * w + 8 ≤ Z by omega) (by omega)]; exact hm3) (by rfl) (by rfl))
    fun s₃ ⟨m3', k3⟩ => ?_)
  refine WP.block_append (WP.mono (stepCount_ok ((k3.gpr (by decide)).trans ((g .t0 (by decide)).trans ht0)) hw')
    fun s₄ ⟨⟨c4, a1, m4⟩, k4⟩ => ?_)
  have k34 := k3.trans k4
  obtain ⟨ve, vb⟩ := r2Init_vals hw' hw (off B dV)
  refine WP.mono (WP.keep [.s1, .s2, .s3] (Q := fun t =>
      t.mem = m3.writeW (off B (dV + 8 * (eOf w / 64))) (1#64 <<< (eOf w % 64)) ∧ t.gpr .a1 = s₄.gpr .a1) (by
    have h2' : s₄.gpr .a2 = off B dV := (k34.gpr (by decide)).trans ((g .a2 (by decide)).trans h2)
    have ht' : s₄.gpr .t0 = BitVec.ofNat 64 w := (k34.gpr (by decide)).trans ((g .t0 (by decide)).trans ht0)
    have ea : off B dV + BitVec.ofNat 64 (8 * (eOf w / 64)) = off B (dV + 8 * (eOf w / 64)) := off_add _ _ _
    have he : eOf w / 64 < w := by simp only [eOf]; omega
    brun [h2', ht', c4, exec_sllReg, ve, ea, vb, m4, m3', exec_li,
      (hs.congr (k12.trans k34).2.2).st (show dV + 8 * (eOf w / 64) + 8 ≤ Z by omega),
      (hs.congr (k12.trans k34).2.2).al8 (show dV + 8 * (eOf w / 64) + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t ⟨⟨tm, ta⟩, tk⟩ => ?_
  have he : eOf w / 64 < w := by simp only [eOf]; omega
  refine ⟨⟨?_, by rw [ta, a1], ?_⟩, ?_⟩
  · have hv : (1#64 <<< (eOf w % 64)).toNat = 2 ^ (eOf w % 64) := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (1#64).toNat = 1 from rfl, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ (by decide)))]
    rw [wordsVal_single t.mem B dV (eOf w / 64) (2 ^ (eOf w % 64)) (w + 1) (by omega) fun j hj => ?_, ← Nat.pow_add,
      Nat.div_add_mod]
    rw [tm]
    by_cases hjk : j = eOf w / 64
    · subst hjk; rw [ite_eq_left rfl, ← hv]; exact congrArg BitVec.toNat (word_writeW_self _ _ _ _)
    · rw [ite_eq_right hjk]
      refine (congrArg BitVec.toNat (Outside.word (writeW_outside m3 B (d := dV + 8 * (eOf w / 64))
        (1#64 <<< (eOf w % 64)) (by omega)) (d := dV + 8 * j) (by omega) (by omega))).trans ?_
      rw [← hm3]
      by_cases hjw : j = w
      · subst hjw; exact congrArg BitVec.toNat (word_writeW_self _ _ _ _)
      · refine (congrArg BitVec.toNat (Outside.word (writeW_outside s₂.mem B (d := dV + 8 * w) 0 (by omega))
          (d := dV + 8 * j) (by omega) (by omega))).trans ?_
        exact (congrArg BitVec.toNat (hz j (by omega))).trans rfl
  · have o3 : Outside B dV (8 * (w + 1)) s₂.mem t.mem := by
      rw [tm, ← hm3]
      exact ((writeW_outside s₂.mem B (d := dV + 8 * w) _ (by omega)).mono (by omega) (by omega)).trans
        ((writeW_outside _ B (d := dV + 8 * (eOf w / 64)) _ (by omega)).mono (by omega) (by omega))
    rw [← m1]
    exact (o2.mono (Nat.le_refl _) (by omega)).trans o3
  · exact ((k12.trans k34).trans tk).mono (by decide)

/-- `2^a / 2^b` has no bits below `63` when `b + 63 ≤ a`. -/
theorem pow_chunk_zero {a b : Nat} (h : b + 63 ≤ a) : 2 ^ a / 2 ^ b % 2 ^ 63 = 0 := by
  rw [Nat.pow_div (by omega) (by decide)]
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))

/-- The registers `r2Words` writes. -/
def r2WordsRegs : List Reg := [.a0, .a1, .a3, .a4, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `r2Words`, after `lz` (`a1 = zOf T`, `T` the top word): `x := R² mod n =
2^(128 w) mod n` in array 1, for an odd `n` of `4 ≤ w ≤ 128` words, at least
`2^(64 (w - 1))`, in array 0, changing only arrays 1–3. -/
theorem r2Words_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 (zOf (topW s.mem B w)))
    (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 4 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa r2Words s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep r2WordsRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  have hT := topW_pos (by omega) hN
  generalize hTd : topW s.mem B w = T at hT h1
  -- `T`'s bounds: `2^63 ≤ T 2^z < 2^64`.
  have hTl : T < 2 ^ 64 := by rw [← hTd]; exact BitVec.isLt _
  have l1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hT)
  have l2 := Nat.lt_log2_self (n := T)
  have hl : Nat.log2 T < 64 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt l1 hTl)
  have hb1 : 2 ^ 63 ≤ T * 2 ^ (zOf T) := by
    unfold zOf
    calc 2 ^ 63 = 2 ^ Nat.log2 T * 2 ^ (63 - Nat.log2 T) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ T * 2 ^ (63 - Nat.log2 T) := Nat.mul_le_mul_right _ l1
  have hb2 : T * 2 ^ (zOf T) < 2 ^ 64 := by
    unfold zOf
    calc T * 2 ^ (63 - Nat.log2 T) < 2 ^ (Nat.log2 T + 1) * 2 ^ (63 - Nat.log2 T) :=
          Nat.mul_lt_mul_of_pos_right l2 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  generalize hz : zOf T = z at h1 hb1 hb2
  rw [← hTd] at hb1 hb2
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  have hN0 : 0 < N := by have := Nat.two_pow_pos (64 * (w - 1)); omega
  unfold r2Words
  -- `P` and `d'`.
  refine WP.seq (WP.mono (normTail_ok hs h6 h7 ht0 h1 (by omega) (by omega) (al 0) (al 3) (by omega) (by omega)
    hb1 hb2) fun s₁ ⟨⟨wP, hz63, wD, hD63, wDl, s2D, o1⟩, k1⟩ => ?_)
  rw [hNd] at wD hD63 wDl
  have g1 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0], s₁.gpr r = s.gpr r := fun r hr => k1.gpr (by revert r hr; decide)
  -- `v`.
  refine WP.seq (WP.mono (recip_ok (hs.congr k1.2.2) ((g1 .a6 (by decide)).trans h6) (al 3) (by omega)
    (by rw [s2D, wD]; exact hD63)) fun s₂ ⟨⟨wV, a4, o2⟩, k2⟩ => ?_)
  rw [s2D] at wV
  have k12 := k1.trans k2
  have g2 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0], s₂.gpr r = s.gpr r := fun r hr => k12.gpr (by revert r hr; decide)
  -- `V := 2^(65 w - 63 c)`, `S` steps.
  refine WP.seq (WP.mono (r2Init_ok (hs.congr k12.2.2) ((g2 .a2 (by decide)).trans h2)
    ((g2 .t0 (by decide)).trans ht0) a4 hw hw' (al 1) (by omega)) fun s₃ ⟨⟨x3, a13, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have O3 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₃.mem :=
    Outside.trans (Outside.trans (Outside.mono o1 (by omega) (by omega)) (Outside.mono o2 (by omega) (by omega)))
      (Outside.mono o3 (Nat.le_refl _) (by omega))
  have w3 : ∀ d, slot w 3 ≤ d → d + 8 ≤ slot w 4 → Mont.word s₃.mem B d = Mont.word s₂.mem B d := fun d h1 h2 =>
    Outside.word o3 (Or.inr (by omega)) (by omega)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal O3 (by omega) (by omega), hNd]
  have w38 : Mont.word s₂.mem B (slot w 3 + 8) = Mont.word s₁.mem B (slot w 3 + 8) :=
    Outside.word o2 (Or.inl (by omega)) (by omega)
  have w30 : Mont.word s₂.mem B (slot w 3) = Mont.word s₁.mem B (slot w 3) :=
    Outside.word o2 (Or.inl (by omega)) (by omega)
  have w324 : Mont.word s₂.mem B (slot w 3 + 24) = Mont.word s₁.mem B (slot w 3 + 24) :=
    Outside.word o2 (Or.inr (by omega)) (by omega)
  have hc := cOf_bounds hw'
  have a43 : s₃.gpr .a4 = 0 := (k3.gpr (by decide)).trans a4
  -- The steps, with zero chunks.
  refine WP.seq (WP.mono (steps_ok (mid := [.li .t6 0]) (midRegs := [.t6]) (Q := fun _ _ => True)
    (X := 2 ^ (128 * w)) (S := w + 1 + cOf w) (z := z) (dT := slot w 3) (hs.congr k13.2.2)
    ((k13.gpr (by decide)).trans h2) ((k13.gpr (by decide)).trans h6) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans ht0) a43 a13 (by omega) (by omega) hw (by omega) (al 1) (al 0) (al 3)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [w3 _ (Nat.le_refl _) (by omega), w30]; exact wP) hz63
    (by rw [n3]; exact hD63) (by rw [w3 _ (by omega) (by omega), w38, n3]; exact wD)
    (by rw [w3 _ (by omega) (by omega), w3 _ (by omega) (by omega), w38]; exact wV)
    (by rw [w3 _ (by omega) (by omega), w3 _ (by omega) (by omega), w38, w324, n3]; exact wDl)
    (by rw [x3, Nat.pow_div (by omega) (by decide)]; congr 1; simp only [eOf]; omega)
    (by
      rw [n3, Nat.pow_div (by omega) (by decide)]
      have : 2 ^ (128 * w - 63 * (w + 1 + cOf w)) ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega)
    trivial (fun _ _ _ _ _ _ => trivial)
    (fun j hj u _ => by
      refine WP.keep [.t6] (Q := fun u' => (u'.gpr .t6).toNat / 2 = 2 ^ (128 * w) / 2 ^ (63 * (w + 1 + cOf w - 2 - j)) %
        2 ^ 63 ∧ u'.mem = u.mem) ?_ (by rfl) (by rfl) |> WP.mono <| fun u' ⟨⟨a, b⟩, c⟩ => ⟨a, b, c, trivial⟩
      brun [exec_li]
      rw [pow_chunk_zero (by omega)]; rfl)
    (by decide)) fun s₄ ⟨⟨r, hr, hrm, hV4, o4⟩, k4, _⟩ => ?_)
  rw [n3] at hr hrm
  have k14 := k13.trans k4
  -- `x := r mod n`.
  have n4 : wordsVal s₄.mem B (slot w 0) w = N := by rw [Outside.wordsVal o4 (by omega) (by omega), n3]
  refine WP.mono (finish_ok (dV := slot w 1) (dN := slot w 0) (hs.congr k14.2.2)
    ((k14.gpr (by decide)).trans h2) ((k14.gpr (by decide)).trans h7) ((k14.gpr (by decide)).trans ht0)
    ((k4.gpr (by decide)).trans a43) (al 1) (al 0) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hV4, n4]; exact hr)) fun t ⟨⟨tx, _, to⟩, tk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [tx, hV4, n4, hrm]
  · exact Outside.trans O3 (Outside.trans (Outside.mono o4 (Nat.le_refl _) (by omega))
      (Outside.mono to (Nat.le_refl _) (by omega)))
  · exact (k14.trans tk).mono (by decide)

end VG.Proof.Bignum.RISCV64
