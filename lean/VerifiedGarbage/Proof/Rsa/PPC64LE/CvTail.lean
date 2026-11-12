module
-- separate module: its proofs (the tail's shift and division) are not re-checked with every change to the
-- inverse's phase (`CvArithB.lean`)

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyDiv
import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # `vg_rsa_crt_values` on PPC64LE: the inverse's tail by words

For a balanced key, `CrtValues.arith` runs the inverse without its doublings
(`InvBatch.inverseS`) and then `CrtValues.tail`, `y := y 2^K mod m` for
`K = 5 (3 ν + 2) = 64 Q + T` (`ν = w / 4`): `y`'s words times `2^T` (which
may be 1) into word `Q` of a zeroed array (`shlLoop_ok`, by `mul` and
`mulhu`: the model has no shift by a register), and one division by words
(`KeyDiv.divW_ok`). -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs copy)
open VG.Impl.Rsa.PPC64LE.CrtValues (aDR aDQ nArr tailSetup pow2T shlBody tail)
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-! ## `2^T` -/

theorem ofNat_dbl (i : Nat) : BitVec.ofNat 64 (2 ^ i) + BitVec.ofNat 64 (2 ^ i) = BitVec.ofNat 64 (2 ^ (i + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]

/-- `pow2T`: `r12 := 2^T`, from `r12 = 1` and `T < 64` in `r7`. -/
theorem pow2T_ok {s : State} {T : Nat} (h7 : s.gpr .r7 = BitVec.ofNat 64 T) (h12 : s.gpr .r12 = BitVec.ofNat 64 1)
    (hT : T < 64) :
    WP isa pow2T s fun t => t.gpr .r12 = BitVec.ofNat 64 (2 ^ T) ∧ t.mem = s.mem ∧ Keep [.r7, .r12] s t := by
  unfold pow2T
  refine WP.ite (s.gpr .r7 == 0) (eval_zero s .r7) (fun hz => ?_) (fun hz => ?_)
  · have : T = 0 := by
      have e : s.gpr .r7 = 0 := by simpa using hz
      rw [h7] at e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat] at this; simp at this; omega
    subst this
    exact WP.block_nil ⟨h12, rfl, Keep.refl _ _⟩
  · have hT0 : 0 < T := by
      rcases Nat.eq_zero_or_pos T with e | e
      · subst e; simp [h7] at hz
      · exact e
    refine WP.mono (wp_countdown (body := .block ([.add .r12 .r12 .r12, .subi .r7 .r7 1] : List Instr))
      (cnt := .r7) (N := T) (by omega) hT0
      (fun i t => t.gpr .r12 = BitVec.ofNat 64 (2 ^ i) ∧ t.mem = s.mem ∧ Keep [.r7, .r12] s t)
      (fun i hi t ⟨j12, jm, jk⟩ hc => ?_) ⟨by simpa using h12, rfl, Keep.refl _ _⟩ h7) fun t h => h
    refine WP.mono (WP.keep [.r7, .r12] (Q := fun u => (u.gpr .r12 = BitVec.ofNat 64 (2 ^ (i + 1)) ∧
      u.mem = t.mem) ∧ u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1) (by prun [j12, ofNat_dbl]) (by decide))
      fun u ⟨⟨⟨u12, um⟩, u7⟩, ku⟩ => ⟨⟨u12, um.trans jm, (jk.trans ku).mono (by decide)⟩, u7⟩

/-! ## `y 2^T` -/

theorem mul_pow_eq_shl (x : BitVec 64) (T : Nat) : x * BitVec.ofNat 64 (2 ^ T) = x <<< T := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat]

/-- A word times `2^T < 2^64`, the carry `c < 2^T` in: the low word or'ed with
the carry and the high word are the product plus the carry. -/
theorem shlMul_arith (x c : BitVec 64) {T : Nat} (hT : T < 64) (hc : c.toNat < 2 ^ T) :
    (x * BitVec.ofNat 64 (2 ^ T) ||| c).toNat + 2 ^ 64 * (x.toNat * (2 ^ T % 2 ^ 64) / 2 ^ 64) =
      x.toNat * 2 ^ T + c.toNat ∧ x.toNat * (2 ^ T % 2 ^ 64) / 2 ^ 64 < 2 ^ T := by
  have hp : 2 ^ T % 2 ^ 64 = 2 ^ T := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hT)
  rw [hp, mul_pow_eq_shl x T]
  have hx := x.isLt
  have h1 : (x <<< T).toNat = x.toNat * 2 ^ T % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hd : x <<< T &&& c = 0 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases h : i < T
    · simp [h]
    · have : c.toNat < 2 ^ i := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))
      simp [h, BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1]
  have hlo : x.toNat * 2 ^ T % 2 ^ 64 + c.toNat < 2 ^ 64 := by
    have e : 2 ^ 64 = 2 ^ T * 2 ^ (64 - T) := by rw [← Nat.pow_add]; congr 1; omega
    have h2 : 2 ^ T ∣ x.toNat * 2 ^ T % 2 ^ 64 :=
      (Nat.dvd_mod_iff (by rw [e]; exact Nat.dvd_mul_right _ _)).mpr (Nat.dvd_mul_left _ _)
    obtain ⟨k, hk⟩ := h2
    have : x.toNat * 2 ^ T % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [hk, e] at this ⊢
    have : k < 2 ^ (64 - T) := Nat.lt_of_mul_lt_mul_left this
    have : 2 ^ T * k + 2 ^ T ≤ 2 ^ T * 2 ^ (64 - T) := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega
  have hhi : x.toNat * 2 ^ T / 2 ^ 64 < 2 ^ T := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    calc x.toNat * 2 ^ T < 2 ^ 64 * 2 ^ T := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      _ = 2 ^ T * 2 ^ 64 := Nat.mul_comm _ _
  refine ⟨?_, hhi⟩
  rw [Nat.mod_eq_of_lt hlo]
  have := Nat.mod_add_div (x.toNat * 2 ^ T) (2 ^ 64)
  omega

/-- `[o] := [a] 2^T` over `m` words (`countLoop .r8 shlBody`), `2^T` in `r12`, the
carry in `r9` from 0: the words and the carry out. -/
theorem shlLoop_ok {s : State} {B : Addr} {Z dO dA m T : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h8 : s.gpr .r8 = BitVec.ofNat 64 m)
    (h9 : s.gpr .r9 = 0) (h12 : s.gpr .r12 = BitVec.ofNat 64 (2 ^ T)) (hT : T < 64)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) (hA : dA + 8 * m ≤ Z)
    (hdis : dA + 8 * m ≤ dO ∨ dO + 8 * m ≤ dA) :
    WP isa (countLoop .r8 shlBody) s fun t =>
      wordsVal t.mem B dO m + 2 ^ (64 * m) * (t.gpr .r9).toNat = wordsVal s.mem B dA m * 2 ^ T ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep [.r0, .r3, .r5, .r6, .r8, .r9] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧ (t.gpr .r9).toNat < 2 ^ T ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .r9).toNat = wordsVal s.mem B dA i * 2 ^ T ∧
      Keep [.r0, .r3, .r5, .r6, .r8, .r9] s t
  refine WP.mono (wp_countdown (body := .block (shlBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h9]; exact Nat.two_pow_pos _, Outside.refl _ _ _ _,
      by rw [h9]; simp [wordsVal], Keep.refl _ _⟩ h8)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have j12 : t.gpr .r12 = BitVec.ofNat 64 (2 ^ T) := (jk.gpr _ (by decide)).trans h12
  have hst : WP isa (.block (shlBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        (t'.gpr .r9).toNat = (word t.mem B (dA + 8 * i)).toNat * (2 ^ T % 2 ^ 64) / 2 ^ 64 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dA + 8 * i) * BitVec.ofNat 64 (2 ^ T) ||| t.gpr .r9)) ∧
      Keep [.r0, .r3, .r5, .r6, .r8, .r9] t t' := by
    refine WP.keep _ ?_ (by decide)
    mcrun [shlBody, j5, j6, j12, word, exec_load_d, exec_store_d, BitVec.add_zero,
      (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)]
    have hx := (t.mem.readW (off B (dA + 8 * i)) 64).isLt
    have hy : 2 ^ T % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' hx hy))
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l9]; exact (shlMul_arith (word t.mem B (dA + 8 * i)) (t.gpr .r9) hT j9).2
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    have ar := (shlMul_arith (word t.mem B (dA + 8 * i)) (t.gpr .r9) hT j9).1
    rw [lm, Loops.wordsVal_write_top _ _ _ _ _ (by omega_arith), l9, wordsVal_succ_top s.mem B dA i, ← wa,
      ← Loops.pow64_mul i]
    generalize (word t.mem B (dA + 8 * i) * BitVec.ofNat 64 (2 ^ T) ||| t.gpr .r9).toNat = L at ar ⊢
    generalize (word t.mem B (dA + 8 * i)).toNat * (2 ^ T % 2 ^ 64) / 2 ^ 64 = H at ar ⊢
    generalize (word t.mem B (dA + 8 * i)).toNat = X at ar ⊢
    generalize (t.gpr .r9).toNat = C at ar jeq ⊢
    generalize 2 ^ (64 * i) = P at jeq ⊢
    rw [Nat.add_mul, ← jeq]
    have e : P * L + 2 ^ 64 * P * H = P * C + P * (X * 2 ^ T) := by
      rw [show 2 ^ 64 * P * H = P * (2 ^ 64 * H) by ring, ← Nat.mul_add, ar]; ring
    linarith [e]

end VG.Proof.Rsa.PPC64LE.CrtValues

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs copy)
open VG.Impl.Rsa.PPC64LE.CrtValues (aDR aDQ nArr tailSetup pow2T shlBody tail)
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-- `tailSetup`, `w = 4 wd`: `K = 5 (3 wd + 2) = 64 Q + T`, `y`'s address, word
`Q` of `aDR`'s, `T`, `wd + 1` words, no carry and `1`. -/
theorem tailSetup_ok {s : State} {B : Addr} {Z w wd : Nat} (h : Ws s B Z w nArr) (hw : w = 4 * wd) :
    WP isa (.block tailSetup) s fun t => Ws t B Z w nArr ∧ t.mem = s.mem ∧
      t.gpr .r6 = off B (arr w VG.Impl.Rsa.PPC64LE.InvBatch.aY) ∧ t.gpr .r5 = off B (arr w aDR + 8 * ((15 * wd + 10) / 64)) ∧
      t.gpr .r7 = BitVec.ofNat 64 ((15 * wd + 10) % 64) ∧ t.gpr .r8 = BitVec.ofNat 64 (wd + 1) ∧
      t.gpr .r9 = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 1 ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fD := h.arr_fit (j := aDR) (by decide)
  have hS : S w = 4 * (w + 2) := rfl
  rw [tailSetup, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide) (by decide) ?_
  have e3 : BitVec.ofNat 64 w >>> 2 = BitVec.ofNat 64 wd := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  have eK : BitVec.ofNat 64 wd <<< 4 - BitVec.ofNat 64 wd + BitVec.ofNat 64 10 = BitVec.ofNat 64 (15 * wd + 10) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have eT : BitVec.ofNat 64 (15 * wd + 10) &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 ((15 * wd + 10) % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 15 * wd + 10 < 2 ^ 64 by omega), show 63 % 2 ^ 64 = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have eQ : (BitVec.ofNat 64 (15 * wd + 10) >>> 6) <<< 3 = BitVec.ofNat 64 (8 * ((15 * wd + 10) / 64)) := by
    apply BitVec.eq_of_toNat_eq
    have : wd ≤ 256 := by omega
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show 15 * wd + 10 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (15 * wd + 10) / 2 ^ 6 * 2 ^ 3 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * ((15 * wd + 10) / 64) < 2 ^ 64 by omega)]
    omega
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r12] (Q := fun u =>
      u.gpr .r5 = off B (arr w aDR + 8 * ((15 * wd + 10) / 64)) ∧
      u.gpr .r7 = BitVec.ofNat 64 ((15 * wd + 10) % 64) ∧ u.gpr .r8 = BitVec.ofNat 64 (wd + 1) ∧
      u.gpr .r9 = 0 ∧ u.gpr .r12 = BitVec.ofNat 64 1 ∧ u.mem = s.mem) ?_ (by decide))
    fun u ⟨⟨u5, u7, u8, u9, u12, um⟩, ku⟩ => ?_
  · prun [h.r29, e3, eK, eT, eQ, off_add, VG.Proof.Rsa.PPC64LE.InvBatch.ofNat_succ]
    rfl
  have k : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12] s u :=
    (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans ku).mono (by decide)
  refine ⟨h.of_keep k, um, ?_, u5, u7, u8, u9, u12, k⟩
  rw [ku.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]

end VG.Proof.Rsa.PPC64LE.CrtValues

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs copy)
open VG.Impl.Rsa.PPC64LE.CrtValues (aDR aDQ nArr tailSetup pow2T shlBody tail)
open VG.Impl.Rsa.PPC64LE.InvBatch (aY aF aG aMin)
open VG.Proof.Rsa.PPC64LE.InvBatch (keep_val)
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)

/-- The registers `tail` changes. -/
abbrev tailRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- `tail`, `w = 4 wd`: `y := y 2^K mod m`, `K = 5 (3 wd + 2)`, exact where
`m`'s top word (of `wd`) is not zero. -/
theorem tail_ok {s : State} {B : Addr} {Z w wd : Nat} (h : Ws s B Z w nArr) (hw : w = 4 * wd) (hwd : 4 ≤ wd) :
    WP isa tail s fun t => Ws t B Z w nArr ∧ KeyWorkspace.Keep B w [aDR, aY, aF, aG, aDQ] [] s.mem t.mem ∧
      (num s.mem B w aY < num s.mem B w aMin → num s.mem B w aMin < 2 ^ (64 * wd) →
        2 ^ (64 * (wd - 1)) ≤ num s.mem B w aMin →
        num t.mem B w aY = num s.mem B w aY * 2 ^ (5 * (3 * wd + 2)) % num s.mem B w aMin) ∧
      Keep tailRegs s t := by
  generalize hy : num s.mem B w aY = y
  generalize hm : num s.mem B w aMin = m
  have := h.wle
  have hnw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have fitZ : ∀ j < nArr, arr w j + S w ≤ Z := fun j hj => h.arr_fit hj
  have fD := fitZ aDR (by decide)
  have fY := fitZ aY (by decide)
  have fF := fitZ aF (by decide)
  have dYD := arr_disj (w := w) (show aY ≠ aDR by decide)
  generalize hQ : (15 * wd + 10) / 64 = Q
  generalize hT : (15 * wd + 10) % 64 = T
  have hK : 5 * (3 * wd + 2) = 64 * Q + T := by omega
  have hQw : 2 * Q + 2 * (wd + 1) ≤ w := by omega
  have hT64 : T < 64 := by omega
  rw [tail]; simp only [seqs]
  -- `aDR = 0`.
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.InvBatch.zeroW_ws_ok h (j := aDR) (by decide) (by decide))
    fun t1 ⟨h1, K1, o1, z1, k1⟩ => ?_
  -- The pointers, `T` and the count.
  rw [WP.seq_iff]
  refine WP.mono (tailSetup_ok h1 hw) fun t2 ⟨h2, m2, p6, p5, p7, p8, p9, p12, k2⟩ => ?_
  rw [hQ] at p5
  rw [hT] at p7
  -- `2^T`.
  rw [WP.seq_iff]
  refine WP.mono (pow2T_ok p7 p12 hT64) fun t3 ⟨q12, m3, k3⟩ => ?_
  have h3 := h2.of_keep k3
  -- `y 2^T` into word `Q` of `aDR`.
  rw [WP.seq_iff]
  refine WP.mono (shlLoop_ok (dO := arr w aDR + 8 * Q) (dA := arr w aY) (m := wd + 1) (T := T) h3.scr
    (by rw [k3.gpr _ (by decide)]; exact p5) (by rw [k3.gpr _ (by decide)]; exact p6)
    (by rw [k3.gpr _ (by decide)]; exact p8) (by rw [k3.gpr _ (by decide)]; exact p9) q12 hT64
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t4 ⟨v4, o4, k4⟩ => ?_
  have h4 := h3.of_keep k4
  have yW : y < m → m < 2 ^ (64 * wd) → wordsVal t3.mem B (arr w aY) (wd + 1) = y := fun hym hmw => by
    rw [m3, m2, wordsVal_eq_val32]
    refine VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w) ?_ (by omega)
      (Nat.lt_of_lt_of_le (Nat.lt_trans hym hmw) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [← hy]; exact keep_val K1 (j := aY) (k := w) (by omega) (by decide) (by simp) (fit _ (by decide))
  have hyT : y < m → m < 2 ^ (64 * wd) → y * 2 ^ T < 2 ^ (64 * (wd + 1)) := fun hym hmw => by
    rw [show 64 * (wd + 1) = 64 * wd + 64 by omega, Nat.pow_add]
    exact Nat.mul_lt_mul'' (Nat.lt_trans hym hmw) (Nat.pow_lt_pow_right (by decide) hT64)
  have v4' : y < m → m < 2 ^ (64 * wd) → wordsVal t4.mem B (arr w aDR + 8 * Q) (wd + 1) = y * 2 ^ T :=
      fun hym hmw => by
    have hyT := hyT hym hmw
    rw [yW hym hmw] at v4
    rcases Nat.eq_zero_or_pos (t4.gpr .r9).toNat with e | e
    · rw [e, Nat.mul_zero, Nat.add_zero] at v4; exact v4
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * (wd + 1))) e
      omega
  -- `num aDR = y 2^K`.
  have m13 : t3.mem = t1.mem := by rw [m3, m2]
  have zlow : ∀ i < 2 * Q, w32 t4.mem B (arr w aDR + 4 * i) = 0 := fun i hi => by
    unfold w32
    rw [VG.Proof.Rsa.PPC64LE.InvBatch.Outside.readW32 o4 (by omega) (by omega), m13]
    exact z1 i (by omega)
  have zhigh : ∀ i, 2 * Q + 2 * (wd + 1) ≤ i → i < w + 2 → w32 t4.mem B (arr w aDR + 4 * i) = 0 :=
    fun i hi1 hi2 => by
      unfold w32
      rw [VG.Proof.Rsa.PPC64LE.InvBatch.Outside.readW32 o4 (by omega) (by omega), m13]
      exact z1 i hi2
  have nD : y < m → m < 2 ^ (64 * wd) → num t4.mem B w aDR = y * 2 ^ (5 * (3 * wd + 2)) := fun hym hmw => by
    show val32 t4.mem B (arr w aDR) w = _
    have e1 := val32_append t4.mem B (arr w aDR) (2 * Q) (w - 2 * Q)
    have e2 := val32_append t4.mem B (arr w aDR + 4 * (2 * Q)) (2 * (wd + 1)) (w - 2 * Q - 2 * (wd + 1))
    rw [show 2 * Q + (w - 2 * Q) = w by omega] at e1
    rw [show 2 * (wd + 1) + (w - 2 * Q - 2 * (wd + 1)) = w - 2 * Q by omega] at e2
    rw [VG.Proof.Rsa.PPC64LE.InvBatch.val32_zero zlow, Nat.zero_add, e2,
      show arr w aDR + 4 * (2 * Q) = arr w aDR + 8 * Q by omega, ← wordsVal_eq_val32, v4' hym hmw,
      VG.Proof.Rsa.PPC64LE.InvBatch.val32_zero (k := w - 2 * Q - 2 * (wd + 1)) (fun i hi => by
        rw [show arr w aDR + 8 * Q + 4 * (2 * (wd + 1)) + 4 * i = arr w aDR + 4 * (2 * Q + 2 * (wd + 1) + i) by omega]
        exact zhigh _ (by omega) (by omega)), Nat.mul_zero, Nat.add_zero] at e1
    rw [e1, hK, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (32 * (2 * Q))),
      show 32 * (2 * Q) = 64 * Q by omega, Nat.mul_assoc]
  -- `[aY] = 0`, `[aF] = m`, its top word fixed.
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.InvBatch.zeroW_ws_ok h4 (j := aY) (by decide) (by decide))
    fun t5 ⟨h5, K5, _, _, k5⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (copy_ok h5 (o := aF) (a := aMin) (by decide) (by decide) (by decide) (by decide))
    fun t6 ⟨h6, K6, v6, k6, _⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_ok h6 (m := aF) (by decide) (by decide) hw hwd)
    fun t7 ⟨m7, h7, k7⟩ => ?_
  have K14 : KeyWorkspace.Keep B w [aDR] [] s.mem t4.mem := K1.trans (by
    rw [← m13]; exact KeyWorkspace.Keep.of_arr (o := aDR) (d := 8 * Q) o4 (by omega) (by simp))
  have o7 : Outside B (arr w aF + 8 * (wd - 1)) 8 t6.mem t7.mem := by
    rw [m7]; exact writeW_outside _ B _ (by omega)
  have K7 : KeyWorkspace.Keep B w [aF] [] t6.mem t7.mem :=
    KeyWorkspace.Keep.of_arr (o := aF) (d := 8 * (wd - 1)) o7 (by omega) (by simp)
  have K47 : KeyWorkspace.Keep B w [aY, aF] [] t4.mem t7.mem :=
    (K5.mono (by simp)).trans ((K6.mono (by simp)).trans (K7.mono (by simp)))
  have mF : m < 2 ^ (64 * wd) → wordsVal t6.mem B (arr w aF) wd = m := fun hmw => by
    rw [wordsVal_eq_val32]
    refine VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w) ?_ (by omega)
      (by rw [show 32 * (2 * wd) = 64 * wd by omega]; exact hmw)
    show num t6.mem B w aF = m
    rw [v6, ← hm]
    exact (keep_val K5 (j := aMin) (k := w) (by omega) (by decide) (by simp) (fit _ (by decide))).trans
      (keep_val K14 (j := aMin) (k := w) (by omega) (by decide) (by simp) (fit _ (by decide)))
  have ft := VG.Proof.Rsa.PPC64LE.KeyDiv.fixTop_val (mem := t6.mem) (B := B) (d := arr w aF) (wd := wd)
    (by omega) (by omega)
  rw [← m7] at ft
  obtain ⟨hTop, hfix⟩ := ft
  have nD7 : y < m → m < 2 ^ (64 * wd) → num t7.mem B w aDR = y * 2 ^ (5 * (3 * wd + 2)) := fun hym hmw =>
    (keep_val K47 (j := aDR) (k := w) (by omega) (by decide) (by simp) (fit _ (by decide))).trans (nD hym hmw)
  -- The division.
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.divW_ok h7 (a := aDR) (r := aY) (m := aF) (t := aG) (sv := aDQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw hwd hTop)
    fun t ⟨tr, ht, kt, mt⟩ => ?_
  refine ⟨ht, ?_, fun hym hmw hb => ?_, ?_⟩
  · exact (K14.mono (by simp)).trans ((K47.mono (by simp)).trans (mt.mono (by simp)))
  · rw [tr, nD7 hym hmw, hfix (by rw [mF hmw]; exact hb), mF hmw]
  · exact (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans kt).mono (by decide)

end VG.Proof.Rsa.PPC64LE.CrtValues

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (aDR aDQ nArr tail shape)
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.PPC64LE (invBatchArrs)

/-- `shape`: `r0 = 0` exactly for `Shape`, from `p_len` and `q_len` (`r20`,
`r22`) and `w`. -/
theorem shape_ok {s : State} {w pL qL : Nat} (hw : s.gpr .r29 = BitVec.ofNat 64 w)
    (hp : s.gpr .r20 = BitVec.ofNat 64 pL) (hq : s.gpr .r22 = BitVec.ofNat 64 qL) (hw' : w < 2 ^ 32)
    (hp' : pL < 2 ^ 32) (hq' : qL < 2 ^ 32) :
    WP isa (.block shape) s fun t => (t.gpr .r0 = 0 ↔ KeyCheck.Shape w pL qL) ∧ t.mem = s.mem ∧
      Keep [.r0, .r3, .r12] s t := by
  refine WP.mono (WP.keep [.r0, .r3, .r12] (Q := fun t => (t.gpr .r0 = 0 ↔ KeyCheck.Shape w pL qL) ∧
      t.mem = s.mem) (by
    unfold shape
    prun [hw, hp, hq]
    exact KeyCheck.shape_bits hw' hp' hq') (by decide)) fun t ⟨⟨h0, hm⟩, k'⟩ => ⟨h0, hm, k'⟩


/-- The inverse of `x` modulo `m`: without its doublings (`inverseS`) for a
balanced key, else `inverse`. -/
theorem invB_ok [InvLaw] {s : State} {B : Addr} {Z w pL qL : Nat} (h : Ws s B Z w nArr) (hw : 10 ≤ w)
    (hwe : w % 2 = 0) (h11 : s.gpr .r11 = BitVec.ofNat 64 ((max pL qL + 3) / 4))
    (h20 : s.gpr .r20 = BitVec.ofNat 64 pL) (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL)
    (hpw : pL ≤ 4 * w) (hqw : qL ≤ 4 * w) {x m : Nat}
    (hx : num s.mem B w 0 = x) (hxn : x < 2 ^ (32 * ((max pL qL + 3) / 4))) (hm : num s.mem B w 8 = m)
    (hmn : m < 2 ^ (32 * ((max pL qL + 3) / 4))) (hodd : m % 2 = 1) :
    WP isa (seqs [.block shape, .ite (.zero .d .r0) VG.Impl.Rsa.PPC64LE.InvBatch.inverseS
      VG.Impl.Rsa.PPC64LE.InvBatch.inverse]) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w invBatchArrs [] s.mem t.mem ∧ Keep (.r10 :: InvBatch.kRegs) s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (KeyCheck.Shape w pL qL → (m : Int) ∣ ((num t.mem B w 3 * 2 ^ (5 * (3 * (w / 4) + 2)) % m : Nat) : Int) *
          x - num t.mem B w 1 ∧ num t.mem B w 3 < m) ∧
        (¬ KeyCheck.Shape w pL qL → (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧
          num t.mem B w 3 < m)) := by
  have := h.wle
  have hn1 : 1 ≤ (max pL qL + 3) / 4 := by omega
  have hnw : (max pL qL + 3) / 4 ≤ w := by omega
  have hfit : (max pL qL + 3) / 4 + (max pL qL + 3) / 4 % 2 ≤ w := by omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h.r29 h20 h22 (by omega) (by omega) (by omega)) fun s1 ⟨z1, m1, k1⟩ => ?_
  have h1 := h.of_keep k1
  have e11 : s1.gpr .r11 = BitVec.ofNat 64 ((max pL qL + 3) / 4) := (k1.gpr _ (by decide)).trans h11
  have x1 : num s1.mem B w 0 = x := by rw [m1]; exact hx
  have m1' : num s1.mem B w 8 = m := by rw [m1]; exact hm
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun hz => ?_)
  · -- Balanced: `inverseS`.
    have hs := z1.1 (by simpa using hz)
    obtain ⟨p8, hpw2, hpq, p32⟩ := hs
    have hν : ((max pL qL + 3) / 4 + 1) / 2 = w / 4 := by omega
    refine WP.mono (InvLaw.inverseS_ok h1 (by decide) (by decide) hw e11 hn1 hnw hfit x1 hxn m1' hmn hodd)
      fun t ⟨ht, Kt, kt, vt⟩ => ?_
    rw [hν] at vt
    rw [m1] at Kt
    refine ⟨ht, Kt, (k1.trans kt).mono (by decide), fun hm1 => ?_⟩
    obtain ⟨g, d, l⟩ := vt hm1
    exact ⟨g, fun _ => ⟨d, l⟩, fun hn => absurd ⟨p8, hpw2, hpq, p32⟩ hn⟩
  · -- Otherwise: `inverse`.
    have hs : ¬ KeyCheck.Shape w pL qL := fun hs => by simp [z1.2 hs] at hz
    refine WP.mono (InvLaw.inverse_ok h1 (by decide) (by decide) hw e11 hn1 hnw hfit x1 hxn m1' hmn hodd)
      fun t ⟨ht, Kt, kt, vt⟩ => ?_
    rw [m1] at Kt
    refine ⟨ht, Kt, (k1.trans kt).mono (by decide), fun hm1 => ?_⟩
    obtain ⟨g, d, l⟩ := vt hm1
    exact ⟨g, fun h' => absurd h' hs, fun _ => ⟨d, l⟩⟩

end VG.Proof.Rsa.PPC64LE.CrtValues
