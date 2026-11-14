module
-- separate module: builds in parallel with the other stages of `det_ok` (`RdCorrect.lean`)

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyDiv
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdShift
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the divisions

`divA_ok`: `m = ⌊a / n⌋` and `r = a mod n` (wide), and whether `m < n`;
`divB_ok`: `n - r` divided by `m + 1` (narrow), and whether it is exact.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Proof.Rsa.RecoverDet (wsub wsub_neg wsub_of_le)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (S arr num arr_disj)
open VG.Impl.Rsa.PPC64LE.RecoverDet (divA divB sB0 sB1 sLt sExact sCz)

section
variable {s0 s : State} {A : Bool → Nat → Nat} {V : Nat → Nat} {live : List (Bool × Nat)} {ls : List Nat}

/-- A number's low words, where it is below `2^(64 h)`. -/
theorem wordsVal_low {m : Mem} {B : Addr} {d h k : Nat} (hlt : val32 m B d (2 * (h + k)) < 2 ^ (64 * h)) :
    wordsVal m B d h = val32 m B d (2 * (h + k)) := by
  rw [wordsVal_eq_val32]
  have e := val32_append m B d (2 * h) (2 * k)
  rw [show 2 * h + 2 * k = 2 * (h + k) by omega_using [], show 32 * (2 * h) = 64 * h by omega_using []] at e
  rw [e] at hlt ⊢
  have : val32 m B (d + 4 * (2 * h)) (2 * k) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * (2 * h)) (2 * k)) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * h)) z; omega_using [hlt, this]
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- A number's low words. -/
theorem wordsVal_mod_low (m : Mem) (B : Addr) (d h k : Nat) :
    wordsVal m B d h = val32 m B d (2 * (h + k)) % 2 ^ (64 * h) := by
  rw [wordsVal_eq_val32]
  have e := val32_append m B d (2 * h) (2 * k)
  rw [show 2 * h + 2 * k = 2 * (h + k) by omega_using [], show 32 * (2 * h) = 64 * h by omega_using []] at e
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  rw [← show 32 * (2 * h) = 64 * h by omega_using []]; exact val32_lt _ _ _ _

/-- The word division on the wide view (`KeyDiv.divQ`): `[a] := ⌊[a] / [m]⌋`
and `[r] := [a] mod [m]`, for `[m] < 2^(64 h)` with its top word not zero,
through the wide arrays `t` and `sv`. -/
theorem DS.divQW (h : DS s0 true A live V ls s) {a r m t sv : Nat}
    (top : 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) ≤ A true m % 2 ^ (64 * ((kK s0 + 7) / 8)))
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ ∀ j ∈ [r, t, sv, a], Sep (true, j) e)
    (ha : (true, a) ∈ live := by decide) (hn : (true, m) ∈ live := by decide) (hr : r < vN true := by decide)
    (ht : t < vN true := by decide) (hsv : sv < vN true := by decide) (hrm : r ≠ m := by decide)
    (hrt : r ≠ t := by decide) (hrsv : r ≠ sv := by decide) (hmt : m ≠ t := by decide)
    (hmsv : m ≠ sv := by decide) (htsv : t ≠ sv := by decide) (har : a ≠ r := by decide)
    (ham : a ≠ m := by decide) (hat : a ≠ t := by decide) (hasv : a ≠ sv := by decide) :
    WP isa (VG.Impl.Rsa.PPC64LE.KeyDiv.divQ a r m t sv [.subi .r11 .r29 6, .lsr .d .r11 .r11 1]
      [.lsr .d .r4 .r29 1]) s fun u =>
      DS s0 true (upd (upd A true a (A true a / (A true m % 2 ^ (64 * ((kK s0 + 7) / 8))))) true r
        (A true a % (A true m % 2 ^ (64 * ((kK s0 + 7) / 8))))) ((true, r) :: (true, a) :: live') V ls u ∧
        Keep VG.Proof.Rsa.PPC64LE.KeyDiv.divRegs s u := by
  have w1 := h.base.sz.w1
  have w2 := h.base.sz.w2
  have haN := h.live_lt _ ha
  have hmN := h.live_lt _ hn
  simp only at haN hmN
  generalize ehh : (kK s0 + 7) / 8 = hh at top ⊢
  have eww : ww (kK s0) = 2 * hh + 2 := by simp only [ww]; omega_using [ehh]
  have eW : vw s0 true = 2 * (2 * hh + 3) := by rw [vw_true]; simp only [wW]; omega_using [eww]
  have ws := h.ws
  have fa := ws.arr_fit haN
  simp only [S] at fa
  have dj : ∀ {x y : Nat}, x ≠ y → arr (vw s0 true) x + 8 * (2 * hh + 3) ≤ arr (vw s0 true) y ∨
      arr (vw s0 true) y + S (vw s0 true) ≤ arr (vw s0 true) x := fun hxy => by
    have := arr_disj (w := vw s0 true) hxy
    simp only [S] at this ⊢; omega_using [eW, this]
  -- `r11 := 2 h` and `r4 := 2 h + 3` from `r29 = W`.
  have hdw : ∀ u : State, Ws u (rvB s0) (rvZ s0) (vw s0 true) (vN true) →
      WP isa (.block [.subi .r11 .r29 6, .lsr .d .r11 .r11 1]) u fun u' =>
        u'.gpr .r11 = BitVec.ofNat 64 (2 * hh) ∧ u'.mem = u.mem ∧ Keep [.r11] u u' := fun u hu => by
    have e : (BitVec.ofNat 64 (vw s0 true) - BitVec.ofNat 64 6) >>> 1 = BitVec.ofNat 64 (2 * hh) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, eW]
      omega
    exact WP.mono (WP.keep [.r11] (Q := fun u' => u'.gpr .r11 = BitVec.ofNat 64 (2 * hh) ∧ u'.mem = u.mem)
      (by prun [exec_subi (show Reg.r29 ≠ .r0 by decide) (show 6 ≤ 2 ^ 15 by decide),
        exec_lsr_d (show 1 < 64 by decide), hu.r29, e]) (by decide)) fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  have haw : ∀ u : State, Ws u (rvB s0) (rvZ s0) (vw s0 true) (vN true) → u.gpr .r11 = BitVec.ofNat 64 (2 * hh) →
      WP isa (.block [.lsr .d .r4 .r29 1]) u fun u' =>
        u'.gpr .r4 = BitVec.ofNat 64 (2 * hh + 3) ∧ u'.mem = u.mem ∧ Keep [.r4] u u' := fun u hu _ => by
    have e : BitVec.ofNat 64 (vw s0 true) >>> 1 = BitVec.ofNat 64 (2 * hh + 3) := by
      rw [eW]; exact VG.Proof.Bignum.PPC64LE.mont_ofNat_shr1 (by omega)
    exact WP.mono (WP.keep [.r4] (Q := fun u' => u'.gpr .r4 = BitVec.ofNat 64 (2 * hh + 3) ∧ u'.mem = u.mem)
      (by prun [exec_lsr_d (show 1 < 64 by decide), hu.r29, e]) (by decide)) fun _ ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  -- The divisor: `[m]`'s low `h` words.
  have hM : wordsVal s.mem (rvB s0) (arr (vw s0 true) m) hh = A true m % 2 ^ (64 * hh) := by
    rw [wordsVal_mod_low _ _ _ hh (hh + 3), ← h.val hn, show 2 * (hh + (hh + 3)) = vw s0 true by rw [eW]; omega_using []]
  have hX : wordsVal s.mem (rvB s0) (arr (vw s0 true) a) (2 * hh + 3) = A true a := by
    rw [← h.val ha, wordsVal_eq_val32, eW]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.KeyDiv.divG_ok true (a := a) (r := r) (m := m) (t := t) (sv := sv)
    (D := hh) (A := 2 * hh + 3) (v := 2 * hh + 3) ws hr hmN ht hsv hrm hrt hrsv hmt hmsv htsv
    (vN_le true) eW (by omega) (by omega) (by omega_using []) (by omega_using []) (by omega) haN (by omega_using [eW, fa])
    (dj har) (fun _ => dj ham) (dj hat) (dj hasv)
    hdw haw (by rw [hM]; exact top)) fun u ⟨ur, uq, wu, kr, uo⟩ => ⟨?_, kr⟩
  rw [hX, hM] at ur
  rw [hX, hM] at uq
  have k : KeyWorkspace.Keep (rvB s0) (vw s0 true) [r, t, sv, a] [] s.mem u.mem := by
    show Outs _ _ _ _
    refine VG.Proof.Rsa.PPC64LE.KeyDiv.Outs.cover uo fun x hx => ?_
    simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [KeyWorkspace.ranges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [KeyWorkspace.ranges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [KeyWorkspace.ranges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(arr (vw s0 true) a, S (vw s0 true)), by simp [KeyWorkspace.ranges], Nat.le_refl _,
        by simp only [S]; omega_using [eW]⟩
  have hu := h.wrs wu (js := [r, t, sv, a]) (fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> with_reducible assumption) k hl kr
  have va : num u.mem (rvB s0) (vw s0 true) a = A true a / (A true m % 2 ^ (64 * hh)) := by
    rw [← uq rfl]; show val32 _ _ _ _ = _; rw [wordsVal_eq_val32, eW]
  have vr : num u.mem (rvB s0) (vw s0 true) r = A true a % (A true m % 2 ^ (64 * hh)) := by
    rw [← ur]; show val32 _ _ _ _ = _; rw [wordsVal_eq_val32, eW]
  have hu1 := hu.add (o := a) haN va (fun e he => sep_ne ((hl e he).2 a (by simp)))
  refine hu1.add (o := r) hr vr (fun e he => ?_)
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · exact fun e => har (Prod.mk.inj e).2
  · exact sep_ne ((hl e he).2 r (by simp))

/-- `divA`: `m` and `r` of `a` by `n`, and whether `m < n`. -/
theorem divA_ok (h : DS s0 true A (pL 12) V [sB1, sB0] s) (z : A true 15 = 0)
    (top : 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) ≤ A false 32) (nlt : A false 32 < 2 ^ (64 * ((kK s0 + 7) / 8))) :
    WP isa divA s fun t => ∃ A' V',
      DS s0 true A' [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)] V'
        [sLt, sB1, sB0] t ∧
      A' true 17 = A true 17 / A false 32 ∧ A' true 18 = A true 17 % A false 32 ∧ A' true 19 = A false 32 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧
      V' sLt = b2n (decide (A true 17 / A false 32 < A false 32)) ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  unfold divA
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy (o := 19) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 17), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono h1.toNB fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.widen (k := 19) (a := 32) (by decide) (by decide) (by rd_simp [z]) (by decide)
    (by decide) (live' := [(true, 17), (true, 15), (true, 9), (false, 32)]) (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono h3.toWB fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.divQW (a := 17) (r := 18) (m := 19) (t := 21) (sv := 20)
    (by rd_simp; rw [Nat.mod_eq_of_lt nlt]; exact top) (live' := [(true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.sub3 (o := 20) (a := 17) (c := 19) (by decide) (by decide) (by decide)
    (live' := [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s7 ⟨h7, b7, _⟩ => ?_)
  refine WP.mono (h7.stBorrowB (sl := sLt) (by decide) b7 (by split <;> decide) (ls' := [sB1, sB0]) (by decide))
    fun t ⟨ht, _⟩ => ⟨_, _, ht.drop (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rd_simp [z, Nat.mod_eq_of_lt nlt]

/-- `fixTop j`, for `W = 4 h + 6`: word `h - 1` of `[j]` or'ed with whether it is zero. -/
theorem fixTop_ok {s : State} {B : Addr} {Z w N j H : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256)
    (hw : w = 4 * H + 6) (hH : 1 ≤ H) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.fixTop j)) s fun t =>
      t.mem = s.mem.writeW (off B (arr w j + 8 * (H - 1)))
        (word s.mem B (arr w j + 8 * (H - 1)) ||| BitVec.ofNat 64
          (if word s.mem B (arr w j + 8 * (H - 1)) = 0#64 then 1 else 0)) ∧
      Keep [.r0, .r3, .r5, .r9, .r11] s t := by
  have := h.wle
  have hnw := h.nowrap
  have fj := h.arr_fit hj
  simp only [S] at fj
  have e11 : (BitVec.ofNat 64 w - BitVec.ofNat 64 6) <<< 1 = BitVec.ofNat 64 (8 * H) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using [hw]
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.fixTop
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have h' := h.of_keep (Keep.write s .r5 (off B (arr w j)))
  refine WP.mono (WP.keep [.r0, .r3, .r5, .r9, .r11] (Q := fun t => t.mem = s.mem.writeW (off B (arr w j + 8 * (H - 1)))
        (word s.mem B (arr w j + 8 * (H - 1)) ||| BitVec.ofNat 64
          (if word s.mem B (arr w j + 8 * (H - 1)) = 0#64 then 1 else 0))) ?_ (by decide))
    fun t ⟨tm, tk⟩ => ⟨tm, ((Keep.write _ .r5 _).trans tk).mono (by decide)⟩
  have ea : off B (arr w j + 8 * H) - BitVec.ofNat 64 8 = off B (arr w j + 8 * (H - 1)) := by
    rw [VG.Proof.Rsa.PPC64LE.RdShift.off_sub B (by omega_arith)]; congr 1; omega_arith
  prun [gpr_write, mem_write, h.r29, e11, ea, h.scr.ld (show arr w j + 8 * (H - 1) + 8 ≤ Z by omega_arith),
    h.scr.st (show arr w j + 8 * (H - 1) + 8 ≤ Z by omega_arith)]
  have ew : word s.mem B (arr w j + 8 * (H - 1)) = s.mem.readW (off B (arr w j + 8 * (H - 1))) 64 := rfl
  rw [ew]
  generalize s.mem.readW (off B (arr w j + 8 * (H - 1))) 64 = y
  rw [BitVec.or_comm (0#64 - y) y, VG.Proof.Rsa.PPC64LE.RdShift.nz_bit]
  by_cases hy : y = 0#64
  · subst hy; rfl
  · simp only [hy, ↓reduceIte]; rfl

/-- Word `a` of `k`. -/
theorem wordsVal_mid (m : Mem) (B : Addr) {d k a : Nat} (ha : a < k) :
    wordsVal m B d k = wordsVal m B d a + 2 ^ (64 * a) * (word m B (d + 8 * a)).toNat +
      2 ^ (64 * a) * 2 ^ 64 * wordsVal m B (d + 8 * a + 8) (k - a - 1) := by
  have e := VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_append m B d a (k - a)
  rw [Nat.add_sub_cancel' (Nat.le_of_lt ha), show k - a = (k - a - 1) + 1 by omega_using [ha],
    VG.Proof.Rsa.PPC64LE.RdShift.wordsVal_succ_low] at e
  rw [e, Nat.mul_add, Nat.mul_assoc]; exact (Nat.add_assoc _ _ _).symm

/-- Word `a` of `k` written. -/
theorem wordsVal_write_mid (m : Mem) (B : Addr) {d k a : Nat} (ha : a < k) (v : BitVec 64)
    (fit : d + 8 * k ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * a)) v) B d k = wordsVal m B d a + 2 ^ (64 * a) * v.toNat +
      2 ^ (64 * a) * 2 ^ 64 * wordsVal m B (d + 8 * a + 8) (k - a - 1) := by
  have o := writeW_outside m B (d := d + 8 * a) v (by omega_arith)
  rw [wordsVal_mid _ B ha, word_writeW_self, o.wordsVal (by omega_arith) (by omega_arith),
    o.wordsVal (by omega_arith) (by omega_arith)]

/-- After the fix-up, word `a` is not zero. -/
theorem top_fix (X a : Nat) :
    2 ^ (64 * a) ≤ (X + (if X / 2 ^ (64 * a) % 2 ^ 64 = 0 then 2 ^ (64 * a) else 0)) % 2 ^ (64 * (a + 1)) := by
  have eP : 2 ^ (64 * (a + 1)) = 2 ^ (64 * a) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1
  rw [eP]
  have hP := Nat.two_pow_pos (64 * a)
  have hK : 2 ≤ 2 ^ 64 := Nat.one_lt_two_pow (by decide)
  generalize 2 ^ (64 * a) = P at hP ⊢
  generalize 2 ^ 64 = K at hK ⊢
  have e1 : X = X % P + P * (X / P % K) + P * K * (X / P / K) := by
    calc X = X % P + P * (X / P) := (Nat.mod_add_div X P).symm
      _ = X % P + P * (X / P % K + K * (X / P / K)) := by rw [Nat.mod_add_div (X / P) K]
      _ = _ := by rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc]
  have hlo : X % P < P := Nat.mod_lt _ hP
  have hy : X / P % K < K := Nat.mod_lt _ (by omega_using [hK])
  generalize X / P % K = y at e1 hy ⊢
  rw [e1]
  generalize X % P = lo at hlo
  generalize X / P / K = q
  have h2 := Nat.mul_le_mul_left P hK
  by_cases y0 : y = 0
  · subst y0
    simp only [↓reduceIte, Nat.mul_zero, Nat.add_zero]
    rw [show lo + P * K * q + P = lo + P + P * K * q by omega_using [], Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega_using [hlo, h2])]
    omega_using []
  · simp only [y0, ↓reduceIte]
    rw [Nat.add_zero]
    have hy1 : P * (y + 1) ≤ P * K := Nat.mul_le_mul_left P hy
    rw [Nat.mul_succ] at hy1
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega_using [hlo, hy1])]
    have : P * 1 ≤ P * y := Nat.mul_le_mul_left P (by omega_using [y0])
    omega_using [this]

/-- `fixTop j` on the wide view: word `h - 1` of `[j]` set to one if it is zero. -/
theorem DS.fixTopW (h : DS s0 true A live V ls s) {j : Nat} (hj : (true, j) ∈ live) {live' : List (Bool × Nat)}
    (hl : ∀ e ∈ live', e ∈ live ∧ Sep (true, j) e) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.fixTop j)) s fun t =>
      DS s0 true (upd A true j (A true j + (if A true j / 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) % 2 ^ 64 = 0
        then 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) else 0))) ((true, j) :: live') V ls t ∧
        Keep [.r0, .r3, .r5, .r9, .r11] s t := by
  have w1 := h.base.sz.w1
  have hjN := h.live_lt _ hj
  simp only at hjN
  generalize ehh : (kK s0 + 7) / 8 = H
  have eww : ww (kK s0) = 2 * H + 2 := by simp only [ww]; omega_using [ehh]
  have eW : vw s0 true = 4 * H + 6 := by rw [vw_true]; simp only [wW]; omega_using [eww]
  have eL : vw s0 true = 2 * (2 * H + 3) := by omega_using [eW]
  have fj := h.ws.arr_fit hjN
  have hnw := h.ws.nowrap
  simp only [S] at fj
  refine WP.mono (fixTop_ok h.ws hjN (vN_le true) eW (by omega)) fun t ⟨tm, kt⟩ => ⟨?_, kt⟩
  have k : KeyWorkspace.Keep (rvB s0) (vw s0 true) [j] [] s.mem t.mem := by
    rw [tm]
    exact KeyWorkspace.Keep.of_arr (d := 8 * (H - 1)) (writeW_outside _ _ _ (by omega_arith))
      (by simp only [S]; omega_using [eW]) (by simp)
  refine h.wr (h.ws.of_keep kt) hjN k ?_ hl kt
  have ex : A true j = wordsVal s.mem (rvB s0) (arr (vw s0 true) j) (2 * H + 3) := by
    rw [← h.val hj, VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ eL]
  have hy : A true j / 2 ^ (64 * (H - 1)) % 2 ^ 64 = (word s.mem (rvB s0) (arr (vw s0 true) j + 8 * (H - 1))).toNat := by
    rw [ex, wordsVal_word (by omega_using [])]
  rw [hy, VG.Proof.Rsa.PPC64LE.RdShift.num_words _ _ _ eL, tm,
    wordsVal_write_mid _ _ (show H - 1 < 2 * H + 3 by omega_using []) _ (by omega_arith), ex,
    wordsVal_mid _ _ (show H - 1 < 2 * H + 3 by omega_using [])]
  generalize word s.mem (rvB s0) (arr (vw s0 true) j + 8 * (H - 1)) = y
  generalize wordsVal s.mem (rvB s0) (arr (vw s0 true) j) (H - 1) = lo
  generalize wordsVal s.mem (rvB s0) (arr (vw s0 true) j + 8 * (H - 1) + 8) (2 * H + 3 - (H - 1) - 1) = hi
  generalize 2 ^ (64 * (H - 1)) = P
  generalize (2 : Nat) ^ 64 = K
  by_cases hy0 : y = 0#64
  · subst hy0
    have e1 : (0#64 ||| BitVec.ofNat 64 (if (0#64 : BitVec 64) = 0#64 then 1 else 0)).toNat = 1 := by decide
    rw [e1, show (0#64 : BitVec 64).toNat = 0 from rfl]
    simp only [↓reduceIte]
    omega_using []
  · have hyt : y.toNat ≠ 0 := fun e => hy0 (BitVec.eq_of_toNat_eq e)
    have e1 : (y ||| BitVec.ofNat 64 (if y = 0#64 then 1 else 0)) = y := by
      simp only [hy0, ↓reduceIte]; exact BitVec.or_zero
    rw [e1]
    simp only [hyt, ↓reduceIte]
    exact (Nat.add_zero _).symm

/-- The values of the normalized division: `m₁ 2^(64 c)` and `D 2^(64 c)` for `m₁`'s leading zero
words `c` in `h`. -/
theorem divB_arith {H c M1 D bw : Nat} (hc : RdShift.ClzOf M1 H c) (m0 : M1 ≠ 0) (dlt : D < 2 ^ (64 * H))
    (hbw : 64 * (2 * H) ≤ bw) :
    M1 * 2 ^ (64 * c) % 2 ^ bw = M1 * 2 ^ (64 * c) ∧ M1 * 2 ^ (64 * c) < 2 ^ (64 * H) ∧
      M1 * 2 ^ (64 * c) / 2 ^ (64 * (H - 1)) % 2 ^ 64 ≠ 0 ∧ D * 2 ^ (64 * c) % 2 ^ bw = D * 2 ^ (64 * c) := by
  obtain ⟨cle, -, hb⟩ := hc
  obtain ⟨lo, hi⟩ := hb m0
  have cH : c < H := by
    refine Nat.lt_of_le_of_ne cle fun e => ?_
    rw [e, Nat.sub_self, Nat.mul_zero, Nat.pow_zero] at hi
    omega_using [m0, hi]
  have e1 : 2 ^ (64 * (H - c - 1)) * 2 ^ (64 * c) = 2 ^ (64 * (H - 1)) := by
    rw [← Nat.pow_add]; congr 1; omega_using [cH]
  have e2 : 2 ^ (64 * (H - c)) * 2 ^ (64 * c) = 2 ^ (64 * H) := by
    rw [← Nat.pow_add]; congr 1; omega_using [cle]
  have e3 : 2 ^ 64 * 2 ^ (64 * (H - 1)) = 2 ^ (64 * H) := by
    rw [← Nat.pow_add]; congr 1; omega_using [cH]
  have pc := Nat.two_pow_pos (64 * c)
  have mlo : 2 ^ (64 * (H - 1)) ≤ M1 * 2 ^ (64 * c) := e1 ▸ Nat.mul_le_mul_right _ lo
  have mhi : M1 * 2 ^ (64 * c) < 2 ^ (64 * H) := e2 ▸ Nat.mul_lt_mul_of_pos_right hi pc
  have hW : 2 ^ (64 * H) ≤ 2 ^ bw := Nat.pow_le_pow_right (by decide) (by omega_using [hbw])
  have dhi : D * 2 ^ (64 * c) < 2 ^ bw := by
    have : D * 2 ^ (64 * c) < 2 ^ (64 * H) * 2 ^ (64 * c) := Nat.mul_lt_mul_of_pos_right dlt pc
    rw [← Nat.pow_add] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [hbw, cle]))
  refine ⟨Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le mhi hW), mhi, ?_, Nat.mod_eq_of_lt dhi⟩
  have hp := Nat.two_pow_pos (64 * (H - 1))
  have q1 : 1 ≤ M1 * 2 ^ (64 * c) / 2 ^ (64 * (H - 1)) := (Nat.le_div_iff_mul_le hp).mpr (by omega_using [mlo])
  have q2 : M1 * 2 ^ (64 * c) / 2 ^ (64 * (H - 1)) < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [e3]; exact mhi)
  rw [Nat.mod_eq_of_lt q2]; omega_using [m0, hb, lo, hi, e1, e2, e3, pc, mlo, mhi, dhi, hp, q1, q2]

theorem DS.named {b : Bool} (h : DS s0 b A live V ls s) : ∃ A', A' = A ∧ DS s0 b A' live V ls s :=
  ⟨A, rfl, h⟩

/-- `divB`: `n - r` by `m + 1` (narrow), and whether the remainder is zero, where `m < n` and `r < n`. -/
theorem divB_ok (h : DS s0 true A [(true, 17), (true, 18), (true, 19), (true, 15), (true, 9), (false, 32)] V
      [sLt, sB1, sB0] s) (z : A true 15 = 0) (nlt : A false 32 < 2 ^ (64 * ((kK s0 + 7) / 8))) :
    WP isa divB s fun t => ∃ Q R A' V', DS s0 false A' dbL V' [sExact, sLt, sB1, sB0] t ∧
      (A true 17 % 2 ^ (32 * ww (kK s0)) < A false 32 → A true 18 % 2 ^ (32 * ww (kK s0)) < A false 32 →
        Q = wsub (32 * ww (kK s0)) (A false 32) (A true 18 % 2 ^ (32 * ww (kK s0))) /
          ((A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0))) ∧
        R = wsub (32 * ww (kK s0)) (A false 32) (A true 18 % 2 ^ (32 * ww (kK s0))) %
          ((A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0)))) ∧
      A' false 25 = Q ∧ A' false 23 = wsub (32 * ww (kK s0)) 0 1 ∧ A' false 30 = 0 ∧ A' true 19 = A true 19 ∧
      A' true 15 = 0 ∧ A' true 9 = A true 9 ∧ A' false 32 = A false 32 ∧
      V' sExact = b2n (decide (R = 0)) ∧ V' sLt = V sLt ∧ V' sB0 = V sB0 ∧ V' sB1 = V sB1 := by
  have w1 := h.base.sz.w1
  have P1 : 1 < 2 ^ (32 * ww (kK s0)) := Nat.one_lt_two_pow (by omega_using [w1])
  have hHw : (kK s0 + 7) / 8 < vw s0 false + 1 := by rw [vw_false]; simp only [ww]; omega_using []
  have hnb : 32 * ww (kK s0) = 64 * ((kK s0 + 7) / 8) + 64 := by simp only [ww]; omega_using []
  have hbw : 64 * (2 * ((kK s0 + 7) / 8)) ≤ 32 * vw s0 true := by rw [vw_true]; simp only [wW, ww]; omega_using []
  unfold divB
  simp only [seqs]
  refine WP.seq (WP.mono h.toNB fun s1 ⟨h1, _⟩ => ?_)
  have h1a := ((h1.addLow (k := 15) (by decide) (by decide) (by decide)).addLow (k := 17) (by decide) (by decide)
    (by decide)).addLow (k := 18) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (h1a.copy (o := 22) (a := 30) (by decide) (by decide) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 17), (true, 18), (true, 19), (true, 15), (true, 9),
      (false, 32)]) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.setOneB (j := 22) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.sub3 (o := 23) (a := 30) (c := 22) (by decide) (by decide) (by decide)
    (live' := [(false, 36), (false, 34), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s4 ⟨h4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.sub3 (o := 24) (a := 34) (c := 23) (by decide) (by decide) (by decide)
    (live' := [(false, 23), (false, 36), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s5 ⟨h5, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.sub3 (o := 25) (a := 32) (c := 36) (by decide) (by decide) (by decide)
    (live' := [(false, 24), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s6 ⟨h6, _, _⟩ => ?_)
  obtain ⟨A6, eA6, h6⟩ := h6.named
  generalize eM : (A true 17 % 2 ^ (32 * ww (kK s0)) + 1) % 2 ^ (32 * ww (kK s0)) = M1
  generalize eD : wsub (32 * ww (kK s0)) (A false 32) (A true 18 % 2 ^ (32 * ww (kK s0))) = D
  have a24 : A6 false 24 = M1 := by
    rw [eA6, ← eM, ← wsub_neg (Nat.mod_lt _ (Nat.two_pow_pos _)) P1]; rd_simp [z]
  have a25 : A6 false 25 = D := by rw [eA6, ← eD]; rd_simp [z]
  have a23 : A6 false 23 = wsub (32 * ww (kK s0)) 0 1 := by rw [eA6]; rd_simp [z]
  have a30 : A6 false 30 = 0 := by rw [eA6]; rd_simp [z]
  have a19 : A6 true 19 = A true 19 := by rw [eA6]; rd_simp [z]
  have a15 : A6 true 15 = 0 := by rw [eA6]; rd_simp [z]
  have a9 : A6 true 9 = A true 9 := by rw [eA6]; rd_simp [z]
  have a32 : A6 false 32 = A false 32 := by rw [eA6]; rd_simp [z]
  -- The leading zero words of `m + 1`.
  refine WP.seq (WP.mono (RdShift.DS.clzWN h6 (m := 24) (sl := sCz) (by decide) (by decide)
    (ls' := [sLt, sB1, sB0]) (by decide)) fun s7 ⟨c, hc, h7, _⟩ => ?_)
  rw [a24] at hc
  have cH := hc.1
  refine WP.seq (WP.mono h7.toWB fun s8 ⟨h8, _⟩ => ?_)
  refine WP.seq (WP.mono (h8.copy (o := 4) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(false, 25), (false, 24), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s9 ⟨h9, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h9.copy (o := 5) (a := 15) (by decide) (by decide) (by decide)
    (live' := [(true, 4), (false, 25), (false, 24), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9),
      (false, 32)]) (by decide)) fun s10 ⟨h10, _, _⟩ => ?_)
  refine WP.seq (WP.mono h10.toNB fun s11 ⟨h11, _⟩ => ?_)
  refine WP.seq (WP.mono (h11.widen (k := 4) (a := 24) (by decide) (by decide) (by rd_simp [a15]) (by decide)
    (by decide) (live' := [(true, 5), (false, 25), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9),
      (false, 32)]) (by decide)) fun s12 ⟨h12, _⟩ => ?_)
  refine WP.seq (WP.mono (h12.widen (k := 5) (a := 25) (by decide) (by decide) (by rd_simp [a15]) (by decide)
    (by decide) (live' := [(true, 4), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)])
    (by decide)) fun s13 ⟨h13, _⟩ => ?_)
  refine WP.seq (WP.mono h13.toWB fun s14 ⟨h14, _⟩ => ?_)
  obtain ⟨A14, eA14, h14⟩ := h14.named
  have b4 : A14 true 4 = M1 := by rw [eA14]; rd_simp [a24]
  have b5 : A14 true 5 = D := by rw [eA14]; rd_simp [a25]
  have b23 : A14 false 23 = wsub (32 * ww (kK s0)) 0 1 := by rw [eA14]; rd_simp [a23]
  have b30 : A14 false 30 = 0 := by rw [eA14]; rd_simp [a30]
  have b19 : A14 true 19 = A true 19 := by rw [eA14]; rd_simp [a19]
  have b15 : A14 true 15 = 0 := by rw [eA14]; rd_simp [a15]
  have b9 : A14 true 9 = A true 9 := by rw [eA14]; rd_simp [a9]
  have b32 : A14 false 32 = A false 32 := by rw [eA14]; rd_simp [a32]
  -- `m + 1` and `n - r` shifted up by `c` words; the divisor's word `h - 1` not zero.
  have vc : updV V sCz c sCz = c := by rd_simp [sCz]
  refine WP.seq (WP.mono (RdShift.DS.shlByW false h14 (j := 4) (sw := sCz) (sb := sCz) (by decide) (by decide)
    (by decide) (by rw [vc]; omega_using [hHw, cH]) (fun e => absurd e (by decide))
    (live' := [(true, 5), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s15 ⟨h15, _⟩ => ?_)
  refine WP.seq (WP.mono (DS.fixTopW h15 (j := 4) (by decide)
    (live' := [(true, 5), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s16 ⟨h16, _⟩ => ?_)
  refine WP.seq (WP.mono (RdShift.DS.shlByW false h16 (j := 5) (sw := sCz) (sb := sCz) (by decide) (by decide)
    (by decide) (by rw [vc]; omega_using [hHw, cH]) (fun e => absurd e (by decide))
    (live' := [(true, 4), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s17 ⟨h17, _⟩ => ?_)
  obtain ⟨A17, eA17, h17⟩ := h17.named
  generalize eX : M1 * 2 ^ (64 * c) % 2 ^ (32 * vw s0 true) = X
  generalize eF : X + (if X / 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) % 2 ^ 64 = 0 then
    2 ^ (64 * ((kK s0 + 7) / 8 - 1)) else 0) = F
  have c4 : A17 true 4 = F := by
    rw [eA17, ← eF, ← eX]; rd_simp [vc, b4]
  have c5 : A17 true 5 = D * 2 ^ (64 * c) % 2 ^ (32 * vw s0 true) := by
    rw [eA17]; rd_simp [vc, b5]
  have topF : 2 ^ (64 * ((kK s0 + 7) / 8 - 1)) ≤ F % 2 ^ (64 * ((kK s0 + 7) / 8)) := by
    have := top_fix X ((kK s0 + 7) / 8 - 1)
    rw [show (kK s0 + 7) / 8 - 1 + 1 = (kK s0 + 7) / 8 by omega_using [w1, hnb], eF] at this
    exact this
  -- The division.
  refine WP.seq (WP.mono (h17.divQW (a := 5) (r := 6) (m := 4) (t := 7) (sv := 3) (by rw [c4]; exact topF)
    (live' := [(true, 4), (false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun s18 ⟨h18, _⟩ => ?_)
  obtain ⟨A18, eA18, h18⟩ := h18.named
  have d5 : A18 true 5 = D * 2 ^ (64 * c) % 2 ^ (32 * vw s0 true) / (F % 2 ^ (64 * ((kK s0 + 7) / 8))) := by
    rw [eA18, ← c4, ← c5]; rd_simp
  have d6 : A18 true 6 = D * 2 ^ (64 * c) % 2 ^ (32 * vw s0 true) % (F % 2 ^ (64 * ((kK s0 + 7) / 8))) := by
    rw [eA18, ← c4, ← c5]; rd_simp
  have d15 : A18 true 15 = 0 := by rw [eA18, eA17]; rd_simp [b15]
  refine WP.seq (WP.mono (h18.eqS (d := sExact) (a := 6) (c := 15) (by decide) (by decide) (by decide)
    (ls' := [sLt, sB1, sB0]) (by decide)) fun s19 ⟨h19, _⟩ => ?_)
  refine WP.seq (WP.mono h19.toNB fun s20 ⟨h20, _⟩ => ?_)
  have h20' := h20.addLow (k := 5) (by decide) (by decide) (by decide)
  refine WP.mono (h20'.copy (o := 25) (a := 10) (by decide) (by decide) (by decide)
    (live' := [(false, 23), (false, 30), (true, 19), (true, 15), (true, 9), (false, 32)]) (by decide))
    fun t ⟨ht, _, _⟩ => ?_
  obtain ⟨At, eAt, ht⟩ := ht.named
  have e25 : At false 25 = A18 true 5 % 2 ^ (32 * ww (kK s0)) := by rw [eAt]; rd_simp
  -- Where `m < n` and `r < n`: `m + 1 ≤ n` and `n - r` have at most `h` words, and the division is theirs.
  have hv : A true 17 % 2 ^ (32 * ww (kK s0)) < A false 32 → A true 18 % 2 ^ (32 * ww (kK s0)) < A false 32 →
      F % 2 ^ (64 * ((kK s0 + 7) / 8)) = M1 * 2 ^ (64 * c) ∧
      D * 2 ^ (64 * c) % 2 ^ (32 * vw s0 true) = D * 2 ^ (64 * c) ∧ M1 ≠ 0 ∧ D < 2 ^ (64 * ((kK s0 + 7) / 8)) := by
    intro hm hr
    have hp : 2 ^ (64 * ((kK s0 + 7) / 8)) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega_using [hnb])
    have eM1 : M1 = A true 17 % 2 ^ (32 * ww (kK s0)) + 1 := by rw [← eM]; exact Nat.mod_eq_of_lt (by omega_using [nlt, hm, hp])
    have eD' : D = A false 32 - A true 18 % 2 ^ (32 * ww (kK s0)) := by
      rw [← eD]; exact wsub_of_le (by omega_using [nlt, hp]) (Nat.le_of_lt hr)
    have M1lt : M1 < 2 ^ (64 * ((kK s0 + 7) / 8)) := by omega_using [nlt, hm, eM1]
    have m0 : M1 ≠ 0 := by omega_using [eM1]
    have dlt : D < 2 ^ (64 * ((kK s0 + 7) / 8)) := by omega_using [nlt, eD']
    rw [Nat.mod_eq_of_lt M1lt] at hc
    obtain ⟨x1, x2, x3, x4⟩ := divB_arith hc m0 dlt hbw
    have eX' : X = M1 * 2 ^ (64 * c) := by rw [← eX, x1]
    have eF' : F = X := by
      rw [← eF]
      rw [eX']
      simp only [x3, ↓reduceIte]
      exact Nat.add_zero _
    exact ⟨by rw [eF', eX', Nat.mod_eq_of_lt x2], x4, m0, dlt⟩
  refine ⟨At false 25, if A true 17 % 2 ^ (32 * ww (kK s0)) < A false 32 ∧ A true 18 % 2 ^ (32 * ww (kK s0)) <
    A false 32 then D % M1 else A18 true 6, At, _, ht.drop (by decide) (by decide), fun hm hr => ?_, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [eAt, eA18, eA17]; rd_simp [b23]
  · rw [eAt, eA18, eA17]; rd_simp [b30]
  · rw [eAt, eA18, eA17]; rd_simp [b19]
  · rw [eAt, eA18, eA17]; rd_simp [b15]
  · rw [eAt, eA18, eA17]; rd_simp [b9]
  · rw [eAt, eA18, eA17]; rd_simp [b32]
  · by_cases hc2 : A true 17 % 2 ^ (32 * ww (kK s0)) < A false 32 ∧ A true 18 % 2 ^ (32 * ww (kK s0)) < A false 32
    · obtain ⟨eF', eN, m0, _⟩ := hv hc2.1 hc2.2
      have z6 : A18 true 6 = 0 ↔ D % M1 = 0 := by
        rw [d6, eF', eN, Nat.mul_mod_mul_right]
        exact ⟨fun e => (Nat.mul_eq_zero.mp e).resolve_right (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)),
          fun e => by rw [e, Nat.zero_mul]⟩
      simp only [hc2, and_self, ↓reduceIte]
      rd_simp [sCz, d15, z6]
    · simp only [hc2, ↓reduceIte]
      rd_simp [sCz, d15]
  · rd_simp [sCz]
  · rd_simp [sCz]
  · rd_simp [sCz]
  · obtain ⟨eF', eN, m0, dlt⟩ := hv hm hr
    refine ⟨?_, by simp only [hm, hr, and_self, ↓reduceIte]⟩
    have hp : 2 ^ (64 * ((kK s0 + 7) / 8)) ≤ 2 ^ (32 * ww (kK s0)) := Nat.pow_le_pow_right (by decide) (by omega_using [hnb])
    rw [e25, d5, eF', eN, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _),
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hv, hm, hr, hp]))]


end

end VG.Proof.Rsa.PPC64LE.RecDet
