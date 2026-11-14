module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.WordDivQ
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
import VerifiedGarbage.Proof.Rsa.RISCV64.RdShift
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The second stage of `vg_rsa_recover_primes_det` on RISC-V

From the GCD on, what `Impl/Rsa/RISCV64/RecoverDet.lean`'s pieces compute,
each as an operation on the working space (`Ws`) from the numbers it reads to
what `Proof/Rsa/RecoverDetModel.lean` names, in the narrow (`w` words, 63
arrays) or the wide (`W2 w` words, 31 arrays) view:

* `divA_ok`: `a = g · 2^k x mod 2^wb`, `m = ⌊a / n⌋`, `r = a mod n` and
  whether `m < n`, by words (`WordDivQ.divQ_ok`) with `n`'s `w - 1` words, its
  top word not zero; the registers a division borrows saved in the header
  around it (`saveDiv_ok`, `restDiv_ok`);
* `divB_ok`: `m + 1` and `n - r`, both shifted up by the leading zero words of
  `m + 1` (`clz_ok`, `RdShift.shlStages_ok`), the divisor's top word made
  nonzero (`fixTopH_ok`), their quotient by words and whether the remainder is
  zero, exact where `m < n`, `r < n` and `n < 2^(64 (w - 1))` (`divB1_ok`,
  `divB2_ok`);
* `minus4n_ok`: `b`, `b²`, `4 n`, `b² - 4 n` and its two checks;
* `maskOf_ok`, `factors_ok`: the factors and the mask of every check.

Every frame is in the narrow view; `st2Regs` are the registers the steps may
change.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs sub3 subN mov seqs copy sel half eqS stBorrow)

open VG.Impl.Rsa.RISCV64.Div (div divK)
open VG.Impl.Rsa.RISCV64.RecoverDet (ctxW ctxw shl shlC mulLow sqB divA divB minus4n factors
  maskOf next wN wA wR wDt wT2 wG wX3 wB wSq wOne aN aZero aOne aNeg1 aM1 aD aRm aSy aTy aDf
  aP aQ aNy sLt sExact sC1 sC2 sBb sOk5 sMask sB0 sB1)
open VG.Proof.Rsa.RecoverDet (wsub sqOf fourN prod_iter)

/-- The registers the steps of the second stage may change. -/
abbrev st2Regs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .s7, .a2, .a3, .a6, .s8, .s9, .s10]

/-! ## Helpers -/

/-- `sub3`, and only the first `w` words of `o` change. -/
theorem sub3o_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048)
    (aA : Ahead (arr w o) (arr w a) w) (aB : Ahead (arr w o) (arr w b) w) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      Outside B (arr w o) (8 * w) s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (64 * w) * (t.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [VG.Impl.Rsa.RISCV64.Keys.sub3, subN, WP.seq_iff]
  refine ptrs_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun t p0 p1 p2 kt mt => ?_
  have hb' : WP isa (.block [.addi .t3 .s9 ((0 : Nat) : Int), .li .t4 0]) t fun u =>
      (u.gpr .t0 = off B (arr w o) ∧ u.gpr .t1 = off B (arr w a) ∧ u.gpr .t2 = off B (arr w b) ∧
        u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = 0 ∧ u.mem = t.mem) ∧ Keep [.t3, .t4] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show (0 : Nat) < 2048 by omega_arith), fin64_exec_li_zero, p0, p1, p2,
      (h.of_keep kt).s9, add_ofNat_zero']
  refine WP.mono hb' fun u ⟨⟨u0, u1, u2, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u0 u1 u2 u3 (by rw [u4]; decide) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith) (by omega_arith) aA aB) ?_
  intro t' ⟨b4, veq, out, kt'⟩
  rw [u4, um, mt] at veq
  rw [um, mt] at out
  exact ⟨hu.of_keep kt', Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), out, by simpa using veq, b4, Keep.trans' k₁ kt'⟩

/-- A subtraction modulo `2^b` as the code leaves it, and its borrow. -/
theorem wsub_of_sub {b x a c β : Nat} (hv : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = wsub b a c ∧ (β = 1 ↔ a < c) := by
  unfold wsub
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at hv
    refine ⟨?_, by omega⟩
    rw [show a + 2 ^ b - c = x + 2 ^ b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · simp only [Nat.mul_one] at hv
    refine ⟨?_, by omega⟩
    rw [show a + 2 ^ b - c = x by omega, Nat.mod_eq_of_lt hx]

/-- `b²` as the model computes it. -/
theorem sqOf_eq {nb wb b : Nat} (hb : b < 2 ^ nb) (hw : nb ≤ wb) : sqOf nb wb b = b * b % 2 ^ wb := by
  have : b < 2 ^ wb := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hw)
  unfold sqOf
  rw [prod_iter _ _ _ this]
  simp only
  rw [Nat.mod_eq_of_lt hb]

/-- The upper half of a wide array, apart from a write of the low `w` words of its low half. -/
theorem hiW_out {m m' : Mem} {B : Addr} {w j : Nat} (h : Outside B (arr w (2 * j)) (8 * w) m m')
    (fit : arr w (2 * j + 1) + 8 * w ≤ 2 ^ 64) : hiW m' B w j = hiW m B w j := by
  have := arr_succ w (2 * j)
  have hS : S w = 8 * (w + 2) := rfl
  exact Mont.Outside.wordsVal h (by omega_arith) (by omega_arith)

/-- The upper half of a wide array, apart from a frame of other narrow arrays. -/
theorem hiW_frame {m m' : Mem} {B : Addr} {w j : Nat} {js ds : List Nat} (f : Frame B w js ds m m')
    (hj : ∀ k ∈ js, k ≠ 2 * j ∧ k ≠ 2 * j + 1) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w (2 * j + 1) + S w ≤ 2 ^ 64) : hiW m' B w j = hiW m B w j := by
  have := arr_succ w (2 * j)
  have hS : S w = 8 * (w + 2) := rfl
  refine f.words (fun k hk => ?_) (fun d hd' => ?_) (by omega_arith)
  · obtain ⟨h1, h2⟩ := hj k hk
    rcases Nat.lt_or_gt_of_ne h1 with c | c
    · have := arr_end (w := w) c; omega_arith
    · have c' : 2 * j + 1 < k := by omega_using [h2, c]
      have := arr_end (w := w) c'; omega_arith
  · have := hd d hd'; have := hdr_le_arr w (2 * j); omega_arith

/-- `-1` as the code leaves it. -/
theorem st2_neg_one_of {x β P : Nat} (hv : x + 1 = 0 + P * β) (hβ : β ≤ 1) : x = P - 1 := by
  rcases (by omega_arith : β = 0 ∨ β = 1) with rfl | rfl <;> simp at hv <;> omega_using [hv]

/-- `m + 1` as the code leaves it: `m - (P - 1)`. -/
theorem st2_m1_of {x m β P : Nat} (hv : x + (P - 1) = m + P * β) (hx : x < P) (hm : m < P) (hβ : β ≤ 1) :
    x = (m + 1) % P := by
  rcases (by omega_arith : β = 0 ∨ β = 1) with rfl | rfl
  · simp at hv
    have : m = P - 1 := by omega_using [hm, hv]
    subst this; rw [show P - 1 + 1 = P by omega_using [hx], Nat.mod_self]; omega_using [hv]
  · simp at hv; rw [Nat.mod_eq_of_lt (by omega_using [hx, hv])]; omega_using [hx, hv]

/-! ## `a`, `m` and `r`, and `b`, by words -/

open VG.Impl.Rsa.RISCV64.RecoverDet (saveDiv restDiv divSaved halfH)

theorem rd_wr_other {m : Mem} {B : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (he : e + 8 ≤ 2 ^ 64) (hd : d + 8 ≤ 2 ^ 64) : word (m.writeW (off B e) v) B d = word m B d :=
  (writeW_outside m B v he).word h hd

/-- The header slots a division's borrowed registers are kept in. -/
abbrev divSlots : List Nat := [104, 112, 120, 168, 176, 184]

/-- `saveDiv`: the registers a division borrows into their header slots. -/
theorem saveDiv_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block saveDiv) s fun t => Ws t B Z w N ∧ Frame B w [] divSlots s.mem t.mem ∧ Keep [] s t ∧
      word t.mem B 104 = s.gpr .s1 ∧ word t.mem B 112 = s.gpr .s2 ∧ word t.mem B 120 = s.gpr .s3 ∧
      word t.mem B 168 = s.gpr .s4 ∧ word t.mem B 176 = s.gpr .a0 ∧ word t.mem B 184 = s.gpr .a1 := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hh : hdr = 256 := rfl
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off B 104) (s.gpr .s1)).writeW (off B 112) (s.gpr .s2)).writeW (off B 120) (s.gpr .s3)).writeW
        (off B 168) (s.gpr .s4)).writeW (off B 176) (s.gpr .a0)).writeW (off B 184) (s.gpr .a1)) (by
    simp only [saveDiv, divSaved, List.map]
    brun [h.s11, h.scr.st (d := 104) (n := 8) (by omega_arith), h.scr.al8 (d := 104) (by omega_arith) (by decide),
      h.scr.st (d := 112) (n := 8) (by omega_arith), h.scr.al8 (d := 112) (by omega_arith) (by decide),
      h.scr.st (d := 120) (n := 8) (by omega_arith), h.scr.al8 (d := 120) (by omega_arith) (by decide),
      h.scr.st (d := 168) (n := 8) (by omega_arith), h.scr.al8 (d := 168) (by omega_arith) (by decide),
      h.scr.st (d := 176) (n := 8) (by omega_arith), h.scr.al8 (d := 176) (by omega_arith) (by decide),
      h.scr.st (d := 184) (n := 8) (by omega_arith), h.scr.al8 (d := 184) (by omega_arith) (by decide)])
    (by rfl) (by rfl)) fun t ⟨tm, k⟩ => ?_
  refine ⟨h.of_keep k, ?_, k, ?_⟩
  · rw [tm]
    have f := fun (m : Mem) (d : Nat) (v : BitVec 64) (hd : d ∈ divSlots) =>
      ((slot_write (m := m) (B := B) (w := w) (d := d) v (by simp at hd; omega_arith)).1.mono (by simp)
        (fun x hx => by simp at hx; subst hx; exact hd) : Frame B w [] divSlots m (m.writeW (off B d) v))
    exact (((((f _ 104 _ (by simp)).trans (f _ 112 _ (by simp))).trans (f _ 120 _ (by simp))).trans
      (f _ 168 _ (by simp))).trans (f _ 176 _ (by simp))).trans (f _ 184 _ (by simp))
  · rw [tm]
    simp (disch := omega_arith) only [rd_wr_other, Mont.word_writeW_self, and_self]

/-- `restDiv`: the borrowed registers back from their header slots. -/
theorem restDiv_ok {u : State} {B : Addr} {Z w N : Nat} (h : Ws u B Z w N) {v1 v2 v3 v4 v5 v6 : BitVec 64}
    (e1 : word u.mem B 104 = v1) (e2 : word u.mem B 112 = v2) (e3 : word u.mem B 120 = v3)
    (e4 : word u.mem B 168 = v4) (e5 : word u.mem B 176 = v5) (e6 : word u.mem B 184 = v6) :
    WP isa (.block restDiv) u fun t => (t.gpr .s1 = v1 ∧ t.gpr .s2 = v2 ∧ t.gpr .s3 = v3 ∧ t.gpr .s4 = v4 ∧
      t.gpr .a0 = v5 ∧ t.gpr .a1 = v6 ∧ t.mem = u.mem) ∧ Keep [.s1, .s2, .s3, .s4, .a0, .a1] u t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hh : hdr = 256 := rfl
  have r1 : u.mem.readW (off B 104) 64 = v1 := e1
  have r2 : u.mem.readW (off B 112) 64 = v2 := e2
  have r3 : u.mem.readW (off B 120) 64 = v3 := e3
  have r4 : u.mem.readW (off B 168) 64 = v4 := e4
  have r5 : u.mem.readW (off B 176) 64 = v5 := e5
  have r6 : u.mem.readW (off B 184) 64 = v6 := e6
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [restDiv, divSaved, List.map]
  brun [h.s11, r1, r2, r3, r4, r5, r6,
    h.scr.ld (d := 104) (n := 8) (by omega_arith), h.scr.al8 (d := 104) (by omega_arith) (by decide),
    h.scr.ld (d := 112) (n := 8) (by omega_arith), h.scr.al8 (d := 112) (by omega_arith) (by decide),
    h.scr.ld (d := 120) (n := 8) (by omega_arith), h.scr.al8 (d := 120) (by omega_arith) (by decide),
    h.scr.ld (d := 168) (n := 8) (by omega_arith), h.scr.al8 (d := 168) (by omega_arith) (by decide),
    h.scr.ld (d := 176) (n := 8) (by omega_arith), h.scr.al8 (d := 176) (by omega_arith) (by decide),
    h.scr.ld (d := 184) (n := 8) (by omega_arith), h.scr.al8 (d := 184) (by omega_arith) (by decide)]

/-- `halfH`: `t0 := W / 2 - 2 = w - 1` in the wide view. -/
theorem halfH_ok {s : State} {B : Addr} {Z w M : Nat} (h : Ws s B Z (W2 w) M) (hw : 1 ≤ w) :
    WP isa (.block halfH) s fun t => (t.gpr .t0 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ∧ Keep [.t0] s t := by
  have hle := h.wle
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : W2 w = 2 * (w + 1) := by simp only [W2]; omega_using []
  have hs : (BitVec.ofNat 64 (w - 1 + 2)) = BitVec.ofNat 64 (w + 1) := by congr 1; omega_using [hw]
  simp only [halfH]
  brun [h.s9, e, shr1_ofNat (w + 1) (by omega_arith), exec_addi_neg_nat (m := 2) (by decide)]
  rw [← hs, sub_ofNat2]

open VG.Impl.Rsa.RISCV64.RecoverDet (wDig wTmp wSD wSN)
open VG.Impl.Rsa.RISCV64 (WordDiv.divCore)
open VG.Proof.Rsa.RecoverDet (wsub_of_le)

/-- The registers the divisions may change (those they borrow restored). -/
abbrev dvRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .a6, .a7, .s0, .s7, .s8, .s9, .s10]

/-- The words of a zero number past its first `k`. -/
theorem words_hi_zero {m : Mem} {B : Addr} {d w k : Nat} (h : wordsVal m B d w = 0) (hk : k ≤ w) :
    wordsVal m B (d + 8 * k) (w - k) = 0 := by
  have e := wordsVal_append m B d k (w - k)
  rw [show k + (w - k) = w by omega_using [hk], h] at e
  have := Nat.two_pow_pos (64 * k)
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * k) (w - k)) with z | z
  · exact z
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * k)) z; omega_arith

/-- A header word kept by a frame of arrays only. -/
theorem frame_hword {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (f : Frame B w js [] m m') {e : Nat}
    (he : e + 8 ≤ hdr) : word m' B e = word m B e :=
  BitVec.eq_of_toNat_eq (Frame.slot f he (by simp))

theorem divSlots_le : ∀ e ∈ divSlots, e + 8 ≤ hdr := by decide

/-- The borrowed registers restored after a division, from the saved slots kept. -/
theorem keep_restored {s t u : State} {rs : List Reg} (k₁ : Keep rs s t) (k₂ : Keep [.s1, .s2, .s3, .s4, .a0, .a1] t u)
    (e1 : u.gpr .s1 = s.gpr .s1) (e2 : u.gpr .s2 = s.gpr .s2) (e3 : u.gpr .s3 = s.gpr .s3)
    (e4 : u.gpr .s4 = s.gpr .s4) (e5 : u.gpr .a0 = s.gpr .a0) (e6 : u.gpr .a1 = s.gpr .a1)
    {out : List Reg} (hsub : ∀ r ∈ rs, r ∈ out ∨ r ∈ [Reg.s1, .s2, .s3, .s4, .a0, .a1] := by decide) :
    Keep out s u := by
  refine ⟨fun r hr => ?_, k₂.2.1.trans k₁.2.1, k₂.2.2.trans k₁.2.2⟩
  by_cases hk : r ∈ [Reg.s1, .s2, .s3, .s4, .a0, .a1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e1, e2, e3, e4, e5, e6]
  · have h1 : r ∉ rs := fun hm => (hsub r hm).elim hr hk
    exact (k₂.gpr hk).trans (k₁.gpr h1)

/-- `divA`, narrow view to wide: `n` into `wN`, `a = g · 2^k x mod 2^(64 W)`, `m = ⌊a / n⌋` (`wDt`),
`r = a mod n` (`wR`) and whether `m < n`, by words (`divQ_ok`) with `n`'s `w - 1` words, its top
word not zero. -/
theorem divA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024)
    (hw : 5 ≤ w) (hw' : w ≤ 184) (hNz : hiW s.mem B w wN = 0)
    (hA0 : num s.mem B (W2 w) wA = 0) (hR0 : num s.mem B (W2 w) wR = 0)
    (hQ0 : wordsVal s.mem B (arr (W2 w) wDt) (W2 w + 1) = 0)
    (hnT : 2 ^ (64 * (w - 2)) ≤ num s.mem B w aN) (hnl : num s.mem B w aN < 2 ^ (64 * (w - 1))) :
    WP isa divA s fun t => Ws t B Z (W2 w) 31 ∧
      Frame B w (halves [wN, wA, wR, wDt, wT2, wDig, wTmp]) (sLt :: divSlots) s.mem t.mem ∧ Keep dvRegs s t ∧
      num t.mem B (W2 w) wN = num s.mem B w aN ∧
      num t.mem B (W2 w) wDt =
        num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) / num s.mem B w aN ∧
      num t.mem B (W2 w) wR =
        num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) % num s.mem B w aN ∧
      slot t.mem B sLt = (if num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) /
        num s.mem B w aN < num s.mem B w aN then 1 else 0) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold divA
  -- 1: `n` into the low half of the wide `wN`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (o := 2 * wN) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, f1, v1, r1, o1⟩ => ?_
  -- 2: the wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h1 hW (by decide)) fun t2 ⟨⟨h2, m2⟩, r2⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h2.fit64 hj
  have f1W := f1.toWide
  rw [← m2] at f1 f1W o1 v1
  have a2 : num t2.mem B (W2 w) wA = 0 := by
    rw [f1W.num (by decide) (by simp) (fW _ (by decide)), hA0]
  have g2 : num t2.mem B (W2 w) wG = num s.mem B (W2 w) wG := f1W.num (by decide) (by simp) (fW _ (by decide))
  have x2 : num t2.mem B (W2 w) wX3 = num s.mem B (W2 w) wX3 :=
    f1W.num (by decide) (by simp) (fW _ (by decide))
  have hz2 : hiW t2.mem B w wN = 0 := by
    have f29 : arr w (2 * wN + 1) + 8 * w ≤ 2 ^ 64 := by
      have := fit (2 * wN + 1) (by decide); simp only [S] at this; omega_arith
    rw [hiW_out o1 f29]; exact hNz
  have n2 : num t2.mem B (W2 w) wN = num s.mem B w aN := by
    rw [numW_low (j := wN) hz2]; exact v1
  -- 3: `a`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mulLow_ok h2 (o := wA) (y := wG) (x := wX3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a2) fun t3 ⟨h3, f3, _, v3, r3⟩ => ?_
  rw [g2, x2] at v3
  generalize hAv : num s.mem B (W2 w) wG * num s.mem B (W2 w) wX3 % 2 ^ (64 * W2 w) = A at v3 ⊢
  generalize hnv : num s.mem B w aN = n at hnT hnl n2 ⊢
  have n3 : num t3.mem B (W2 w) wN = n := by rw [f3.num (by decide) (by simp) (fW _ (by decide)), n2]
  have R3 : num t3.mem B (W2 w) wR = 0 := by
    rw [f3.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide)), hR0]
  have Q3 : wordsVal t3.mem B (arr (W2 w) wDt) (W2 w + 1) = 0 := by
    rw [f3.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := W2 w) (show wA ≠ wDt by decide); simp only [S] at this ⊢; omega_arith)
      (by simp) (by have := fW wDt (by decide); simp only [S] at this ⊢; omega_arith),
      f1W.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := W2 w) (show wN ≠ wDt by decide); simp only [S] at this ⊢; omega_arith)
      (by simp) (by have := fW wDt (by decide); simp only [S] at this ⊢; omega_arith), hQ0]
  -- 4: save the borrowed registers, `t0 := w - 1`, `t6 := W`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveDiv_ok h3) fun t4 ⟨h4, f4, k4, e1, e2, e3, e4, e5, e6⟩ => ?_
  refine WP.mono (halfH_ok h4 (by omega_using [hw])) fun t5 ⟨⟨c5, m5⟩, k5⟩ => ?_
  have h5 := h4.of_keep k5
  have hb : WP isa (.block [mov .t6 .s9]) t5 fun x =>
      (x.gpr .t6 = BitVec.ofNat 64 (W2 w) ∧ x.gpr .t0 = BitVec.ofNat 64 (w - 1) ∧ x.mem = t5.mem) ∧
        Keep [.t6] t5 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [mov]
    brun [h5.s9, c5, exec_addi_nat (m := 0) (by decide), BitVec.add_zero]
  refine WP.mono hb fun t6 ⟨⟨c6, c6', m6⟩, k6⟩ => ?_
  have h6 := h5.of_keep k6
  have hdS := divSlots_le
  have M6 : t6.mem = t4.mem := m6.trans m5
  have hW2 : W2 w = 2 * w + 2 := rfl
  have N6 : num t6.mem B (W2 w) wN = n := by
    rw [M6, f4.num (by simp) (fun d hd => hdS d hd) (fW _ (by decide)), n3]
  have nl6 : wordsVal t6.mem B (arr (W2 w) wN) (w - 1) = n := words_low (by omega_using [hW2]) N6 hnl
  have hT : 0 < (word t6.mem B (arr (W2 w) wN + 8 * (w - 1 - 1))).toNat :=
    top_pos (by omega_using [hw]) (by rw [nl6, show w - 1 - 1 = w - 2 by omega_using []]; exact hnT)
  have R6 : num t6.mem B (W2 w) wR = 0 := by
    rw [M6, f4.num (by simp) (fun d hd => hdS d hd) (fW _ (by decide)), R3]
  have r6 : wordsVal t6.mem B (arr (W2 w) wR) (w - 1 + 1) = 0 :=
    words_low (by omega_using [hW2]) R6 (Nat.two_pow_pos _)
  have q6 : wordsVal t6.mem B (arr (W2 w) wDt) (W2 w + 1) = 0 := by
    rw [M6, f4.words (by simp) (fun e he => .inr (Nat.le_trans (hdS e he) (hdr_le_arr _ _)))
      (by have := fW wDt (by decide); simp only [S] at this ⊢; omega_arith)]
    exact Q3
  have A6 : wordsVal t6.mem B (arr (W2 w) wA) (W2 w) = A := by
    change num t6.mem B (W2 w) wA = A
    rw [M6, f4.num (by simp) (fun d hd => hdS d hd) (fW _ (by decide))]; exact v3
  -- 5: `m = ⌊a / n⌋` and `r = a mod n` by words.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divQ_ok h6 (a := wA) (r := wR) (m := wN) (t := wTmp) (dig := wDig) (q := wDt)
    (v := w - 1) (Wd := W2 w) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega_using [hw]) (by omega_using [hW2]) (by omega_using [hW2]) (by omega_using []) (by omega_using [hw', hW2]) (by omega_using [hw, hW2]) c6' c6 r6 q6 hT)
    fun t7 ⟨h7, f7, k7, v7, z7, rest7, q7⟩ => ?_
  rw [A6, nl6] at v7 q7
  -- 6: the borrowed registers back.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have sw : ∀ e, e + 8 ≤ hdr → word t7.mem B e = word t4.mem B e := fun e he => by
    rw [frame_hword f7 he, M6]
  refine WP.mono (restDiv_ok h7 ((sw _ (by decide)).trans e1) ((sw _ (by decide)).trans e2)
    ((sw _ (by decide)).trans e3) ((sw _ (by decide)).trans e4) ((sw _ (by decide)).trans e5)
    ((sw _ (by decide)).trans e6)) fun t8 ⟨⟨g1, g2, g3, g4, g5, g6, m8⟩, k8⟩ => ?_
  have h8 := h7.of_keep k8
  have K3 : Keep (opRegs ++ [.s9, .s10] ++ mulRegs) s t3 :=
    Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (r3.mono (by decide)))
  have K7 : Keep (opRegs ++ [.s9, .s10] ++ mulRegs ++ [.t0, .t6] ++ divQRegs) s t7 :=
    Keep.trans' (K3.mono (by decide)) (Keep.trans' (k4.mono (by decide)) (Keep.trans' (k5.mono (by decide))
      (Keep.trans' (k6.mono (by decide)) (k7.mono (by decide)))))
  have K8 : Keep dvRegs s t8 := keep_restored K7 k8
    (g1.trans (K3.gpr (by decide))) (g2.trans (K3.gpr (by decide))) (g3.trans (K3.gpr (by decide)))
    (g4.trans (K3.gpr (by decide))) (g5.trans (K3.gpr (by decide))) (g6.trans (K3.gpr (by decide)))
  -- 7: `m < n`.
  have F8 : Frame B (W2 w) [wR, wTmp, wDig, wDt] [] t6.mem t8.mem := by rw [m8]; exact f7
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h8 (o := wT2) (a := wDt) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t9 ⟨h9, f9, v9, b9, r9⟩ => ?_
  refine WP.mono (stBorrow_ok h9 (sl := sLt) (by decide) (by decide)) fun t ⟨h10, f10, s10, r10⟩ => ?_
  have Dt8 : num t8.mem B (W2 w) wDt = A / n := by
    rw [m8]; exact words_low (by omega_using []) q7 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (by rw [← hAv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
  have N8 : num t8.mem B (W2 w) wN = n := by rw [F8.num (by decide) (by simp) (fW _ (by decide)), N6]
  have e10 : ∀ j, j < 31 → j ≠ wT2 → num t.mem B (W2 w) j = num t8.mem B (W2 w) j := fun j hj hj' => by
    rw [f10.num (by simp) (by decide) (fW _ hj), f9.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj)]
  refine ⟨h10, ?_, Keep.trans' K8 (Keep.trans' (r9.mono (by decide)) (r10.mono (by decide))), ?_, ?_, ?_, ?_⟩
  · rw [M6] at F8
    exact ((((((f1.mono (js' := halves [wN, wA, wR, wDt, wT2, wDig, wTmp]) (ds' := sLt :: divSlots) (by decide)
      (by simp)).trans (f3.toNarrow.mono (by decide) (by simp))).trans (f4.toNarrow.mono (by decide) (by simp))).trans
      (F8.toNarrow.mono (by decide) (by simp))).trans (f9.toNarrow.mono (by decide) (by simp))).trans
      (f10.toNarrow.mono (by decide) (by simp)))
  · rw [e10 _ (by decide) (by decide), N8]
  · rw [e10 _ (by decide) (by decide), Dt8]
  · rw [e10 _ (by decide) (by decide)]
    have R7 : wordsVal t6.mem B (arr (W2 w) wR + 8 * (w - 1 + 1)) (W2 w - 1 - (w - 1)) = 0 := by
      have := words_hi_zero R6 (k := w - 1 + 1) (by omega_using [hW2])
      rwa [show W2 w - (w - 1 + 1) = W2 w - 1 - (w - 1) by omega_using []] at this
    rw [m8]
    exact num_of_low (by omega_using [hW2]) v7 z7 (by rw [rest7, R7])
  · rw [s10]
    rw [N8, Dt8] at v9
    have W := (wsub_of_sub v9 (wordsVal_lt _ _ _ _) (by rw [← N8]; exact wordsVal_lt _ _ _ _) b9).2
    split
    · exact W.mpr (by assumption)
    · rename_i c
      omega_using [b9, W, c]

/-! ## The leading zero words -/

open VG.Impl.Rsa.RISCV64.RecoverDet (clz fixTopH shlWords)

/-- The index of the highest nonzero word of `f` below `i`, 0 if none. -/
def hiIdx (f : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | i + 1 => if f i = 0 then hiIdx f i else i

/-- A number of `i` words is below `2^(64 (hiIdx + 1))`, and at least `2^(64 hiIdx)` if not zero. -/
theorem hiIdx_spec (m : Mem) (B : Addr) (d : Nat) : ∀ i,
    hiIdx (fun j => word m B (d + 8 * j)) i ≤ i - 1 ∧
    wordsVal m B d i < 2 ^ (64 * (hiIdx (fun j => word m B (d + 8 * j)) i + 1)) ∧
    (0 < wordsVal m B d i → 2 ^ (64 * hiIdx (fun j => word m B (d + 8 * j)) i) ≤ wordsVal m B d i)
  | 0 => by simp [hiIdx, wordsVal]
  | i + 1 => by
    obtain ⟨ih1, ih2, ih3⟩ := hiIdx_spec m B d i
    rw [wordsVal_succ_top]
    simp only [hiIdx]
    by_cases hz : word m B (d + 8 * i) = 0
    · simp only [hz, ite_true]
      exact ⟨by omega_using [ih1], ih2, ih3⟩
    · simp only [hz, ite_false]
      have hp : 0 < (word m B (d + 8 * i)).toNat :=
        Nat.pos_of_ne_zero fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      have l := wordsVal_lt m B d i
      have lw := (word m B (d + 8 * i)).isLt
      refine ⟨by omega_using [], ?_, fun _ => ?_⟩
      · have : wordsVal m B d i + 2 ^ (64 * i) * (word m B (d + 8 * i)).toNat < 2 ^ (64 * i) * 2 ^ 64 := by
          have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show (word m B (d + 8 * i)).toNat + 1 ≤ 2 ^ 64 by omega_using [])
          rw [Nat.mul_add, Nat.mul_one] at this; omega_using [l, this]
        rwa [← Nat.pow_add, show 64 * i + 64 = 64 * (i + 1) by omega_using []] at this
      · have := Nat.le_mul_of_pos_right (2 ^ (64 * i)) hp; omega_using [this]

/-- The registers `clz` writes. -/
abbrev clzRegs : List Reg := [.a5, .a4, .t1, .t2, .t3, .t4, .t5, .s7]

/-- `clz D`: `s7 := k - 1 - hiIdx`, from `t0 = k` (`k` of `w` words of `[D]`). -/
theorem clz_ok {s : State} {B : Addr} {Z w N D k : Nat} (h : Ws s B Z w N) (hD : D < N) (hN : N ≤ 2048)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ w) :
    WP isa (clz D) s fun t => t.mem = s.mem ∧
      t.gpr .s7 = BitVec.ofNat 64 (k - 1 - hiIdx (fun j => word s.mem B (arr w D + 8 * j)) k) ∧
      Keep clzRegs s t := by
  have fit := h.arr_fit hD
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have al := arr_al w D
  have hs := h.scr
  generalize hf : (fun j => word s.mem B (arr w D + 8 * j)) = f
  generalize hd : arr w D = d at fit al hf
  unfold clz
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show D < 2048 by omega_using [hD, hN]) ?_
  rw [hd]
  have hb : WP isa (.block [.li .a4 0, .li .t1 0, .li .t2 0, mov .t3 .t0]) (s.write .a5 (off B d)) fun u =>
      (u.gpr .a5 = off B d ∧ u.gpr .a4 = 0 ∧ u.gpr .t1 = 0 ∧ u.gpr .t2 = 0 ∧ u.gpr .t3 = BitVec.ofNat 64 k ∧
        u.gpr .t0 = BitVec.ofNat 64 k ∧ u.mem = s.mem) ∧ Keep [.a4, .t1, .t2, .t3] (s.write .a5 (off B d)) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [mov]
    brun [ht0, fin64_exec_li_zero, exec_addi_nat (m := 0) (by decide), BitVec.add_zero]
  refine WP.mono hb fun u ⟨⟨u5, u4, u1, u2, u3, u0, um⟩, uk⟩ => ?_
  have uk' : Keep clzRegs s u := ((Keep.write _ _ _).trans uk).mono (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .a5 = off B (d + 8 * i) ∧ t.gpr .t1 = BitVec.ofNat 64 i ∧ t.gpr .t2 = BitVec.ofNat 64 (hiIdx f i) ∧
      t.gpr .a4 = 0 ∧ t.gpr .t0 = BitVec.ofNat 64 k ∧ t.mem = s.mem ∧ Keep clzRegs s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .t3) (N := k) (by omega_using [hkw, hwl]) (by omega_using [hk]) Inv
    (fun i hi t ⟨j5, j1, j2, j4, j0, jm, jk⟩ _ => ?_)
    ⟨by rw [u5]; rfl, u1, u2, u4, u0, um, uk'⟩ u3) fun t ⟨t5, t1, t2, t4, t0, tm, tk⟩ => ?_)
  · have hs' := hs.congr jk.2.2
    have wa : t.mem.readW (off B (d + 8 * i)) 64 = f i := by rw [jm, ← hf]
    refine WP.mono (WP.keep clzRegs (Q := fun t' =>
        t'.gpr .a5 = off B (d + 8 * i) + BitVec.ofNat 64 8 ∧ t'.gpr .t1 = BitVec.ofNat 64 i + BitVec.ofNat 64 1 ∧
        t'.gpr .t2 = t.gpr .t2 ^^^ ((t.gpr .t2 ^^^ t.gpr .t1) &&& (0 - (if f i = 0 then 0 else 1))) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧ t'.gpr .a4 = 0 ∧ t'.gpr .t0 = BitVec.ofNat 64 k ∧
        t'.mem = t.mem) (by
      brun [j5, j1, j4, j0, wa, bit_lt, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide),
        exec_addi_nat (show 1 < 2048 by decide),
        hs'.ld (show d + 8 * i + 8 ≤ Z by omega_using [hkw, hS, fit, hi]), hs'.al8 (show d + 8 * i + 8 ≤ Z by omega_using [hkw, hS, fit, hi]) (by omega_using [al])])
      (by rfl) (by rfl)) fun t' ⟨⟨l5, l1, l2, l3, l4, l0, lm⟩, lk⟩ =>
        ⟨⟨?_, ?_, ?_, l4, l0, by rw [lm, jm], jk.trans lk |>.mono (by decide)⟩, l3⟩
    · rw [l5, off_add, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []]
    · rw [l1, ← BitVec.ofNat_add]
    · rw [l2, j2, j1]
      have hm : (if f i = 0 then (0 : BitVec 64) else 1) = if (!decide (f i = 0)) then 1 else 0 := by
        by_cases hz : f i = 0 <;> simp [hz]
      rw [hm, selb]
      simp only [hiIdx]
      by_cases hz : f i = 0
      · simp [hz]
      · simp only [hz, decide_false, Bool.not_false, ite_true]
        rw [ite_eq_right not_false]
  · have hle := (hiIdx_spec s.mem B d k).1
    rw [← hf] at t2
    have hb2 : WP isa (.block [.sub .s7 .t0 .t2, .addi .s7 .s7 (-1)]) t fun x =>
        (x.gpr .s7 = BitVec.ofNat 64 (k - 1 - hiIdx f k) ∧ x.mem = t.mem) ∧ Keep [.s7] t x := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [t0, t2, exec_addi_neg_nat (m := 1) (by decide)]
      rw [← hf]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have hkk : k < 2 ^ 64 := by omega_using [hkw, hwl]
      rw [Nat.mod_eq_of_lt hkk, Nat.mod_eq_of_lt (show hiIdx (fun j => word s.mem B (d + 8 * j)) k < 2 ^ 64 by omega_using [hle, hkk])]
      omega_using [hk, hle, hkk]
    refine WP.mono hb2 fun x ⟨⟨x7, xm⟩, xk⟩ => ⟨by rw [xm, tm], x7, (tk.trans xk).mono (by decide)⟩

/-- A top word plus one where it is zero: never zero, and unchanged otherwise. -/
theorem fixTop_val (y : BitVec 64) :
    (y + (if y < 1#64 then 1#64 else 0#64)) = if y = 0 then 1 else y := by
  by_cases hy : y = 0
  · subst hy; rfl
  · have : ¬ y < 1#64 := by
      rw [BitVec.lt_def]; intro h
      exact hy (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat] at h; simp; omega_using [h]))
    rw [ite_eq_right this, ite_eq_right hy, BitVec.add_zero]

/-- `fixTopH D` (`t0 = k`): `[D]`'s word `k - 1` plus one if it is zero. -/
theorem fixTopH_ok {s : State} {B : Addr} {Z w N D k : Nat} (h : Ws s B Z w N) (hD : D < N) (hN : N ≤ 2048)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ w) :
    WP isa (.block (fixTopH D)) s fun t => Ws t B Z w N ∧
      t.mem = s.mem.writeW (off B (arr w D + 8 * (k - 1)))
        (if word s.mem B (arr w D + 8 * (k - 1)) = 0 then 1 else word s.mem B (arr w D + 8 * (k - 1))) ∧
      Keep [.t3, .t5, .t6] s t := by
  have fit := h.arr_fit hD
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have al := arr_al w D
  have hs := h.scr
  generalize he : arr w D + 8 * (k - 1) = e
  have he8 : e + 8 ≤ Z := by omega_using [hkw, fit, hS, he]
  have ha : e % 8 = 0 := by omega_using [al, he]
  rw [show fixTopH D = (ptr .t3 D ++ [.shift .sll .d .t5 .t0 3, .add .t3 .t3 .t5, .addi .t3 .t3 (-8)]) ++
    [.load .d .t5 .t3 0, .li .t6 1, .sltu .t6 .t5 .t6, .add .t5 .t5 .t6, .store .d .t5 .t3 0] by
      simp [fixTopH], WP.block_append_iff]
  refine ptr_ok h (by decide) (by decide) (show D < 2048 by omega_using [hD, hN]) ?_
  have hb : WP isa (.block [.shift .sll .d .t5 .t0 3, .add .t3 .t3 .t5, .addi .t3 .t3 (-8)])
      (s.write .t3 (off B (arr w D))) fun u => (u.gpr .t3 = off B e ∧ u.mem = s.mem) ∧
        Keep [.t5, .t3] (s.write .t3 (off B (arr w D))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ht0, exec_addi_neg_nat (m := 8) (by decide)]
    rw [shl3_ofNat, off_add, ← he, show arr w D + 8 * k = arr w D + 8 * (k - 1) + 8 by omega_using [hk], ← off_add, BitVec.add_sub_cancel]
  refine WP.mono hb fun u ⟨⟨u3, um⟩, uk⟩ => ?_
  have hs' := hs.congr ((Keep.write _ _ _).trans uk).2.2
  have rd : u.mem.readW (off B e) 64 = word s.mem B e := by rw [um]
  refine WP.mono (WP.keep [.t5, .t6] (Q := fun t => t.mem = s.mem.writeW (off B e)
      (word s.mem B e + (if word s.mem B e < 1#64 then 1#64 else 0#64))) (by
    brun [u3, rd, um, BitVec.add_zero, hs'.ld he8, hs'.al8 he8 ha, hs'.st he8,
      exec_li (imm := 1) (by decide)]
    rfl) (by rfl) (by rfl)) fun t ⟨tm, tk⟩ => ?_
  have K : Keep [.t3, .t5, .t6] s t :=
    (((Keep.write _ _ _).trans uk).trans tk).mono (by decide)
  refine ⟨h.of_keep K, by rw [tm, fixTop_val], K⟩

/-! ## `b` -/

open VG.Impl.Rsa.RISCV64.InvBatch (zeroW zeros)

/-- Writing back the word just read changes nothing. -/
theorem rd_writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 64) = m := by
  funext x
  by_cases h : (x - a).toNat < 8
  · simp only [Mem.writeW, Mem.write, Mem.readW, show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq,
      h, ite_true]
    rw [Mem.extractLsb'_read m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · simp only [Mem.writeW, Mem.write, show (64 : Nat) / 8 = 8 from rfl, h, ite_false]

/-- `zeroW j`: `[j]`'s `w + 1` words := 0. -/
theorem zeroW1_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (zeroW j) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w j) (w + 1) = 0 ∧ Keep [.t0, .t3, .t5] s t := by
  have fj := h.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := arr_al w j
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by omega_using [hj, hN]) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.s9, exec_addi_nat (m := 1) (by decide)]
    exact (BitVec.ofNat_add _ _).symm
  have k1 : Keep [.t0, .t3, .t5] s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep [.t0, .t3, .t5] s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (Loops.zeroLoop_ok (dO := arr w j) (n := w + 1) (h.of_keep k2).scr
    (by rw [ky.gpr (by decide)]; exact u0) (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega_using []) (by omega_arith)
    (by omega_using [this]) (by omega_using [fj, hS])) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  exact ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega_using [hS]) (by simp), z, Keep.trans' k2 (kt.mono (by decide))⟩

/-- `divB` from the normalization on (narrow): `m + 1` (`M`, wide in `wSD`) and `n - r` (`D`, wide in
`wSN`) shifted up by the leading zero words of `M`'s `h = w - 1`, the divisor's top word made
nonzero, their quotient into `aD` and whether the remainder is zero; exact where `0 < M`,
`M < 2^(64 h)` and `D < 2^(64 h)`. -/
theorem divB2_ok {s : State} {B : Addr} {Z w M D : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024)
    (hw : 5 ≤ w) (hw' : w ≤ 129)
    (hSD : num s.mem B (W2 w) wSD = M) (hSN : num s.mem B (W2 w) wSN = D)
    (hR0 : wordsVal s.mem B (arr (W2 w) wR) (W2 w + 1) = 0)
    (hT0 : wordsVal s.mem B (arr (W2 w) wT2) (W2 w + 1) = 0) (hZ0 : num s.mem B w aZero = 0) :
    WP isa (seqs [.block (ctxW ++ saveDiv ++ halfH), clz wSD, shlWords wSD, shlWords wSN,
      .block (halfH ++ fixTopH wSD ++ halfH ++ ([.add .t6 .t0 .t0] : List Instr)),
      WordDiv.divCore wSN wR wSD wTmp (some (wDig, wT2)), .block restDiv, .block ctxw, copy aD (2 * wT2),
      eqS sExact (2 * wR) aZero]) s fun t => Ws t B Z w 63 ∧
      Frame B w (aD :: halves [wSD, wSN, wR, wT2, wDig, wTmp]) (sExact :: divSlots) s.mem t.mem ∧
      Keep dvRegs s t ∧ slot t.mem B sExact ≤ 1 ∧
      (0 < M → M < 2 ^ (64 * (w - 1)) → D < 2 ^ (64 * (w - 1)) →
        num t.mem B w aD = D / M ∧ slot t.mem B sExact = if D % M = 0 then 1 else 0) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hW2 : W2 w = 2 * w + 2 := rfl
  have hdS := divSlots_le
  -- 1: the wide view, the borrowed registers saved, `t0 := h`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctxW_ok (M := 31) h hW (by decide)) fun t1 ⟨⟨h1, m1⟩, k1⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  refine WP.mono (saveDiv_ok h1) fun t2 ⟨h2, f2, k2, e1, e2, e3, e4, e5, e6⟩ => ?_
  refine WP.mono (halfH_ok h2 (by omega_using [hw])) fun t3 ⟨⟨c3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep k3
  rw [m1] at f2
  have M3 : t3.mem = t2.mem := m3
  -- 2: `s7 := z`, the leading zero words of `M`'s `h`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clz_ok h3 (D := wSD) (k := w - 1) (by decide) (by decide) c3 (by omega_using [hw]) (by omega_using [hW2]))
    fun t4 ⟨m4, c4, k4⟩ => ?_
  have h4 := h3.of_keep k4
  generalize hhi : hiIdx (fun j => word t3.mem B (arr (W2 w) wSD + 8 * j)) (w - 1) = hi at c4
  generalize hz : w - 1 - 1 - hi = z at c4
  have hz128 : z < 2 ^ 7 := by omega_using [hw', hz]
  -- 3, 4: both shifted up by `z` words.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlStages_ok h4 (X := wSD) (R := .s7) (r := z) (b := 0) (by decide) (by decide) c4
    (by omega_using [hz128]) (by decide) (by decide) (by decide) (by rw [Nat.pow_zero, Nat.div_one]; omega_using [hW2, hz]) 7 (Nat.le_refl _))
    fun t5 ⟨h5, f5, v5, k5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shlStages_ok h5 (X := wSN) (R := .s7) (r := z) (b := 0) (by decide) (by decide)
    (by rw [k5.gpr (by decide)]; exact c4) (by omega_using [hz128]) (by decide) (by decide) (by decide)
    (by rw [Nat.pow_zero, Nat.div_one]; omega_using [hW2, hz]) 7 (Nat.le_refl _)) fun t6 ⟨h6, f6, v6, k6⟩ => ?_
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hz128] at v5 v6
  -- 5: `t0 := h`, the divisor's top word made nonzero, `t6 := 2 h`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (halfH_ok h6 (by omega_using [hw])) fun t7 ⟨⟨c7, m7⟩, k7⟩ => ?_
  have h7 := h6.of_keep k7
  refine WP.mono (fixTopH_ok h7 (D := wSD) (k := w - 1) (by decide) (by decide) c7 (by omega_using [hw]) (by omega_using [hW2]))
    fun t8 ⟨h8, m8, k8⟩ => ?_
  refine WP.mono (halfH_ok h8 (by omega_using [hw])) fun t9 ⟨⟨c9, m9⟩, k9⟩ => ?_
  have h9 := h8.of_keep k9
  have hb : WP isa (.block [.add .t6 .t0 .t0]) t9 fun x =>
      (x.gpr .t6 = BitVec.ofNat 64 (2 * (w - 1)) ∧ x.gpr .t0 = BitVec.ofNat 64 (w - 1) ∧ x.mem = t9.mem) ∧
        Keep [.t6] t9 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [c9]
    rw [← BitVec.ofNat_add, show w - 1 + (w - 1) = 2 * (w - 1) by omega_using []]
  refine WP.mono hb fun t10 ⟨⟨c10, c10', m10⟩, k10⟩ => ?_
  have h10 := h9.of_keep k10
  rw [m7] at m8
  generalize he : arr (W2 w) wSD + 8 * (w - 1 - 1) = e at m8
  have fSD := fW wSD (by decide)
  have he8 : e + 8 ≤ 2 ^ 64 := by simp only [S] at fSD; omega_using [hW2, he, fSD]
  have M10 : t10.mem = t6.mem.writeW (off B e)
      (if word t6.mem B e = 0 then 1 else word t6.mem B e) := by rw [m10, m9, m8]
  -- The arrays but `wSD` and `wSN`, from `s` to the division.
  have keepA : ∀ j k, j < 31 → j ≠ wSD → j ≠ wSN → k ≤ W2 w + 2 →
      wordsVal t10.mem B (arr (W2 w) j) k = wordsVal s.mem B (arr (W2 w) j) k := fun j k hj h1 h2 hk => by
    have fj := fW j hj
    have d1 := arr_disj (w := W2 w) h1
    have d2 := arr_disj (w := W2 w) h2
    have hS : S (W2 w) = 8 * (W2 w + 2) := rfl
    rw [M10, (writeW_outside _ B _ he8).wordsVal (by omega_using [hW, hw, hw', hW2, hz, he, fSD, he8, hk, fj, d1, d2, hS]) (by omega_using [hk, fj, hS]),
      f6.words (by simp; omega_using [hk, d2, hS]) (by simp) (by omega_using [hk, fj, hS]), f5.words (by simp; omega_using [hk, d1, hS]) (by simp) (by omega_using [hk, fj, hS]), m4, M3,
      f2.words (by simp) (fun e he => .inr (Nat.le_trans (hdS e he) (hdr_le_arr _ _))) (by omega_using [hk, fj, hS])]
  have hT8 : 0 < (word t10.mem B (arr (W2 w) wSD + 8 * (w - 1 - 1))).toNat := by
    rw [he, M10, word_writeW_self]
    split
    · decide
    · rename_i hy
      exact Nat.pos_of_ne_zero fun e0 => hy (BitVec.eq_of_toNat_eq (by rw [e0]; rfl))
  -- 6: the division by words.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divQ_ok h10 (a := wSN) (r := wR) (m := wSD) (t := wTmp) (dig := wDig) (q := wT2)
    (v := w - 1) (Wd := 2 * (w - 1)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega_using [hw]) (by omega_using [hW2]) (by omega_using [hw]) (by omega_using [hW2]) (by omega_using [hw']) (by omega_using [hW2]) c10' c10
    (by rw [keepA _ _ (by decide) (by decide) (by decide) (by omega_using [hW2])]
        exact words_low (by omega_using [hW2]) hR0 (Nat.two_pow_pos _))
    (by rw [keepA _ _ (by decide) (by decide) (by decide) (by omega_using [])]; exact hT0) hT8)
    fun t11 ⟨h11, f11, k11, v11, z11, rest11, q11⟩ => ?_
  -- 7: the borrowed registers back.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have sw : ∀ x, x + 8 ≤ hdr → word t11.mem B x = word t2.mem B x := fun x hx => by
    have := hdr_le_arr (W2 w) wSD
    rw [frame_hword f11 hx, M10, rd_wr_other _ (by omega_using [he, hx, this]) he8 (by omega_using [fSD, hx, this]), frame_hword f6 hx,
      frame_hword f5 hx, m4, M3]
  refine WP.mono (restDiv_ok h11 ((sw _ (by decide)).trans e1) ((sw _ (by decide)).trans e2)
    ((sw _ (by decide)).trans e3) ((sw _ (by decide)).trans e4) ((sw _ (by decide)).trans e5)
    ((sw _ (by decide)).trans e6)) fun t12 ⟨⟨g1, g2, g3, g4, g5, g6, m12⟩, k12⟩ => ?_
  have h12 := h11.of_keep k12
  -- 8: the narrow view; `aD` and whether the remainder is zero.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h12 (by omega_using [hw]) h.fits) fun t13 ⟨⟨h13, m13⟩, k13⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h13 (o := aD) (a := 2 * wT2) (by decide) (by decide) (by decide) (by decide))
    fun t14 ⟨h14, f14, v14, k14, _⟩ => ?_
  refine WP.mono (eqS_ok h14 (d := sExact) (a := 2 * wR) (b := aZero) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨h15, f15, s15, k15⟩ => ?_
  have K1 : Keep ([.s9, .s10] ++ [.t0] ++ clzRegs ++ stRegs ++ [.t0] ++ [.t3, .t5, .t6] ++ [.t0] ++ [.t6] ++
      divQRegs) s t11 :=
    Keep.trans' (k1.mono (by decide)) (Keep.trans' (k2.mono (by decide)) (Keep.trans' (k3.mono (by decide))
      (Keep.trans' (k4.mono (by decide)) (Keep.trans' (k5.mono (by decide)) (Keep.trans' (k6.mono (by decide))
        (Keep.trans' (k7.mono (by decide)) (Keep.trans' (k8.mono (by decide)) (Keep.trans' (k9.mono (by decide))
          (Keep.trans' (k10.mono (by decide)) (k11.mono (by decide)))))))))))
  have K12 : Keep dvRegs s t12 := keep_restored K1 k12
    (g1.trans (k1.gpr (by decide)))
    (g2.trans (k1.gpr (by decide)))
    (g3.trans (k1.gpr (by decide)))
    (g4.trans (k1.gpr (by decide)))
    (g5.trans (k1.gpr (by decide)))
    (g6.trans (k1.gpr (by decide)))
  refine ⟨h15, ?_, Keep.trans' K12 (Keep.trans' (k13.mono (by decide)) (Keep.trans' (k14.mono (by decide))
    (k15.mono (by decide)))), by rw [s15]; split <;> decide, fun hM0 hMh hDh => ?_⟩
  · have F10 : Frame B (W2 w) [wSD] [] t6.mem t10.mem := by
      rw [M10, ← he]
      exact Frame.of_arr (o := wSD) (d := 8 * (w - 1 - 1)) (n := 8) (by rw [he]; exact writeW_outside _ B _ he8)
        (by simp only [S]; omega_using [hW2]) (by simp)
    rw [← M3, ← m4] at f2
    have F12 : Frame B (W2 w) [wR, wTmp, wDig, wT2] [] t10.mem t13.mem := by rw [m13, m12]; exact f11
    exact (((((((f2.toNarrow.mono (js' := aD :: halves [wSD, wSN, wR, wT2, wDig, wTmp])
      (ds' := sExact :: divSlots) (by decide) (by simp)).trans (f5.toNarrow.mono (by decide) (by simp))).trans
      (f6.toNarrow.mono (by decide) (by simp))).trans (F10.toNarrow.mono (by decide) (by simp))).trans
      (F12.toNarrow.mono (by decide) (by simp))).trans (f14.mono (by simp) (by simp))).trans
      (f15.mono (by simp) (by simp)))
  · have hz2 : 0 < 2 ^ (64 * z) := Nat.two_pow_pos _
    have M4 : num t4.mem B (W2 w) wSD = M := by
      rw [m4, M3, f2.num (by simp) (fun d hd => hdS d hd) (fW _ (by decide)), hSD]
    have Mh : wordsVal t3.mem B (arr (W2 w) wSD) (w - 1) = M :=
      words_low (w := W2 w) (by omega_using [hW2]) (by rw [← m4]; exact M4) hMh
    obtain ⟨hiL, hiU, hiD⟩ := hiIdx_spec t3.mem B (arr (W2 w) wSD) (w - 1)
    rw [hhi, Mh] at hiU hiD
    rw [hhi] at hiL
    have hiD' := hiD hM0
    have ez : hi + 1 + z = w - 1 := by rw [← hz]; omega_using [hw, hiL]
    have MZu : M * 2 ^ (64 * z) < 2 ^ (64 * (w - 1)) := by
      have := Nat.mul_lt_mul_of_pos_right hiU hz2
      rwa [← Nat.pow_add, show 64 * (hi + 1) + 64 * z = 64 * (w - 1) by omega_using [hw, hz, hiL]] at this
    have MZl : 2 ^ (64 * (w - 1 - 1)) ≤ M * 2 ^ (64 * z) := by
      have := Nat.mul_le_mul_right (2 ^ (64 * z)) hiD'
      rwa [← Nat.pow_add, show 64 * hi + 64 * z = 64 * (w - 1 - 1) by omega_using [hz, hiL]] at this
    have pW : 2 ^ (64 * (w - 1)) ≤ 2 ^ (64 * W2 w) := Nat.pow_le_pow_right (by decide) (by omega_using [hW2])
    have S5 : wordsVal t5.mem B (arr (W2 w) wSD) (W2 w) = M * 2 ^ (64 * z) := by
      rw [v5]; change num t4.mem B (W2 w) wSD * _ % _ = _; rw [M4, Nat.mod_eq_of_lt (by omega_using [MZu, pW])]
    have S6 : wordsVal t6.mem B (arr (W2 w) wSD) (W2 w) = M * 2 ^ (64 * z) := by
      rw [f6.words (fun j hj => by
          simp only [List.mem_singleton] at hj; subst hj
          have := arr_disj (w := W2 w) (show wSN ≠ wSD by decide); simp only [S] at this ⊢; omega_using [this])
        (by simp) (by simp only [S] at fSD; omega_using [fSD]), S5]
    have S6h : wordsVal t6.mem B (arr (W2 w) wSD) (w - 1) = M * 2 ^ (64 * z) :=
      words_low (w := W2 w) (by omega_using [hW2]) S6 MZu
    have y0 := top_pos (m := t6.mem) (B := B) (d := arr (W2 w) wSD) (v := w - 1) (by omega_using [hw]) (by rw [S6h]; exact MZl)
    rw [he] at y0
    have hy : ¬ word t6.mem B e = 0 := fun e0 => by rw [e0] at y0; exact absurd y0 (by decide)
    have T10 : t10.mem = t6.mem := by rw [M10, ite_eq_right hy]; exact rd_writeW_readW _ _
    have N5 : wordsVal t5.mem B (arr (W2 w) wSN) (W2 w) = D := by
      rw [f5.words (fun j hj => by
          simp only [List.mem_singleton] at hj; subst hj
          have := arr_disj (w := W2 w) (show wSD ≠ wSN by decide); simp only [S] at this ⊢; omega_using [this])
        (by simp) (by have := fW wSN (by decide); simp only [S] at this ⊢; omega_using [this])]
      change num t4.mem B (W2 w) wSN = D
      rw [m4, M3, f2.num (by simp) (fun d hd => hdS d hd) (fW _ (by decide)), hSN]
    have DZu : D * 2 ^ (64 * z) < 2 ^ (64 * (2 * (w - 1))) := by
      have := Nat.mul_lt_mul_of_pos_right hDh hz2
      rw [← Nat.pow_add] at this
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [hz]))
    have N6 : wordsVal t10.mem B (arr (W2 w) wSN) (2 * (w - 1)) = D * 2 ^ (64 * z) := by
      rw [T10]
      refine words_low (w := W2 w) (by omega_using [hW2]) ?_ DZu
      rw [v6, N5, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le DZu (Nat.pow_le_pow_right (by decide) (by omega_using [hW2])))]
    have S10 : wordsVal t10.mem B (arr (W2 w) wSD) (w - 1) = M * 2 ^ (64 * z) := by rw [T10]; exact S6h
    rw [N6, S10, Nat.mul_div_mul_right _ _ hz2] at q11
    rw [N6, S10, Nat.mul_mod_mul_right] at v11
    have hDM : D / M < 2 ^ (64 * w) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_lt_of_le hDh (Nat.pow_le_pow_right (by decide) (by omega_using [])))
    have T13 : t13.mem = t11.mem := by rw [m13, m12]
    have Q13 : num t13.mem B w (2 * wT2) = D / M := by
      rw [T13]; change wordsVal t11.mem B (arr w (2 * wT2)) w = _
      rw [← arr_W2]; exact words_low (by omega_using [hW2]) q11 hDM
    have R13 : num t13.mem B w (2 * wR) = D % M * 2 ^ (64 * z) := by
      rw [T13]; change wordsVal t11.mem B (arr w (2 * wR)) w = _
      rw [← arr_W2]
      have e := wordsVal_succ_top t11.mem B (arr (W2 w) wR) (w - 1)
      rw [show w - 1 + 1 = w by omega_using [hw]] at e
      rw [e, z11, v11]
      simp
    have Z13 : num t13.mem B w aZero = 0 := by
      rw [T13]; change wordsVal t11.mem B (arr w (2 * 21)) w = _
      rw [← arr_W2, f11.words (fun j hj => by
          have hj' : j ≠ 21 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl | rfl | rfl <;> decide
          have := arr_disj (w := W2 w) hj'
          simp only [S] at this ⊢; omega_using [hW2, this])
        (by simp) (by have := fW 21 (by decide); simp only [S] at this ⊢; omega_using [hW2, this]),
        keepA _ _ (by decide) (by decide) (by decide) (by omega_using [hW2]), arr_W2]
      exact hZ0
    refine ⟨?_, ?_⟩
    · rw [f15.num (by simp) (by decide) (fit _ (by decide)), v14, Q13]
    · rw [s15, f14.num (by decide) (by simp) (fit _ (by decide)), f14.num (by decide) (by simp) (fit _ (by decide)),
        R13, Z13]
      have iff0 : D % M * 2 ^ (64 * z) = 0 ↔ D % M = 0 :=
        ⟨fun e0 => (Nat.mul_eq_zero.mp e0).resolve_right (Nat.pos_iff_ne_zero.mp hz2),
          fun e0 => by rw [e0, Nat.zero_mul]⟩
      by_cases c : D % M = 0
      · rw [ite_eq_left (iff0.mpr c), ite_eq_left c]
      · rw [ite_eq_right (fun e0 => c (iff0.mp e0)), ite_eq_right c]

/-- The upper half of a wide array, zero where its first `W + 1` words are. -/
theorem hiW_of_zero {m : Mem} {B : Addr} {w j : Nat} (h : wordsVal m B (arr (W2 w) j) (W2 w + 1) = 0) :
    hiW m B w j = 0 := by
  have z := words_hi_zero (k := w) (words_low (w := W2 w + 1) (v := W2 w) (by omega_using []) h (Nat.two_pow_pos _))
    (by simp only [W2]; omega_using [])
  unfold hiW
  rw [← arr_W2, show w + 2 = W2 w - w by simp only [W2]; omega_using []]
  exact z

/-- `divB` to the normalization (wide to narrow): `-1`, `m + 1` and `n - r` (narrow), copied into the
zeroed wide `wSD` and `wSN`; `wR` and `wT2` zeroed. -/
theorem divB1_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (W2 w) 31) (hfit : arr w 63 ≤ Z)
    (hW : W2 w ≤ 1024) (hw : 5 ≤ w) (hZ0 : num s.mem B w aZero = 0) (hOne : num s.mem B w aOne = 1) :
    WP isa (seqs [.block ctxw, sub3 aNeg1 aZero aOne, sub3 aM1 (2 * wDt) aNeg1, sub3 aD aN (2 * wR), .block ctxW,
      zeroW wSD, zeroW wSN, zeroW wR, zeroW wT2, .block ctxw, copy (2 * wSD) aM1, copy (2 * wSN) aD]) s
      fun t => Ws t B Z w 63 ∧
      Frame B w ([aNeg1, aM1, aD] ++ halves [wSD, wSN, wR, wT2]) [] s.mem t.mem ∧ Keep dvRegs s t ∧
      num t.mem B w aNeg1 = 2 ^ (64 * w) - 1 ∧
      num t.mem B (W2 w) wSD = (num s.mem B (W2 w) wDt % 2 ^ (64 * w) + 1) % 2 ^ (64 * w) ∧
      num t.mem B (W2 w) wSN = wsub (64 * w) (num s.mem B w aN) (num s.mem B (W2 w) wR % 2 ^ (64 * w)) ∧
      wordsVal t.mem B (arr (W2 w) wR) (W2 w + 1) = 0 ∧ wordsVal t.mem B (arr (W2 w) wT2) (W2 w + 1) = 0 ∧
      num t.mem B w aZero = 0 := by
  -- 1: the narrow view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h (by omega_using [hw]) hfit) fun t1 ⟨⟨h1, m1⟩, r1⟩ => ?_
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  -- 2: `-1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (o := aNeg1) (a := aZero) (b := aOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, f2, v2, b2, r2⟩ => ?_
  rw [m1, hZ0, hOne] at v2
  have neg2 := st2_neg_one_of v2 b2
  -- 3: `m + 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 (o := aM1) (a := 2 * wDt) (b := aNeg1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t3 ⟨h3, f3, v3, b3, r3⟩ => ?_
  have a2 : num t2.mem B w (2 * wDt) = num s.mem B (W2 w) wDt % 2 ^ (64 * w) := by
    rw [f2.num (by decide) (by simp) (fit _ (by decide)), m1, num_low]
  rw [a2, neg2] at v3
  have m3 := st2_m1_of v3 (wordsVal_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) b3
  -- 4: `n - r`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (o := aD) (a := aN) (b := 2 * wR) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t4 ⟨h4, f4, v4, b4, r4⟩ => ?_
  have n3 : num t3.mem B w aN = num s.mem B w aN := by
    rw [f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide)), m1]
  have r3' : num t3.mem B w (2 * wR) = num s.mem B (W2 w) wR % 2 ^ (64 * w) := by
    rw [f3.num (by decide) (by simp) (fit _ (by decide)), f2.num (by decide) (by simp) (fit _ (by decide)),
      m1, num_low]
  rw [n3, r3'] at v4
  have d4 := (wsub_of_sub v4 (wordsVal_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) b4).1
  -- 5: the wide view; four arrays zeroed.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h4 hW (by decide)) fun t5 ⟨⟨h5, m5⟩, r5⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h5.fit64 hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h5 (j := wSD) (by decide) (by decide)) fun t6 ⟨h6, f6, z6, r6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h6 (j := wSN) (by decide) (by decide)) fun t7 ⟨h7, f7, z7, r7⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h7 (j := wR) (by decide) (by decide)) fun t8 ⟨h8, f8, z8, r8⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h8 (j := wT2) (by decide) (by decide)) fun t9 ⟨h9, f9, z9, r9⟩ => ?_
  -- 6: the narrow view; the copies.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h9 (by omega_using [hw]) hfit) fun t10 ⟨⟨h10, m10⟩, r10⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h10 (o := 2 * wSD) (a := aM1) (by decide) (by decide) (by decide) (by decide))
    fun t11 ⟨h11, f11, v11, r11, o11⟩ => ?_
  refine WP.mono (copy_ok h11 (o := 2 * wSN) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨h12, f12, v12, r12, o12⟩ => ?_
  -- Wide arrays through the zeroing.
  have zw : ∀ {j k : Nat} {m m' : Mem}, j < 31 → (∀ i ∈ [j], i ≠ k) → k < 31 →
      Frame B (W2 w) [j] [] m m' → wordsVal m' B (arr (W2 w) k) (W2 w + 1) = wordsVal m B (arr (W2 w) k) (W2 w + 1) :=
    fun {j k m m'} hj hjk hk f => by
      have hS : S (W2 w) = 8 * (W2 w + 2) := rfl
      have fk := fW k hk
      refine f.words (fun i hi => ?_) (by simp) (by omega_using [hS, fk])
      have := arr_disj (w := W2 w) (hjk i hi)
      omega_using [hS, this]
  -- The narrow arrays the copies write, against wide ones (`2 j` and `2 j + 1` are wide `j`).
  have nw : ∀ {o k : Nat} {m m' : Mem}, o < 63 → o / 2 ≠ k → k < 31 →
      Frame B w [o] [] m m' → wordsVal m' B (arr (W2 w) k) (W2 w + 1) = wordsVal m B (arr (W2 w) k) (W2 w + 1) :=
    fun {o k m m'} ho hok hk f => by
      have hS : S w = 8 * (w + 2) := rfl
      have hS2 : S (W2 w) = 8 * (W2 w + 2) := rfl
      have fk := fW k hk
      refine f.words (fun i hi => ?_) (by simp) (by omega_using [hS2, fk])
      simp only [List.mem_singleton] at hi; subst hi
      rw [arr_W2]
      rcases Nat.lt_or_gt_of_ne (show i ≠ 2 * k by omega_using [hok]) with c | c
      · have := arr_end (w := w) c; right; omega_using [this]
      · have c' : 2 * k + 1 < i := by omega_using [hok, c]
        have := arr_end (w := w) c'; have := arr_succ w (2 * k); simp only [S, W2] at this ⊢; left; omega_arith
  have M10 : t10.mem = t9.mem := m10
  -- `wSD` and `wSN`'s upper halves zero.
  have hiSD : hiW t.mem B w wSD = 0 := by
    have f29 := fit (2 * wSD + 1) (by decide); simp only [S] at f29
    rw [hiW_frame f12 (by decide) (by simp) (fit _ (by decide)), hiW_out o11 (by omega_using [f29]), M10]
    refine hiW_of_zero ?_
    rw [zw (by decide) (by decide) (by decide) f9, zw (by decide) (by decide) (by decide) f8,
      zw (by decide) (by decide) (by decide) f7]
    exact z6
  have hiSN : hiW t.mem B w wSN = 0 := by
    have f29 := fit (2 * wSN + 1) (by decide); simp only [S] at f29
    rw [hiW_out o12 (by omega_using [f29]), hiW_frame f11 (by decide) (by simp) (fit _ (by decide)), M10]
    refine hiW_of_zero ?_
    rw [zw (by decide) (by decide) (by decide) f9, zw (by decide) (by decide) (by decide) f8]
    exact z7
  have R9 : wordsVal t9.mem B (arr (W2 w) wR) (W2 w + 1) = 0 := by
    rw [zw (by decide) (by decide) (by decide) f9]; exact z8
  have T9 := z9
  rw [← M10] at R9 T9
  have K : Keep dvRegs s t :=
    Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans' (r3.mono (by decide))
      (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide)) (Keep.trans' (r6.mono (by decide))
        (Keep.trans' (r7.mono (by decide)) (Keep.trans' (r8.mono (by decide)) (Keep.trans' (r9.mono (by decide))
          (Keep.trans' (r10.mono (by decide)) (Keep.trans' (r11.mono (by decide)) (r12.mono (by decide))))))))))))
  -- The narrow arrays the wide zeroing keeps.
  have nk : ∀ j, j < 63 → j / 2 ≠ wSD → j / 2 ≠ wSN → j / 2 ≠ wR → j / 2 ≠ wT2 →
      num t9.mem B w j = num t4.mem B w j := fun j hj h1 h2 h3 h4 => by
    have F : Frame B (W2 w) [wSD, wSN, wR, wT2] [] t5.mem t9.mem :=
      (((f6.mono (by simp) (by simp)).trans (f7.mono (by simp) (by simp))).trans (f8.mono (by simp) (by simp))).trans
        (f9.mono (by simp) (by simp))
    have FN := F.toNarrow
    rw [FN.num (fun k hk => by
        simp only [halves, List.flatMap_cons, List.flatMap_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hk
        omega_using [h1, h2, h3, h4, hk]) (by simp) (fit _ hj), m5]
  have e12 : ∀ j, j < 63 → j ≠ 2 * wSD → j ≠ 2 * wSN → num t.mem B w j = num t10.mem B w j := fun j hj a b => by
    rw [f12.num (by simpa using fun e => b e.symm) (by simp) (fit _ hj),
      f11.num (by simpa using fun e => a e.symm) (by simp) (fit _ hj)]
  refine ⟨h12, ?_, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m5] at f6
    rw [M10] at f11
    rw [m1] at f2
    exact ((((((((f2.mono (js' := [aNeg1, aM1, aD] ++ halves [wSD, wSN, wR, wT2]) (by simp) (by simp)).trans
      (f3.mono (by simp) (by simp))).trans (f4.mono (by simp) (by simp))).trans
      ((f6.toNarrow.mono (by decide) (by simp)))).trans (f7.toNarrow.mono (by decide) (by simp))).trans
      (f8.toNarrow.mono (by decide) (by simp))).trans (f9.toNarrow.mono (by decide) (by simp))).trans
      ((f11.mono (by decide) (by simp)).trans (f12.mono (by decide) (by simp))))
  · rw [e12 _ (by decide) (by decide) (by decide), M10, nk _ (by decide) (by decide) (by decide) (by decide)
      (by decide), f4.num (by decide) (by simp) (fit _ (by decide)), f3.num (by decide) (by simp) (fit _ (by decide)),
      neg2]
  · rw [numW_split, hiSD, Nat.mul_zero, Nat.add_zero, f12.num (by decide) (by simp) (fit _ (by decide)), v11, M10, nk _ (by decide) (by decide) (by decide)
      (by decide) (by decide), f4.num (by decide) (by simp) (fit _ (by decide)), m3]
  · rw [numW_split, hiSN, Nat.mul_zero, Nat.add_zero, v12, f11.num (by decide) (by simp) (fit _ (by decide)), M10,
      nk _ (by decide) (by decide) (by decide) (by decide) (by decide), d4]
  · rw [nw (by decide) (by decide) (by decide) f12, nw (by decide) (by decide) (by decide) f11]; exact R9
  · rw [nw (by decide) (by decide) (by decide) f12, nw (by decide) (by decide) (by decide) f11]; exact T9
  · rw [e12 _ (by decide) (by decide) (by decide), M10, nk _ (by decide) (by decide) (by decide) (by decide)
      (by decide), f4.num (by decide) (by simp) (fit _ (by decide)), f3.num (by decide) (by simp) (fit _ (by decide)),
      f2.num (by decide) (by simp) (fit _ (by decide)), m1, hZ0]

/-- `divB`, wide view to narrow: `-1`, and where `m < n`, `r < n` and `n < 2^(64 (w - 1))`, the
quotient of `n - r` by `m + 1` (`aD`) and whether it is exact, by words (`divB1_ok`, `divB2_ok`). -/
theorem divB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (W2 w) 31) (hfit : arr w 63 ≤ Z)
    (hW : W2 w ≤ 1024) (hw : 5 ≤ w) (hw' : w ≤ 129) (hZ0 : num s.mem B w aZero = 0)
    (hOne : num s.mem B w aOne = 1) :
    WP isa divB s fun t => Ws t B Z w 63 ∧
      Frame B w ([aNeg1, aM1, aD] ++ halves [wSD, wSN, wR, wT2, wDig, wTmp]) (sExact :: divSlots) s.mem t.mem ∧
      Keep dvRegs s t ∧ num t.mem B w aNeg1 = 2 ^ (64 * w) - 1 ∧ slot t.mem B sExact ≤ 1 ∧
      (num s.mem B (W2 w) wDt < num s.mem B w aN → num s.mem B (W2 w) wR < num s.mem B w aN →
        num s.mem B w aN < 2 ^ (64 * (w - 1)) →
        num t.mem B w aD = (num s.mem B w aN - num s.mem B (W2 w) wR) / (num s.mem B (W2 w) wDt + 1) ∧
        slot t.mem B sExact =
          if (num s.mem B w aN - num s.mem B (W2 w) wR) % (num s.mem B (W2 w) wDt + 1) = 0 then 1 else 0) := by
  have e : divB = seqs (([.block ctxw, Impl.Rsa.RISCV64.Keys.sub3 aNeg1 aZero aOne,
      Impl.Rsa.RISCV64.Keys.sub3 aM1 (2 * wDt) aNeg1, Impl.Rsa.RISCV64.Keys.sub3 aD aN (2 * wR),
      .block ctxW, zeroW wSD, zeroW wSN, zeroW wR, zeroW wT2, .block ctxw, copy (2 * wSD) aM1,
      copy (2 * wSN) aD] : List (Prog isa)) ++
    [.block (ctxW ++ saveDiv ++ halfH), clz wSD, shlWords wSD, shlWords wSN,
      .block (halfH ++ fixTopH wSD ++ halfH ++ [.add .t6 .t0 .t0]),
      WordDiv.divCore wSN wR wSD wTmp (some (wDig, wT2)), .block restDiv, .block ctxw, copy aD (2 * wT2),
      eqS sExact (2 * wR) aZero]) := rfl
  rw [e, wp_seqs_append (by simp) (by simp)]
  refine WP.mono (divB1_ok h hfit hW hw hZ0 hOne) fun t1 ⟨h1, f1, k1, neg1, sd1, sn1, r1, t21, z1⟩ => ?_
  refine WP.mono (divB2_ok h1 hW hw hw' sd1 sn1 r1 t21 z1) fun t ⟨h2, f2, k2, x2, v2⟩ => ?_
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h1.fit64 hj
  refine ⟨h2, (f1.mono (by decide) (by simp)).trans (f2.mono (by decide) (by simp)),
    Keep.trans' k1 k2, ?_, x2, fun hm hr hn => ?_⟩
  · rw [f2.num (by decide) (by decide) (fit _ (by decide)), neg1]
  · have pw : 2 ^ (64 * (w - 1)) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega_using [])
    have hm' : num s.mem B (W2 w) wDt % 2 ^ (64 * w) = num s.mem B (W2 w) wDt := Nat.mod_eq_of_lt (by omega_using [hm, hn, pw])
    have hr' : num s.mem B (W2 w) wR % 2 ^ (64 * w) = num s.mem B (W2 w) wR := Nat.mod_eq_of_lt (by omega_using [hr, hn, pw])
    rw [hm', Nat.mod_eq_of_lt (by omega_using [hm, hn, pw])] at v2
    rw [hr', wsub_of_le (by omega_using [hn, pw]) (by omega_using [hr])] at v2
    exact v2 (by omega_using []) (by omega_using [hm, hn]) (by omega_using [hn])


/-! ## `b² - 4 n` -/

/-- A doubling as the code leaves it. -/
theorem st2_dbl_of {x c y P : Nat} (hv : x + P * c = y) (hx : x < P) : x = y % P := by
  subst hv; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem minus4n_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hW : W2 w ≤ 1024)
    (hNeg : num s.mem B w aNeg1 = 2 ^ (64 * w) - 1) (hBz : hiW s.mem B w wB = 0)
    (hSq0 : num s.mem B (W2 w) wSq = 0) (hOne : num s.mem B (W2 w) wOne = 1) :
    WP isa minus4n s fun t => Ws t B Z (W2 w) 31 ∧
      Frame B w (aD :: halves [wB, wSq, wN, wR, wT2]) [sC1, sC2] s.mem t.mem ∧ Keep st2Regs s t ∧
      num t.mem B w aD = (num s.mem B w aD + 1) % 2 ^ (64 * w) ∧
      num t.mem B (W2 w) wSq = num t.mem B w aD * num t.mem B w aD % 2 ^ (64 * W2 w) ∧
      num t.mem B (W2 w) wN = fourN (64 * W2 w) (num s.mem B (W2 w) wN) ∧
      num t.mem B (W2 w) wR = wsub (64 * W2 w) (num t.mem B (W2 w) wSq) (num t.mem B (W2 w) wN) ∧
      slot t.mem B sC1 = (if num t.mem B (W2 w) wSq < num t.mem B (W2 w) wN then 1 else 0) ∧
      slot t.mem B sC2 = (if num t.mem B (W2 w) wR < 1 then 1 else 0) := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have P1 : 1 ≤ 2 ^ (64 * w) := Nat.one_le_two_pow
  unfold minus4n
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have aN1 : Ahead (arr w aD) (arr w aNeg1) w := by
    simpa using ahead_of_ne (w := w) (o := aD) (a := aNeg1) (by decide) 0 (by decide)
  refine WP.mono (sub3_gen_ok h (o := aD) (a := aD) (b := aNeg1) (by decide) (by decide) (by decide)
    (by decide) (ahead_self _ _ _) aN1) fun t1 ⟨h1, f1, v1, b1, r1⟩ => ?_
  rw [hNeg] at v1
  have d1 := st2_m1_of v1 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (o := 2 * wB) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, f2, v2, r2, o2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok (M := 31) h2 hW (by decide)) fun t3 ⟨⟨h3, m3⟩, r3⟩ => ?_
  have fW : ∀ j < 31, arr (W2 w) j + S (W2 w) ≤ 2 ^ 64 := fun j hj => h3.fit64 hj
  have f1W := f1.toWide
  have f2W := f2.toWide
  rw [← m3] at f2 f2W o2 v2
  have hz2 : hiW t3.mem B w wB = 0 := by
    have f37 : arr w (2 * wB + 1) + 8 * w ≤ 2 ^ 64 := by
      have := fit (2 * wB + 1) (by decide); simp only [S] at this; omega_arith
    rw [hiW_out o2 f37, hiW_frame f1 (by decide) (by simp) (fit _ (by decide)), hBz]
  have B3 : num t3.mem B (W2 w) wB = num t1.mem B w aD := by rw [numW_low (j := wB) hz2]; exact v2
  have D3 : num t3.mem B w aD = num t1.mem B w aD := by
    rw [f2.num (by decide) (by simp) (fit _ (by decide))]
  have Q3 : num t3.mem B (W2 w) wSq = 0 := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide)), hSq0]
  have N3 : num t3.mem B (W2 w) wN = num s.mem B (W2 w) wN := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide))]
  have O3 : num t3.mem B (W2 w) wOne = 1 := by
    rw [f2W.num (by decide) (by simp) (fW _ (by decide)), f1W.num (by decide) (by simp) (fW _ (by decide)), hOne]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hB3 : num t3.mem B (W2 w) wB < 2 ^ (64 * (W2 w / 2 - 1)) := by
    rw [B3, show W2 w / 2 - 1 = w by simp only [W2]; omega_using []]; exact wordsVal_lt _ _ _ _
  refine WP.mono (sqB_ok h3 (o := wSq) (x := wB) (by decide) (by decide) (by decide) (by decide)
    (by simp only [W2]; omega_using []) (by have := h.wpos; simp only [W2]; omega_using [this]) Q3 hB3) fun t4 ⟨h4, f4, _, v4, r4⟩ => ?_
  have hsq : num t1.mem B w aD * num t1.mem B w aD < 2 ^ (64 * W2 w) := by
    have := wordsVal_lt t1.mem B (arr w aD) w
    calc _ < 2 ^ (64 * w) * 2 ^ (64 * w) := Nat.mul_lt_mul'' this this
      _ ≤ 2 ^ (64 * W2 w) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by simp only [W2]; omega_using [])
  rw [B3, ← Nat.mod_eq_of_lt hsq] at v4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h4 (j := wN) (by decide) (by decide)) fun t5 ⟨h5, f5, _, v5, c5, r5⟩ => ?_
  rw [f4.num (by decide) (by simp) (fW _ (by decide)), N3] at v5
  have N5 := st2_dbl_of v5 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h5 (j := wN) (by decide) (by decide)) fun t6 ⟨h6, f6, _, v6, c6, r6⟩ => ?_
  rw [N5] at v6
  have N6 := st2_dbl_of v6 (wordsVal_lt _ _ _ _)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h6 (o := wR) (a := wSq) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t7 ⟨h7, f7, v7, b7, r7⟩ => ?_
  have S6 : num t6.mem B (W2 w) wSq = num t4.mem B (W2 w) wSq := by
    rw [f6.num (by decide) (by simp) (fW _ (by decide)), f5.num (by decide) (by simp) (fW _ (by decide))]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stBorrow_ok h7 (sl := sC1) (by decide) (by decide)) fun t8 ⟨h8, f8, s8, r8⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h8 (o := wT2) (a := wR) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t9 ⟨h9, f9, v9, b9, r9⟩ => ?_
  refine WP.mono (stBorrow_ok h9 (sl := sC2) (by decide) (by decide)) fun t ⟨h10, f10, s10, r10⟩ => ?_
  -- What the last steps keep.
  have eW : ∀ j < 31, j ≠ wT2 → num t.mem B (W2 w) j = num t8.mem B (W2 w) j := fun j hj hj' => by
    rw [f10.num (by simp) (by decide) (fW _ hj), f9.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj),
      f8.num (by simp) (by decide) (fW _ hj)]
  have e8 : ∀ j < 31, j ≠ wR → num t8.mem B (W2 w) j = num t6.mem B (W2 w) j := fun j hj hj' => by
    rw [f8.num (by simp) (by decide) (fW _ hj), f7.num (by simpa using fun e => hj' e.symm) (by simp) (fW _ hj)]
  have R8 : num t8.mem B (W2 w) wR = num t7.mem B (W2 w) wR := f8.num (by simp) (by decide) (fW _ (by decide))
  have One8 : num t8.mem B (W2 w) wOne = 1 := by
    rw [e8 _ (by decide) (by decide), f6.num (by decide) (by simp) (fW _ (by decide)),
      f5.num (by decide) (by simp) (fW _ (by decide)), f4.num (by decide) (by simp) (fW _ (by decide)), O3]
  have mo : ∀ {js ds : List Nat} {m m' : Mem}, Frame B (W2 w) js ds m m' →
      (∀ j ∈ halves js, j ∈ halves [wSq, wN, wR, wT2]) → (∀ d ∈ ds, d ∈ [sC1, sC2]) →
      Frame B w (halves [wSq, wN, wR, wT2]) [sC1, sC2] m m' := fun f hj hd => f.toNarrow.mono hj hd
  have fT : Frame B w (halves [wSq, wN, wR, wT2]) [sC1, sC2] t3.mem t.mem :=
    ((((((mo f4 (by decide) (by decide)).trans (mo f5 (by decide) (by decide))).trans
      (mo f6 (by decide) (by decide))).trans (mo f7 (by decide) (by decide))).trans
      (mo f8 (by decide) (by decide))).trans (mo f9 (by decide) (by decide))).trans
      (mo f10 (by decide) (by decide))
  have Dt : num t.mem B w aD = num t1.mem B w aD := by
    rw [fT.num (by decide) (by decide) (fit _ (by decide)), D3]
  have hSq : num t.mem B (W2 w) wSq = num t6.mem B (W2 w) wSq := by
    rw [eW _ (by decide) (by decide), e8 _ (by decide) (by decide)]
  have hN : num t.mem B (W2 w) wN = num t6.mem B (W2 w) wN := by
    rw [eW _ (by decide) (by decide), e8 _ (by decide) (by decide)]
  have hR : num t.mem B (W2 w) wR = num t7.mem B (W2 w) wR := by rw [eW _ (by decide) (by decide), R8]
  rw [R8, One8] at v9
  have W7 := wsub_of_sub v7 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b7
  have W9 := wsub_of_sub v9 (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by simp only [W2]; omega_using [])) b9
  refine ⟨h10, ?_, ?_, by rw [Dt, d1], by rw [hSq, Dt, S6, v4], by rw [hN, N6, fourN], ?_, ?_, ?_⟩
  · exact ((f1.mono (by decide) (by simp)).trans (f2.mono (by decide) (by simp))).trans
      (fT.mono (by decide) (by decide))
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans'
      (r3.mono (by decide)) (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide))
        (Keep.trans' (r6.mono (by decide)) (Keep.trans' (r7.mono (by decide)) (Keep.trans' (r8.mono (by decide))
          (Keep.trans' (r9.mono (by decide)) (r10.mono (by decide))))))))))
  · rw [hR, hSq, hN, W7.1]
  · have S1 : slot t.mem B sC1 = slot t8.mem B sC1 := by
      rw [f10.slot (by decide) (by decide), f9.slot (by decide) (by simp)]
    rw [S1, s8, hSq, hN]
    split
    · exact W7.2.mpr (by assumption)
    · have := W7.2; omega_arith
  · rw [s10, hR]
    split
    · exact W9.2.mpr (by assumption)
    · have := W9.2; omega_arith

/-! ## The factors and the mask -/

theorem st2_xor1_toNat {x : BitVec 64} (hx : x.toNat ≤ 1) : (x ^^^ 1#64).toNat = 1 - x.toNat := by
  rw [xor_bits hx (by decide)]
  change (x.toNat + 1) % 2 = _
  omega_using [hx]

theorem st2_and_le1 {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x &&& y).toNat = x.toNat * y.toNat ∧ (x &&& y).toNat ≤ 1 := by
  rw [and01 hx hy]
  refine ⟨rfl, ?_⟩
  rcases (by omega_using [hx] : x.toNat = 0 ∨ x.toNat = 1) with e | e <;> rw [e] <;> omega_arith

theorem maskOf_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (b0 : slot s.mem B sB0 ≤ 1) (b1 : slot s.mem B sB1 ≤ 1) (lt : slot s.mem B sLt ≤ 1)
    (ex : slot s.mem B sExact ≤ 1) (c1 : slot s.mem B sC1 ≤ 1) (c2 : slot s.mem B sC2 ≤ 1)
    (ok : slot s.mem B sOk5 ≤ 1) :
    WP isa (.block maskOf) s fun t => Ws t B Z w N ∧ Frame B w [] [sMask] s.mem t.mem ∧
      slot t.mem B sMask = (1 - slot s.mem B sB0) * (1 - slot s.mem B sB1) * slot s.mem B sLt *
        slot s.mem B sExact * (1 - slot s.mem B sC1) * (1 - slot s.mem B sC2) * slot s.mem B sOk5 ∧
      Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  have hk : WP isa (.block maskOf) s fun u =>
      (u.mem = s.mem.writeW (off B sMask) ((((((((word s.mem B sB0 ^^^ 1#64) &&& (word s.mem B sB1 ^^^ 1#64)) &&&
        word s.mem B sLt) &&& word s.mem B sExact) &&& (word s.mem B sC1 ^^^ 1#64)) &&&
        (word s.mem B sC2 ^^^ 1#64)) &&& word s.mem B sOk5))) ∧ Keep [.t5, .t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [maskOf, h.s11, h.scr.st (d := sMask) (n := 8) (by simp only [sMask]; omega_arith),
      h.scr.al8 (d := sMask) (by simp only [sMask]; omega_arith) (by decide),
      h.scr.ld (d := sB0) (n := 8) (by simp only [sB0]; omega_arith),
      h.scr.al8 (d := sB0) (by simp only [sB0]; omega_arith) (by decide),
      h.scr.ld (d := sB1) (n := 8) (by simp only [sB1]; omega_arith),
      h.scr.al8 (d := sB1) (by simp only [sB1]; omega_arith) (by decide),
      h.scr.ld (d := sLt) (n := 8) (by simp only [sLt]; omega_arith),
      h.scr.al8 (d := sLt) (by simp only [sLt]; omega_arith) (by decide),
      h.scr.ld (d := sExact) (n := 8) (by simp only [sExact]; omega_arith),
      h.scr.al8 (d := sExact) (by simp only [sExact]; omega_arith) (by decide),
      h.scr.ld (d := sC1) (n := 8) (by simp only [sC1]; omega_arith),
      h.scr.al8 (d := sC1) (by simp only [sC1]; omega_arith) (by decide),
      h.scr.ld (d := sC2) (n := 8) (by simp only [sC2]; omega_arith),
      h.scr.al8 (d := sC2) (by simp only [sC2]; omega_arith) (by decide),
      h.scr.ld (d := sOk5) (n := 8) (by simp only [sOk5]; omega_arith),
      h.scr.al8 (d := sOk5) (by simp only [sOk5]; omega_arith) (by decide),
      show sB0 < 2048 by decide, show sB1 < 2048 by decide, show sLt < 2048 by decide,
      show sExact < 2048 by decide, show sC1 < 2048 by decide, show sC2 < 2048 by decide,
      show sOk5 < 2048 by decide, show sMask < 2048 by decide, add_ofNat_zero']
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := sMask) ((((((((word s.mem B sB0 ^^^ 1#64) &&&
    (word s.mem B sB1 ^^^ 1#64)) &&& word s.mem B sLt) &&& word s.mem B sExact) &&& (word s.mem B sC1 ^^^ 1#64)) &&&
    (word s.mem B sC2 ^^^ 1#64)) &&& word s.mem B sOk5)) (by simp only [sMask]; omega_arith)
  rw [← mu] at sw
  refine ⟨h.of_keep ku, sw.1, ?_, ku.mono (by decide)⟩
  rw [sw.2]
  have x0 := st2_xor1_toNat (x := word s.mem B sB0) b0
  have x1 := st2_xor1_toNat (x := word s.mem B sB1) b1
  have x4 := st2_xor1_toNat (x := word s.mem B sC1) c1
  have x5 := st2_xor1_toNat (x := word s.mem B sC2) c2
  have a1 := st2_and_le1 (x := word s.mem B sB0 ^^^ 1#64) (y := word s.mem B sB1 ^^^ 1#64) (by rw [x0]; omega_using [])
    (by rw [x1]; omega_using [])
  have a2 := st2_and_le1 a1.2 lt
  have a3 := st2_and_le1 a2.2 ex
  have a4 := st2_and_le1 a3.2 (y := word s.mem B sC1 ^^^ 1#64) (by rw [x4]; omega_using [])
  have a5 := st2_and_le1 a4.2 (y := word s.mem B sC2 ^^^ 1#64) (by rw [x5]; omega_using [])
  have a6 := st2_and_le1 a5.2 ok
  rw [a6.1, a5.1, a4.1, a3.1, a2.1, a1.1, x0, x1, x4, x5]

theorem st2_li0_ok (s : State) :
    WP isa (.block [.li .t4 0]) s fun u => (u.gpr .t4 = 0 ∧ u.mem = s.mem) ∧ Keep [.t4] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [fin64_exec_li_zero]

theorem factors_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w 63) (hZ0 : num s.mem B w aZero = 0)
    (b0 : slot s.mem B sB0 ≤ 1) (b1 : slot s.mem B sB1 ≤ 1) (lt : slot s.mem B sLt ≤ 1)
    (ex : slot s.mem B sExact ≤ 1) (c1 : slot s.mem B sC1 ≤ 1) (c2 : slot s.mem B sC2 ≤ 1)
    (ok : slot s.mem B sOk5 ≤ 1) :
    WP isa factors s fun t => Ws t B Z w 63 ∧ Frame B w [aP, aQ, aNy] [sMask] s.mem t.mem ∧
      Keep st2Regs s t ∧
      num t.mem B w aP = (num s.mem B w aD + num s.mem B w aSy) % 2 ^ (64 * w) / 2 ∧
      num t.mem B w aQ = wsub (64 * w) (num s.mem B w aD) (num s.mem B w aSy) / 2 ∧
      slot t.mem B sMask = (1 - slot s.mem B sB0) * (1 - slot s.mem B sB1) * slot s.mem B sLt *
        slot s.mem B sExact * (1 - slot s.mem B sC1) * (1 - slot s.mem B sC2) * slot s.mem B sOk5 := by
  have fit : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  unfold factors
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (add_ok h (o := aP) (a := aD) (b := aSy) (z := aZero) (t := aNy) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hZ0) fun t1 ⟨h1, f1, v1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (st2_li0_ok t1) fun t2 ⟨⟨u2, m2⟩, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok (h1.of_keep r2) (j := aP) (by decide) (by decide) (by rw [u2]; decide))
    fun t3 ⟨h3, f3, v3, _, r3⟩ => ?_
  rw [m2, u2, v1] at v3
  rw [m2] at f3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (o := aQ) (a := aD) (b := aSy) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t4 ⟨h4, f4, v4, b4, r4⟩ => ?_
  have e3 : ∀ j < 63, j ≠ aP → j ≠ aNy → num t3.mem B w j = num s.mem B w j := fun j hj h1' h2' => by
    rw [f3.num (by simpa using fun e => h1' e.symm) (by simp) (fit _ hj),
      f1.num (by simp; exact ⟨fun e => h2' e.symm, fun e => h1' e.symm⟩) (by simp) (fit _ hj)]
  rw [e3 _ (by decide) (by decide) (by decide), e3 _ (by decide) (by decide) (by decide)] at v4
  have Q4 := (wsub_of_sub v4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) b4).1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (st2_li0_ok t4) fun t5 ⟨⟨u5, m5⟩, r5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok (h4.of_keep r5) (j := aQ) (by decide) (by decide) (by rw [u5]; decide))
    fun t6 ⟨h6, f6, v6, _, r6⟩ => ?_
  rw [m5, u5, Q4] at v6
  rw [m5] at f6
  have fA : Frame B w [aP, aQ, aNy] [] s.mem t6.mem :=
    ((f1.mono (by decide) (by simp)).trans (f3.mono (by decide) (by simp))).trans
      ((f4.mono (by decide) (by simp)).trans (f6.mono (by decide) (by simp)))
  have sl : ∀ d, d + 8 ≤ hdr → slot t6.mem B d = slot s.mem B d := fun d hd => fA.slot hd (by simp)
  refine WP.mono (maskOf_ok h6 (by rw [sl _ (by decide)]; exact b0) (by rw [sl _ (by decide)]; exact b1)
    (by rw [sl _ (by decide)]; exact lt) (by rw [sl _ (by decide)]; exact ex) (by rw [sl _ (by decide)]; exact c1)
    (by rw [sl _ (by decide)]; exact c2) (by rw [sl _ (by decide)]; exact ok)) fun t ⟨h7, f7, s7, r7⟩ => ?_
  refine ⟨h7, (fA.mono (js' := [aP, aQ, aNy]) (ds' := [sMask]) (by decide) (by simp)).trans
    (f7.mono (by simp) (by decide)), ?_, ?_, ?_, ?_⟩
  · exact Keep.trans' (r1.mono (by decide)) (Keep.trans' (r2.mono (by decide)) (Keep.trans' (r3.mono (by decide))
      (Keep.trans' (r4.mono (by decide)) (Keep.trans' (r5.mono (by decide)) (Keep.trans' (r6.mono (by decide))
        (r7.mono (by decide)))))))
  · rw [f7.num (by simp) (by decide) (fit _ (by decide)), f6.num (by decide) (by simp) (fit _ (by decide)),
      f4.num (by decide) (by simp) (fit _ (by decide)), v3]
    simp
  · rw [f7.num (by simp) (by decide) (fit _ (by decide)), v6]
    simp
  · rw [s7, sl _ (by decide), sl _ (by decide), sl _ (by decide), sl _ (by decide), sl _ (by decide),
      sl _ (by decide), sl _ (by decide)]

end VG.Proof.Rsa.RISCV64.Keys
