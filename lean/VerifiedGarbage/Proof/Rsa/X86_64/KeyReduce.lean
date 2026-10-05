import VerifiedGarbage.Proof.Rsa.X86_64.KeyDbl
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# `vg_rsa_check_key` on x86-64: reduction by restoring division

The loop of `reduce`: for each word of `x` from the top (`wordStep`), each
of its bits from the top (`bitStep`) is shifted out of `r15` as the carry
of `dblIn`: `r := 2 r + b mod m`. After the top `i` words, `r` is their
number modulo `m` (`reduceLoop_ok`), when `m > 0`.
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Bits -/

theorem shl_add_self (V : BitVec 64) (b : Nat) : (V <<< b) + (V <<< b) = V <<< (b + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_succ]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, ← Nat.two_mul, Nat.mul_comm 2, Nat.mul_assoc]

/-- The carry of doubling `V <<< b` is bit `63 - b` of `V`. -/
theorem cf_shl (V : BitVec 64) {b : Nat} (hb : b < 64) :
    decide (2 ^ 64 ≤ (V <<< b).toNat + (V <<< b).toNat) = decide (V.toNat / 2 ^ (63 - b) % 2 = 1) := by
  have h1 : decide (2 ^ 64 ≤ (V <<< b).toNat + (V <<< b).toNat) = (V <<< b).msb := by
    rw [BitVec.msb_eq_decide]; simp only [Nat.add_one_sub_one]; congr 1; apply propext; omega
  rw [h1, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD]
  have e1 : 64 - 1 - b = 63 - b := by omega
  rw [e1, show decide (64 - 1 < 64) = true by decide, show decide (64 - 1 < b) = false by simp; omega,
    Nat.testBit_eq_decide_div_mod_eq]
  rfl

theorem bit_split (V k : Nat) : V / 2 ^ k = 2 * (V / 2 ^ (k + 1)) + V / 2 ^ k % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem ofNat_sub_one {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1' : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub, h1']
  simp only [BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e; have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; exact this
  · intro e; subst e; rfl

theorem dbl_mod (X c M : Nat) : (2 * (X % M) + c) % M = (2 * X + c) % M := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem toNat_decide {n : Nat} (p : Prop) [Decidable p] (h : p ↔ (n : Nat) % 2 = 1) :
    (decide p).toNat = n % 2 := by
  by_cases hp : p
  · simp only [hp, decide_true, Bool.toNat_true]; exact (h.mp hp).symm
  · have := mt h.mpr hp
    simp only [hp, decide_false, Bool.toNat_false]; omega

/-! ## One bit -/

/-- The working arrays `reduce` writes: `dblIn`'s accumulator and
temporary, and `r`. -/
def redRs (eA eT eo w : Nat) : List (Nat × Nat) := [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)]

/-- Where `reduce`'s loop works: `r` at `eo`, `m` at `em`, the accumulator
and temporary at `eA` and `eT`, and `x` at `eS`, `cnt` words. -/
structure RedLay (B : Addr) (Z w eo em eA eT eS cnt : Nat) : Prop where
  w1 : 1 ≤ w
  w2 : w < 2 ^ 31
  cnt1 : 1 ≤ cnt
  cnt2 : cnt < 2 ^ 31
  ho : eo + 8 * w ≤ Z
  hm : em + 8 * w ≤ Z
  hA : eA + 8 * (w + 1) ≤ Z
  hT : eT + 8 * w ≤ Z
  hS : eS + 8 * cnt ≤ Z
  sAo : eo + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eo
  sAm : em + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ em
  sAT : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT
  sTm : eT + 8 * w ≤ em ∨ em + 8 * w ≤ eT
  sTo : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo
  som : eo + 8 * w ≤ em ∨ em + 8 * w ≤ eo
  sSA : eS + 8 * cnt ≤ eA ∨ eA + 8 * (w + 1) ≤ eS
  sST : eS + 8 * cnt ≤ eT ∨ eT + 8 * w ≤ eS
  sSo : eS + 8 * cnt ≤ eo ∨ eo + 8 * w ≤ eS

/-- The registers `reduce`'s loop keeps. -/
structure RedRegs (B : Addr) (w eo em eA eT eS : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = off B eo
  r10 : t.gpr .r10 = off B em
  r8 : t.gpr .r8 = off B eA
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  si : t.gpr .rsi = off B eT
  r9 : t.gpr .r9 = off B eS

theorem RedRegs.keep {B : Addr} {w eo em eA eT eS : Nat} {t t' : State} (h : RedRegs B w eo em eA eT eS t)
    {rs : List Reg} (k : Keep rs t t') (hr : ∀ r ∈ [Reg.rbx, .r10, .r8, .r12, .rsi, .r9], r ∉ rs) :
    RedRegs B w eo em eA eT eS t' :=
  ⟨(k.gpr (hr _ (by simp))).trans h.bx, (k.gpr (hr _ (by simp))).trans h.r10, (k.gpr (hr _ (by simp))).trans h.r8,
    (k.gpr (hr _ (by simp))).trans h.r12, (k.gpr (hr _ (by simp))).trans h.si, (k.gpr (hr _ (by simp))).trans h.r9⟩

/-- After `b` bits of the word `V`, from `r = P mod M` (`M` the number at
`em`, unchanged). -/
structure BitInv (s₁ : State) (B : Addr) (Z w eo em eA eT eS : Nat) (P : Nat) (V : BitVec 64) (b : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  regs : RedRegs B w eo em eA eT eS t
  keep : Keep [.rax, .rbp, .r14, .rdx, .r11, .r15] s₁ t
  r15 : t.gpr .r15 = V <<< b
  r11 : t.gpr .r11 = BitVec.ofNat 64 (64 - b)
  frm : Frm B (redRs eA eT eo w) s₁.mem t.mem
  val : 0 < wv s₁.mem B em w →
    wv t.mem B eo w = (P * 2 ^ b + V.toNat / 2 ^ (64 - b)) % wv s₁.mem B em w

theorem bitStep_ok {s₁ : State} {B : Addr} {Z w eo em eA eT eS cnt : Nat} {P : Nat} {V : BitVec 64}
    (hL : RedLay B Z w eo em eA eT eS cnt) {b : Nat} (hb : b < 64) {t : State}
    (hI : BitInv s₁ B Z w eo em eA eT eS P V b t) :
    WP isa bitStep t fun t' => t'.zf = some (decide (b + 1 = 64)) ∧
      BitInv s₁ B Z w eo em eA eT eS P V (b + 1) t' := by
  have hn := hI.scr.nowrap
  obtain ⟨w1, w2, -, -, ho, hm, hA, hT, -, sAo, sAm, sAT, sTm, sTo, som, -, -, -⟩ := hL
  have hM : wv t.mem B em w = wv s₁.mem B em w :=
    hI.frm.wv_eq (fun r hr => by
      simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)
  unfold bitStep
  refine WP.seq (WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t₁ =>
      t₁.gpr .r15 = V <<< (b + 1) ∧ t₁.gpr .rbp = mask (decide (V.toNat / 2 ^ (63 - b) % 2 = 1)) ∧
      t₁.mem = t.mem) (by
    xrun [hI.r15, shl_add_self]
    rw [cf_shl V hb]; rfl) rfl) fun t₁ ⟨⟨h15, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hI.scr.congr k₁.2.2
  have rg₁ := hI.regs.keep k₁ (by decide)
  refine WP.seq (WP.mono (dblIn_ok hs₁ rg₁.bx rg₁.r10 rg₁.r8 rg₁.r12 rg₁.si hbp w1 w2 ho hm hA hT sAo sAm sAT
    sTm sTo) fun t₂ ⟨hv₂, hf₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have rg₂ := rg₁.keep k₂ (by decide)
  have h11 : t₂.gpr .r11 = BitVec.ofNat 64 (64 - b) := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.r11)
  refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.zf = some (decide (b + 1 = 64)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (64 - (b + 1)) ∧ t'.mem = t₂.mem) (by
    xrun [h11, ofNat_sub_one (n := 64 - b) (by omega) (by omega), ofNat_beq_zero (show 64 - b - 1 < 2 ^ 64 by omega)]
    exact ⟨by congr 1; apply propext; omega, by congr 1⟩) rfl)
    fun t' ⟨⟨hz, h11', hm'⟩, k'⟩ => ⟨hz, ?_⟩
  have k12 := (k₁.trans k₂).trans k'
  refine ⟨hs₂.congr k'.2.2, rg₂.keep k' (by decide), (hI.keep.trans k12).mono (by decide),
    (k'.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h15), h11', ?_, fun hM0 => ?_⟩
  · rw [hm']
    exact hI.frm.trans (by rw [← hm₁]; exact hf₂)
  · rw [hm']
    have hR : wv t₁.mem B eo w = (P * 2 ^ b + V.toNat / 2 ^ (64 - b)) % wv s₁.mem B em w := by
      rw [hm₁]; exact hI.val hM0
    have hM₁ : wv t₁.mem B em w = wv s₁.mem B em w := by rw [hm₁]; exact hM
    rw [hM₁] at hv₂
    rw [hv₂ (by rw [hR]; exact Nat.mod_lt _ hM0), hR, dbl_mod]
    congr 1
    have hc := toNat_decide (V.toNat / 2 ^ (63 - b) % 2 = 1) (n := V.toNat / 2 ^ (63 - b)) Iff.rfl
    have hs := bit_split V.toNat (63 - b)
    rw [show 63 - b + 1 = 64 - b by omega] at hs
    rw [hc, show 64 - (b + 1) = 63 - b by omega, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-! ## One word, and the loop -/

/-- After the top `i` words of `x` (`cnt` words at `eS`): `r` their number
modulo `M`. -/
structure WInv (s₀ : State) (B : Addr) (Z w eo em eA eT eS cnt : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  regs : RedRegs B w eo em eA eT eS t
  keep : Keep [.rax, .rbp, .r14, .rdx, .r11, .r15, .r13] s₀ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 (cnt - i)
  frm : Frm B (redRs eA eT eo w) s₀.mem t.mem
  val : 0 < wv s₀.mem B em w →
    wv t.mem B eo w = wv s₀.mem B (eS + 8 * (cnt - i)) i % wv s₀.mem B em w

theorem frm_word {B : Addr} {Z w eo eA eT d : Nat} {m m' : Mem} (h : Frm B (redRs eA eT eo w) m m')
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 ≤ Z) (sA : d + 8 ≤ eA ∨ eA + 8 * (w + 1) ≤ d)
    (sT : d + 8 ≤ eT ∨ eT + 8 * w ≤ d) (so : d + 8 ≤ eo ∨ eo + 8 * w ≤ d) : word m' B d = word m B d :=
  h.word_eq (fun r hr => by
    simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)

theorem frm_wv {B : Addr} {Z w eo eA eT d k : Nat} {m m' : Mem} (h : Frm B (redRs eA eT eo w) m m')
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 * k ≤ Z) (sA : d + 8 * k ≤ eA ∨ eA + 8 * (w + 1) ≤ d)
    (sT : d + 8 * k ≤ eT ∨ eT + 8 * w ≤ d) (so : d + 8 * k ≤ eo ∨ eo + 8 * w ≤ d) : wv m' B d k = wv m B d k :=
  h.wv_eq (fun r hr => by
    simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)

theorem wordStep_ok {s₀ : State} {B : Addr} {Z w eo em eA eT eS cnt : Nat}
    (hL : RedLay B Z w eo em eA eT eS cnt) {i : Nat} (hi : i < cnt) {t : State}
    (hI : WInv s₀ B Z w eo em eA eT eS cnt i t) :
    WP isa wordStep t fun t' => t'.zf = some (decide (i + 1 = cnt)) ∧
      WInv s₀ B Z w eo em eA eT eS cnt (i + 1) t' := by
  have hn := hI.scr.nowrap
  have hL' := hL
  obtain ⟨w1, w2, c1, c2, ho, hm, hA, hT, hS, sAo, sAm, sAT, sTm, sTo, som, sSA, sST, sSo⟩ := hL'
  have hM : wv t.mem B em w = wv s₀.mem B em w := frm_wv hI.frm hn hm sAm (by omega) (by omega)
  have hV : word t.mem B (eS + 8 * (cnt - i - 1)) = word s₀.mem B (eS + 8 * (cnt - i - 1)) :=
    frm_word hI.frm hn (by omega) (by omega) (by omega) (by omega)
  unfold wordStep
  refine WP.seq (WP.mono (WP.keep [.r13, .r15, .r11] (Q := fun t₁ =>
      t₁.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1) ∧
      t₁.gpr .r15 = word s₀.mem B (eS + 8 * (cnt - i - 1)) ∧ t₁.gpr .r11 = BitVec.ofNat 64 64 ∧
      t₁.mem = t.mem) (by
    xrun [hI.r13, ofNat_sub_one (n := cnt - i) (by omega) (by omega), State.ea, ix,
      addr0 hI.regs.r9 rfl, hI.scr.ld (show eS + 8 * (cnt - i - 1) + 8 ≤ Z by omega), hV]) rfl) fun t₁ ⟨⟨h13, h15, h11, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hI.scr.congr k₁.2.2
  have rg₁ := hI.regs.keep k₁ (by decide)
  have hb0 : BitInv t₁ B Z w eo em eA eT eS (wv s₀.mem B (eS + 8 * (cnt - i)) i)
      (word s₀.mem B (eS + 8 * (cnt - i - 1))) 0 t₁ :=
    ⟨hs₁, rg₁, Keep.refl _ _, by rw [h15, BitVec.shiftLeft_zero], h11, Frm.refl _ _ _, fun hM0 => by
      rw [hm₁] at hM0 ⊢
      rw [hM] at hM0 ⊢
      rw [hI.val hM0, Nat.pow_zero, Nat.mul_one, Nat.sub_zero,
        Nat.div_eq_of_lt (word s₀.mem B (eS + 8 * (cnt - i - 1))).isLt, Nat.add_zero]⟩
  refine WP.seq (wp_upto (a := 0) (N := 64) (by decide)
    (BitInv t₁ B Z w eo em eA eT eS (wv s₀.mem B (eS + 8 * (cnt - i)) i) (word s₀.mem B (eS + 8 * (cnt - i - 1))))
    (fun b _ hb t hb' => bitStep_ok hL hb hb') (fun t₂ hB => ?_) hb0)
  have h13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1) := (hB.keep.gpr (by decide)).trans h13
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.zf = some (decide (i + 1 = cnt)) ∧ t'.mem = t₂.mem ∧
      t'.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1)) (by
    xrun [h13₂, BitVec.and_self, ofNat_beq_zero (show cnt - i - 1 < 2 ^ 64 by omega)]
    congr 1; apply propext; omega) rfl) fun t' ⟨⟨hz, hm', h13'⟩, k'⟩ => ⟨hz, ?_⟩
  have k2 := hB.keep.trans k'
  refine ⟨hB.scr.congr k'.2.2, hB.regs.keep k' (by decide), ((hI.keep.trans k₁).trans k2).mono (by decide),
    by rw [h13', show cnt - (i + 1) = cnt - i - 1 by omega], ?_, fun hM0 => ?_⟩
  · rw [hm']
    exact hI.frm.trans (by rw [← hm₁]; exact hB.frm)
  · have hM₁ : wv t₁.mem B em w = wv s₀.mem B em w := by rw [hm₁, hM]
    rw [hm', hB.val (by rw [hM₁]; exact hM0), hM₁, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      show cnt - (i + 1) = cnt - i - 1 by omega, show i + 1 = 1 + i by omega, wv_add,
      show eS + 8 * (cnt - i - 1) + 8 * 1 = eS + 8 * (cnt - i) by omega]
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero,
      show 64 * 1 = 64 from rfl]
    rw [Nat.mul_comm (2 ^ 64), Nat.add_comm]

theorem reduceLoop_ok {s₀ : State} {B : Addr} {Z w eo em eA eT eS cnt : Nat}
    (hL : RedLay B Z w eo em eA eT eS cnt) (hs : Scr s₀ B Z) (hr : RedRegs B w eo em eA eT eS s₀)
    (h13 : s₀.gpr .r13 = BitVec.ofNat 64 cnt) (hR : wv s₀.mem B eo w = 0) :
    WP isa (.loop wordStep .ne) s₀ fun t => Scr t B Z ∧
      Keep [.rax, .rbp, .r14, .rdx, .r11, .r15, .r13] s₀ t ∧ Frm B (redRs eA eT eo w) s₀.mem t.mem ∧
      (0 < wv s₀.mem B em w → wv t.mem B eo w = wv s₀.mem B eS cnt % wv s₀.mem B em w) := by
  refine wp_upto (a := 0) (N := cnt) (by have := hL.cnt1; omega) (WInv s₀ B Z w eo em eA eT eS cnt)
    (fun i _ hi t hI => wordStep_ok hL hi hI) (fun t hI => ⟨hI.scr, hI.keep, hI.frm, fun hM0 => ?_⟩)
    ⟨hs, hr, Keep.refl _ _, by rw [h13, Nat.sub_zero], Frm.refl _ _ _, fun _ => by rw [hR]; simp [wv]⟩
  rw [hI.val hM0, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- `reduce cnt`: `[aR] := x mod [aM]` for the number `x` of the `N` words
of the accumulator, `N` the count the instructions `cnt` compute from `w`,
when `[aM] > 0`. -/
theorem reduce_ok {cnt : List Instr} {N : Nat} {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hcnt : ∀ t, t.gpr .r13 = BitVec.ofNat 64 w →
      WP isa (.block cnt) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 N ∧ t'.mem = t.mem ∧ Keep [.r13] t t')
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 28) (hN : 1 ≤ N) (hN' : N ≤ 2 * w + 4) :
    WP isa (seqs (reduce cnt)) s fun t => Good t B Z w minv ∧
      (0 < wv s.mem B (slot w aM) w →
        wv t.mem B (slot w aR) w = wv s.mem B (slot w Public.aAcc) N % wv s.mem B (slot w aM) w) ∧
      Arrays B w [aR, Public.aX, aT] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := by unfold slot hdrBytes; omega
  have sl : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun j => by unfold slot hdrBytes; rfl
  show WP isa (.seq (Impl.Rsa.X86_64.Crt.zeroArr aR) (.seq (.block _) (.loop wordStep .ne))) s _
  refine WP.seq (WP.mono (zeroArr_ok hg hZ hw (by omega) (show aR < 8 by decide))
    fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have a₁ : Arrays B w [aR, Public.aX, aT] s.mem s₁.mem :=
    Arrays.of_outside (j := aR) (by simp) ho₁ (Nat.le_refl _) (by omega)
  have hs₁ := hg.scr.congr k₁.2.2
  have hH₁ := a₁.hdr hg.hdr
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₁.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13] (Q := fun t =>
      RedRegs B w (slot w aR) (slot w aM) (slot w Public.aX) (slot w aT) (slot w Public.aAcc) t ∧
      t.gpr .r13 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem)
    (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ (sArr aR) (by unfold sArr aR; omega),
      hl₁ (sArr aM) (by unfold sArr aM; omega), hl₁ (sArr Public.aX) (by unfold sArr Public.aX; omega),
      hl₁ sW (by decide), hl₁ (sArr aT) (by unfold sArr aT; omega),
      hl₁ (sArr Public.aAcc) (by unfold sArr Public.aAcc; omega), hH₁.harr aR (by decide),
      hH₁.harr aM (by decide), hH₁.harr Public.aX (by decide), hH₁.harr aT (by decide),
        hH₁.harr Public.aAcc (by decide), hH₁.hw]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl) fun s₂ ⟨⟨rg₂, h13₂, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (hcnt s₂ h13₂) fun s₃ ⟨h13₃, hm₃, k₃⟩ => ?_
  have rg₃ := rg₂.keep k₃ (by decide)
  have hs₃ := hs₁.congr (k₂.trans k₃).2.2
  have hL : RedLay B Z w (slot w aR) (slot w aM) (slot w Public.aX) (slot w aT) (slot w Public.aAcc) N := by
    refine ⟨hw, by omega, hN, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [sl, aR, aM, aT, Public.aX, Public.aAcc] <;> omega
  have hR₃ : wv s₃.mem B (slot w aR) w = 0 := by
    rw [hm₃, hm₂]
    have := wv_add s₁.mem B (slot w aR) w 2
    omega
  refine WP.mono (reduceLoop_ok hL hs₃ rg₃ h13₃ hR₃) fun t ⟨hst, kt, ft, hv⟩ => ?_
  have k := ((k₁.trans k₂).trans k₃).trans kt
  have at₃ : Arrays B w [aR, Public.aX, aT] s₃.mem t.mem := fun x hx => ft x fun r hr => by
    simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h1 := hx Public.aX (by simp); have h2 := hx aT (by simp); have h3 := hx aR (by simp)
    simp only [sl, aR, aT, Public.aX] at h1 h2 h3
    rcases hr with rfl | rfl | rfl <;> simp only [sl, aR, aT, Public.aX] <;> omega
  have a₃ : Arrays B w [aR, Public.aX, aT] s.mem s₃.mem := by rw [hm₃, hm₂]; exact a₁
  have hM : wv s₃.mem B (slot w aM) w = wv s.mem B (slot w aM) w := by
    rw [hm₃, hm₂]; exact a₁.wv_eq (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp only [sl, aR, aT, Public.aX, aM] <;> omega)
      (by rw [sl]; unfold aM; omega)
  have hS : wv s₃.mem B (slot w Public.aAcc) N = wv s.mem B (slot w Public.aAcc) N := by
    rw [hm₃, hm₂]; exact a₁.wv_eq (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp only [sl, aR, aT, Public.aX, Public.aAcc] <;> omega)
      (by rw [sl]; unfold Public.aAcc; omega)
  refine ⟨⟨hst, (k.gpr (by decide)).trans hg.rdi, at₃.hdr (a₃.hdr hg.hdr)⟩, fun hM0 => ?_, a₃.trans at₃,
    k.mono (by decide)⟩
  rw [← hM] at hM0 ⊢
  rw [hv hM0, hS]

end VG.Proof.Rsa.X86_64.Key
