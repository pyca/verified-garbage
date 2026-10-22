module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.Recip
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv

/-!
# `R² mod m` by word steps with ADX: the reciprocal

`R2Adx.recipN` (`Impl/Bignum/X86_64/R2Adx.lean`): `recipGuess` leaves some
guess of `v = ⌊(2^128 - 1) / d⌋ - 2^64` in `rcx`, of which nothing is
proven but that it is a word (`recipGuess_ok`); `recipDown` then lowers it while
`(2^64 + v) d ≥ 2^128` (`down_ok`, `downLoop_ok`), and `recipUp` raises it
while `(2^64 + v + 1) d < 2^128` (`up_ok`, `upLoop_ok`), which leaves the
largest `v` with `(2^64 + v) d < 2^128`: `v` itself (`recipN_ok`, with
`R2Words.recip`'s statement, `R2w.recip_ok`), by `Recip.recip_exact`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.Recip

/-! ## The guess -/

/-- What a Newton step leaves in `rcx`, from `v` in `rcx` and `d` in `rsi`. -/
def stepV (v d : BitVec 64) : BitVec 64 :=
  let e := (BitVec.ofNat 64 (v.toNat * d.toNat / 2 ^ 64) + d) ^^^ BitVec.allOnes 64
  v + (e + BitVec.ofNat 64 (e.toNat * v.toNat / 2 ^ 64))

/-- `n` Newton steps from `v`. -/
def stepsV (d : BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0, v => v
  | n + 1, v => stepsV d n (stepV v d)

/-- What `recipGuess` leaves in `rcx`, for `d = m[w - 1]`. -/
def guessV (d : BitVec 64) : BitVec 64 := stepsV d 6 (d ^^^ BitVec.allOnes 64)

/-- A Newton step writes only `rdx`, `r14`, `rax`, `r11` and `rcx`. -/
theorem recipStep_ok (s : State) :
    WP isa (.block recipStep) s fun t => t.gpr .rcx = stepV (s.gpr .rcx) (s.gpr .rsi) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi ∧ Keep [.rdx, .r14, .rax, .r11, .rcx] s t := by
  exact WP.mono (WP.keep [.rdx, .r14, .rax, .r11, .rcx] (c := .block recipStep)
    (Q := fun t => t.gpr .rcx = stepV (s.gpr .rcx) (s.gpr .rsi) ∧ t.mem = s.mem ∧ t.gpr .rsi = s.gpr .rsi)
    (by unfold recipStep; xrun [execMulx, R2w.sxm1]; rfl) rfl)
    fun t ⟨⟨hcx, hm, hsi⟩, k⟩ => ⟨hcx, hm, hsi, k⟩

/-- `n` Newton steps. -/
theorem recipSteps_ok (n : Nat) (s : State) :
    WP isa (.block (List.replicate n recipStep).flatten) s fun t =>
      t.gpr .rcx = stepsV (s.gpr .rsi) n (s.gpr .rcx) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi ∧ Keep [.rdx, .r14, .rax, .r11, .rcx] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    exact WP.mono (recipStep_ok s) fun t ⟨hcx, hm, hsi, k⟩ => WP.mono (ih t) fun t' ⟨hcx', hm', hsi', k'⟩ =>
      ⟨by rw [hcx', hsi, hcx]; rfl, hm'.trans hm, hsi'.trans hsi,
        (k.trans k').mono (by decide)⟩

/-- `recipGuess`: `d = m[w - 1]` into `rsi`, for `m` at `r10` of `w` words, and
`guessV d` into `rcx`. -/
theorem recipGuess_ok {t : State} {B : Addr} {Z w em : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hM : em + 8 * w ≤ Z) :
    WP isa (.block recipGuess) t fun t' => t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧
      t'.gpr .rcx = guessV (word t.mem B (em + 8 * (w - 1))) ∧ t'.mem = t.mem ∧
      Keep [.rsi, .rcx, .rdx, .r14, .rax, .r11] t t' := by
  rw [show recipGuess = ([.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rcx (.reg .rsi), .alu .xor .rcx (.imm (-1))] :
      List Instr) ++ (List.replicate 6 recipStep).flatten from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' => t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧
      t'.gpr .rcx = word t.mem B (em + 8 * (w - 1)) ^^^ BitVec.allOnes 64 ∧ t'.mem = t.mem) (by
    xrun [State.ea, ix, addrm8 h10 h12 hw, hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hM]),
      R2w.sxm1]) rfl) fun t₁ ⟨⟨hsi₁, hcx₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (recipSteps_ok 6 t₁) fun t' ⟨hcx', hm', hsi', k'⟩ =>
    ⟨hsi'.trans hsi₁, by rw [hcx', hsi₁, hcx₁]; rfl, hm'.trans hm₁, (k₁.trans k').mono (by decide)⟩

/-! ## The corrections -/

theorem toNat_ofNat64 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem hi_lt {v D : Nat} (hv : v < 2 ^ 64) (hD : D < 2 ^ 64) : v * D / 2 ^ 64 < 2 ^ 64 := by
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  exact Nat.mul_lt_mul'' hv hD

theorem down_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block recipDown) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v - (over v D).toNat) ∧
      t'.zf = some (!over v D) ∧ t'.mem = t.mem ∧ Keep [.rdx, .r14, .rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rdx, .r14, .rax, .rcx] (c := .block recipDown) (Q := fun t' =>
    t'.gpr .rcx = BitVec.ofNat 64 (v - (over v D).toNat) ∧ t'.zf = some (!over v D) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  unfold recipDown
  xrun [execMulx, hcx, hsi]
  rw [toNat_ofNat64 hv, toNat_ofNat64 hD, toNat_ofNat64 (hi_lt hv hD)]
  unfold over
  by_cases hc : 2 ^ 64 ≤ v * D / 2 ^ 64 + D
  · have hv1 : 1 ≤ v := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [h0, Nat.zero_mul, Nat.zero_div] at hc
      omega_using [hc, hD]
    simp only [decide_eq_true hc, Bool.toNat_true, Bool.not_true]
    rw [BitVec.and_self, show BitVec.setWidth 64 (BitVec.ofBool true) = BitVec.ofNat 64 1 from rfl,
      BitVec.zero_sub, ← BitVec.sub_eq_add_neg, R2w.ofNat_sub_ofNat64 hv1]
    exact ⟨rfl, beq_eq_false_iff_ne.mpr fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_neg, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_using [this]⟩
  · simp only [decide_eq_false hc, Bool.toNat_false, Bool.not_false, Nat.sub_zero]
    rw [show BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 from rfl, BitVec.sub_zero, BitVec.add_zero,
      BitVec.and_self]
    exact ⟨rfl, rfl⟩

theorem upA_ok {t : State} {v : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa (.block [.mov .rdx (.reg .rcx), .alu .add .rdx (.imm 1), .alu .sbb .r11 (.reg .r11)]) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (v + 1) ∧ t'.gpr .r11 = mask (decide (v + 1 = 2 ^ 64)) ∧
      t'.mem = t.mem ∧ Keep [.rdx, .r11] t t' := by
  refine WP.mono (WP.keep [.rdx, .r11] (Q := fun t' => t'.gpr .rdx = BitVec.ofNat 64 (v + 1) ∧
    t'.gpr .r11 = mask (decide (v + 1 = 2 ^ 64)) ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  xrun [hcx]
  refine ⟨by rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat], ?_⟩
  rw [toNat_ofNat64 hv, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    decide_eq_decide.mpr (show 2 ^ 64 ≤ v + 1 ↔ v + 1 = 2 ^ 64 by omega_using [hv])]
  rfl

theorem upB_ok {t : State} {x D : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 x)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block [.mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax)]) t
      fun t' => t'.gpr .rax = mask (over (x % 2 ^ 64) D) ∧ t'.mem = t.mem ∧ Keep [.r14, .rax] t t' := by
  refine WP.mono (WP.keep [.r14, .rax] (Q := fun t' => t'.gpr .rax = mask (over (x % 2 ^ 64) D) ∧
    t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  xrun [execMulx, hdx, hsi]
  rw [BitVec.toNat_ofNat x, toNat_ofNat64 hD, toNat_ofNat64 (hi_lt (Nat.mod_lt x (by decide)) hD)]
  rfl

theorem mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;>
    simp only [mask_true, mask_false, Bool.or_true, Bool.or_false, BitVec.allOnes_or, BitVec.or_allOnes,
      BitVec.or_self]

theorem mask_xor (c : Bool) : mask c ^^^ BitVec.allOnes 64 = mask (!c) := by
  cases c
  · rw [BitVec.xor_allOnes, mask_false, Bool.not_false, mask_true, show (0 : BitVec 64) = 0#64 from rfl,
      BitVec.not_zero]
  · rw [BitVec.xor_allOnes, mask_true, Bool.not_true, mask_false, BitVec.not_allOnes]; rfl

theorem upC_ok {t : State} {v : Nat} {a b : Bool} (hax : t.gpr .rax = mask a) (h11 : t.gpr .r11 = mask b)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 v) :
    WP isa (.block [.alu .or .rax (.reg .r11), .alu .xor .rax (.imm (-1)), .alu .sub .rcx (.reg .rax),
      .alu .test .rax (.reg .rax)]) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (!a && !b).toNat) ∧
      t'.zf = some (a || b) ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (!a && !b).toNat) ∧
    t'.zf = some (a || b) ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  xrun [hax, h11, hcx, R2w.sxm1]
  rw [mask_or, mask_xor, BitVec.and_self]
  cases a <;> cases b
  · rw [show (!(false || false)) = true from rfl, mask_true]
    refine ⟨BitVec.eq_of_toNat_eq ?_, beq_eq_false_iff_ne.mpr fun h => ?_⟩
    · rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (!false && !false).toNat = 1 from rfl]
      omega_using []
    · have := congrArg BitVec.toNat h
      rw [BitVec.toNat_allOnes, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_using [this]
  all_goals
    rw [show ∀ x y : Bool, (!(x || y)) = false → mask (!(x || y)) = 0#64 from fun x y h => by rw [h]; rfl]
    · exact ⟨by rw [BitVec.sub_zero]; rfl, rfl⟩
    · rfl

theorem up_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block recipUp) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (up v D).toNat) ∧
      t'.zf = some (!up v D) ∧ t'.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t t' := by
  rw [show recipUp = ([.mov .rdx (.reg .rcx), .alu .add .rdx (.imm 1), .alu .sbb .r11 (.reg .r11)] : List Instr) ++
      (([.mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      ([.alu .or .rax (.reg .r11), .alu .xor .rax (.imm (-1)), .alu .sub .rcx (.reg .rax),
        .alu .test .rax (.reg .rax)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (upA_ok hcx hv) fun t₁ ⟨h1dx, h111, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (upB_ok h1dx ((k₁.gpr (by decide)).trans hsi) hD) fun t₂ ⟨h2ax, hm₂, k₂⟩ => ?_
  refine WP.mono (upC_ok h2ax ((k₂.gpr (by decide)).trans h111)
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hcx))) fun t' ⟨h3cx, h3z, hm₃, k₃⟩ => ?_
  have hu : (!over ((v + 1) % 2 ^ 64) D && !decide (v + 1 = 2 ^ 64)) = up v D := by
    unfold up
    by_cases h : v + 1 = 2 ^ 64
    · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    · rw [Nat.mod_eq_of_lt (by omega_using [hv, h]), Bool.and_comm]
  refine ⟨by rw [h3cx, hu], by rw [h3z, ← hu, Bool.not_and, Bool.not_not, Bool.not_not], by rw [hm₃, hm₂, hm₁],
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## The loops -/

/-- `recipDown` while it lowers `v`: then `(2^64 + v) d < 2^128`. -/
theorem downLoop_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.loop (.block recipDown) .ne) t fun t' => ∃ v', t'.gpr .rcx = BitVec.ofNat 64 v' ∧ v' < 2 ^ 64 ∧
      over v' D = false ∧ t'.mem = t.mem ∧ Keep [.rdx, .r14, .rax, .rcx] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => s.gpr .rcx = BitVec.ofNat 64 n ∧ n < 2 ^ 64 ∧ s.mem = t.mem ∧
    Keep [.rdx, .r14, .rax, .rcx] t s) (fun n s ⟨h1, h2, h3, k⟩ => ?_) v t ⟨hcx, hv, rfl, Keep.refl _ _⟩
  refine WP.mono (down_ok h1 h2 ((k.gpr (by decide)).trans hsi) hD) fun s' ⟨h1', hz, hm', k'⟩ => ?_
  cases ho : over n D
  · rw [ho, Bool.toNat_false, Nat.sub_zero] at h1'
    exact .inl ⟨by simp only [eval, hz, ho, Option.map_some, Bool.not_false, Bool.not_true],
      n, h1', h2, ho, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · have hn := over_pos hD ho
    rw [ho, Bool.toNat_true] at h1'
    exact .inr ⟨by simp only [eval, hz, ho, Option.map_some, Bool.not_true, Bool.not_false],
      n - 1, by omega_using [hn], h1', by omega_using [h2], hm'.trans h3, (k.trans k').mono (by decide)⟩

/-- `recipUp` while it raises `v`, from `v` with `(2^64 + v) d < 2^128`: then
also `up v d` is false. -/
theorem upLoop_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (ho : over v D = false) (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.loop (.block recipUp) .ne) t fun t' => ∃ v', t'.gpr .rcx = BitVec.ofNat 64 v' ∧ v' < 2 ^ 64 ∧
      over v' D = false ∧ up v' D = false ∧ t'.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ u, n = 2 ^ 64 - u ∧ s.gpr .rcx = BitVec.ofNat 64 u ∧ u < 2 ^ 64 ∧
    over u D = false ∧ s.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t s)
    (fun n s ⟨u, hn, h1, h2, ho', h3, k⟩ => ?_) (2 ^ 64 - v) t ⟨v, rfl, hcx, hv, ho, rfl, Keep.refl _ _⟩
  refine WP.mono (up_ok h1 h2 ((k.gpr (by decide)).trans hsi) hD) fun s' ⟨h1', hz, hm', k'⟩ => ?_
  cases hu : up u D
  · rw [hu, Bool.toNat_false, Nat.add_zero] at h1'
    exact .inl ⟨by simp only [eval, hz, hu, Option.map_some, Bool.not_false, Bool.not_true],
      u, h1', h2, ho', hu, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · rw [hu, Bool.toNat_true] at h1'
    unfold up at hu
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
    exact .inr ⟨by simp only [eval, hz, up, hu, Option.map_some, decide_false, Bool.not_false, Bool.and_self,
        Bool.not_not],
      2 ^ 64 - (u + 1), by omega_using [hn, h2, hu.1], u + 1, rfl, h1', by omega_using [h2, hu.1], hu.2,
      hm'.trans h3, (k.trans k').mono (by decide)⟩

/-! ## The reciprocal -/

/-- `recipN`: `v` for `d = m[w - 1] ≥ 2^63` into the word at `r8`, for `m` at
`r10` of `w` words, as `R2Words.recip` (`R2w.recip_ok`). -/
theorem recipN_ok {t : State} {B : Addr} {Z w em ev : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (h8 : t.gpr .r8 = off B ev)
    (hw : 1 ≤ w) (hM : em + 8 * w ≤ Z) (hE : ev + 8 ≤ Z)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat) :
    WP isa recipN t fun t' => t'.mem = t.mem.writeW (off B ev)
        (BitVec.ofNat 64 ((2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)) ∧
      Keep [.rsi, .rdx, .rax, .rcx, .r13, .r11, .r14, .r15] t t' := by
  generalize hD : word t.mem B (em + 8 * (w - 1)) = Dw at hd
  have hD' := Dw.isLt
  have eD : Dw = BitVec.ofNat 64 Dw.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold recipN
  refine WP.seq (WP.mono (recipGuess_ok hs h10 h12 hw hM) fun t₁ ⟨h1si, _, hm₁, k₁⟩ => ?_)
  rw [hD, eD] at h1si
  have hv₁ := (t₁.gpr .rcx).isLt
  refine WP.seq (WP.mono (downLoop_ok (v := (t₁.gpr .rcx).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hv₁ h1si hD') fun t₂ ⟨v₂, h2cx, hv₂, ho₂, hm₂, k₂⟩ => ?_)
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 Dw.toNat := (k₂.gpr (by decide)).trans h1si
  refine WP.seq (WP.mono (upLoop_ok h2cx hv₂ ho₂ h2si hD') fun t₃ ⟨v₃, h3cx, hv₃, ho₃, hu₃, hm₃, k₃⟩ => ?_)
  have hs₃ := ((hs.congr k₁.2.2).congr k₂.2.2).congr k₃.2.2
  have h38 : t₃.gpr .r8 = off B ev := by
    rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), h8]
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₃.mem.writeW (off B ev) (t₃.gpr .rcx)) (by
    xrun [State.ea, at0, h38, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs₃.st hE]) rfl)
    fun t' ⟨hm', k'⟩ => ⟨?_, ((k₁.trans k₂).trans (k₃.trans k')).mono (by decide)⟩
  rw [hm', hm₃, hm₂, hm₁, h3cx, recip_exact hd hD' ho₃ hu₃]

end VG.Proof.Bignum.X86_64.R2ax
