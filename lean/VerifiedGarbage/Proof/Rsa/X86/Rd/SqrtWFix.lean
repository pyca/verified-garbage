module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWWin
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Add
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

-- separate module: the digit step's corrections, proven apart from the step so a change rebuilds only them

/-! # The square root by words on i686: a digit step's corrections

The words `m`, `m + 1` of `sqD` (`m = j - 1`) as one 64-bit number `e`: `toE` doubles
its low word and subtracts one (`e = (y₁, 0) + 2 q̂ - 1`), `updX` adds one; `fixX` adds the
window of `sqD` (`L + 1` words from word `m`) to `T` (`sqT`, `L + 1` words) where `T`'s top bit is
set, by `R2Words`' `addBody` (`WordRt.addLoop_ok`), and subtracts two from `e` there.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sCt sqZ sqD sqT nl toE updX fixX mulSubX copyBackX hCnt winPtrs)

variable {B : Addr} {Z len : Nat}

/-- The two stores of a pair of words through `ebx`: `eax` low, `edx` high. -/
theorem store2_ok {t : State} {Q : State → Prop} (ws : Ws t B Z) {x : Nat} (pb : PtrAt t B .ebx x)
    (hx : x + 8 ≤ Z)
    (k : ∀ u, Keeps [] t u → Outside B x 8 t.mem u.mem → w32 u.mem B x = (t.gpr .eax).toNat →
      w32 u.mem B (x + 4) = (t.gpr .edx).toNat → WP isa (.block []) u Q) :
    WP isa (.block [.store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx]) t Q := by
  have nw := ws.nowrap
  refine wp_storeS (ea_ptr ws pb (d := 0) (by omega)) (ws_write ws (by omega)) fun u₁ M₁ => ?_
  have pb₁ : PtrAt u₁ B .ebx x := by rw [PtrAt, M₁.gpr]; exact pb
  refine wp_storeS (ea_ptr (ws.of_wr M₁.wr) pb₁ (d := 4) (by omega)) (ws_write (ws.of_wr M₁.wr) (by omega))
    fun u₂ M₂ => ?_
  have m₂ : u₂.mem = (t.mem.writeW (off B x) (t.gpr .eax)).writeW (off B (x + 4)) (t.gpr .edx) := by
    rw [M₂.mem, M₁.mem, M₁.gpr, Nat.add_zero]
  have O₁ := writeW32_outside t.mem B (d := x) (t.gpr .eax) (by omega)
  have O₂ := writeW32_outside (t.mem.writeW (off B x) (t.gpr .eax)) B (d := x + 4) (t.gpr .edx) (by omega)
  rw [← m₂] at O₂
  refine k u₂ ((M₁.keeps _).trans (M₂.keeps _))
    ((O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))) ?_ ?_
  · rw [m₂, w32_write_ne (size := Z) nw (by omega) (by omega) (by omega), w32_write_self]
  · rw [m₂, w32_write_self]

theorem bool_toNat (c : Prop) [Decidable c] : (decide c).toNat = if c then 1 else 0 := by
  by_cases h : c <;> simp [h]

/-- `toE`'s arithmetic: `(lo, hi) ↦ (2 lo + β hi - 1) mod 2^64` by words. -/
theorem toE_arith {lo hi : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    ((lo + lo) % 2 ^ 32 + (2 ^ 32 - 1)) % 2 ^ 32 +
      2 ^ 32 * (((hi + 0 + (if 2 ^ 32 ≤ lo + lo then 1 else 0)) % 2 ^ 32 + 2 ^ 32 * 2 - 0 -
        (if (lo + lo) % 2 ^ 32 < 1 then 1 else 0)) % 2 ^ 32) =
      (2 * lo + 2 ^ 32 * hi + 2 ^ 64 - 1) % 2 ^ 64 := by
  split <;> split <;> omega

/-- `updX`'s arithmetic: `(lo, hi) ↦ (lo + β hi + 1) mod 2^64` by words. -/
theorem updX_arith {lo hi : Nat} (hlo : lo < 2 ^ 32) (_hhi : hi < 2 ^ 32) :
    (lo + 1) % 2 ^ 32 + 2 ^ 32 * ((hi + 0 + (if 2 ^ 32 ≤ lo + 1 then 1 else 0)) % 2 ^ 32) =
      (lo + 2 ^ 32 * hi + 1) % 2 ^ 64 := by
  split <;> omega

/-- `fixX`'s last arithmetic: `(lo, hi) ↦ (lo + β hi + 2^64 - d) mod 2^64` by words, `d ≤ 2`. -/
theorem sub2_arith {lo hi d : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) (hd : d ≤ 2) :
    (lo + 2 ^ 32 - d) % 2 ^ 32 + 2 ^ 32 * ((hi + 2 ^ 32 * 2 - 0 - (if lo < d then 1 else 0)) % 2 ^ 32) =
      (lo + 2 ^ 32 * hi + 2 ^ 64 - d) % 2 ^ 64 := by
  split <;> omega

theorem toE_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) :
    WP isa (.block toE) s fun t => RtWs wid t B Z len 22 ∧
      Outside B (arr (kw len) sqD + 4 * (j - 1)) 8 s.mem t.mem ∧
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) + 2 ^ 32 * w32 t.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) =
        (2 * w32 s.mem B (arr (kw len) sqD + 4 * (j - 1)) +
          2 ^ 32 * w32 s.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) + 2 ^ 64 - 1) % 2 ^ 64 ∧
      Keeps [.eax, .ebx, .edx, .esi] s t := by
  have nw := h.ws.workspace.nowrap
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  simp only [S] at fd
  obtain ⟨x, ex⟩ : ∃ x, arr (kw len) sqD + 4 * (j - 1) = x := ⟨_, rfl⟩
  rw [ex]
  have hx : x + 8 ≤ Z := by omega
  unfold toE
  refine winPtrs_ok h hm hC hj1 (by omega) fun u K mu _ pb _ _ => ?_
  rw [ex] at pb
  have ws := h.rt.of_keeps K
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun u₁ U₁ _ => wp_addS rfl fun u₂ U₂ c₂ => ?_
  have pb₂ : PtrAt u₂ B .ebx x := by rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact pb
  refine wp_movS (readSrc_ptr (ws.of_wr (U₂.wr.trans U₁.wr)) pb₂ (d := 4) (by omega)) fun u₃ U₃ c₃ => ?_
  refine wp_adcS rfl (c₃.trans c₂) fun u₄ U₄ c₄ => wp_subS rfl fun u₅ U₅ c₅ =>
    wp_sbbS rfl c₅ fun u₆ U₆ _ => ?_
  have K₆ : Keeps [.eax, .edx] u u₆ := (U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans
      ((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))))))
  have m₆ : u₆.mem = s.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, mu]
  have pb₆ : PtrAt u₆ B .ebx x := by rw [PtrAt, K₆.1 _ (by decide)]; exact pb
  refine store2_ok (ws.of_keeps K₆) pb₆ hx fun t Kt Ot e0 e4 => WP.block_nil ?_
  have Kst : Keeps [.eax, .ebx, .edx, .esi] s t :=
    (K.mono (by decide)).trans ((K₆.mono (by decide)).trans (Kt.mono (by decide)))
  rw [m₆] at Ot
  refine ⟨h.keep Kst (by decide) (by decide) (Ot.mono (Nat.zero_le _) (by omega)), Ot, ?_, Kst⟩
  have lo : (u₁.gpr .eax).toNat = w32 s.mem B x := by
    rw [U₁.gpr, mu, Nat.add_zero]
  have hi : (u₃.gpr .edx).toNat = w32 s.mem B (x + 4) := by
    rw [U₃.gpr, U₂.mem, U₁.mem, mu]
  have l1 : w32 s.mem B x < 2 ^ 32 := (s.mem.readW (off B x) 32).isLt
  have l2 : w32 s.mem B (x + 4) < 2 ^ 32 := (s.mem.readW (off B (x + 4)) 32).isLt
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have e0' : (0 : BitVec 32).toNat = 0 := rfl
  have a₂ : (u₂.gpr .eax).toNat = (w32 s.mem B x + w32 s.mem B x) % 2 ^ 32 := by
    rw [U₂.gpr, BitVec.toNat_add, lo]
  have a₅ : (u₅.gpr .eax).toNat = ((w32 s.mem B x + w32 s.mem B x) % 2 ^ 32 + (2 ^ 32 - 1)) % 2 ^ 32 := by
    rw [U₅.gpr, BitVec.toNat_sub, U₄.other _ (by decide), U₃.other _ (by decide), a₂, e1]; omega
  have d₄ : (u₄.gpr .edx).toNat = (w32 s.mem B (x + 4) + 0 +
      (if 2 ^ 32 ≤ w32 s.mem B x + w32 s.mem B x then 1 else 0)) % 2 ^ 32 := by
    rw [U₄.gpr, VG.Proof.Mont.X86.add3_toNat, hi, e0', lo, bool_toNat]
  have d₆ : (u₆.gpr .edx).toNat = ((w32 s.mem B (x + 4) + 0 +
      (if 2 ^ 32 ≤ w32 s.mem B x + w32 s.mem B x then 1 else 0)) % 2 ^ 32 + 2 ^ 32 * 2 - 0 -
      (if (w32 s.mem B x + w32 s.mem B x) % 2 ^ 32 < 1 then 1 else 0)) % 2 ^ 32 := by
    rw [U₆.gpr, VG.Proof.Mont.X86.sub3_toNat, U₅.other _ (by decide), d₄, e0', bool_toNat,
      U₄.other _ (by decide), U₃.other _ (by decide), a₂, e1]
  rw [e0, e4, U₆.other _ (by decide), a₅, d₆]
  exact toE_arith l1 l2

theorem updX_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) :
    WP isa (.block updX) s fun t => RtWs wid t B Z len 22 ∧
      Outside B (arr (kw len) sqD + 4 * (j - 1)) 8 s.mem t.mem ∧
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) + 2 ^ 32 * w32 t.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) =
        (w32 s.mem B (arr (kw len) sqD + 4 * (j - 1)) +
          2 ^ 32 * w32 s.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) + 1) % 2 ^ 64 ∧
      Keeps [.eax, .ebx, .edx, .esi] s t := by
  have nw := h.ws.workspace.nowrap
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  simp only [S] at fd
  obtain ⟨x, ex⟩ : ∃ x, arr (kw len) sqD + 4 * (j - 1) = x := ⟨_, rfl⟩
  rw [ex]
  have hx : x + 8 ≤ Z := by omega
  unfold updX
  refine winPtrs_ok h hm hC hj1 (by omega) fun u K mu _ pb _ _ => ?_
  rw [ex] at pb
  have ws := h.rt.of_keeps K
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  have pb₁ : PtrAt u₁ B .ebx x := by rw [PtrAt, U₁.other _ (by decide)]; exact pb
  refine wp_movS (readSrc_ptr (ws.of_wr U₁.wr) pb₁ (d := 4) (by omega)) fun u₂ U₂ _ => ?_
  refine wp_addS rfl fun u₃ U₃ c₃ => wp_adcS rfl c₃ fun u₄ U₄ _ => ?_
  have K₄ : Keeps [.eax, .edx] u u₄ := (U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem, mu]
  have pb₄ : PtrAt u₄ B .ebx x := by rw [PtrAt, K₄.1 _ (by decide)]; exact pb
  refine store2_ok (ws.of_keeps K₄) pb₄ hx fun t Kt Ot e0 e4 => WP.block_nil ?_
  have Kst : Keeps [.eax, .ebx, .edx, .esi] s t :=
    (K.mono (by decide)).trans ((K₄.mono (by decide)).trans (Kt.mono (by decide)))
  rw [m₄] at Ot
  refine ⟨h.keep Kst (by decide) (by decide) (Ot.mono (Nat.zero_le _) (by omega)), Ot, ?_, Kst⟩
  have lo : (u₂.gpr .eax).toNat = w32 s.mem B x := by
    rw [U₂.other _ (by decide), U₁.gpr, mu, Nat.add_zero]
  have hi : (u₃.gpr .edx).toNat = w32 s.mem B (x + 4) := by
    rw [U₃.other _ (by decide), U₂.gpr, U₁.mem, mu]
  have l1 : w32 s.mem B x < 2 ^ 32 := (s.mem.readW (off B x) 32).isLt
  have l2 : w32 s.mem B (x + 4) < 2 ^ 32 := (s.mem.readW (off B (x + 4)) 32).isLt
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have e0' : (0 : BitVec 32).toNat = 0 := rfl
  have a₄ : (u₄.gpr .eax).toNat = (w32 s.mem B x + 1) % 2 ^ 32 := by
    rw [U₄.other _ (by decide), U₃.gpr, BitVec.toNat_add, lo, e1]
  have d₄ : (u₄.gpr .edx).toNat = (w32 s.mem B (x + 4) + 0 + (if 2 ^ 32 ≤ w32 s.mem B x + 1 then 1 else 0)) % 2 ^ 32 := by
    rw [U₄.gpr, VG.Proof.Mont.X86.add3_toNat, hi, e0', lo, bool_toNat, e1]
  rw [e0, e4, a₄, d₄]
  exact updX_arith l1 l2

theorem sbb_mask (c : Bool) : (if c then BitVec.allOnes 32 else (0 : BitVec 32)) =
    VG.Proof.Bignum.X86.R2Words.bmask c := by
  cases c <;> rfl

theorem dbl_top {w : Nat} (hw : w < 2 ^ 32) : decide (2 ^ 32 ≤ w + w) = decide (2 ^ 31 ≤ w) := by
  by_cases h : 2 ^ 31 ≤ w
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega

theorem and2_mask (c : Bool) :
    (VG.Proof.Bignum.X86.R2Words.bmask c &&& (2 : BitVec 32)).toNat = if c then 2 else 0 := by
  cases c <;> rfl

/-- `fixX`'s first block: `ebx` at the window of `sqD`, `ebp` at `T`, the mask of `T`'s top bit in
`ecx` (and the header word `hCnt`), no carry in `esi`, `edi` the `L + 1` words' bytes. -/
theorem fixHead_ok {s : State} {Q : State → Prop} (h : RtWs wid s B Z len 22) {a j : Nat}
    (hm : MLen s B Z nl a) (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a)
    (hW : wq a + 3 ≤ kw len)
    (kk : ∀ u, PtrAt u B .ebx (arr (kw len) sqD + 4 * (j - 1)) → PtrAt u B .ebp (arr (kw len) sqT) →
      u.gpr .edi = BitVec.ofNat 32 (4 * (wq a - (j - 1) + 3)) →
      u.gpr .ecx = VG.Proof.Bignum.X86.R2Words.bmask
        (decide (2 ^ 31 ≤ w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2)))) →
      u.gpr .esi = VG.Proof.Bignum.X86.R2Words.bmask false →
      u.mem = s.mem.writeW (off B hCnt) (u.gpr .ecx) →
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u → Q u) :
    WP isa (.block (winPtrs ++ VG.Impl.Rsa.X86.KeyRt.arrPtr wid .ebp sqT .eax ++
      ([.mov .eax (.reg .ebp), .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)),
        .alu .add .eax (.reg .eax), .alu .sbb .ecx (.reg .ecx), .store (sc hCnt) .ecx,
        .mov .esi (.imm 0), .mov .edi (.reg .edx), .alu .add .edi (.imm 4)] : List Instr))) s Q := by
  have nw := h.ws.workspace.nowrap
  have ft := h.ws.arr_fit (j := sqT) (by decide)
  have hd := h.ws.hdr_le
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at ft
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hd
  have hwa : wq a ≤ 256 := by have := hm.le; simp only [wq]; omega
  rw [List.append_assoc]
  refine winPtrs_ok h hm hC hj1 (by omega) fun u K mu _ pb ed _ => ?_
  have h₀ := h.keep K (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h₀) h₀.lenLe h₀.edi (r := .ebp)
    (t := .eax) (j := sqT) (by decide) (by decide) (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  refine wp_movS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ => ?_
  have ed₂ : (u₂.gpr .edx).toNat = 4 * (wq a - (j - 1) + 2) := by
    rw [U₂.other _ (by decide), K₁.1 _ (by decide)]; exact ed
  have pa₂ : PtrAt u₂ B .eax (arr (kw len) sqT) := by rw [PtrAt, U₂.gpr]; exact p₁
  have pa₃ : PtrAt u₃ B .eax (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2)) := by
    rw [PtrAt, U₃.gpr, ptr_add pa₂, ed₂]
  have K₃ : Keeps [.eax, .ebx, .edx, .esi, .ebp] s u₃ := (K.mono (by decide)).trans
    ((K₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))))
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, U₂.mem, m₁, mu]
  have ws₃ := h.rt.of_keeps K₃
  refine wp_movS (readSrc_ptr ws₃ pa₃ (d := 0) (by omega)) fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ c₅ => ?_
  have w₄ : (u₄.gpr .eax).toNat = w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2)) := by
    rw [U₄.gpr, m₃, Nat.add_zero]
  rw [w₄, dbl_top (s.mem.readW _ 32).isLt] at c₅
  refine VG.X86.Wp.wp_sbb_self c₅ fun u₆ U₆ => ?_
  rw [sbb_mask] at U₆
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u₆ := (K₃.mono (by decide)).trans
    ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))))
  have hws₆ := h.ws.rest K₆
  refine wp_storeS (hws₆.workspace.ea (d := hCnt) (by simp only [hCnt]; omega))
    (hws₆.workspace.write (d := hCnt) (n := 4) (by simp only [hCnt]; omega)) fun u₇ M₇ => ?_
  refine wp_movS rfl fun u₈ U₈ _ => wp_movS rfl fun u₉ U₉ _ => wp_addS rfl fun u₁₀ U₁₀ _ => WP.block_nil ?_
  have K₁₀ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u₁₀ := (K₆.mono (by decide)).trans
    ((M₇.keeps _).trans ((U₈.keeps.mono (by decide)).trans
      ((U₉.keeps.mono (by decide)).trans (U₁₀.keeps.mono (by decide)))))
  have cx : u₁₀.gpr .ecx = u₆.gpr .ecx := by
    rw [U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), M₇.gpr]
  refine kk u₁₀ ?_ ?_ ?_ ?_ ?_ ?_ K₁₀
  · rw [PtrAt, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), M₇.gpr,
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide), K₁.1 _ (by decide)]; exact pb
  · rw [PtrAt, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), M₇.gpr,
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide)]; exact p₁
  · apply BitVec.eq_of_toNat_eq
    have e4 : (4 : BitVec 32).toNat = 4 := rfl
    rw [U₁₀.gpr, U₉.gpr, BitVec.toNat_add, U₈.other _ (by decide), M₇.gpr, U₆.other _ (by decide),
      U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), ed₂, e4, BitVec.toNat_ofNat]
    omega
  · rw [cx, U₆.gpr]
  · rw [U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.gpr]; rfl
  · rw [U₁₀.mem, U₉.mem, U₈.mem, M₇.mem, cx, U₆.mem, U₅.mem, U₄.mem, m₃]

/-- `fixX`'s last block: `edi` back, then the window's two words of `sqD` less `2` where the mask
in `hCnt` is set. -/
theorem fixTail_ok {s v : State} {Q : State → Prop} (h : RtWs wid s B Z len 22) {a j : Nat}
    (hm : MLen s B Z nl a) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len)
    (K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v) (O : Outside B 0 Z s.mem v.mem)
    (hC : slot v.mem B sCt = j) {cb : Bool}
    (hd : BitVec.ofNat 32 (slot v.mem B hCnt) = VG.Proof.Bignum.X86.R2Words.bmask cb)
    (kk : ∀ t, Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t →
      Outside B (arr (kw len) sqD + 4 * (j - 1)) 8 v.mem t.mem →
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) + 2 ^ 32 * w32 t.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) =
        (w32 v.mem B (arr (kw len) sqD + 4 * (j - 1)) +
          2 ^ 32 * w32 v.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) + 2 ^ 64 - if cb then 2 else 0) % 2 ^ 64 →
      Q t) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi wid ++ winPtrs ++
      ([.mov .ecx (.mem (sc hCnt)), .alu .and .ecx (.imm 2), .mov .eax (.mem (at_ .ebx 0)),
        .mov .edx (.mem (at_ .ebx 4)), .alu .sub .eax (.reg .ecx), .alu .sbb .edx (.imm 0),
        .store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx] : List Instr))) v Q := by
  have nw := h.ws.workspace.nowrap
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  have hdr := h.ws.hdr_le
  simp only [S] at fd
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  obtain ⟨x, ex⟩ : ∃ x, arr (kw len) sqD + 4 * (j - 1) = x := ⟨_, rfl⟩
  rw [ex] at kk
  have hx : x + 8 ≤ Z := by omega
  simp only [VG.Impl.Rsa.X86.KeyRt.restoreEdi, List.cons_append, List.nil_append]
  have ca := h.wsArg.keep K (by decide) O
  refine wp_movS ca.readSrc fun t₁ U₁ _ => ?_
  have K₁ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((K.trans (U₁.keeps.mono (by decide))).mono (by decide)) (U₁.gpr.trans h.edi_eq.symm)
  have O₁ : Outside B 0 Z s.mem t₁.mem := by rw [U₁.mem]; exact O
  have h₁ := h.keep K₁ (by decide) (by decide) O₁
  have hm₁ := hm.keep K₁ (by decide) O₁
  refine winPtrs_ok h₁ hm₁ (by rw [U₁.mem]; exact hC) hj1 (by omega) fun u Ku mu _ pb _ _ => ?_
  rw [ex] at pb
  have hws := h₁.ws.rest Ku
  refine wp_movS (readHdr hws (d := hCnt) (by simp only [hCnt, VG.Impl.Rsa.X86.Keys.hdr]; omega)) fun u₁ V₁ _ => ?_
  rw [mu, U₁.mem, hd] at V₁
  refine VG.X86.Wp.wp_andi fun u₂ V₂ => ?_
  have pb₂ : PtrAt u₂ B .ebx x := by rw [PtrAt, V₂.other _ (by decide), V₁.other _ (by decide)]; exact pb
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t₁ u₂ :=
    (Ku.mono (by decide)).trans ((V₁.keeps.mono (by decide)).trans (V₂.keeps.mono (by decide)))
  have m₂ : u₂.mem = v.mem := by rw [V₂.mem, V₁.mem, mu, U₁.mem]
  have ws₂ := h₁.rt.of_keeps K₂
  refine wp_movS (readSrc_ptr ws₂ pb₂ (d := 0) (by omega)) fun u₃ V₃ _ => ?_
  have pb₃ : PtrAt u₃ B .ebx x := by rw [PtrAt, V₃.other _ (by decide)]; exact pb₂
  refine wp_movS (readSrc_ptr (ws₂.of_wr V₃.wr) pb₃ (d := 4) (by omega)) fun u₄ V₄ _ => ?_
  refine wp_subS rfl fun u₅ V₅ c₅ => wp_sbbS rfl c₅ fun u₆ V₆ _ => ?_
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] t₁ u₆ := K₂.trans ((V₃.keeps.mono (by decide)).trans
    ((V₄.keeps.mono (by decide)).trans ((V₅.keeps.mono (by decide)).trans (V₆.keeps.mono (by decide)))))
  have m₆ : u₆.mem = v.mem := by rw [V₆.mem, V₅.mem, V₄.mem, V₃.mem, m₂]
  have K₆' : Keeps [.eax, .ecx, .edx] u u₆ := (V₁.keeps.mono (by decide)).trans ((V₂.keeps.mono (by decide)).trans
    ((V₃.keeps.mono (by decide)).trans ((V₄.keeps.mono (by decide)).trans
      ((V₅.keeps.mono (by decide)).trans (V₆.keeps.mono (by decide))))))
  have pb₆ : PtrAt u₆ B .ebx x := by rw [PtrAt, K₆'.1 _ (by decide)]; exact pb
  refine store2_ok (h₁.rt.of_keeps K₆) pb₆ hx fun t Kt Ot e0 e4 => WP.block_nil ?_
  rw [m₆] at Ot
  refine kk t (K₁.trans (K₆.trans (Kt.mono (by decide)))) Ot ?_
  have lo : (u₄.gpr .eax).toNat = w32 v.mem B x := by
    rw [V₄.other _ (by decide), V₃.gpr, m₂, Nat.add_zero]
  have hi : (u₅.gpr .edx).toNat = w32 v.mem B (x + 4) := by
    rw [V₅.other _ (by decide), V₄.gpr, V₃.mem, m₂]
  have cx₃ : (u₃.gpr .ecx).toNat = if cb then 2 else 0 := by
    rw [V₃.other _ (by decide), V₂.gpr, V₁.gpr, and2_mask]
  have cx : (u₄.gpr .ecx).toNat = if cb then 2 else 0 := by rw [V₄.other _ (by decide)]; exact cx₃
  have l1 : w32 v.mem B x < 2 ^ 32 := (v.mem.readW (off B x) 32).isLt
  have l2 : w32 v.mem B (x + 4) < 2 ^ 32 := (v.mem.readW (off B (x + 4)) 32).isLt
  have e0' : (0 : BitVec 32).toNat = 0 := rfl
  have hd2 : (if cb then 2 else 0) ≤ 2 := by split <;> omega
  have a₆ : (u₆.gpr .eax).toNat = (w32 v.mem B x + 2 ^ 32 - if cb then 2 else 0) % 2 ^ 32 := by
    rw [V₆.other _ (by decide), V₅.gpr, BitVec.toNat_sub, lo]; simp only [cx]; omega
  have d₆ : (u₆.gpr .edx).toNat = (w32 v.mem B (x + 4) + 2 ^ 32 * 2 - 0 -
      (if w32 v.mem B x < (if cb then 2 else 0) then 1 else 0)) % 2 ^ 32 := by
    rw [V₆.gpr, VG.Proof.Mont.X86.sub3_toNat, hi, e0', bool_toNat, lo]; simp only [cx]
  rw [e0, e4, a₆, d₆]
  exact sub2_arith l1 l2 hd2

/-- `fixX`'s head and add loop: where its tail starts (`edi` the loop's count, the mask in `hCnt`). -/
theorem fixHL_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) :
    WP isa (.seq (.block (winPtrs ++ VG.Impl.Rsa.X86.KeyRt.arrPtr wid .ebp sqT .eax ++
      ([.mov .eax (.reg .ebp), .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)),
        .alu .add .eax (.reg .eax), .alu .sbb .ecx (.reg .ecx), .store (sc hCnt) .ecx,
        .mov .esi (.imm 0), .mov .edi (.reg .edx), .alu .add .edi (.imm 4)] : List Instr)))
      (.loop (.block VG.Impl.Bignum.X86.R2Words.addBody) .ne)) s fun v =>
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v ∧ Outside B 0 Z s.mem v.mem ∧
      slot v.mem B sCt = j ∧ ∃ cb, BitVec.ofNat 32 (slot v.mem B hCnt) = VG.Proof.Bignum.X86.R2Words.bmask cb := by
  have nw := h.ws.workspace.nowrap
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  have ft := h.ws.arr_fit (j := sqT) (by decide)
  have dj := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) (j := sqD) (k := sqT) (by decide)
  have aD : 160 ≤ arr (kw len) sqD := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have he : hCnt = 48 := rfl
  have hs : sCt = 96 := rfl
  have aT : 160 ≤ arr (kw len) sqT := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have hdr := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  simp only [S] at fd ft dj
  refine WP.seq (fixHead_ok h hm hC hj1 hj hW fun u pb pp di cx si mu K => ?_)
  have ws := h.rt.of_keeps K
  have g : VG.Proof.Rsa.X86.WordRt.SubGeo B Z (arr (kw len) sqD + 4 * (j - 1)) (arr (kw len) sqD + 4 * (j - 1))
      (arr (kw len) sqT) (wq a - (j - 1) + 3) :=
    ⟨nw, by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.addLoop_ok ws g (u := u) ⟨by simpa using pb,
    by simpa using pp, by rw [Nat.sub_zero]; exact di, cx, Keeps.refl _ _, Outside.refl _ _ _ _,
    false, si, by simp [val32]⟩) fun u' I => ?_
  have Oh : Outside B hCnt 4 s.mem u.mem := by
    rw [mu]; exact writeW32_outside _ _ _ (by simp only [hCnt]; omega)
  have Ou : Outside B 0 Z s.mem u'.mem :=
    (Oh.mono (Nat.zero_le _) (by simp only [hCnt]; omega)).trans (I.out.mono (Nat.zero_le _) (by omega))
  have hcnt : slot u'.mem B hCnt = (u.gpr .ecx).toNat := by
    rw [slot, I.out.w32 (.inl (by simp only [hCnt]; omega)) (by simp only [hCnt]; omega), mu, w32_write_self]
  refine ⟨K.trans I.keep, Ou, ?_, _, by rw [hcnt, BitVec.ofNat_toNat, BitVec.setWidth_eq, cx]⟩
  rw [slot, I.out.w32 (.inl (by omega)) (by omega), Oh.w32 (.inr (by omega)) (by omega)]; exact hC

theorem fixX_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) :
    WP isa fixX s fun t => RtWs wid t B Z len 22 ∧ Keep B (kw len) [sqT, sqD] [hCnt] s.mem t.mem ∧
      (∀ i, i < kw len + 2 → i ≠ j - 1 → i ≠ j →
        w32 t.mem B (arr (kw len) sqD + 4 * i) = w32 s.mem B (arr (kw len) sqD + 4 * i)) ∧
      (∃ c, c < 2 ∧ val32 t.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) + 2 ^ (32 * (wq a - (j - 1) + 3)) * c =
        val32 s.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) +
          if 2 ^ 31 ≤ w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2))
          then val32 s.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 3) else 0) ∧
      w32 t.mem B (arr (kw len) sqD + 4 * (j - 1)) + 2 ^ 32 * w32 t.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) =
        (w32 s.mem B (arr (kw len) sqD + 4 * (j - 1)) +
          2 ^ 32 * w32 s.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) + 2 ^ 64 -
          if 2 ^ 31 ≤ w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2)) then 2 else 0) % 2 ^ 64 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  have ft := h.ws.arr_fit (j := sqT) (by decide)
  have dj := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) (j := sqD) (k := sqT) (by decide)
  have aD : 160 ≤ arr (kw len) sqD := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have he : hCnt = 48 := rfl
  have hs : sCt = 96 := rfl
  have aT : 160 ≤ arr (kw len) sqT := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have hdr := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  simp only [S] at fd ft dj
  obtain ⟨cb, ecb⟩ : ∃ cb, decide (2 ^ 31 ≤ w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2))) = cb :=
    ⟨_, rfl⟩
  have pcb : (2 ^ 31 ≤ w32 s.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2))) ↔ cb = true := by
    rw [← ecb]; simp
  simp only [pcb]
  unfold fixX
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (fixHead_ok h hm hC hj1 hj hW fun u pb pp di cx si mu K => ?_)
  rw [ecb] at cx
  have ws := h.rt.of_keeps K
  have g : VG.Proof.Rsa.X86.WordRt.SubGeo B Z (arr (kw len) sqD + 4 * (j - 1)) (arr (kw len) sqD + 4 * (j - 1))
      (arr (kw len) sqT) (wq a - (j - 1) + 3) :=
    ⟨nw, by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.WordRt.addLoop_ok ws g (u := u) ⟨by simpa using pb,
    by simpa using pp, by rw [Nat.sub_zero]; exact di, cx, Keeps.refl _ _, Outside.refl _ _ _ _,
    false, si, by simp [val32]⟩) fun u' I => ?_)
  obtain ⟨c', _, hval⟩ := I.val
  have Oh : Outside B hCnt 4 s.mem u.mem := by
    rw [mu]; exact writeW32_outside _ _ _ (by simp only [hCnt]; omega)
  have Ou : Outside B 0 Z s.mem u'.mem :=
    (Oh.mono (Nat.zero_le _) (by simp only [hCnt]; omega)).trans (I.out.mono (Nat.zero_le _) (by omega))
  have hcnt : slot u'.mem B hCnt = (u.gpr .ecx).toNat := by
    rw [slot, I.out.w32 (.inl (by simp only [hCnt]; omega)) (by simp only [hCnt]; omega), mu, w32_write_self]
  have hd : BitVec.ofNat 32 (slot u'.mem B hCnt) = VG.Proof.Bignum.X86.R2Words.bmask cb := by
    rw [hcnt, BitVec.ofNat_toNat, BitVec.setWidth_eq, cx]
  have hC' : slot u'.mem B sCt = j := by
    rw [slot, I.out.w32 (.inl (by omega)) (by omega), Oh.w32 (.inr (by omega)) (by omega)]; exact hC
  refine fixTail_ok h hm hj1 hj hW (K.trans I.keep) Ou hC' hd fun t Kt Ot ev => ?_
  have Ot' : Outside B 0 Z s.mem t.mem := Ou.trans (Ot.mono (Nat.zero_le _) (by omega))
  -- `u'` against `s` below `T`.
  have below : ∀ e, e + 4 ≤ arr (kw len) sqT → hCnt + 4 ≤ e → w32 u'.mem B e = w32 s.mem B e := fun e h1 h2 => by
    rw [I.out.w32 (.inl h1) (by omega), Oh.w32 (.inr h2) (by omega)]
  refine ⟨h.keep Kt (by decide) (by decide) Ot', ?_, ?_, ⟨c'.toNat, Bool.toNat_lt _, ?_⟩, ?_, Kt⟩
  · exact (Keep.of_slot Oh (by simp)).trans ((Keep.of_arr (o := sqT) (d := 0) (by simpa using I.out)
      (by simp only [S]; omega) (by simp)).trans (Keep.of_arr (o := sqD) (d := 4 * (j - 1)) Ot
      (by simp only [S]; omega) (by simp)))
  · intro i hi1 hi2 hi3
    rw [Ot.w32 (by omega) (by omega)]
    exact below _ (by omega) (by simp only [hCnt]; omega)
  · have eT : val32 t.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) =
        val32 u'.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) := Ot.val32 (.inr (by omega)) (by omega)
    have eT' : val32 u.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) =
        val32 s.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) := Oh.val32 (.inr (by simp only [hCnt]; omega)) (by omega)
    have eD : val32 u.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 3) =
        val32 s.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 3) :=
      Oh.val32 (.inr (by simp only [hCnt]; omega)) (by omega)
    rw [eT, hval, eT', eD]
  · rw [ev, below _ (by omega) (by simp only [hCnt]; omega), below _ (by omega) (by simp only [hCnt]; omega)]

end VG.Proof.Rsa.X86.Recover
