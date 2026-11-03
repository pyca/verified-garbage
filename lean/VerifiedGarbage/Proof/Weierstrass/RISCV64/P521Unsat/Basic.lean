module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Unsat
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: limbs

What the kernels share. The numbers a function's nine words stand for (`Impl/Weierstrass/RISCV64/P521Unsat.lean`):
`lw X i`, word `i` of a number `X` (GenWide's `xv`, for operands in memory),
`uv X`, the number of its words as limbs, `Σ lw X i 2⁵⁸ⁱ`, and `Tight X`;
what every kernel starts from (`CoreOk`, GenWide's), the reads of its
operands and the writes of its working space, and the copy of the limbs at
`Z` to `[t2]` (`copyZ_ok`); the product's columns (`pipe_ok`) and their
values (`mulCols_sum`, `sqCols_sum`).
-/

@[expose] public section

-- `2⁵²²` is a numeral.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Impl.Weierstrass.RISCV64.GenWide (T SO)
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW xv ov colsV_congr colsV_lt)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## Limbs -/

/-- Word `i` of a number. -/
def lw (X i : Nat) : Nat := X / 2 ^ (64 * i) % 2 ^ 64

/-- The number of the limbs `f 0`, …, `f (n - 1)`. -/
def lv (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lv f n + 2 ^ (58 * n) * f n

/-- The number a number's nine words stand for, as limbs. -/
def uv (X : Nat) : Nat := lv (lw X) 9

/-- Limbs below `2⁵⁹`, the last below `2⁵⁸`. -/
def TightF (f : Nat → Nat) : Prop := (∀ i < 8, f i < 2 ^ 59) ∧ f 8 < 2 ^ 58

/-- A number's words are tight limbs. -/
def Tight (X : Nat) : Prop := TightF (lw X)

/-- P-521's prime. -/
abbrev p : Nat := 2 ^ 521 - 1

theorem lv_congr {f g : Nat → Nat} : ∀ {n}, (∀ i < n, f i = g i) → lv f n = lv g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [lv, lv, lv_congr fun i hi => h i (by omega), h n (by omega)]

theorem lw_colsV (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) : ∀ n, ∀ i < n, lw (colsV f n) i = f i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hX := colsV_lt f hf n
    rw [colsV, lw]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      rw [show ((2 : Nat) ^ 64) ^ (i + d + 1) * f (i + d + 1) = 2 ^ (64 * i) * (2 ^ 64 * ((2 ^ 64) ^ d * f (i + d + 1))) by
          rw [Nat.pow_mul, Nat.pow_add, Nat.pow_add, Nat.pow_one]; ac_rfl,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
      exact lw_colsV f hf (i + d + 1) i h
    · rw [← Nat.pow_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (by rw [Nat.pow_mul]; exact hX), Nat.zero_add, Nat.mod_eq_of_lt (hf i)]

/-- Word `i` of an operand in memory. -/
theorem lw_xv (m : Mem) (A : Addr) {i : Nat} (hi : i < 9) : lw (xv m A 9) i = dw m A (8 * i) :=
  lw_colsV (fun j => dw m A (8 * j)) (fun _ => dw_lt _ _ _) 9 i hi

theorem uv_xv (m : Mem) (A : Addr) : uv (xv m A 9) = lv (fun i => dw m A (8 * i)) 9 :=
  lv_congr fun _ hi => lw_xv m A hi

theorem tight_xv {m : Mem} {A : Addr} :
    Tight (xv m A 9) ↔ TightF (fun i => dw m A (8 * i)) := by
  unfold Tight TightF
  rw [lw_xv m A (by decide : 8 < 9)]
  exact ⟨fun ⟨h, h8⟩ => ⟨fun i hi => by have := h i hi; rwa [lw_xv m A (by omega)] at this, h8⟩,
    fun ⟨h, h8⟩ => ⟨fun i hi => by rw [lw_xv m A (by omega)]; exact h i hi, h8⟩⟩

theorem TightF.lt {f : Nat → Nat} (h : TightF f) {i : Nat} (hi : i < 9) : f i < 2 ^ 59 := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h.1 i hi
  · exact Nat.lt_trans h.2 (by decide)

/-! ## Registers -/

/-- The mask `2⁵⁸ - 1`. -/
abbrev M58 : BitVec 64 := BitVec.ofNat 64 (2 ^ 58 - 1)

theorem and_M58 (x : BitVec 64) : (x &&& M58).toNat = x.toNat % 2 ^ 58 := by
  rw [BitVec.toNat_and, show M58.toNat = 2 ^ 58 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem shl_toNat (x : BitVec 64) (k : Nat) : (x <<< k).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem shr_toNat (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(x >> s) | (y << t)`, `s + t = 64`, is `x / 2^s + (y mod 2^s) 2^t`. -/
theorem shr_or_shl (x y : BitVec 64) {s t : Nat} (hst : s + t = 64) :
    ((x >>> s) ||| (y <<< t)).toNat = x.toNat / 2 ^ s + y.toNat % 2 ^ s * 2 ^ t := by
  have hx := x.isLt
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ t := by rw [← Nat.pow_add, hst]
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, e64, Nat.mul_mod_mul_right]
  have hlt : x.toNat / 2 ^ s < 2 ^ t := Nat.div_lt_of_lt_mul (by rw [← e64]; exact hx)
  rw [Nat.or_comm, Nat.mul_comm (y.toNat % 2 ^ s), ← Nat.two_pow_add_eq_or_of_lt hlt]
  omega

/-- `mask`: `a6 = 2⁵⁸ - 1`. -/
theorem mask_ok {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Keeps [.a6] s s' → s'.gpr .a6 = M58 → WP isa (.block is) s' Q) :
    WP isa (.block (mask ++ is)) s Q := by
  refine WP.cons (exec_li (by decide)) (wp_srl (by decide) fun s' u => k s' ?_ ?_)
  · refine ⟨fun r hr => ?_, u.mem, u.rd, u.wr, u.sp⟩
    rw [u.other r (by simpa using hr), RegUpd.gpr_write_of_ne _ _ (by simpa using hr)]
  · rw [u.gpr, RegUpd.gpr_write_self]; decide

/-! ## The kernel's context -/

theorem core_of {b A B O : Addr} {s s' : State} (h : CoreOk 9 b A B O s)
    (g : ∀ r, r ∉ clobW → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    CoreOk 9 b A B O s' :=
  ⟨⟨by rw [g _ (by decide), h.ctx.a3], h.ctx.al, by rw [hwr]; exact h.ctx.wr⟩, h.nowrap,
    by rw [g _ (by decide), h.a], by rw [g _ (by decide), h.b'], by rw [g _ (by decide), h.o], h.aal, h.bal, h.oal,
    by rw [hrd, hwr]; exact h.ain, by rw [hrd, hwr]; exact h.bin, by rw [hwr]; exact h.ow, h.onw,
    h.adis, h.bdis, h.odis, h.k7, h.k30⟩

theorem T9 : T 9 = 1472 := rfl
theorem Z_eq : Z = 1472 := rfl
theorem Y_eq : Y = 1544 := rfl

/-- A part of the own working space within it. -/
theorem own_sub {b : Addr} {d n : Nat} (hd : 1472 ≤ d) (hn : d + n ≤ 1632) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (ownR 9 b) :=
  Offset.sub b hd (by rw [T9]; omega)

/-- What stays from the kernel's start `s0`: the registers outside `clobW`,
and memory outside the own working space and `[O]`. -/
structure Kept (b O : Addr) (s0 s : State) : Prop where
  gpr : ∀ r, r ∉ clobW → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s0.mem s.mem

theorem Kept.refl (b O : Addr) (s : State) : Kept b O s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {b O : Addr} {s0 s1 s2 : State} (h₁ : Kept b O s0 s1) (h₂ : Kept b O s1 s2) : Kept b O s0 s2 :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₁.frame.trans h₂.frame⟩

theorem Kept.keeps {b O : Addr} {s0 s s' : State} (h : Kept b O s0 s) {rs : List Reg} (hk : Keeps rs s s')
    (hc : ∀ r ∈ rs, r ∈ clobW := by decide) : Kept b O s0 s' :=
  ⟨fun r hr => (hk.1 r fun h => hr (hc r h)).trans (h.gpr r hr), hk.2.2.1.trans h.rd, hk.2.2.2.1.trans h.wr,
    hk.2.2.2.2.trans h.sp, by rw [hk.2.1]; exact h.frame⟩

theorem Kept.upd {b O : Addr} {s0 s s' : State} (h : Kept b O s0 s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∈ clobW := by decide) : Kept b O s0 s' :=
  ⟨fun r hr => (u.other r fun e => hr (e ▸ hd)).trans (h.gpr r hr), u.rd.trans h.rd, u.wr.trans h.wr,
    u.sp.trans h.sp, by rw [u.mem]; exact h.frame⟩

theorem Kept.core {b A B O : Addr} {s0 s : State} (hC : CoreOk 9 b A B O s0) (h : Kept b O s0 s) :
    CoreOk 9 b A B O s :=
  core_of hC h.gpr h.rd h.wr

/-- A write to the own working space. -/
theorem Kept.sd {b O : Addr} {s0 s s' : State} (h : Kept b O s0 s) {d : Nat} (hd : 1472 ≤ d) (hd' : d + 8 ≤ 1632)
    {v : BitVec 64} (u : Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) v)) :
    Kept b O s0 s' :=
  ⟨fun r hr => by rw [u.gpr]; exact h.gpr r hr, u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp, by
    rw [u.mem]
    exact h.frame.writeW (List.mem_cons_self ..) _
      (Offset.contains b hd (by rw [T9]; omega) (by rw [T9]; omega))⟩

/-- An operand's word, apart from the own working space. -/
theorem dwA_kept {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {m : Mem}
    (hf : Frame [ownR 9 b] s0.mem m) {i : Nat} (hi : i < 9) :
    dw m A (8 * i) = dw s0.mem A (8 * i) :=
  dw_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact hC.adis i hi

theorem dwB_kept {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {m : Mem}
    (hf : Frame [ownR 9 b] s0.mem m) {i : Nat} (hi : i < 9) :
    dw m B (8 * i) = dw s0.mem B (8 * i) :=
  dw_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact hC.bdis i hi

/-- `ld t, 8i(t4)`. -/
theorem ldA_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {is : List Instr} {Q : State → Prop}
    {t : Reg} {i : Nat} (hi : i < 9)
    (k : ∀ s', Upd s s' t (s.mem.readW (A + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .t4 (8 * i) :: is)) s Q :=
  wp_ld (by omega) (by rw [hC.a]) (al8 hC.aal (by omega)) (hC.ain i hi) k

/-- `ld t, 8i(t5)`. -/
theorem ldB_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {is : List Instr} {Q : State → Prop}
    {t : Reg} {i : Nat} (hi : i < 9)
    (k : ∀ s', Upd s s' t (s.mem.readW (B + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .t5 (8 * i) :: is)) s Q :=
  wp_ld (by omega) (by rw [hC.b']) (al8 hC.bal (by omega)) (hC.bin i hi) k

/-- `sd t, 8i(t2)`. -/
theorem sdO_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {is : List Instr} {Q : State → Prop}
    {t : Reg} {i : Nat} (hi : i < 9)
    (k : ∀ s', Mupd s s' (s.mem.writeW (O + BitVec.ofNat 64 (8 * i)) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .t2 (8 * i) :: is)) s Q :=
  wp_sd (by omega) (by rw [hC.o]) (al8 hC.oal (by omega)) (hC.ow i hi) k

/-- A write to `[O]`. -/
theorem Kept.sdO {b O : Addr} {s0 s s' : State} (h : Kept b O s0 s) {i : Nat} (hi : i < 9) {v : BitVec 64} (u : Mupd s s' (s.mem.writeW (O + BitVec.ofNat 64 (8 * i)) v)) :
    Kept b O s0 s' :=
  ⟨fun r hr => by rw [u.gpr]; exact h.gpr r hr, u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp, by
    rw [u.mem]
    exact h.frame.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains_base O (by omega) (by omega))⟩

/-- A word of the own working space, unchanged by a write to `[O]`. -/
theorem dw_own_sdO {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {m : Mem} {i d : Nat} (hi : i < 9)
    (hd : 1472 ≤ d) (hd' : d + 8 ≤ 1632) (v : BitVec 64) :
    dw (m.writeW (O + BitVec.ofNat 64 (8 * i)) v) b d = dw m b d := by
  unfold dw
  rw [Mem.readW_writeW_sep (w := 64) (w' := 64) ?_ (by decide)]
  have hs : Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ (ownR 9 b) := own_sub hd hd'
  have hO : Region.Sub ⟨O + BitVec.ofNat 64 (8 * i), 8⟩ ⟨O, 8 * 9⟩ := Offset.sub_base O (by omega)
  exact Region.Disjoint.sep (fun x h₁ h₂ => hC.odis x (hO x h₂) (hs x h₁)) (Region.contains_self _ _)
    (Region.contains_self _ _)

/-! ## The copy to `[t2]` -/

/-- After the words from `j₀` to `j₀ + k` of `copyZ j₀`. -/
structure CopyInv (b O : Addr) (s0 : State) (j₀ k : Nat) (s : State) : Prop where
  kept : Kept b O s0 s
  keeps : ∀ r, r ≠ .a1 → s.gpr r = s0.gpr r
  own : ∀ d, 1472 ≤ d → d + 8 ≤ 1632 → dw s.mem b d = dw s0.mem b d
  outs : ∀ j < 9, dw s.mem O (8 * j) = if j₀ ≤ j ∧ j < j₀ + k then dw s0.mem b (Z + 8 * j) else dw s0.mem O (8 * j)

theorem copyZ_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {j₀ : Nat} (hj : j₀ ≤ 9) :
    WP isa (.block (copyZ j₀)) s0 fun s => Kept b O s0 s ∧ (∀ r, r ≠ .a1 → s.gpr r = s0.gpr r) ∧
      ∀ j < 9, dw s.mem O (8 * j) = if j₀ ≤ j then dw s0.mem b (Z + 8 * j) else dw s0.mem O (8 * j) := by
  have hb := hC.nowrap
  have hO := hC.onw
  unfold copyZ
  rw [List.range'_eq_map_range, List.flatMap_map]
  refine WP.mono (wp_range_flatMap (M := isa) (CopyInv b O s0 j₀) (N := 9 - j₀) (fun k s hk h => ?_) (9 - j₀)
    (Nat.le_refl _) s0 ⟨Kept.refl _ _ _, fun _ _ => rfl, fun _ _ _ => rfl, fun j _ => by
      rw [ite_eq_right (by omega)]⟩) fun s h => ⟨h.kept, h.keeps, fun j hj' => by
        rw [h.outs j hj']; by_cases e : j₀ ≤ j
        · rw [ite_eq_left ⟨e, by omega⟩, ite_eq_left e]
        · rw [ite_eq_right (by omega), ite_eq_right e]⟩
  have hCs := h.kept.core hC
  refine ld_ok hCs.ctx (d := Z + 8 * (j₀ + k)) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s1 u1 => ?_
  have hC1 := core_of hCs (fun r _ => u1.other r (by rintro rfl; contradiction)) u1.rd u1.wr
  refine sdO_ok hC1 (i := j₀ + k) (by omega) fun s2 u2 => WP.block_nil ⟨(h.kept.upd u1).sdO (by omega) u2,
    fun r hr => by rw [u2.gpr, u1.other r hr, h.keeps r hr], fun d hd hd' => ?_, fun j hj' => ?_⟩
  · rw [u2.mem, dw_own_sdO hC (by omega) hd hd', u1.mem, h.own d hd hd']
  · rw [u2.mem, u1.gpr]
    by_cases e : j = j₀ + k
    · subst e
      rw [dw_write_self, ite_eq_left ⟨by omega, by omega⟩, ← h.own _ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)]
      rfl
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), u1.mem, h.outs j hj']
      by_cases e' : j₀ ≤ j ∧ j < j₀ + k
      · rw [ite_eq_left e', ite_eq_left ⟨e'.1, by omega⟩]
      · rw [ite_eq_right e', ite_eq_right (by omega)]

/-! ## The product's columns

`pipe ts cs` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`) for any table of
terms `ts` whose columns are the pairs `ps c` (`Tab`), each operand a limb of
`[t4]`, `[t5]` or `Y` (`srcOk`) below `2⁶⁰`: each term's product added to
the accumulator, with the next term's product and the one after's operands,
which the pipeline (`Pipe`) carries from term to term (`pstep_ok`), the
terms of a column (`pterms_ok`), its end (`colEnd_ok`) and the columns
(`pcol_ok`) by induction: the limbs at `Z` and what is left in the
accumulator, past `2⁵²²`, are the columns' sum (`pipe_ok`).
-/

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8)

/-! ## Sums of terms -/

/-- The sum of `f` over `l`. -/
def tsum {α : Type} (f : α → Nat) (l : List α) : Nat := (l.map f).sum

theorem tsum_nil {α : Type} (f : α → Nat) : tsum f [] = 0 := rfl

theorem tsum_append {α : Type} (f : α → Nat) (l l' : List α) : tsum f (l ++ l') = tsum f l + tsum f l' := by
  simp [tsum]

theorem tsum_singleton {α : Type} (f : α → Nat) (a : α) : tsum f [a] = f a := by simp [tsum]

theorem tsum_le {α : Type} {f : α → Nat} {B : Nat} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ B) → tsum f l ≤ l.length * B
  | [], _ => by simp [tsum]
  | a :: l, h => by
    have h1 := h a (List.mem_cons_self ..)
    have h2 := tsum_le (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [tsum, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    rw [Nat.succ_mul]; omega

/-! ## The operands -/

/-- The operands the code names: limbs of `[t4]` or `[t5]`, or of `Y`. -/
def srcOk (x : Src) : Bool :=
  ((x.1 == .t4 || x.1 == .t5) && x.2 % 8 == 0 && decide (x.2 < 72)) ||
    (x.1 == .a3 && x.2 % 8 == 0 && decide (1544 ≤ x.2) && decide (x.2 < 1616))

theorem srcOk_cases {x : Src} (h : srcOk x = true) :
    (∃ i < 9, x = (.t4, 8 * i)) ∨ (∃ i < 9, x = (.t5, 8 * i)) ∨ (∃ j < 9, x = (.a3, Y + 8 * j)) := by
  obtain ⟨r, o⟩ := x
  simp only [srcOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h | h, h8⟩, hl⟩⟩ | ⟨⟨⟨h, h8⟩, hl⟩, hu⟩
  · exact .inl ⟨o / 8, by omega, by rw [h]; congr 1; omega⟩
  · exact .inr (.inl ⟨o / 8, by omega, by rw [h]; congr 1; omega⟩)
  · exact .inr (.inr ⟨(o - 1544) / 8, by omega, by rw [h, Y_eq]; congr 1; omega⟩)

theorem srcOk_reg {x : Src} (h : srcOk x = true) : x.1 ∉ clobW := by
  rcases srcOk_cases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> dsimp only <;> decide

/-- An operand's word in a state. -/
def sv (s : State) (x : Src) : Nat := dw s.mem (s.gpr x.1) x.2

/-- The limbs at `Z`, the column outputs. -/
abbrev Zr (b : Addr) : Region := ⟨b + BitVec.ofNat 64 Z, 72⟩

/-- Loading an operand. -/
theorem ldS_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {x : Src} (hx : srcOk x = true)
    {t : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (s.gpr x.1 + BitVec.ofNat 64 x.2) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t x.1 x.2 :: is)) s Q := by
  rcases srcOk_cases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact wp_ld (by omega) rfl (by rw [hC.a]; exact al8 hC.aal (by omega)) (by rw [hC.a]; exact hC.ain i hi) k
  · exact wp_ld (by omega) rfl (by rw [hC.b']; exact al8 hC.bal (by omega)) (by rw [hC.b']; exact hC.bin i hi) k
  · exact wp_ld (by rw [Y_eq]; omega) rfl (by rw [hC.ctx.a3]; exact al8 hC.ctx.al (by rw [Y_eq]; omega))
      (by rw [hC.ctx.a3]; exact hC.ctx.inR (by rw [Y_eq]; omega)) k

/-- An operand's word, unchanged by writes to `Z`. -/
theorem sv_frame {b A B O : Addr} {s1 s : State} (hC : CoreOk 9 b A B O s1) {x : Src} (hx : srcOk x = true)
    (hg : s.gpr x.1 = s1.gpr x.1) (hf : Frame [Zr b] s1.mem s.mem) : sv s x = sv s1 x := by
  unfold sv
  rw [hg]
  refine dw_frame hf fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  have hb := hC.nowrap
  rcases srcOk_cases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [hC.a]; exact (hC.adis i hi).sub_right (own_sub (by rw [Z_eq]) (by rw [Z_eq]; omega))
  · rw [hC.b']; exact (hC.bdis i hi).sub_right (own_sub (by rw [Z_eq]) (by rw [Z_eq]; omega))
  · rw [hC.ctx.a3]
    exact Offset.disjoint b (Or.inr (by rw [Y_eq, Z_eq]; omega)) (by rw [Y_eq]; omega) (by rw [Z_eq]; omega)

/-! ## The pipeline -/

/-- What the terms keep, from the product's start `s1`. -/
structure PInv (b : Addr) (s1 s : State) : Prop where
  gpr : ∀ r, r ∉ clobW → s.gpr r = s1.gpr r
  rd : s.rd = s1.rd
  wr : s.wr = s1.wr
  sp : s.sp = s1.sp
  a6 : s.gpr .a6 = s1.gpr .a6
  frame : Frame [Zr b] s1.mem s.mem

theorem PInv.keeps {b : Addr} {s1 s s' : State} (h : PInv b s1 s) {rs : List Reg} (hk : Keeps rs s s')
    (hc : ∀ r ∈ rs, r ∈ clobW ∧ r ≠ .a6) : PInv b s1 s' :=
  ⟨fun r hr => (hk.1 r fun h => hr (hc r h).1).trans (h.gpr r hr), hk.2.2.1.trans h.rd, hk.2.2.2.1.trans h.wr,
    hk.2.2.2.2.trans h.sp, (hk.1 _ fun h => (hc _ h).2 rfl).trans h.a6, by rw [hk.2.1]; exact h.frame⟩

/-- The accumulator. -/
abbrev acc (s : State) : Nat := (s.gpr .a4).toNat + 2 ^ 64 * (s.gpr .a5).toNat

/-- The pipeline at term `n`: its product in `PR n`, the next term's operands in `a1` and `a2`. -/
structure Pipe (s1 : State) (ts : List Tm) (n : Nat) (s : State) : Prop where
  prod : n < ts.length → (s.gpr (PR n).1).toNat + 2 ^ 64 * (s.gpr (PR n).2).toNat =
    sv s1 (tm ts n).2.1 * sv s1 (tm ts n).2.2
  ops : n + 1 < ts.length → (s.gpr .a1).toNat = sv s1 (tm ts (n + 1)).2.1 ∧
    (s.gpr .a2).toNat = sv s1 (tm ts (n + 1)).2.2

theorem PR_cases (n : Nat) : PR n = (.a7, .t0) ∨ PR n = (.t3, .t6) := by
  unfold PR; split <;> simp

theorem PR_mod (n : Nat) : PR (n % 2) = PR n := by
  simp only [PR, Nat.mod_mod]

theorem PR_mod1 (n : Nat) : PR (n % 2 + 1) = PR (n + 1) := by
  simp only [PR]; rw [show (n % 2 + 1) % 2 = (n + 1) % 2 by omega]

theorem PR_clob (n : Nat) : ∀ r ∈ [(PR n).1, (PR n).2], r ∈ clobW ∧ r ≠ .a6 := by
  rcases PR_cases n with h | h <;> rw [h] <;> decide

/-- Term `n`'s product, if it is one. -/
theorem mulN_ok (ts : List Tm) (n : Nat) {s : State} :
    WP isa (.block (mulN ts n)) s fun s' =>
      (n < ts.length → (s'.gpr (PR n).1).toNat + 2 ^ 64 * (s'.gpr (PR n).2).toNat =
        (s.gpr .a1).toNat * (s.gpr .a2).toNat) ∧ Keeps [(PR n).1, (PR n).2] s s' := by
  unfold mulN
  split
  · have hr : (PR n).1 ≠ .a1 ∧ (PR n).1 ≠ .a2 ∧ (PR n).1 ≠ (PR n).2 := by
      rcases PR_cases n with h | h <;> rw [h] <;> decide
    exact WP.mono (mulWide_ok hr.1 hr.2.1 hr.2.2) fun _ ⟨e, k⟩ => ⟨fun _ => e, k⟩
  · exact WP.block_nil ⟨fun h => absurd h ‹_›, Keeps.refl _ _⟩

/-- The operands are the code's. -/
abbrev SrcsOk (ts : List Tm) : Prop := ∀ n < ts.length, srcOk (tm ts n).2.1 = true ∧ srcOk (tm ts n).2.2 = true

/-- Term `n`'s operands, if it is one. -/
theorem ldN_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) {ts : List Tm} (hsrc : SrcsOk ts)
    (n : Nat) {s : State} (hI : PInv b s1 s) :
    WP isa (.block (ldN ts n)) s fun s' => Keeps [.a1, .a2] s s' ∧
      (n < ts.length → (s'.gpr .a1).toNat = sv s1 (tm ts n).2.1 ∧ (s'.gpr .a2).toNat = sv s1 (tm ts n).2.2) := by
  unfold ldN
  split
  · rename_i hn
    obtain ⟨hx, hy⟩ := hsrc n hn
    have hCs : CoreOk 9 b A B O s := core_of hC hI.gpr hI.rd hI.wr
    refine ldS_ok hCs hx fun s₁ u₁ => ?_
    have hC₁ : CoreOk 9 b A B O s₁ := core_of hCs (fun r hr => u₁.other r fun e => hr (by rw [e]; decide)) u₁.rd u₁.wr
    refine ldS_ok hC₁ hy fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩, fun _ => ⟨?_, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other _ hr.2, u₁.other _ hr.1]
    · rw [u₂.other _ (by decide), u₁.gpr]
      exact sv_frame hC hx (hI.gpr _ (srcOk_reg hx)) hI.frame
    · rw [u₂.gpr, u₁.mem, u₁.other _ fun e => srcOk_reg hy (by rw [e]; decide)]
      exact sv_frame hC hy (hI.gpr _ (srcOk_reg hy)) hI.frame
  · exact WP.block_nil ⟨Keeps.refl _ _, fun h => absurd h ‹_›⟩

/-- The registers of a step, by the parity of its term. -/
theorem regs_step₁ : ∀ e < 2,
    (PR (e + 1)).1 ≠ .a1 ∧ (PR (e + 1)).1 ≠ .a2 ∧ (PR (e + 1)).1 ≠ (PR (e + 1)).2 ∧
    (PR e).1 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ (PR e).2 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧
    (PR e).1 ∉ [Reg.a1, .a2] ∧ (PR e).2 ∉ [Reg.a1, .a2] := by decide

theorem regs_step₂ : ∀ e < 2,
    Reg.a4 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧ Reg.a5 ∉ [(PR (e + 1)).1, (PR (e + 1)).2] ∧
    (PR e).1 ≠ .a4 ∧ (PR e).1 ≠ .a5 ∧ (PR e).2 ≠ .a4 ∧ (PR e).2 ≠ (PR e).1 := by decide

theorem regs_step₃ : ∀ e < 2,
    (PR (e + 1)).1 ∉ [Reg.a4, .a5, (PR e).1] ∧ (PR (e + 1)).2 ∉ [Reg.a4, .a5, (PR e).1] ∧
    (PR (e + 1)).1 ∉ [Reg.a1, .a2] ∧ (PR (e + 1)).2 ∉ [Reg.a1, .a2] := by decide

theorem regs_step₄ : ∀ e < 2, ∀ r ∈ [Reg.a4, .a5, (PR e).1], r ∈ clobW ∧ r ≠ .a6 := by decide

/-- Term `n`: the next product and operands, then this one's sums. -/
theorem pstep_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) {ts : List Tm} (hsrc : SrcsOk ts)
    {n : Nat} (hn : n < ts.length) {s : State} (hI : PInv b s1 s) (hp : Pipe s1 ts n s)
    (hb : acc s + sv s1 (tm ts n).2.1 * sv s1 (tm ts n).2.2 < 2 ^ 128) :
    WP isa (.block (pstep ts n)) s fun s' => PInv b s1 s' ∧ s'.mem = s.mem ∧ Pipe s1 ts (n + 1) s' ∧
      acc s' = acc s + sv s1 (tm ts n).2.1 * sv s1 (tm ts n).2.2 := by
  have he : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have h₁ := regs_step₁ _ he
  have h₂ := regs_step₂ _ he
  have h₃ := regs_step₃ _ he
  have sc := regs_step₄ _ he
  rw [PR_mod, PR_mod1] at h₁ h₂ h₃
  rw [PR_mod] at sc
  obtain ⟨-, -, -, p1n, p2n, p1a, p2a⟩ := h₁
  obtain ⟨a4n, a5n, p14, p15, p24, p21⟩ := h₂
  obtain ⟨q1s, q2s, q1a, q2a⟩ := h₃
  have a4a : Reg.a4 ∉ [Reg.a1, .a2] := by decide
  have a5a : Reg.a5 ∉ [Reg.a1, .a2] := by decide
  have a1s : Reg.a1 ∉ [Reg.a4, .a5, (PR n).1] := by rcases PR_cases n with h | h <;> rw [h] <;> decide
  have a2s : Reg.a2 ∉ [Reg.a4, .a5, (PR n).1] := by rcases PR_cases n with h | h <;> rw [h] <;> decide
  unfold pstep
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (mulN_ok ts (n + 1)) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have hI₁ := hI.keeps k₁ (PR_clob _)
  refine WP.block_append (WP.mono (ldN_ok hC hsrc (n + 2) hI₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have hI₂ := hI₁.keeps k₂ (by decide)
  have g : ∀ r, r ∉ [(PR (n + 1)).1, (PR (n + 1)).2] → r ∉ [Reg.a1, .a2] → s₂.gpr r = s.gpr r :=
    fun r h₁ h₂ => (k₂.1 r h₂).trans (k₁.1 r h₁)
  have pp := hp.prod hn
  rw [← g _ p1n p1a, ← g _ p2n p2a] at pp
  have ha : acc s₂ = acc s := by simp only [acc]; rw [g _ a4n a4a, g _ a5n a5a]
  refine WP.mono (add2_ok p14 (by decide) (Ne.symm p15) p24 p21) fun s₃ ⟨e₃, k₃⟩ => ?_
  refine ⟨hI₂.keeps k₃ sc, by rw [k₃.2.1, k₂.2.1, k₁.2.1], ⟨fun hn1 => ?_, fun hn2 => ?_⟩, ?_⟩
  · rw [k₃.1 _ q1s, k₃.1 _ q2s, k₂.1 _ q1a, k₂.1 _ q2a, e₁ hn1]
    obtain ⟨o1, o2⟩ := hp.ops hn1
    rw [o1, o2]
  · rw [k₃.1 _ a1s, k₃.1 _ a2s]
    exact e₂ hn2
  · show acc s₃ = _
    simp only [acc] at ha ⊢
    rw [e₃, ha, pp, Nat.mod_eq_of_lt hb]

theorem tsum_snoc {α : Type} (f : α → Nat) (l : List α) (a : α) : tsum f (l ++ [a]) = tsum f l + f a := by
  simp [tsum]

/-- Two pairs of operands are the same (a test `decide` evaluates cheaply). -/
def srcEq (x y : Src × Src) : Bool := x.1.1 == y.1.1 && x.1.2 == y.1.2 && x.2.1 == y.2.1 && x.2.2 == y.2.2

theorem srcEq_eq {x y : Src × Src} (h : srcEq x y = true) : x = y := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := y
  simp only [srcEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- What the code of a table of terms `ts` needs: its terms are column `c`'s
pairs `ps c` in order, from `pstart` on, at least one and at most nine. -/
structure Tab (ts : List Tm) (ps : Nat → List (Src × Src)) : Prop where
  get : ∀ c < 9, ∀ m < 9, m < (ps c).length →
    srcEq ((ps c).getD m ((.t4, 0), (.t4, 0))) (tm ts (pstart (fun c => (ps c).length) c + m)).2 = true
  le : ∀ c < 9, pstart (fun c => (ps c).length) c + (ps c).length ≤ ts.length
  src : SrcsOk ts
  len : ∀ c < 9, 0 < (ps c).length ∧ (ps c).length ≤ 9

theorem Tab.get' {ts : List Tm} {ps : Nat → List (Src × Src)} (ht : Tab ts ps) {c : Nat} (hc : c < 9) {k : Nat}
    (hk : k < (ps c).length) : (ps c)[k] = (tm ts (pstart (fun c => (ps c).length) c + k)).2 := by
  have e := srcEq_eq (ht.get c hc k (by have := (ht.len c hc).2; omega) hk)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at e

theorem Tab.take {ts : List Tm} {ps : Nat → List (Src × Src)} (ht : Tab ts ps) {c : Nat} (hc : c < 9) {m : Nat}
    (hm : m < (ps c).length) :
    (ps c).take (m + 1) = (ps c).take m ++ [(tm ts (pstart (fun c => (ps c).length) c + m)).2] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, ht.get' hc hm]
  rfl

/-- A term of a column is below `2¹²⁰`. -/
theorem Tab.term_le {ts : List Tm} {ps : Nat → List (Src × Src)} (ht : Tab ts ps) {s1 : State}
    (hlt : ∀ n < ts.length, sv s1 (tm ts n).2.1 < 2 ^ 60 ∧ sv s1 (tm ts n).2.2 < 2 ^ 60) {c : Nat} (hc : c < 9) :
    ∀ q ∈ ps c, sv s1 q.1 * sv s1 q.2 ≤ 2 ^ 120 := fun q hq => by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
  obtain ⟨l1, l2⟩ := hlt (pstart (fun c => (ps c).length) c + k) (by have := ht.le c hc; omega)
  rw [ht.get' hc hk]
  exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt l1 l2) (by decide))

theorem pstart_succ (cs : Nat → Nat) (c : Nat) : pstart cs (c + 1) = pstart cs c + cs c := by
  simp [pstart, List.range_succ]

/-- A column's value. -/
def col (s1 : State) (ps : Nat → List (Src × Src)) (c : Nat) : Nat := tsum (fun q => sv s1 q.1 * sv s1 q.2) (ps c)

/-- The operands are below `2⁶⁰`. -/
def SrcsLt (s1 : State) (ts : List Tm) : Prop :=
  ∀ n < ts.length, sv s1 (tm ts n).2.1 < 2 ^ 60 ∧ sv s1 (tm ts n).2.2 < 2 ^ 60

/-- Column `c`'s first `m` terms, by induction on them. -/
theorem pterms_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) {ts : List Tm}
    {ps : Nat → List (Src × Src)} (ht : Tab ts ps) (hlt : SrcsLt s1 ts) {c : Nat} (hc : c < 9) :
    ∀ m ≤ (ps c).length, ∀ s, PInv b s1 s → Pipe s1 ts (pstart (fun c => (ps c).length) c) s → acc s < 2 ^ 70 →
      WP isa (.block ((List.range' (pstart (fun c => (ps c).length) c) m).flatMap (pstep ts))) s fun s' =>
        PInv b s1 s' ∧ s'.mem = s.mem ∧ Pipe s1 ts (pstart (fun c => (ps c).length) c + m) s' ∧
        acc s' = acc s + tsum (fun q => sv s1 q.1 * sv s1 q.2) ((ps c).take m)
  | 0, _, s, hI, hp, _ => WP.block_nil ⟨hI, rfl, hp, by simp [tsum]⟩
  | m + 1, hm, s, hI, hp, hv => by
    rw [List.range'_concat, Nat.one_mul, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (pterms_ok hC ht hlt hc m (by omega) s hI hp hv) fun s₁ ⟨hI₁, m₁, hp₁, hv₁⟩ => ?_)
    have hn : pstart (fun c => (ps c).length) c + m < ts.length := by have := ht.le c hc; omega
    have hle : ∀ q ∈ (ps c).take m, sv s1 q.1 * sv s1 q.2 ≤ 2 ^ 120 := fun q hq =>
      ht.term_le hlt hc q (List.mem_of_mem_take hq)
    have hts := tsum_le hle
    have hlen : ((ps c).take m).length ≤ 9 := by rw [List.length_take]; have := (ht.len c hc).2; omega
    obtain ⟨l1, l2⟩ := hlt _ hn
    have hxy : sv s1 (tm ts (pstart (fun c => (ps c).length) c + m)).2.1 *
        sv s1 (tm ts (pstart (fun c => (ps c).length) c + m)).2.2 < 2 ^ 120 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt l1 l2) (by decide)
    have h9 : ((ps c).take m).length * 2 ^ 120 ≤ 9 * 2 ^ 120 := Nat.mul_le_mul_right _ hlen
    refine WP.mono (pstep_ok hC ht.src hn hI₁ hp₁ (by rw [hv₁]; omega))
      fun s₂ ⟨hI₂, m₂, hp₂, hv₂⟩ => ⟨hI₂, m₂.trans m₁, by rw [← Nat.add_assoc]; exact hp₂, ?_⟩
    rw [hv₂, hv₁, ht.take hc (by omega), tsum_snoc]
    omega

/-- The end of column `c`: `Z[c]` the accumulator's low 58 bits, the accumulator shifted right by 58. -/
theorem colEnd_ok {b : Addr} {s : State} (hc : Ctx b s) (h6 : s.gpr .a6 = M58) (e : Nat) {c : Nat} (hc9 : c < 9) :
    WP isa (.block (colEnd e c)) s fun s' =>
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * c)) (s.gpr .a4 &&& M58) ∧
      (s.gpr .a4 &&& M58).toNat = acc s % 2 ^ 58 ∧ acc s' = acc s / 2 ^ 58 ∧
      (∀ r, r ∉ [Reg.a4, .a5, (PR e).1, (PR e).2] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hr : (PR e).1 ≠ (PR e).2 ∧ (PR e).1 ≠ .a4 ∧ (PR e).1 ≠ .a5 ∧ (PR e).1 ≠ .a6 ∧ (PR e).2 ≠ .a4 ∧
      (PR e).2 ≠ .a5 ∧ (PR e).2 ≠ .a6 ∧ (PR e).1 ≠ .a3 := by
    rcases PR_cases e with h | h <;> rw [h] <;> decide
  obtain ⟨r12, r14, r15, r16, r24, r25, r26, r13⟩ := hr
  unfold colEnd
  refine wp_and fun s₁ u₁ => ?_
  have hc₁ : Ctx b s₁ := ⟨by rw [u₁.other _ (Ne.symm r13), hc.a3], hc.al, by rw [u₁.wr]; exact hc.wr⟩
  refine sd_ok hc₁ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s₂ u₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h6]
  · rw [and_M58]; simp only [acc]; omega
  · have e4 : s₆.gpr .a4 = (s.gpr .a4 >>> 58) ||| (s.gpr .a5 <<< 6) := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ r12, u₃.gpr, u₄.gpr, u₃.other _ (Ne.symm r15), u₂.gpr,
        u₁.other _ (Ne.symm r14), u₁.other _ (Ne.symm r15)]
    have e5 : s₆.gpr .a5 = s.gpr .a5 >>> 58 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (Ne.symm r25), u₃.other _ (Ne.symm r15), u₂.gpr,
        u₁.other _ (Ne.symm r15)]
    simp only [acc]
    rw [e4, e5, shr_or_shl _ _ (by decide : 58 + 6 = 64), shr_toNat]
    have := (s.gpr .a4).isLt
    have := (s.gpr .a5).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.2, u₃.other _ hr.2.2.1, u₂.gpr, u₁.other _ hr.2.2.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- After `c` columns: the limbs below `Z + 8 c` and the accumulator hold the
first `c` columns' sum, and the pipeline is at column `c`'s first term. -/
structure CInv (b : Addr) (s1 : State) (ts : List Tm) (ps : Nat → List (Src × Src)) (c : Nat) (s : State) : Prop where
  inv : PInv b s1 s
  pipe : Pipe s1 ts (pstart (fun c => (ps c).length) c) s
  accLt : acc s < 2 ^ 70
  lt : ∀ c' < c, dw s.mem b (Z + 8 * c') < 2 ^ 58
  val : lv (fun c' => dw s.mem b (Z + 8 * c')) c + 2 ^ (58 * c) * acc s = lv (col s1 ps) c

/-- Column `c`: its terms, then its end. -/
theorem pcol_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) (h6 : s1.gpr .a6 = M58) {ts : List Tm}
    {ps : Nat → List (Src × Src)} (ht : Tab ts ps) (hlt : SrcsLt s1 ts) {c : Nat} (hc : c < 9) {s : State}
    (h : CInv b s1 ts ps c s) :
    WP isa (.block (pcol ts (fun c => (ps c).length) c)) s (CInv b s1 ts ps (c + 1)) := by
  have hb := hC.nowrap
  unfold pcol
  refine WP.block_append (WP.mono (pterms_ok hC ht hlt hc _ (Nat.le_refl _) s h.inv h.pipe h.accLt)
    fun s₁ ⟨hI₁, m₁, hp₁, hv₁⟩ => ?_)
  rw [List.take_length] at hv₁
  rw [← pstart_succ] at hp₁
  have hc₁ : Ctx b s₁ := ⟨by rw [hI₁.gpr _ (by decide), hC.ctx.a3], hC.ctx.al, by rw [hI₁.wr]; exact hC.ctx.wr⟩
  have h6₁ : s₁.gpr .a6 = M58 := hI₁.a6.trans h6
  -- The registers of the last term's product, apart from the next one's and the operands.
  have hpos := (ht.len c hc).1
  have hpar : PR (pstart (fun c => (ps c).length) (c + 1) + 1) =
      PR (pstart (fun c => (ps c).length) (c + 1) - 1) := by
    rw [pstart_succ] at hp₁ ⊢
    simp only [PR]; rw [show (pstart (fun c => (ps c).length) c + (ps c).length + 1) % 2 =
      (pstart (fun c => (ps c).length) c + (ps c).length - 1) % 2 by omega]
  have hreg : ∀ r ∈ [(PR (pstart (fun c => (ps c).length) (c + 1))).1, (PR (pstart (fun c => (ps c).length) (c + 1))).2,
      Reg.a1, .a2, .a6], r ∉ [Reg.a4, .a5, (PR (pstart (fun c => (ps c).length) (c + 1) + 1)).1,
        (PR (pstart (fun c => (ps c).length) (c + 1) + 1)).2] := by
    have := Nat.mod_lt (pstart (fun c => (ps c).length) (c + 1)) (by decide : 0 < 2)
    rw [← PR_mod, ← PR_mod1]
    revert this
    generalize pstart (fun c => (ps c).length) (c + 1) % 2 = e
    revert e
    decide
  refine WP.mono (colEnd_ok hc₁ h6₁ (pstart (fun c => (ps c).length) (c + 1) + 1) hc)
    fun s₂ ⟨hm, hlo, ha, hg, hrd, hwr, hsp⟩ => ?_
  have hg' : ∀ r, r ∉ clobW → s₂.gpr r = s₁.gpr r := fun r hr => hg r fun h => hr (by
    have := PR_clob (pstart (fun c => (ps c).length) (c + 1) + 1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | h | h
    · decide
    · decide
    · exact (this _ (by rw [h]; simp)).1
    · exact (this _ (by rw [h]; simp)).1)
  have hacc1 : acc s₁ < 2 ^ 128 := by
    rw [hv₁]
    have hle : ∀ q ∈ ps c, sv s1 q.1 * sv s1 q.2 ≤ 2 ^ 120 := ht.term_le hlt hc
    have := tsum_le hle
    have h9 : (ps c).length * 2 ^ 120 ≤ 9 * 2 ^ 120 := Nat.mul_le_mul_right _ (ht.len c hc).2
    have := h.accLt
    omega
  refine ⟨⟨fun r hr => (hg' r hr).trans (hI₁.gpr r hr), hrd.trans hI₁.rd, hwr.trans hI₁.wr, hsp.trans hI₁.sp,
      (hg _ (hreg _ (by simp))).trans hI₁.a6, ?_⟩,
    ⟨fun hn => ?_, fun hn => ?_⟩, ?_, fun c' hc' => ?_, ?_⟩
  · rw [hm]
    exact hI₁.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)
      (by rw [Z_eq]; omega))
  · rw [hg _ (hreg _ (by simp)), hg _ (hreg _ (by simp))]; exact hp₁.prod hn
  · rw [hg _ (hreg _ (by simp)), hg _ (hreg _ (by simp))]; exact hp₁.ops hn
  · rw [ha]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hacc1)
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hc' | rfl
    · rw [dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega), m₁]
      exact h.lt c' hc'
    · rw [dw_write_self, hlo]; exact Nat.mod_lt _ (by decide)
  · have ea : lv (fun c' => dw s₂.mem b (Z + 8 * c')) c = lv (fun c' => dw s.mem b (Z + 8 * c')) c :=
      lv_congr fun c' hc' => by
        rw [hm, dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega), m₁]
    have ek : dw s₂.mem b (Z + 8 * c) = acc s₁ % 2 ^ 58 := by rw [hm, dw_write_self, hlo]
    have hval := h.val
    rw [lv, ea, ek, ha, lv, ← hval, hv₁]
    rw [show 58 * (c + 1) = 58 * c + 58 by omega, Nat.pow_add]
    simp only [col]
    have hd := Nat.div_add_mod (acc s + tsum (fun q => sv s1 q.1 * sv s1 q.2) (ps c)) (2 ^ 58)
    generalize (2 : Nat) ^ (58 * c) = K
    generalize hX : acc s + tsum (fun q => sv s1 q.1 * sv s1 q.2) (ps c) = X at hd ⊢
    have h2 : K * (2 ^ 58 * (X / 2 ^ 58)) + K * (X % 2 ^ 58) =
        K * acc s + K * tsum (fun q => sv s1 q.1 * sv s1 q.2) (ps c) := by
      rw [← Nat.mul_add, hd, ← hX, Nat.mul_add]
    rw [Nat.mul_assoc]
    omega

/-- The columns, by induction. -/
theorem columns_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) (h6 : s1.gpr .a6 = M58) {ts : List Tm}
    {ps : Nat → List (Src × Src)} (ht : Tab ts ps) (hlt : SrcsLt s1 ts) :
    ∀ n ≤ 9, ∀ s, CInv b s1 ts ps 0 s →
      WP isa (.block ((List.range n).flatMap (pcol ts (fun c => (ps c).length)))) s (CInv b s1 ts ps n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (columns_ok hC h6 ht hlt n (by omega) s h) fun s₁ h₁ =>
      pcol_ok hC h6 ht hlt (by omega) h₁)

/-- `pipe ts`: the columns of the terms `ts` at `Z` and in the accumulator. -/
theorem pipe_ok {b A B O : Addr} {s1 : State} (hC : CoreOk 9 b A B O s1) (h6 : s1.gpr .a6 = M58) {ts : List Tm}
    {ps : Nat → List (Src × Src)} (ht : Tab ts ps) (hlt : SrcsLt s1 ts) :
    WP isa (.block (pipe ts (fun c => (ps c).length))) s1 (CInv b s1 ts ps 9) := by
  unfold pipe
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have hI₂ : PInv b s1 s₂ :=
    (PInv.keeps (s := s1) ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩ (rs := [.a4, .a5])
      ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₂.other _ hr.2, u₁.other _ hr.1],
       by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩ (by decide))
  have hz : acc s₂ = 0 := by
    simp only [acc]; rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  refine WP.block_append (WP.mono (ldN_ok hC ht.src 0 hI₂) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hI₃ := hI₂.keeps k₃ (by decide)
  refine WP.block_append (WP.mono (mulN_ok ts 0) fun s₄ ⟨e₄, k₄⟩ => ?_)
  have hI₄ := hI₃.keeps k₄ (PR_clob 0)
  refine WP.block_append (WP.mono (ldN_ok hC ht.src 1 hI₄) fun s₅ ⟨k₅, e₅⟩ => ?_)
  have hI₅ := hI₄.keeps k₅ (by decide)
  have hacc : acc s₅ = 0 := by
    simp only [acc] at hz ⊢
    rw [k₅.1 .a4 (by decide), k₅.1 .a5 (by decide), k₄.1 .a4 (by decide), k₄.1 .a5 (by decide),
      k₃.1 .a4 (by decide), k₃.1 .a5 (by decide), hz]
  refine columns_ok hC h6 ht hlt 9 (Nat.le_refl _) s₅ ⟨hI₅, ⟨fun hn => ?_, fun hn => ?_⟩, by rw [hacc]; decide,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [hacc]; rfl⟩
  · rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
    rw [show PR 0 = (Reg.a7, Reg.t0) from rfl] at e₄ ⊢
    rw [k₅.1 .a7 (by decide), k₅.1 .t0 (by decide), e₄ hn]
    obtain ⟨o1, o2⟩ := e₃ hn
    rw [o1, o2]
  · rw [show pstart (fun c => (ps c).length) 0 = 0 from rfl] at hn ⊢
    exact e₅ hn

/-! ## The columns' values

The columns of `mulPairs` and `sqPairs` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`),
for operands whose words are the limbs `aᵢ`, `bⱼ` and the doubled limbs at
`Y`: column `c` is `lo c + 2 hi c`, its terms below and past `2⁵²²`
(`mulCol_eq`, `sqCol_eq`), so that the columns' sum and `2⁵²²` times the
part past it are the product and twice that part (`mulCols_sum`,
`sqCols_sum`), which `2⁵²² ≡ 2` makes the product modulo `p` (`mod_cancel`).
-/

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Unsat

/-- The number of the limbs `f 0`, …, `f (n - 1)` in base `W`. -/
def lvW (W : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lvW W f n + W ^ n * f n

theorem lv_eq (f : Nat → Nat) : ∀ n, lv f n = lvW (2 ^ 58) f n
  | 0 => rfl
  | n + 1 => by rw [lv, lvW, lv_eq f n, Nat.pow_mul]

theorem sum_map_two {l : List Nat} {f : Nat → Nat} : (l.map fun i => 2 * f i).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_congr {l : List Nat} {f g : Nat → Nat} (h : ∀ i ∈ l, f i = g i) : (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem tsum_map {β : Type} (f : Src × Src → Nat) (g : β → Src × Src) (l : List β) :
    tsum f (l.map g) = (l.map fun x => f (g x)).sum := by
  simp only [tsum, List.map_map]; rfl

/-! ## The product -/

/-- Column `c`'s terms below `2⁵²²`. -/
def mlo (a b : Nat → Nat) (c : Nat) : Nat := (((List.range 9).filter fun i => i ≤ c).map fun i => a i * b (c - i)).sum

/-- Column `c`'s terms past `2⁵²²`. -/
def mhi (a b : Nat → Nat) (c : Nat) : Nat := (((List.range 9).filter fun i => c < i).map fun i => a i * b (c + 9 - i)).sum

theorem mulCol_eq (v : Src → Nat) (a b : Nat → Nat) (h4 : ∀ i < 9, v (.t4, 8 * i) = a i)
    (h5 : ∀ j < 9, v (.t5, 8 * j) = b j) (hY : ∀ j < 9, v (.a3, Y + 8 * j) = 2 * b j) {c : Nat} (hc : c < 9) :
    tsum (fun q => v q.1 * v q.2) (mulPairs c) = mlo a b c + 2 * mhi a b c := by
  unfold mulPairs mlo mhi
  rw [tsum_append, tsum_map, tsum_map, ← sum_map_two]
  congr 1
  · refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, h5 (c - i) (by omega)]
  · refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, hY (c + 9 - i) (by omega), Nat.mul_left_comm]

/-- The columns of a product. -/
theorem mulCols_sum (a b : Nat → Nat) :
    lv (fun c => mlo a b c + 2 * mhi a b c) 9 + 2 ^ 522 * lv (mhi a b) 9 = lv a 9 * lv b 9 + 2 * lv (mhi a b) 9 := by
  simp only [lv_eq]
  rw [show (2 : Nat) ^ 522 = (2 ^ 58) ^ 9 by rw [← Nat.pow_mul]]
  generalize (2 : Nat) ^ 58 = W
  simp only [lvW, mlo, mhi, List.range_succ, List.range_zero, List.nil_append, List.filter_cons, List.filter_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT,
    Nat.reduceAdd, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  grind

/-! ## The square -/

/-- Column `c`'s cross terms below `2⁵²²`, `aᵢ aⱼ` for `j < i`. -/
def scr (a : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun i => a i * a (c - i)).sum

/-- Column `c`'s square below `2⁵²²`. -/
def sdg (a : Nat → Nat) (c : Nat) : Nat := if c % 2 = 0 then a (c / 2) * a (c / 2) else 0

/-- Column `c`'s cross terms past `2⁵²²`. -/
def shc (a : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun i => a i * a (c + 9 - i)).sum

/-- Column `c`'s square past `2⁵²²`. -/
def shd (a : Nat → Nat) (c : Nat) : Nat := if c % 2 = 1 then a ((c + 9) / 2) * a ((c + 9) / 2) else 0

/-- Column `c` of a square past `2⁵²²`. -/
def shi (a : Nat → Nat) (c : Nat) : Nat := 2 * shc a c + shd a c

theorem sqCol_eq (v : Src → Nat) (a : Nat → Nat) (h4 : ∀ i < 9, v (.t4, 8 * i) = a i)
    (hY : ∀ j < 9, v (.a3, Y + 8 * j) = 2 * a j) {c : Nat} (hc : c < 9) :
    tsum (fun q => v q.1 * v q.2) (sqPairs c) = 2 * scr a c + sdg a c + 2 * shi a c := by
  unfold sqPairs scr sdg shi shc shd
  rw [tsum_append, tsum_append, tsum_append, tsum_map, tsum_map, ← sum_map_two, ← sum_map_two]
  have e1 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun x =>
      v ((Reg.t4, 8 * x), (Reg.a3, Y + 8 * (c - x))).1 * v ((Reg.t4, 8 * x), (Reg.a3, Y + 8 * (c - x))).2).sum =
      (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun i => 2 * (a i * a (c - i))).sum := by
    refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, hY (c - i) (by omega), Nat.mul_left_comm]
  have e2 : (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun x =>
      v ((Reg.a3, Y + 8 * x), (Reg.a3, Y + 8 * (c + 9 - x))).1 *
        v ((Reg.a3, Y + 8 * x), (Reg.a3, Y + 8 * (c + 9 - x))).2).sum =
      (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun i => 2 * (2 * (a i * a (c + 9 - i)))).sum := by
    refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [hY i hi.1, hY (c + 9 - i) (by omega)]
    rw [Nat.mul_assoc, Nat.mul_left_comm (a i), ← Nat.mul_assoc 2 2]
  rw [e1, e2, sum_map_two, sum_map_two, sum_map_two]
  have d1 : tsum (fun q => v q.1 * v q.2)
      (if c % 2 = 0 then [((Reg.t4, 8 * (c / 2)), (Reg.t4, 8 * (c / 2)))] else []) =
      if c % 2 = 0 then a (c / 2) * a (c / 2) else 0 := by
    split
    · rw [tsum_singleton, h4 _ (by omega)]
    · rfl
  have d2 : tsum (fun q => v q.1 * v q.2)
      (if c % 2 = 1 then [((Reg.t4, 8 * ((c + 9) / 2)), (Reg.a3, Y + 8 * ((c + 9) / 2)))] else []) =
      2 * (if c % 2 = 1 then a ((c + 9) / 2) * a ((c + 9) / 2) else 0) := by
    split
    · rw [tsum_singleton]
      dsimp only
      rw [h4 _ (by omega), hY _ (by omega), Nat.mul_left_comm]
    · rfl
  rw [d1, d2]
  omega

/-- The columns of a square. -/
theorem sqCols_sum (a : Nat → Nat) :
    lv (fun c => 2 * scr a c + sdg a c + 2 * shi a c) 9 + 2 ^ 522 * lv (shi a) 9 =
      lv a 9 * lv a 9 + 2 * lv (shi a) 9 := by
  simp only [lv_eq]
  rw [show (2 : Nat) ^ 522 = (2 ^ 58) ^ 9 by rw [← Nat.pow_mul]]
  generalize (2 : Nat) ^ 58 = W
  simp only [lvW, scr, sdg, shi, shc, shd, List.range_succ, List.range_zero, List.nil_append, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceSub, Nat.reduceLeDiff,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, decide_true, decide_false, Bool.false_eq_true,
    ↓reduceIte, List.cons_append, and_self, and_true, and_false, Nat.lt_irrefl]
  grind

/-! ## Modulo `p` -/

theorem lv_fold (f g : Nat → Nat) {C : Nat} (h01 : f 0 + 2 ^ 58 * f 1 = g 0 + 2 ^ 58 * g 1 + 2 * C)
    (h : ∀ j, 2 ≤ j → j < 9 → f j = g j) : lv f 9 = lv g 9 + 2 * C := by
  simp only [lv, Nat.reduceMul, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  rw [h 2 (by decide) (by decide), h 3 (by decide) (by decide), h 4 (by decide) (by decide), h 5 (by decide) (by decide),
    h 6 (by decide) (by decide), h 7 (by decide) (by decide), h 8 (by decide) (by decide)]
  omega


theorem mod_cancel {x y K : Nat} (h : x + 2 ^ 522 * K = y + 2 * K) : x % p = y % p := by
  have e : (2 : Nat) ^ 522 = 2 * p + 2 := by
    have h1 : (2 : Nat) ^ 522 = 2 ^ 521 * 2 := Nat.pow_succ ..
    have h2 := Nat.one_le_two_pow (n := 521)
    show (2 : Nat) ^ 522 = 2 * (2 ^ 521 - 1) + 2
    omega
  rw [e] at h
  have : y = x + p * (2 * K) := by
    have : (2 * p + 2) * K = p * (2 * K) + 2 * K := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  rw [this, Nat.add_mul_mod_self_left]

end VG.Proof.Weierstrass.RISCV64.P521Unsat
