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

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: limbs

The numbers a function's nine words stand for (`Impl/Weierstrass/RISCV64/P521Unsat.lean`):
`lw X i`, word `i` of a number `X` (GenWide's `xv`, for operands in memory),
`uv X`, the number of its words as limbs, `Σ lw X i 2⁵⁸ⁱ`, and `Tight X`;
what every kernel starts from (`CoreOk`, GenWide's), the reads of its
operands and the writes of its working space, and the copy of the limbs at
`Z` to `[t2]` (`copyZ_ok`).
-/

@[expose] public section

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

end VG.Proof.Weierstrass.RISCV64.P521Unsat
