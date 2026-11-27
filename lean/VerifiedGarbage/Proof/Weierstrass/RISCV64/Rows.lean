module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Rows
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sqr
public import VerifiedGarbage.Proof.Framework.RISCV64.Sched
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn

/-!
# Montgomery's multiplication by rows, in registers, on RISC-V: the proofs

`fast` (`Impl/Weierstrass/RISCV64/Rows.lean`) is Montgomery's multiplication
(`fastWith_ok`, `tail_ok`) for a layout whose registers are apart (`LOk`), from the steps up:

* a multiply-accumulate step (`mac_ok`, `mac1_ok`) and a row of them
  (`row_ok`, `row1_ok`);
* the product (`mulProd_ok`) and the square (`sqrProd_ok`);
* the rounds of Montgomery's reduction (`round_ok`, `red_ok`): after `i`
  rounds, the window, `TOP` and the product's words above are `V` with
  `2^(64 i) V = P + Q m` for some `Q < 2^(64 i)`;
* the final subtraction (`csub_ok`), and the registers kept (`save_ok`,
  `restore_ok`).

The emitted code is in another order, which changes nothing (`WP.sched`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Rows

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Rows
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)
open VG.Proof.Weierstrass.RISCV64.GenWide (colsV_congr colsV_succ colsV_shift colsV_lt colsV_split rowTerm sumN sumN_add
  sumN_congr rows_sum sq_sum wp_mulhu xv disj_sub disj_symm)
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.Weierstrass.RISCV64.P256Field (upd_keeps sltu_toNat)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## The layout -/

/-- The registers of a layout that are not its own choice. -/
abbrev base : List Reg := [C, .t4, .t5, .a3, .t2]

/-- The layout's registers are apart, and its places in the working space too. -/
structure LOk (L : Lay) : Prop where
  k4 : 4 ≤ L.k
  k8 : L.k ≤ 8
  vi : ∀ i < L.k, ∀ j < L.k, L.VL.getD i .t0 = L.VL.getD j .t0 → i = j
  vm : ∀ i < L.k, L.VL.getD i .t0 ∈ L.VL
  vo : ∀ r ∈ L.VL, r ∉ base ++ L.LO ++ L.HI ++ L.AL
  ai : ∀ i < L.k, ∀ j < L.k, L.A i = L.A j → i = j
  am : ∀ i < L.k, L.A i ∈ L.AL
  ao : ∀ r ∈ L.AL, r ∉ base ++ L.LO ++ L.HI
  l0 : 0 < L.LO.length
  h0 : 0 < L.HI.length
  lo : ∀ r ∈ L.LO, r ∉ base ++ L.HI
  hi : ∀ r ∈ L.HI, r ∉ base
  ki : ∀ i < L.KR.length, ∀ j < L.KR.length, L.KR.getD i .s6 = L.KR.getD j .s6 → i = j
  ko : ∀ r ∈ L.KR, r ∉ base
  sv8 : L.sv % 8 = 0
  pp8 : L.pp % 8 = 0
  svp : L.sv + 8 * L.KR.length ≤ L.pp
  pp2 : L.pp + 16 * L.k ≤ 2048

theorem getD_mem {l : List Reg} {i : Nat} (h : i < l.length) (d : Reg) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

variable {L : Lay}

theorem LOk.k0 (h : LOk L) : 0 < L.k := Nat.lt_of_lt_of_le (by decide) h.k4

theorem LOk.loM (h : LOk L) (j : Nat) : L.lo j ∈ L.LO := getD_mem (Nat.mod_lt _ h.l0) _
theorem LOk.hiM (h : LOk L) (j : Nat) : L.hi j ∈ L.HI := getD_mem (Nat.mod_lt _ h.h0) _
theorem LOk.vM (h : LOk L) (i : Nat) : L.V i ∈ L.VL := h.vm _ (Nat.mod_lt _ h.k0)

theorem LOk.vinj (h : LOk L) {i j : Nat} (e : L.V i = L.V j) : i % L.k = j % L.k :=
  h.vi _ (Nat.mod_lt _ h.k0) _ (Nat.mod_lt _ h.k0) e

/-- Registers less than `k` apart are different. -/
theorem LOk.vne (h : LOk L) {i j : Nat} (h1 : i < j) (h2 : j < i + L.k) : L.V i ≠ L.V j := fun e => by
  have e := h.vinj e
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h1
  have : (d + 1) % L.k = 0 := by
    have := Nat.sub_mod_eq_zero_of_mod_eq (k := L.k) e.symm
    rwa [show i + d + 1 - i = d + 1 by omega_arith] at this
  rw [Nat.mod_eq_of_lt (by omega_arith)] at this
  omega_arith

theorem Lay.V_add (i : Nat) : L.V (i + L.k) = L.V i := by simp only [Lay.V, Nat.add_mod_right]

/-- The registers the steps of a row write. -/
abbrev clobR (L : Lay) : List Reg := C :: (L.LO ++ L.HI ++ L.VL)

/-- What is apart from a register of a list, from what is apart from the list. -/
theorem ne_of_out {l : List Reg} {r q : Reg} (h : r ∉ l) (hq : q ∈ l) : r ≠ q := fun e => h (e ▸ hq)

/-- A register of the running value is apart from the temporaries and the carry. -/
theorem LOk.vt (h : LOk L) (i j : Nat) : L.V i ∉ [L.lo j, L.hi j, C] := by
  have := h.vo _ (h.vM i)
  simp only [List.mem_append, not_or] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨ne_of_out this.1.1.2 (h.loM j), ne_of_out this.1.2 (h.hiM j), ne_of_out this.1.1.1 (by decide)⟩

/-- A register that the rows do not write. -/
theorem out_iff {r : Reg} : r ∉ clobR L ↔ r ≠ C ∧ r ∉ L.LO ∧ r ∉ L.HI ∧ r ∉ L.VL := by
  simp only [List.mem_cons, List.mem_append, not_or, and_assoc, ne_eq]

theorem LOk.baseO (h : LOk L) {r : Reg} (hr : r ∈ base) (hc : r ≠ C) : r ∉ clobR L := by
  refine out_iff.mpr ⟨hc, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
  · have := h.lo r hl; simp only [List.mem_append, not_or] at this; exact this.1 hr
  · exact h.hi r hl hr
  · have := h.vo r hl; simp only [List.mem_append, not_or] at this; exact this.1.1.1 hr

theorem LOk.aO (h : LOk L) {r : Reg} (hr : r ∈ L.AL) : r ∉ clobR L := by
  have ha := h.ao r hr
  simp only [List.mem_append, not_or] at ha
  refine out_iff.mpr ⟨ne_of_out ha.1.1 (by decide), ha.1.2, ha.2, fun hv => ?_⟩
  have := h.vo r hv; simp only [List.mem_append, not_or] at this; exact this.2 hr

theorem ctx_of {b : Addr} {s s' : State} (h : Ctx b s) (h3 : s'.gpr .a3 = s.gpr .a3) (hw : s'.wr = s.wr) : Ctx b s' :=
  VG.Proof.Weierstrass.RISCV64.GenWide.ctx_of h h3 hw

/-! ## A step -/

private theorem mac1_nat {x y t lo hi c u : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (ht : t < 2 ^ 64)
    (hu : u < 2 ^ 64) (hp : lo + 2 ^ 64 * hi = x * y) (h : u + 2 ^ 64 * c = lo + t) :
    u + 2 ^ 64 * (hi + c) = x * y + t ∧ hi + c < 2 ^ 64 := by
  obtain hxy : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  constructor <;> omega_arith

/-- `v + 2⁶⁴ C := x y + v + C`, or without `v`. -/
theorem mac_ok {acc : Bool} {lo hi x y v : Reg} (hlh : lo ≠ hi) (hlc : lo ≠ C) (hhc : hi ≠ C) (hx : x ∉ [lo, v])
    (hy : y ∉ [lo, v]) (hv : v ∉ [lo, hi, C]) {s : State} :
    WP isa (.block (mac acc lo hi x y v)) s fun s' =>
      (s'.gpr v).toNat + 2 ^ 64 * (s'.gpr C).toNat =
        (s.gpr x).toNat * (s.gpr y).toNat + (if acc then (s.gpr v).toNat else 0) + (s.gpr C).toNat ∧
      Keeps [v, lo, hi, C] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hy hv
  obtain ⟨xl, xv⟩ := hx
  obtain ⟨yl, yv⟩ := hy
  obtain ⟨vl, vh, vc⟩ := hv
  obtain hp := mul_words (s.gpr x) (s.gpr y)
  cases acc
  · simp only [mac, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_add fun s3 u3 => wp_sltu fun s4 u4 => wp_add fun s5 u5 =>
      WP.block_nil ?_
    obtain a2 : s2.gpr v = s.gpr x * s.gpr y := by rw [u2.other _ vh, u1.gpr]
    obtain c2 : s2.gpr C = s.gpr C := by rw [u2.other _ (Ne.symm hhc), u1.other _ (Ne.symm vc)]
    obtain h2 : s2.gpr hi = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xv, u1.other _ yv]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr C := u3.gpr
    obtain l4 : s4.gpr lo = if s2.gpr v + s2.gpr C < s2.gpr C then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vc)]
    obtain e1 := carry (s2.gpr v) (s2.gpr C)
    rw [← l4, ← v3, a2, c2] at e1
    obtain h4 : s4.gpr hi = s2.gpr hi := by rw [u4.other _ (Ne.symm hlh), u3.other _ (Ne.symm vh)]
    obtain c5 : (s5.gpr C).toNat = ((s2.gpr hi).toNat + (s4.gpr lo).toNat) % 2 ^ 64 := by
      rw [u5.gpr, BitVec.toNat_add, h4]
    rw [← h2] at hp
    obtain ⟨n1, n2⟩ := mac1_nat (s.gpr x).isLt (s.gpr y).isLt (s.gpr C).isLt (s3.gpr v).isLt hp e1
    refine ⟨?_, ?_⟩
    · rw [c5, Nat.mod_eq_of_lt n2, u5.other _ vc, u4.other _ vl]; exact n1
    · exact ((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans (upd_keeps u5)
        |>.mono (by simp)
  · simp only [mac, ↓reduceIte]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_add fun s3 u3 => wp_sltu fun s4 u4 => wp_add fun s5 u5 =>
      wp_add fun s6 u6 => wp_sltu fun s7 u7 => wp_add fun s8 u8 => WP.block_nil ?_
    obtain a2 : s2.gpr lo = s.gpr x * s.gpr y := by rw [u2.other _ hlh, u1.gpr]
    obtain h2 : s2.gpr hi = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xl, u1.other _ yl]
    obtain v2 : s2.gpr v = s.gpr v := by rw [u2.other _ vh, u1.other _ vl]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr lo := u3.gpr
    obtain l4 : s4.gpr lo = if s2.gpr v + s2.gpr lo < s2.gpr lo then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vl)]
    obtain e1 := carry (s2.gpr v) (s2.gpr lo)
    rw [← l4, ← v3, a2, v2] at e1
    obtain h4 : s4.gpr hi = s2.gpr hi := by rw [u4.other _ (Ne.symm hlh), u3.other _ (Ne.symm vh)]
    obtain l5 : s5.gpr lo = s2.gpr hi + s4.gpr lo := by rw [u5.gpr, h4]
    obtain v5 : s5.gpr v = s3.gpr v := by rw [u5.other _ vl, u4.other _ vl]
    obtain c5 : s5.gpr C = s.gpr C := by
      rw [u5.other _ (Ne.symm hlc), u4.other _ (Ne.symm hlc), u3.other _ (Ne.symm vc), u2.other _ (Ne.symm hhc),
        u1.other _ (Ne.symm hlc)]
    obtain h7 : s7.gpr hi = if s5.gpr v + s5.gpr C < s5.gpr C then 1 else 0 := by
      rw [u7.gpr, u6.gpr, u6.other _ (Ne.symm vc)]
    obtain e2 := carry (s5.gpr v) (s5.gpr C)
    rw [← h7, v5, c5] at e2
    obtain l7 : s7.gpr lo = s5.gpr lo := by rw [u7.other _ hlh, u6.other _ (Ne.symm vl)]
    obtain c8 : (s8.gpr C).toNat = (((s2.gpr hi).toNat + (s4.gpr lo).toNat) % 2 ^ 64 + (s7.gpr hi).toNat) % 2 ^ 64 := by
      rw [u8.gpr, BitVec.toNat_add, l7, l5, BitVec.toNat_add]
    rw [← h2] at hp
    rw [Nat.add_comm (s.gpr v).toNat] at e1
    obtain ⟨n1, n2⟩ := GenWide.mac_nat (s.gpr x).isLt (s.gpr y).isLt (s.gpr v).isLt (s.gpr C).isLt hp e1 e2
    refine ⟨?_, ?_⟩
    · rw [c8, Nat.mod_eq_of_lt (a := (s2.gpr hi).toNat + _) (by omega_using [n2]), Nat.mod_eq_of_lt n2,
        u8.other _ vc, u7.other _ vh, u6.gpr, v5, c5]
      exact n1
    · exact ((((((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
        (upd_keeps u5)).trans (upd_keeps u6)).trans (upd_keeps u7)).trans (upd_keeps u8)).mono (by simp)

/-- `v + 2⁶⁴ C := x y + v`, or without `v`. -/
theorem mac1_ok {acc : Bool} {lo x y v : Reg} (hlc : lo ≠ C) (hx : x ∉ [lo, v]) (hy : y ∉ [lo, v])
    (hv : v ∉ [lo, C]) {s : State} :
    WP isa (.block (mac1 acc lo x y v)) s fun s' =>
      (s'.gpr v).toNat + 2 ^ 64 * (s'.gpr C).toNat =
        (s.gpr x).toNat * (s.gpr y).toNat + (if acc then (s.gpr v).toNat else 0) ∧
      Keeps [v, lo, C] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hy hv
  obtain ⟨xl, xv⟩ := hx
  obtain ⟨yl, yv⟩ := hy
  obtain ⟨vl, vc⟩ := hv
  obtain hp := mul_words (s.gpr x) (s.gpr y)
  cases acc
  · simp only [mac1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => WP.block_nil ?_
    refine ⟨?_, ((upd_keeps u1).trans (upd_keeps u2)).mono (by simp)⟩
    rw [u2.other _ vc, u1.gpr, u2.gpr, u1.other _ xv, u1.other _ yv]; exact hp
  · simp only [mac1, ↓reduceIte]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_add fun s3 u3 => wp_sltu fun s4 u4 => wp_add fun s5 u5 =>
      WP.block_nil ?_
    obtain a2 : s2.gpr lo = s.gpr x * s.gpr y := by rw [u2.other _ hlc, u1.gpr]
    obtain h2 : s2.gpr C = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xl, u1.other _ yl]
    obtain v2 : s2.gpr v = s.gpr v := by rw [u2.other _ vc, u1.other _ vl]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr lo := u3.gpr
    obtain l4 : s4.gpr lo = if s2.gpr v + s2.gpr lo < s2.gpr lo then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vl)]
    obtain e1 := carry (s2.gpr v) (s2.gpr lo)
    rw [← l4, ← v3, a2, v2] at e1
    obtain h4 : s4.gpr C = s2.gpr C := by rw [u4.other _ (Ne.symm hlc), u3.other _ (Ne.symm vc)]
    obtain c5 : (s5.gpr C).toNat = ((s2.gpr C).toNat + (s4.gpr lo).toNat) % 2 ^ 64 := by
      rw [u5.gpr, BitVec.toNat_add, h4]
    rw [← h2] at hp
    rw [Nat.add_comm (s.gpr v).toNat] at e1
    obtain ⟨n1, n2⟩ := mac1_nat (s.gpr x).isLt (s.gpr y).isLt (s.gpr v).isLt (s3.gpr v).isLt hp e1
    refine ⟨?_, ?_⟩
    · rw [c5, Nat.mod_eq_of_lt n2, u5.other _ vc, u4.other _ vl]; exact n1
    · exact ((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans (upd_keeps u5)
        |>.mono (by simp)

/-! ## A row -/

/-- The number in the `n` registers `V i …`. -/
abbrev rv (L : Lay) (s : State) (i n : Nat) : Nat := colsV (fun j => (s.gpr (L.V (i + j))).toNat) n

/-- After `n` steps of a row from `V i` from `s0`, its start value `V0`. -/
structure RowInv (L : Lay) (x : Nat → Reg) (y V0 i n : Nat) (s0 s : State) : Prop where
  gpr : ∀ r, r ∉ L.LO → r ∉ L.HI → r ≠ C → (∀ j < n, r ≠ L.V (i + j)) → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : rv L s i n + (2 ^ 64) ^ n * (s.gpr C).toNat = V0 + colsV (fun j => (s0.gpr (x j)).toNat) n * y

theorem RowInv.out {x : Nat → Reg} {y V0 i n : Nat} {s0 s : State} (hL : LOk L) (h : RowInv L x y V0 i n s0 s) (r : Reg)
    (hr : r ∉ clobR L) : s.gpr r = s0.gpr r := by
  obtain ⟨a, b, c, d⟩ := out_iff.mp hr
  exact h.gpr r b c a fun j _ e => d (e ▸ hL.vM _)

private theorem row_alg {R E c v c' xy w Cin V0 S : Nat} (hv : R + E * c = V0 + S)
    (e : v + 2 ^ 64 * c' = xy + w + c) (hC : Cin = E * 2 ^ 64 * c') :
    R + E * v + Cin = V0 + E * w + (S + E * xy) := by
  obtain key : E * v + E * 2 ^ 64 * c' = E * xy + E * w + E * c := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e]
  omega_arith

/-- A register apart from the temporaries, the carry and the row's words. -/
theorem keep_mac {v lo hi r : Reg} {s s' : State} (k : Keeps [v, lo, hi, C] s s') (hv : r ≠ v) (hl : r ≠ lo)
    (hh : r ≠ hi) (hc : r ≠ C) : s'.gpr r = s.gpr r := k.1 r (by simp [hv, hl, hh, hc])

/-- The row, its start value the registers' (`acc`) or zero, and the carry in. -/
theorem row_ok (hL : LOk L) {acc : Bool} {x : Nat → Reg} {y : Reg} {i n : Nat} {s0 : State} (hx : ∀ j < n, x j ∉ clobR L)
    (hn : n ≤ L.k) (hy : y ∉ L.LO ∧ y ∉ L.HI ∧ y ≠ C) (hyv : ∀ j < n, y ≠ L.V (i + j)) :
    ∀ j ≤ n, WP isa (.block (row L acc x y i j)) s0
      (RowInv L x (s0.gpr y).toNat ((if acc then rv L s0 i j else 0) + (s0.gpr C).toNat) i j s0)
  | 0, _ => WP.block_nil ⟨fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl, by simp [colsV]⟩
  | j + 1, hj => by
    unfold row
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (row_ok hL hx hn hy hyv j (by omega_arith)) fun s h => ?_)
    obtain vo := hL.vt (i + j) j
    obtain ⟨x0, x1, x2, x3⟩ := out_iff.mp (hx j (by omega_arith))
    obtain lM := hL.loM j
    obtain hM := hL.hiM j
    obtain lo := hL.lo _ lM
    simp only [List.mem_append, not_or] at lo
    obtain hO := hL.hi _ hM
    refine WP.mono (mac_ok (acc := acc) (x := x j) (y := y) (v := L.V (i + j)) (ne_of_out lo.2 hM)
      (ne_of_out lo.1 (by decide)) (ne_of_out hO (by decide))
      (by simp [ne_of_out x1 lM, ne_of_out x3 (hL.vM (i + j))])
      (by simp [ne_of_out hy.1 lM, hyv j (by omega_arith)]) vo) fun s2 ⟨e2, k2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
    obtain dis : ∀ l < j, L.V (i + l) ≠ L.V (i + j) := fun l hl => hL.vne (by omega_arith) (by omega_arith)
    obtain y1 : s.gpr y = s0.gpr y := h.gpr y hy.1 hy.2.1 hy.2.2 fun l hl => hyv l (by omega_arith)
    obtain x1' : s.gpr (x j) = s0.gpr (x j) := h.out hL _ (hx j (by omega_arith))
    obtain vv := hL.vo _ (hL.vM (i + j))
    simp only [List.mem_append, not_or] at vv
    obtain v1 : s.gpr (L.V (i + j)) = s0.gpr (L.V (i + j)) := h.gpr _ vv.1.1.2 vv.1.2 vo.2.2 fun l hl => Ne.symm (dis l hl)
    rw [x1', y1, v1] at e2
    refine ⟨fun r hl hh hc hd => ?_, by rw [k2.2.1, h.mem], by rw [k2.2.2.1, h.rd], by rw [k2.2.2.2.1, h.wr],
      by rw [k2.2.2.2.2, h.sp], ?_⟩
    · rw [keep_mac k2 (hd j (by omega_arith)) (ne_of_out hl lM) (ne_of_out hh hM) hc,
        h.gpr r hl hh hc fun l hl => hd l (by omega_arith)]
    · have hv := h.val
      obtain low : rv L s2 i j = rv L s i j := colsV_congr fun l hl => by
        obtain vl := hL.vt (i + l) j
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vl
        rw [keep_mac k2 (dis l hl) vl.1 vl.2.1 vl.2.2]
      rw [show rv L s2 i (j + 1) = rv L s2 i j + (2 ^ 64) ^ j * (s2.gpr (L.V (i + j))).toNat from rfl, low,
        colsV_succ, Nat.add_mul, Nat.mul_assoc]
      obtain alg := row_alg hv e2 (Cin := (2 ^ 64) ^ (j + 1) * (s2.gpr C).toNat) (by rw [Nat.pow_succ])
      rw [alg]
      cases acc
      · simp
      · simp only [↓reduceIte, rv, colsV_succ]; omega_arith

private theorem row1_alg {R W Xn y c' c E x v w B : Nat} (hv : R + E * c' = W + c + Xn * y)
    (e : v + B * c = x * y + w) : v + B * R + E * B * c' = w + B * W + (x + B * Xn) * y := by grind

/-- A row without the carry in. -/
theorem row1_ok (hL : LOk L) {acc : Bool} {x : Nat → Reg} {y : Reg} {i n : Nat} {s0 : State}
    (hx : ∀ j < n + 1, x j ∉ clobR L) (hn : n < L.k) (hy : y ∉ L.LO ∧ y ∉ L.HI ∧ y ≠ C)
    (hyv : ∀ j < n + 1, y ≠ L.V (i + j)) :
    WP isa (.block (row1 L acc x y i n)) s0
      (RowInv L x (s0.gpr y).toNat (if acc then rv L s0 i (n + 1) else 0) i (n + 1) s0) := by
  unfold row1
  obtain vo := hL.vt i 0
  obtain ⟨x0, x1, x2, x3⟩ := out_iff.mp (hx 0 (by omega_arith))
  obtain lM := hL.loM 0
  obtain lo := hL.lo _ lM
  simp only [List.mem_append, not_or] at lo
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  obtain yv0 : y ≠ L.V i := hyv 0 (by omega_arith)
  refine WP.block_append (WP.mono (mac1_ok (acc := acc) (x := x 0) (y := y) (v := L.V i) (ne_of_out lo.1 (by decide))
    (by simp [ne_of_out x1 lM, ne_of_out x3 (hL.vM i)]) (by simp [ne_of_out hy.1 lM, yv0]) (by simp [vo.1, vo.2.2]))
    fun s2 ⟨e2, k2⟩ => ?_)
  obtain g2 : ∀ r, r ∉ L.LO → r ≠ C → r ≠ L.V i → s2.gpr r = s0.gpr r := fun r hr hc hi =>
    k2.1 r (by simp [ne_of_out hr lM, hc, hi])
  obtain y2 : s2.gpr y = s0.gpr y := g2 y hy.1 hy.2.2 yv0
  refine WP.mono (row_ok hL (acc := acc) (i := i + 1) (n := n) (x := fun j => x (j + 1))
    (fun j hj => hx (j + 1) (by omega_arith)) (by omega_arith) hy
    (fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact hyv _ (by omega_arith)) n (Nat.le_refl _))
    fun s3 h3 => ?_
  obtain nv : ∀ j < n, L.V (i + (j + 1)) ≠ L.V i := fun j hj => Ne.symm (hL.vne (by omega_arith) (by omega_arith))
  obtain vv := hL.vo _ (hL.vM i)
  simp only [List.mem_append, not_or] at vv
  obtain e3 : s3.gpr (L.V i) = s2.gpr (L.V i) := h3.gpr _ vv.1.1.2 vv.1.2 vo.2.2 fun j hj => by
    rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact Ne.symm (nv j hj)
  refine ⟨fun r hl hh hc hd => ?_, by rw [h3.mem, k2.2.1], by rw [h3.rd, k2.2.2.1], by rw [h3.wr, k2.2.2.2.1],
    by rw [h3.sp, k2.2.2.2.2], ?_⟩
  · rw [h3.gpr r hl hh hc fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact hd _ (by omega_arith),
      g2 r hl hc (hd 0 (by omega_arith))]
  · have hv := h3.val
    rw [y2] at hv
    obtain idx : ∀ t : State, rv L t (i + 1) n = colsV (fun j => (t.gpr (L.V (i + (j + 1)))).toNat) n := fun t =>
      colsV_congr fun j _ => by rw [show i + 1 + j = i + (j + 1) by omega_arith]
    obtain r2 : rv L s2 (i + 1) n = rv L s0 (i + 1) n := colsV_congr fun j hj => by
      obtain w := hL.vo _ (hL.vM (i + 1 + j))
      simp only [List.mem_append, not_or] at w
      rw [g2 _ w.1.1.2 (ne_of_out w.1.1.1 (by decide)) (by
        rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact nv j hj)]
    obtain x2' : colsV (fun j => (s2.gpr (x (j + 1))).toNat) n = colsV (fun j => (s0.gpr (x (j + 1))).toNat) n :=
      colsV_congr fun j hj => by
        obtain ⟨a, b, _, d⟩ := out_iff.mp (hx (j + 1) (by omega_arith))
        rw [g2 _ b a (ne_of_out d (hL.vM i))]
    rw [r2, idx s3, idx s0, x2'] at hv
    rw [rv, colsV_shift, colsV_shift (fun j => (s0.gpr (x j)).toNat), rv, colsV_shift, Nat.add_zero, e3, Nat.pow_succ]
    refine (row1_alg hv e2).trans ?_
    cases acc
    · simp
    · simp only [↓reduceIte]

/-! ## The operands -/

/-- The product's place. -/
abbrev PR (L : Lay) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 L.pp, 16 * L.k⟩

theorem LOk.p (hL : LOk L) {j : Nat} (hj : j < 2 * L.k) : L.P j + 8 ≤ 2048 ∧ L.P j % 8 = 0 := by
  have := hL.pp2; have := hL.pp8
  simp only [Lay.P]; omega_arith

/-- A word of the product stored. -/
theorem PR_store (hL : LOk L) {b : Addr} {m m' : Mem} {j : Nat} (hj : j < 2 * L.k) (h : Frame [PR L b] m m') (v : BitVec 64) :
    Frame [PR L b] m (m'.writeW (b + BitVec.ofNat 64 (L.P j)) v) := by
  have := hL.pp2
  exact h.writeW (List.mem_singleton_self _) _ (Offset.contains b (by simp only [Lay.P]; omega_arith)
    (by simp only [Lay.P]; omega_arith) (by omega_arith))

theorem P_write (hL : LOk L) {m : Mem} {b : Addr} {i j : Nat} (hi : i < 2 * L.k) (hj : j < 2 * L.k) (v : BitVec 64) :
    dw (m.writeW (b + BitVec.ofNat 64 (L.P j)) v) b (L.P i) = if i = j then v.toNat else dw m b (L.P i) := by
  obtain ⟨h1, -⟩ := hL.p hi
  obtain ⟨h2, -⟩ := hL.p hj
  simp only [Lay.P] at h1 h2 ⊢
  split
  · rename_i e; subst e; exact dw_write_self ..
  · exact dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- After `n` words of `[t4]` loaded. -/
structure LoadInv (L : Lay) (A : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ L.AL → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, (s.gpr (L.A j)).toNat = dw s0.mem A (8 * j)

theorem LOk.aB (hL : LOk L) {r : Reg} (hr : r ∈ base) : r ∉ L.AL := fun h => by
  have := hL.ao r h; simp only [List.mem_append, not_or] at this; exact this.1.1 hr

theorem loadA_ok (hL : LOk L) {A : Addr} {s0 : State} (h4 : s0.gpr .t4 = A) (hal : A.toNat % 8 = 0)
    (hin : ∀ i < L.k, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (loadA L)) s0 (LoadInv L A s0 L.k) := by
  have hk := hL.k8
  refine wp_range_flatMap (M := isa) (LoadInv L A s0) (fun n s hn h => ?_) L.k (Nat.le_refl _) s0
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine wp_ld (by omega_arith) (by rw [h.gpr _ (hL.aB (by decide)), h4])
    (al8 hal (by omega_arith)) (by rw [h.rd, h.wr]; exact hin n hn) fun s1 u1 => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u1.other r (ne_of_out hr (hL.am n hn)), h.gpr r hr],
    by rw [u1.mem, h.mem], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], fun j hj => ?_⟩
  by_cases e : j = n
  · subst e; rw [u1.gpr, h.mem]; rfl
  · rw [u1.other _ fun e' => e (hL.ai j (by omega_arith) n hn e')]; exact h.val j (by omega_arith)

/-! ## The product -/

/-- The start value of row `i`. -/
abbrev W (L : Lay) (i : Nat) (s : State) (j n : Nat) : Nat := if decide (0 < i) then rv L s j n else 0

/-- What the product needs. -/
structure MulOk (L : Lay) (b A B : Addr) (X : Nat → Nat) (s : State) : Prop where
  ctx : Ctx b s
  regs : ∀ j < L.k, (s.gpr (L.A j)).toNat = X j
  b' : s.gpr .t5 = B
  bal : B.toNat % 8 = 0
  bin : ∀ i < L.k, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  bdis : ∀ i < L.k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (PR L b)

/-- After `i` rows of the product. -/
structure MulInv (L : Lay) (b B : Addr) (X : Nat → Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ Y :: clobR L → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR L b] s0.mem s.mem
  val : colsV (fun j => dw s.mem b (L.P j)) i + (2 ^ 64) ^ i * W L i s i L.k = colsV X L.k * xv s0.mem B i

private theorem mulRow_alg {L E w v R y bv X S B : Nat} (hv : L + E * w = X * bv)
    (e : v + B * R = w + S) (hS : S = X * y) : L + E * v + E * B * R = X * (bv + E * y) := by
  subst hS
  calc L + E * v + E * B * R = L + E * (v + B * R) := by grind
    _ = (L + E * w) + E * (X * y) := by rw [e]; grind
    _ = _ := by rw [hv]; grind

theorem dwB_frame {b B : Addr} {m m' : Mem} {i : Nat} (hf : Frame [PR L b] m m')
    (hd : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (PR L b)) : dw m' B (8 * i) = dw m B (8 * i) :=
  dw_frame hf fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd

/-- The operand's registers, through what the rows write. -/
theorem MulInv.regs (hL : LOk L) {b A B : Addr} {X : Nat → Nat} {s0 s : State} {i : Nat} (h0 : MulOk L b A B X s0)
    (h : MulInv L b B X s0 i s) : ∀ j < L.k, (s.gpr (L.A j)).toNat = X j := fun j hj => by
  obtain a := hL.aO (hL.am j hj)
  rw [h.gpr _ (by
    simp only [List.mem_cons (a := L.A j) (b := Y), not_or]
    exact ⟨fun e => hL.aB (r := Y) (by decide) (e ▸ hL.am j hj), a⟩), h0.regs j hj]

theorem mulRow_ok (hL : LOk L) {b A B : Addr} {X : Nat → Nat} {s0 : State} (h0 : MulOk L b A B X s0) {i : Nat}
    (hi : i < L.k) {s : State} (h : MulInv L b B X s0 i s) : WP isa (.block (mulRow L i)) s (MulInv L b B X s0 (i + 1)) := by
  obtain ⟨p1, p2⟩ := hL.p (j := i) (by omega_arith)
  have k8 := hL.k8
  have k4 := hL.k4
  obtain ⟨l, hl⟩ : ∃ l, L.k = l + 1 := ⟨L.k - 1, by omega_arith⟩
  obtain oA : ∀ j < L.k, L.A j ∉ clobR L := fun j hj => hL.aO (hL.am j hj)
  obtain nY : ∀ j < L.k, L.A j ≠ Y := fun j hj e => hL.aB (r := Y) (by decide) (e ▸ hL.am j hj)
  obtain vY : ∀ j, L.V j ≠ Y := fun j e => by
    have := hL.vo _ (hL.vM j); simp only [List.mem_append, not_or] at this
    exact this.1.1.1 (by rw [e]; decide)
  obtain yO : Y ∉ clobR L := hL.baseO (by decide) (by decide)
  unfold mulRow
  refine wp_ld (by omega_arith) (by rw [h.gpr _ (by
      simp only [List.mem_cons (b := Y), not_or]; exact ⟨by decide, hL.baseO (by decide) (by decide)⟩), h0.b'])
    (al8 h0.bal (by omega_arith)) (by rw [h.rd, h.wr]; exact h0.bin i hi) fun s1 u1 => ?_
  obtain hB : dw s.mem B (8 * i) = dw s0.mem B (8 * i) := dwB_frame h.frame (h0.bdis i hi)
  obtain y0 := out_iff.mp yO
  refine WP.block_append (WP.mono (row1_ok hL (acc := decide (0 < i)) (i := i) (n := L.k - 1) (fun j hj => oA j (by omega_arith))
    (by omega_arith) ⟨y0.2.1, y0.2.2.1, y0.1⟩ fun j _ e => vY _ e.symm) fun s2 h2 => ?_)
  rw [show L.k - 1 + 1 = L.k by omega_arith] at h2
  obtain hc2 : Ctx b s2 := ctx_of h0.ctx (by
      rw [h2.out hL _ (hL.baseO (by decide) (by decide)), u1.other _ (by decide), h.gpr _ (by
        simp only [List.mem_cons (b := Y), not_or]; exact ⟨by decide, hL.baseO (by decide) (by decide)⟩)])
    (by rw [h2.wr, u1.wr, h.wr])
  refine sd_ok hc2 p1 p2 fun s3 u3 => wp_mv fun s4 u4 => WP.block_nil ?_
  obtain hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (L.P i)) (s2.gpr (L.V i)) := by
    rw [u4.mem, u3.mem, h2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, h2.rd, u1.rd, h.rd], by rw [u4.wr, u3.wr, h2.wr, u1.wr, h.wr],
    by rw [u4.sp, u3.sp, h2.sp, u1.sp, h.sp], by rw [hm4]; exact PR_store hL (by omega_arith) h.frame _, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons (b := Y), not_or] at hr
    rw [u4.other r (ne_of_out (out_iff.mp hr.2).2.2.2 (hL.vM i)), u3.gpr, h2.out hL r hr.2, u1.other r hr.1, h.gpr r hr']
  · have hv := h.val
    have e := h2.val
    obtain y1 : (s1.gpr Y).toNat = dw s0.mem B (8 * i) := by rw [u1.gpr, ← hB]; rfl
    obtain rv1 : rv L s1 i L.k = rv L s i L.k := colsV_congr fun j _ => by rw [u1.other _ (vY _)]
    obtain xA : colsV (fun j => (s1.gpr (L.A j)).toNat) L.k = colsV X L.k := colsV_congr fun j hj => by
      rw [u1.other _ (nY j hj), MulInv.regs hL h0 h j hj]
    rw [rv1, y1, xA] at e
    obtain hw : W L (i + 1) s4 (i + 1) L.k = colsV (fun j => (s2.gpr (L.V (i + (j + 1)))).toNat) l +
        (2 ^ 64) ^ l * (s2.gpr C).toNat := by
      simp only [W, Nat.succ_pos, decide_true, ↓reduceIte, rv]
      rw [hl, colsV_succ, show i + 1 + l = i + L.k by omega_arith, Lay.V_add, u4.gpr, u3.gpr]
      congr 1
      refine colsV_congr fun j hj => ?_
      rw [show i + 1 + j = i + (j + 1) by omega_arith,
        u4.other _ (Ne.symm (hL.vne (by omega_arith) (by omega_arith))), u3.gpr]
    obtain low : colsV (fun j => dw s4.mem b (L.P j)) i = colsV (fun j => dw s.mem b (L.P j)) i :=
      colsV_congr fun j hj => by rw [hm4, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    obtain nw : dw s4.mem b (L.P i) = (s2.gpr (L.V i)).toNat := by rw [hm4]; exact dw_write_self ..
    rw [colsV_succ, low, nw, hw, Nat.pow_succ, show xv s0.mem B (i + 1) = xv s0.mem B i + (2 ^ 64) ^ i * dw s0.mem B (8 * i)
      from rfl]
    refine mulRow_alg hv (S := colsV X L.k * dw s0.mem B (8 * i)) ?_ rfl
    show _ = W L i s i L.k + _
    rw [← e, rv, show (fun j => (s2.gpr (L.V (i + j))).toNat) = fun j => (s2.gpr (L.V (i + j))).toNat from rfl]
    rw [hl, colsV_shift, Nat.add_zero, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ', Nat.add_assoc]

/-- After `j` words of the window stored. -/
structure HiInv (L : Lay) (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR L b] s0.mem s.mem
  low : ∀ i < L.k, dw s.mem b (L.P i) = dw s0.mem b (L.P i)
  val : ∀ i < j, dw s.mem b (L.P (L.k + i)) = (s0.gpr (L.V (L.k + i))).toNat

theorem hi_ok (hL : LOk L) {b : Addr} {s0 : State} (hc : Ctx b s0) :
    WP isa (.block ((List.range L.k).flatMap fun j => [.store .d (L.V (L.k + j)) .a3 (L.P (L.k + j))])) s0
      (HiInv L b s0 L.k) := by
  refine wp_range_flatMap (M := isa) (HiInv L b s0) (fun j s hj h => ?_) L.k (Nat.le_refl _) s0
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨p1, p2⟩ := hL.p (j := L.k + j) (by omega_arith)
  refine sd_ok (ctx_of hc (by rw [h.gpr]) h.wr) p1 p2 fun s1 u1 => WP.block_nil ?_
  refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp],
    by rw [u1.mem]; exact PR_store hL (by omega_arith) h.frame _, fun i hi => ?_, fun i hi => ?_⟩
  · rw [u1.mem, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), h.low i hi]
  · rw [u1.mem, P_write hL (by omega_arith) (by omega_arith)]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, h.gpr]
    · rw [ite_eq_right (by omega_arith), h.val i (by omega_arith)]

/-- The words of the product. -/
abbrev pw (L : Lay) (m : Mem) (b : Addr) : Nat := colsV (fun j => dw m b (L.P j)) (2 * L.k)

/-- The registers the products write. -/
abbrev clobP (L : Lay) : List Reg := .t4 :: .t5 :: (L.AL ++ clobR L)

theorem clobP_iff {r : Reg} : r ∉ clobP L ↔ r ≠ .t4 ∧ r ≠ .t5 ∧ r ∉ L.AL ∧ r ∉ clobR L := by
  simp only [List.mem_cons (b := Reg.t4), List.mem_cons (b := Reg.t5), List.mem_append, not_or, ne_eq]

theorem mulProd_ok (hL : LOk L) {b A B : Addr} {s : State} (hc : Ctx b s) (h4 : s.gpr .t4 = A) (h5 : s.gpr .t5 = B)
    (hal : A.toNat % 8 = 0) (hbl : B.toNat % 8 = 0)
    (ain : ∀ i < L.k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (bin : ∀ i < L.k, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8)
    (bdis : ∀ i < L.k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (PR L b)) :
    WP isa (.block (mulProd L)) s fun s' =>
      (∀ r, r ∉ clobP L → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [PR L b] s.mem s'.mem ∧ pw L s'.mem b = xv s.mem A L.k * xv s.mem B L.k := by
  unfold mulProd
  refine WP.block_append (WP.mono (loadA_ok hL h4 hal ain) fun s1 h1 => ?_)
  obtain hc1 : Ctx b s1 := ctx_of hc (h1.gpr _ (hL.aB (by decide))) h1.wr
  obtain hM : MulOk L b A B (fun j => dw s.mem A (8 * j)) s1 :=
    ⟨hc1, h1.val, by rw [h1.gpr _ (hL.aB (by decide)), h5], hbl, by rw [h1.rd, h1.wr]; exact bin, bdis⟩
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (MulInv L b B _ s1) (fun i s' hi h => mulRow_ok hL hM hi h) L.k
    (Nat.le_refl _) s1 ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, by simp [colsV]⟩) fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by
    simp only [List.mem_cons (b := Y), not_or]; exact ⟨by decide, hL.baseO (by decide) (by decide)⟩)) h2.wr
  refine WP.mono (hi_ok hL hc2) fun s3 h3 => ?_
  refine ⟨fun r hr => ?_, by rw [h3.rd, h2.rd, h1.rd], by rw [h3.wr, h2.wr, h1.wr], by rw [h3.sp, h2.sp, h1.sp],
    by rw [← h1.mem]; exact h2.frame.trans h3.frame, ?_⟩
  · obtain ⟨a, _, c, d⟩ := clobP_iff.mp hr
    rw [h3.gpr, h2.gpr r (by simp only [List.mem_cons (b := Y), not_or]; exact ⟨a, d⟩), h1.gpr r c]
  · have hv := h2.val
    simp only [W, hL.k0, decide_true, ↓reduceIte] at hv
    show colsV (fun j => dw s3.mem b (L.P j)) (2 * L.k) = _
    rw [Nat.two_mul, colsV_split, colsV_congr (g := fun j => dw s2.mem b (L.P j)) fun j hj => h3.low j hj,
      colsV_congr (f := fun j => dw s3.mem b (L.P (L.k + j))) (g := fun j => (s2.gpr (L.V (L.k + j))).toNat) fun j hj => h3.val j hj]
    refine hv.trans ?_
    rw [h1.mem]

/-! ## The square -/

/-- After `i` rows of the square's products. -/
structure SqInv (L : Lay) (b : Addr) (X : Nat → Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobR L → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR L b] s0.mem s.mem
  val : 2 ^ 64 * (colsV (fun j => dw s.mem b (L.P (1 + j))) (2 * i) +
    (2 ^ 64) ^ (2 * i) * W L i s (2 * i + 1) (L.k - 1 - i)) = sumN (rowTerm X L.k) i

private theorem sqrRow_alg {L E w v0 v1 R S a X B t : Nat} (hv : B * (L + E * w) = S)
    (e : v0 + B * (v1 + B * R) = w + X * a) (ht : t = a * (E * B) * X) :
    B * (L + E * v0 + E * B * v1 + E * B * B * R) = S + t := by
  subst ht
  calc B * (L + E * v0 + E * B * v1 + E * B * B * R) = B * (L + E * (v0 + B * (v1 + B * R))) := by grind
    _ = B * (L + E * w) + B * (E * (X * a)) := by rw [e]; grind
    _ = _ := by rw [hv]; grind

theorem sqrRow_ok (hL : LOk L) {b : Addr} {X : Nat → Nat} {s0 : State} (hc : Ctx b s0)
    (hX : ∀ j < L.k, (s0.gpr (L.A j)).toNat = X j) {i : Nat} (hi : i < L.k - 1) {s : State}
    (h : SqInv L b X s0 i s) : WP isa (.block (sqrRow L i)) s (SqInv L b X s0 (i + 1)) := by
  obtain ⟨p1, p2⟩ := hL.p (j := 2 * i + 1) (by omega_arith)
  obtain ⟨q1, q2⟩ := hL.p (j := 2 * i + 2) (by omega_arith)
  have k4 := hL.k4
  obtain ⟨n, hn⟩ : ∃ n, L.k - 1 - i = n + 1 := ⟨L.k - 2 - i, by omega_arith⟩
  have hn' : L.k - 2 - i = n := by omega_arith
  obtain oA : ∀ j < L.k, L.A j ∉ clobR L := fun j hj => hL.aO (hL.am j hj)
  obtain y0 := out_iff.mp (oA i (by omega_arith))
  unfold sqrRow
  rw [hn']
  refine WP.block_append (WP.mono (row1_ok hL (acc := decide (0 < i)) (y := L.A i) (i := 2 * i + 1) (n := n)
    (fun j hj => oA _ (by omega_arith)) (by omega_arith) ⟨y0.2.1, y0.2.2.1, y0.1⟩
    fun j _ => ne_of_out y0.2.2.2 (hL.vM _)) fun s2 h2 => ?_)
  refine wp_mv fun s3 u3 => ?_
  obtain a3 : Reg.a3 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain hc3 : Ctx b s3 := ctx_of hc (by
    rw [u3.other _ (ne_of_out (out_iff.mp a3).2.2.2 (hL.vM _)), h2.out hL _ a3, h.gpr _ a3]) (by rw [u3.wr, h2.wr, h.wr])
  refine sd_ok hc3 p1 p2 fun s4 u4 => ?_
  refine sd_ok (ctx_of hc3 (by rw [u4.gpr]) u4.wr) q1 q2 fun s5 u5 => WP.block_nil ?_
  obtain hm5 : s5.mem = (s.mem.writeW (b + BitVec.ofNat 64 (L.P (2 * i + 1))) (s3.gpr (L.V (2 * i + 1)))).writeW
      (b + BitVec.ofNat 64 (L.P (2 * i + 2))) (s3.gpr (L.V (2 * i + 2))) := by
    rw [u5.mem, u4.mem, u4.gpr, u3.mem, h2.mem]
  refine ⟨fun r hr => ?_, by rw [u5.rd, u4.rd, u3.rd, h2.rd, h.rd], by rw [u5.wr, u4.wr, u3.wr, h2.wr, h.wr],
    by rw [u5.sp, u4.sp, u3.sp, h2.sp, h.sp],
    by rw [hm5]; exact PR_store hL (by omega_arith) (PR_store hL (by omega_arith) h.frame _) _, ?_⟩
  · rw [u5.gpr, u4.gpr, u3.other r (ne_of_out (out_iff.mp hr).2.2.2 (hL.vM _)), h2.out hL r hr, h.gpr r hr]
  · have hv := h.val
    have e := h2.val
    obtain a1 : (s.gpr (L.A i)).toNat = X i := by rw [h.gpr _ (oA i (by omega_arith)), hX i (by omega_arith)]
    obtain xA : colsV (fun j => (s.gpr (L.A (i + 1 + j))).toNat) (n + 1) = colsV (fun j => X (i + 1 + j)) (n + 1) :=
      colsV_congr fun j hj => by rw [h.gpr _ (oA _ (by omega_arith)), hX _ (by omega_arith)]
    rw [a1, xA] at e
    -- The row and its carry, as registers.
    obtain hR : rv L s3 (2 * i + 1) (n + 1 + 1) = rv L s2 (2 * i + 1) (n + 1) + (2 ^ 64) ^ (n + 1) * (s2.gpr C).toNat := by
      rw [rv, colsV_succ, show 2 * i + 1 + (n + 1) = i + L.k by omega_arith, u3.gpr]
      congr 1
      exact colsV_congr fun j hj => by rw [u3.other _ (hL.vne (by omega_arith) (by omega_arith))]
    rw [← hR, rv, colsV_shift, colsV_shift] at e
    obtain hg : s5.gpr = s3.gpr := by rw [u5.gpr, u4.gpr]
    obtain hw : W L (i + 1) s5 (2 * (i + 1) + 1) (L.k - 1 - (i + 1)) =
        colsV (fun j => (s3.gpr (L.V (2 * i + 1 + (j + 1 + 1)))).toNat) n := by
      simp only [W, Nat.succ_pos, decide_true, ↓reduceIte]
      rw [show L.k - 1 - (i + 1) = n by omega_arith]
      exact colsV_congr fun j _ => by rw [hg, show 2 * (i + 1) + 1 + j = 2 * i + 1 + (j + 1 + 1) by omega_arith]
    obtain low : colsV (fun j => dw s5.mem b (L.P (1 + j))) (2 * i) = colsV (fun j => dw s.mem b (L.P (1 + j))) (2 * i) :=
      colsV_congr fun j hj => by
        rw [hm5, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
          P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    obtain n0 : dw s5.mem b (L.P (1 + 2 * i)) = (s3.gpr (L.V (2 * i + 1))).toNat := by
      rw [hm5, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
        P_write hL (by omega_arith) (by omega_arith), ite_eq_left (by omega_arith)]
    obtain n1 : dw s5.mem b (L.P (1 + (2 * i + 1))) = (s3.gpr (L.V (2 * i + 2))).toNat := by
      rw [hm5, P_write hL (by omega_arith) (by omega_arith), ite_eq_left (by omega_arith)]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith] at hw ⊢
    rw [colsV_succ, colsV_succ, low, n0, n1, hw, Nat.pow_succ, Nat.pow_succ]
    show _ = sumN _ i + rowTerm _ L.k i
    refine sqrRow_alg hv (w := W L i s (2 * i + 1) (L.k - 1 - i)) (X := colsV (fun j => X (i + 1 + j)) (n + 1)) (a := X i) ?_ ?_
    · rw [hn]
      simp only [Nat.add_zero, Nat.zero_add] at e
      exact e
    · rw [rowTerm, Nat.pow_succ, hn]

/-! ### Doubling -/

theorem bit_mem (j : Nat) : bit j ∈ [Reg.t4, .t5] := by unfold bit; split <;> decide

theorem bit_ne (j : Nat) : bit j ≠ bit (j + 1) := by
  unfold bit
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [ite_eq_left h, ite_eq_right (by omega_arith)]; decide
  · rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]; decide

private theorem dword_nat {p B t bi x c5 c1 c2 u1 u2 : Nat} (hp : p < 2 ^ 64) (hB : B = p / 2 ^ 63) (hbi : bi ≤ 1)
    (ht : t = (p * 2 % 2 ^ 64 + bi) % 2 ^ 64) (hx : x < 2 ^ 64) (hc : c5 ≤ 1) (e1 : u1 + 2 ^ 64 * c1 = t + x)
    (e2 : u2 + 2 ^ 64 * c2 = u1 + c5) :
    u2 + 2 ^ 64 * (c2 + c1) + 2 ^ 64 * B = 2 * p + bi + x + c5 ∧ c2 + c1 ≤ 1 ∧ B ≤ 1 := by
  subst hB
  refine ⟨by omega_using [hp, hbi, ht, e1, e2], by omega_using [hp, hbi, ht, e1, e2, hx, hc], by omega_using [hp]⟩

/-- Word `j` of the product doubled, with a bit, a word and the carry in, a bit and the carry out. -/
theorem dword_ok (hL : LOk L) {b : Addr} {s : State} (hc : Ctx b s) {j : Nat} (hj : j < 2 * L.k) {w h : Reg}
    (hw : w ∉ base) (hh : h ∉ base) (hwh : w ≠ h) (hbi : (s.gpr (bit j)).toNat ≤ 1) (hC : (s.gpr C).toNat ≤ 1) :
    WP isa (.block (dword L j w h)) s fun s' =>
      dw s'.mem b (L.P j) + 2 ^ 64 * (s'.gpr C).toNat + 2 ^ 64 * (s'.gpr (bit (j + 1))).toNat =
        2 * dw s.mem b (L.P j) + (s.gpr (bit j)).toNat + (s.gpr h).toNat + (s.gpr C).toNat ∧
      (s'.gpr C).toNat ≤ 1 ∧ (s'.gpr (bit (j + 1))).toNat ≤ 1 ∧
      (∀ r, r ∉ [w, h, C, bit (j + 1)] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∃ v : BitVec 64, s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (L.P j)) v := by
  obtain ⟨p1, p2⟩ := hL.p hj
  obtain bm : ∀ j, bit j ∈ base := fun j =>
    (by decide : ∀ r ∈ [Reg.t4, .t5], r ∈ base) _ (bit_mem j)
  obtain bc : ∀ j, bit j ≠ C := fun j => (by decide : ∀ r ∈ [Reg.t4, .t5], r ≠ C) _ (bit_mem j)
  obtain b3 : ∀ j, bit j ≠ .a3 := fun j => (by decide : ∀ r ∈ [Reg.t4, .t5], r ≠ .a3) _ (bit_mem j)
  obtain wC : w ≠ C := ne_of_out hw (by decide)
  obtain hC' : h ≠ C := ne_of_out hh (by decide)
  obtain w3 : w ≠ .a3 := ne_of_out hw (by decide)
  obtain h3 : h ≠ .a3 := ne_of_out hh (by decide)
  obtain wb : ∀ j, w ≠ bit j := fun j => ne_of_out hw (bm j)
  obtain hb : ∀ j, h ≠ bit j := fun j => ne_of_out hh (bm j)
  obtain bn := bit_ne j
  unfold dword
  refine ld_ok hc p1 p2 fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 => ?_
  refine wp_add fun s4 u4 => wp_add fun s5 u5 => wp_sltu fun s6 u6 => wp_add fun s7 u7 => wp_sltu fun s8 u8 =>
    wp_add fun s9 u9 => ?_
  obtain hc9 : Ctx b s9 := ctx_of hc (by
      rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (Ne.symm w3), u6.other _ (Ne.symm h3),
        u5.other _ (Ne.symm w3), u4.other _ (Ne.symm w3), u3.other _ (Ne.symm w3),
        u2.other _ (Ne.symm (b3 _)), u1.other _ (Ne.symm w3)])
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine sd_ok hc9 p1 p2 fun s10 u10 => WP.block_nil ?_
  obtain w1 : (s1.gpr w).toNat = dw s.mem b (L.P j) := by rw [u1.gpr]; rfl
  obtain w2 : s2.gpr w = s1.gpr w := u2.other _ (wb _)
  obtain bi3 : s3.gpr (bit j) = s.gpr (bit j) := by
    rw [u3.other _ (Ne.symm (wb _)), u2.other _ bn, u1.other _ (Ne.symm (wb _))]
  obtain h4 : s4.gpr h = s.gpr h := by
    rw [u4.other _ (Ne.symm hwh), u3.other _ (Ne.symm hwh), u2.other _ (hb _), u1.other _ (Ne.symm hwh)]
  obtain C6 : s6.gpr C = s.gpr C := by
    rw [u6.other _ (Ne.symm hC'), u5.other _ (Ne.symm wC), u4.other _ (Ne.symm wC), u3.other _ (Ne.symm wC),
      u2.other _ (Ne.symm (bc _)), u1.other _ (Ne.symm wC)]
  obtain bo9 : s9.gpr (bit (j + 1)) = s2.gpr (bit (j + 1)) := by
    rw [u9.other _ (bc _), u8.other _ (bc _), u7.other _ (Ne.symm (wb _)), u6.other _ (Ne.symm (hb _)),
      u5.other _ (Ne.symm (wb _)), u4.other _ (Ne.symm (wb _)), u3.other _ (Ne.symm (wb _))]
  obtain hB : (s9.gpr (bit (j + 1))).toNat = dw s.mem b (L.P j) / 2 ^ 63 := by
    rw [bo9, u2.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, w1]
  obtain hT1 : (s4.gpr w).toNat = (dw s.mem b (L.P j) * 2 % 2 ^ 64 + (s.gpr (bit j)).toNat) % 2 ^ 64 := by
    rw [u4.gpr, BitVec.toNat_add, u3.gpr, bi3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, w2, w1, Nat.pow_one]
  obtain c1e : s6.gpr h = if s4.gpr w + s4.gpr h < s4.gpr h then 1 else 0 := by
    rw [u6.gpr, u5.gpr, u5.other _ (Ne.symm hwh)]
  obtain w6 : s6.gpr w = s4.gpr w + s4.gpr h := by rw [u6.other _ hwh, u5.gpr]
  obtain c2e : s8.gpr C = if s6.gpr w + s6.gpr C < s6.gpr C then 1 else 0 := by
    rw [u8.gpr, u7.gpr, u7.other C (Ne.symm wC)]
  obtain h8 : s8.gpr h = s6.gpr h := by rw [u8.other _ hC', u7.other _ (Ne.symm hwh)]
  obtain w9 : s9.gpr w = s6.gpr w + s6.gpr C := by rw [u9.other _ wC, u8.other _ wC, u7.gpr]
  obtain m9 : s9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hm : s10.mem = s.mem.writeW (b + BitVec.ofNat 64 (L.P j)) (s9.gpr w) := by rw [u10.mem, m9]
  obtain e1 := carry (s4.gpr w) (s4.gpr h)
  obtain e2 := carry (s6.gpr w) (s6.gpr C)
  rw [← c1e, ← w6, h4] at e1
  rw [← c2e, ← w9, C6] at e2
  obtain ⟨n1, n2, n3⟩ := dword_nat (dw_lt s.mem b (L.P j)) hB hbi hT1 (s.gpr h).isLt hC e1 e2
  obtain h5 : (s9.gpr C).toNat = (s8.gpr C).toNat + (s6.gpr h).toNat := by
    rw [u9.gpr, BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega_using [n2])]
  refine ⟨?_, by rw [u10.gpr, h5]; exact n2, by rw [u10.gpr]; exact n3, fun r hr => ?_,
    by rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr],
    by rw [u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp], _, hm⟩
  · rw [u10.gpr, h5, hm, dw_write_self]; exact n1
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u10.gpr, u9.other r hr.2.2.1, u8.other r hr.2.2.1, u7.other r hr.1, u6.other r hr.2.1, u5.other r hr.1,
      u4.other r hr.1, u3.other r hr.1, u2.other r hr.2.2.2, u1.other r hr.1]

/-- After `i` squares. -/
structure DiagInv (L : Lay) (b : Addr) (X : Nat → Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ .t4 :: .t5 :: clobR L → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR L b] s0.mem s.mem
  cy : (s.gpr C).toNat ≤ 1
  bi : (s.gpr (bit (2 * i))).toNat ≤ 1
  up : ∀ j, 2 * i ≤ j → j < 2 * L.k → dw s.mem b (L.P j) = dw s0.mem b (L.P j)
  val : colsV (fun j => dw s.mem b (L.P j)) (2 * i) + (2 ^ 64) ^ (2 * i) * ((s.gpr C).toNat + (s.gpr (bit (2 * i))).toNat) =
    2 * colsV (fun j => dw s0.mem b (L.P j)) (2 * i) + sumN (fun j => X j * X j * (2 ^ 64) ^ (2 * j)) i

private theorem diag_alg {E B V p0 p1 c b0 c1 b1 c2 b2 n0 n1 lo hi S x : Nat}
    (hv : V + E * (c + b0) = S) (h0 : n0 + B * c1 + B * b1 = 2 * p0 + b0 + lo + c)
    (h1 : n1 + B * c2 + B * b2 = 2 * p1 + b1 + hi + c1) (hx : lo + B * hi = x)
    {Sn U U' : Nat} (hS : S = 2 * U + Sn) (hU : U' = U + E * p0 + E * B * p1) :
    V + E * n0 + E * B * n1 + E * B * B * (c2 + b2) = 2 * U' + (Sn + x * E) := by
  subst hx hU
  rw [hS] at hv
  calc V + E * n0 + E * B * n1 + E * B * B * (c2 + b2)
      = V + E * n0 + E * B * (n1 + B * c2 + B * b2) := by grind
    _ = V + E * (n0 + B * c1 + B * b1) + E * B * (2 * p1 + hi) := by rw [h1]; grind
    _ = (V + E * (c + b0)) + E * (2 * p0 + lo) + E * B * (2 * p1 + hi) := by rw [h0]; grind
    _ = _ := by rw [hv]; grind

theorem diag_ok (hL : LOk L) {b : Addr} {X : Nat → Nat} {s0 : State} (hc : Ctx b s0)
    (hX : ∀ j < L.k, (s0.gpr (L.A j)).toNat = X j) {i : Nat} (hi : i < L.k) {s : State}
    (h : DiagInv L b X s0 i s) : WP isa (.block (diag L i)) s (DiagInv L b X s0 (i + 1)) := by
  have k4 := hL.k4
  obtain vB : ∀ j, L.V j ∉ base := fun j hm => by
    have := hL.vo _ (hL.vM j); simp only [List.mem_append, not_or] at this; exact this.1.1.1 hm
  obtain oA : L.A i ∉ clobR L := hL.aO (hL.am i hi)
  obtain oA' : L.A i ∉ .t4 :: .t5 :: clobR L := by
    simp only [List.mem_cons (b := Reg.t4), List.mem_cons (b := Reg.t5), not_or]
    exact ⟨fun e => hL.aB (r := .t4) (by decide) (e ▸ hL.am i hi), fun e => hL.aB (r := .t5) (by decide) (e ▸ hL.am i hi), oA⟩
  obtain av : ∀ j, L.A i ≠ L.V j := fun j => ne_of_out (out_iff.mp oA).2.2.2 (hL.vM j)
  obtain a3 : Reg.a3 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain bB : ∀ j, bit j ∈ base := fun j => (by decide : ∀ r ∈ [Reg.t4, .t5], r ∈ base) _ (bit_mem j)
  obtain bv : ∀ j l, bit j ≠ L.V l := fun j l e => vB l (e ▸ bB j)
  obtain bc : ∀ j, bit j ≠ C := fun j => (by decide : ∀ r ∈ [Reg.t4, .t5], r ≠ C) _ (bit_mem j)
  obtain cv : ∀ l, C ≠ L.V l := fun l e => vB l (e ▸ (by decide : C ∈ base))
  obtain d01 : L.V (4 * i) ≠ L.V (4 * i + 1) := hL.vne (by omega_arith) (by omega_arith)
  obtain d02 : L.V (4 * i) ≠ L.V (4 * i + 2) := hL.vne (by omega_arith) (by omega_arith)
  obtain d12 : L.V (4 * i + 1) ≠ L.V (4 * i + 2) := hL.vne (by omega_arith) (by omega_arith)
  obtain d13 : L.V (4 * i + 1) ≠ L.V (4 * i + 3) := hL.vne (by omega_arith) (by omega_arith)
  obtain gA : s.gpr (L.A i) = s0.gpr (L.A i) := h.gpr _ oA'
  obtain s3 : s.gpr .a3 = s0.gpr .a3 := h.gpr _ (by
    simp only [List.mem_cons (b := Reg.t4), List.mem_cons (b := Reg.t5), not_or]; exact ⟨by decide, by decide, a3⟩)
  unfold diag
  simp only [List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => ?_
  obtain hp := mul_words (s.gpr (L.A i)) (s.gpr (L.A i))
  obtain l2 : s2.gpr (L.V (4 * i)) = s.gpr (L.A i) * s.gpr (L.A i) := by rw [u2.other _ d01, u1.gpr]
  obtain h2 : s2.gpr (L.V (4 * i + 1)) = BitVec.ofNat 64 ((s.gpr (L.A i)).toNat * (s.gpr (L.A i)).toNat / 2 ^ 64) := by
    rw [u2.gpr, u1.other _ (av _)]
  rw [← l2, ← h2, gA, hX i hi] at hp
  obtain k2 : ∀ r, (∀ l, r ≠ L.V l) → s2.gpr r = s.gpr r := fun r hr => by rw [u2.other r (hr _), u1.other r (hr _)]
  obtain a3v : ∀ l, Reg.a3 ≠ L.V l := fun l => ne_of_out (out_iff.mp a3).2.2.2 (hL.vM l)
  obtain hc2 : Ctx b s2 := ctx_of hc (by rw [k2 _ a3v, s3]) (by rw [u2.wr, u1.wr, h.wr])
  obtain m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.block_append (WP.mono (dword_ok hL hc2 (j := 2 * i) (by omega_arith) (vB _) (vB _) (Ne.symm d02)
    (by rw [k2 _ (bv _)]; exact h.bi) (by rw [k2 _ cv]; exact h.cy)) fun s4 ⟨e4, c4, b4, g4, rd4, wr4, sp4, v4, m4⟩ => ?_)
  obtain nb : ∀ j, Reg.a3 ≠ bit j := fun j => (by decide : ∀ r ∈ [Reg.t4, .t5], Reg.a3 ≠ r) _ (bit_mem j)
  obtain hc4 : Ctx b s4 := ctx_of hc2 (g4 _ (by simp [a3v, nb])) wr4
  refine WP.mono (dword_ok hL hc4 (j := 2 * i + 1) (by omega_arith) (vB _) (vB _) (Ne.symm d13) b4 c4)
    fun s5 ⟨e5, c5, b5, g5, rd5, wr5, sp5, v5, m5⟩ => ?_
  rw [k2 _ (bv _), k2 _ cv, m2] at e4
  obtain hi4 : s4.gpr (L.V (4 * i + 1)) = s2.gpr (L.V (4 * i + 1)) :=
    g4 _ (by simp [d12, Ne.symm d01, Ne.symm (cv _), Ne.symm (bv _ _)])
  rw [hi4] at e5
  obtain p1 : dw s4.mem b (L.P (2 * i + 1)) = dw s.mem b (L.P (2 * i + 1)) := by
    rw [m4, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), m2]
  obtain n0 : dw s5.mem b (L.P (2 * i)) = dw s4.mem b (L.P (2 * i)) := by
    rw [m5, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
  obtain e2 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega_arith
  refine ⟨fun r hr => ?_, by rw [rd5, rd4, u2.rd, u1.rd, h.rd], by rw [wr5, wr4, u2.wr, u1.wr, h.wr],
    by rw [sp5, sp4, u2.sp, u1.sp, h.sp], ?_, c5, by rw [e2]; exact b5, fun j hj hj' => ?_, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons (b := Reg.t4), List.mem_cons (b := Reg.t5), not_or] at hr
    obtain o := out_iff.mp hr.2.2
    obtain rb : ∀ j, r ≠ bit j := fun j e => by
      have := bit_mem j; rw [← e] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e
      · exact hr.1 e
      · exact hr.2.1 e
    obtain rv : ∀ l, r ≠ L.V l := fun l => ne_of_out o.2.2.2 (hL.vM l)
    rw [g5 r (by simp [rv, rb, o.1]), g4 r (by simp [rv, rb, o.1]), k2 r rv, h.gpr r hr']
  · rw [m5, m4, m2]
    exact PR_store hL (by omega_arith) (PR_store hL (by omega_arith) h.frame _) _
  · rw [m5, P_write hL hj' (by omega_arith), ite_eq_right (by omega_arith), m4, P_write hL hj' (by omega_arith),
      ite_eq_right (by omega_arith), m2]
    exact h.up j (by omega_arith) hj'
  · rw [p1, h.up _ (by omega_arith) (by omega_arith)] at e5
    rw [h.up _ (by omega_arith) (by omega_arith)] at e4
    obtain low : colsV (fun j => dw s5.mem b (L.P j)) (2 * i) = colsV (fun j => dw s.mem b (L.P j)) (2 * i) :=
      colsV_congr fun j hj => by
        rw [m5, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), m4,
          P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), m2]
    rw [e2, colsV_succ, colsV_succ, low, n0, Nat.pow_succ, Nat.pow_succ]
    show _ = _ + (sumN _ i + X i * X i * (2 ^ 64) ^ (2 * i))
    exact diag_alg h.val e4 e5 hp rfl (by rw [colsV_succ, colsV_succ, Nat.pow_succ (m := 2 * i) (n := 2 ^ 64)])

/-- The square, from its rows doubled plus its squares, up to a carry there is not. -/
private theorem sq_final {a : Nat → Nat} (ha : ∀ i, a i < 2 ^ 64) {k l n V c X Dg : Nat} (hn : n = 2 * k)
    (hl : k = l + 1) (hX : X = sumN (rowTerm a k) l) (hD : Dg = sumN (fun j => a j * a j * (2 ^ 64) ^ (2 * j)) k)
    (hv : V + (2 ^ 64) ^ n * c = 2 * X + Dg) : V = colsV a k * colsV a k := by
  subst hn hX hD
  obtain hlast : sumN (rowTerm a k) l = sumN (rowTerm a k) k := by
    subst hl
    simp only [sumN, rowTerm, Nat.add_sub_cancel, Nat.sub_self, colsV, Nat.mul_zero, Nat.add_zero]
  rw [hlast, rows_sum] at hv
  obtain hsq := sq_sum a k
  obtain hlt := colsV_lt a ha k
  obtain hlt2 : colsV a k * colsV a k < (2 ^ 64) ^ (2 * k) := by
    rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_two]
    exact Nat.mul_lt_mul_of_lt_of_lt hlt hlt
  generalize ((2 : Nat) ^ 64) ^ (2 * k) = E at hv hlt2
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · omega_using [hsq, hv]
  · have : E ≤ E * c := Nat.le_mul_of_pos_right _ hc
    omega_using [hsq, hlt2, hv, this]

/-- Words of which the first and the last are zero. -/
private theorem cols_ends {f : Nat → Nat} {n l k : Nat} (hl : l = n + 1) (hk : k = l + 1) (h0 : f 0 = 0) (hn : f l = 0) :
    colsV f k = 2 ^ 64 * colsV (fun j => f (1 + j)) n := by
  subst hk hl
  rw [colsV_succ, hn, Nat.mul_zero, Nat.add_zero, colsV_shift, h0, Nat.zero_add,
    colsV_congr (g := fun j => f (1 + j)) fun j _ => by rw [Nat.add_comm]]

theorem sqrProd_ok (hL : LOk L) {b A : Addr} {s : State} (hc : Ctx b s) (h4 : s.gpr .t4 = A)
    (hal : A.toNat % 8 = 0)
    (ain : ∀ i < L.k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (sqrProd L)) s fun s' =>
      (∀ r, r ∉ clobP L → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [PR L b] s.mem s'.mem ∧ pw L s'.mem b = xv s.mem A L.k * xv s.mem A L.k := by
  have k4 := hL.k4
  obtain ⟨l, hl⟩ : ∃ l, L.k = l + 1 := ⟨L.k - 1, by omega_arith⟩
  obtain ⟨p1, p2⟩ := hL.p (j := 0) (by omega_arith)
  obtain ⟨q1, q2⟩ := hL.p (j := 2 * L.k - 1) (by omega_arith)
  unfold sqrProd
  refine WP.block_append (WP.mono (loadA_ok hL h4 hal ain) fun s1 h1 => ?_)
  obtain hc1 : Ctx b s1 := ctx_of hc (h1.gpr _ (hL.aB (by decide))) h1.wr
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SqInv L b _ s1)
    (fun i s' hi h => sqrRow_ok hL hc1 h1.val hi h) (L.k - 1) (Nat.le_refl _) s1
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, by simp [colsV, sumN, W]⟩) fun s2 h2 => ?_)
  obtain a3 : Reg.a3 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ a3) h2.wr
  refine wp_li (imm := 0) (by decide) fun s3 u3 => wp_li (imm := 0) (by decide) fun s4 u4 => ?_
  obtain hc4 : Ctx b s4 := ctx_of hc2 (by rw [u4.other _ (by decide), u3.other _ (by decide)]) (by rw [u4.wr, u3.wr])
  refine sd_ok hc4 p1 p2 fun s5 u5 => ?_
  obtain hc5 : Ctx b s5 := ctx_of hc4 (by rw [u5.gpr]) u5.wr
  refine sd_ok hc5 q1 q2 fun s6 u6 => ?_
  obtain g6 : ∀ r, r ≠ C → r ≠ .t4 → s6.gpr r = s2.gpr r := fun r hC h4 => by
    rw [u6.gpr, u5.gpr, u4.other r h4, u3.other r hC]
  obtain C6 : (s6.gpr C).toNat = 0 := by rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.gpr]; rfl
  obtain t6 : (s6.gpr .t4).toNat = 0 := by rw [u6.gpr, u5.gpr, u4.gpr]; rfl
  obtain C4 : s4.gpr C = 0 := by rw [u4.other _ (by decide), u3.gpr]; rfl
  obtain rd6 : s6.rd = s.rd := by rw [u6.rd, u5.rd, u4.rd, u3.rd, h2.rd, h1.rd]
  obtain wr6 : s6.wr = s.wr := by rw [u6.wr, u5.wr, u4.wr, u3.wr, h2.wr, h1.wr]
  obtain hm6 : s6.mem = (s2.mem.writeW (b + BitVec.ofNat 64 (L.P 0)) (0 : BitVec 64)).writeW
      (b + BitVec.ofNat 64 (L.P (2 * L.k - 1))) (0 : BitVec 64) := by
    rw [u6.mem, u5.mem, u5.gpr, u4.mem, u3.mem, C4]
  obtain hc6 : Ctx b s6 := ctx_of hc5 (by rw [u6.gpr]) u6.wr
  obtain hX6 : ∀ j < L.k, (s6.gpr (L.A j)).toNat = dw s.mem A (8 * j) := fun j hj => by
    obtain o := hL.aO (hL.am j hj)
    rw [g6 _ (out_iff.mp o).1 (fun e => hL.aB (r := .t4) (by decide) (e ▸ hL.am j hj)), h2.gpr _ o]; exact h1.val j hj
  refine WP.mono (wp_range_flatMap (M := isa) (DiagInv L b _ s6)
    (fun i s' hi h => diag_ok hL hc6 hX6 hi h) L.k (Nat.le_refl _) s6
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, by rw [C6]; decide, by show (s6.gpr .t4).toNat ≤ 1; rw [t6]; decide,
      fun _ _ _ => rfl, by
        show colsV _ 0 + (2 ^ 64) ^ 0 * ((s6.gpr C).toNat + (s6.gpr .t4).toNat) = 2 * colsV _ 0 + sumN _ 0
        rw [C6, t6]; rfl⟩) fun s7 h7 => ?_
  obtain f6 : Frame [PR L b] s.mem s6.mem := by
    rw [hm6, ← h1.mem]; exact PR_store hL (by omega_arith) (PR_store hL (by omega_arith) h2.frame _) _
  refine ⟨fun r hr => ?_, by rw [h7.rd, rd6], by rw [h7.wr, wr6],
    by rw [h7.sp, u6.sp, u5.sp, u4.sp, u3.sp, h2.sp, h1.sp], f6.trans h7.frame, ?_⟩
  · obtain ⟨a, b', c, d⟩ := clobP_iff.mp hr
    rw [h7.gpr r (by simp only [List.mem_cons (b := Reg.t4), List.mem_cons (b := Reg.t5), not_or]; exact ⟨a, b', d⟩),
      g6 r (out_iff.mp d).1 a, h2.gpr r d, h1.gpr r c]
  · have hv := h7.val
    have hr := h2.val
    obtain eL : dw s6.mem b (L.P (2 * L.k - 1)) = 0 := by
      rw [hm6, P_write hL (by omega_arith) (by omega_arith), ite_eq_left rfl]; decide
    obtain e0 : dw s6.mem b (L.P 0) = 0 := by
      rw [hm6, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
        P_write hL (by omega_arith) (by omega_arith), ite_eq_left rfl]; decide
    rw [show W L (L.k - 1) s2 (2 * (L.k - 1) + 1) (L.k - 1 - (L.k - 1)) = 0 by
      simp only [W, Nat.sub_self, rv, colsV, ite_self], Nat.mul_zero, Nat.add_zero] at hr
    obtain hp : colsV (fun j => dw s6.mem b (L.P j)) (2 * L.k) =
        sumN (rowTerm (fun j => dw s.mem A (8 * j)) L.k) (L.k - 1) := by
      refine (cols_ends (f := fun j => dw s6.mem b (L.P j)) (n := 2 * (L.k - 1)) (l := 2 * L.k - 1) (k := 2 * L.k)
        (by omega_arith) (by omega_arith) e0 eL).trans ?_
      rw [← hr]
      refine congrArg (2 ^ 64 * ·) (colsV_congr fun j hj => ?_)
      rw [hm6, P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
        P_write hL (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    exact sq_final (a := fun j => dw s.mem A (8 * j)) (k := L.k) (l := L.k - 1) (n := 2 * L.k) (fun _ => dw_lt _ _ _) rfl
      (by omega_arith) hp rfl hv

/-! ## The constants -/

open VG.Impl.Words.RISCV64 (li64)
open VG.Proof.Weierstrass.RISCV64.GenWide (wp_li64)

/-- The modulus's words and `m'` where the reduction reads them. -/
structure MOk (L : Lay) (b : Addr) (m : Nat) (s : State) : Prop where
  ctx : Ctx b s
  regs : ∀ j < L.k, s.gpr (L.A j) = wordOf m j
  ni : s.gpr NI = BitVec.ofNat 64 (negInv m)

/-- After `n` words of the modulus. -/
structure ConstInv (L : Lay) (m : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ L.LO → r ∉ L.AL → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, s.gpr (L.A j) = wordOf m j

theorem LOk.alo (hL : LOk L) {j : Nat} (hj : j < L.k) (i : Nat) : L.A j ≠ L.lo i := fun e => by
  have := hL.ao _ (hL.am j hj)
  simp only [List.mem_append, not_or] at this
  exact this.1.2 (e ▸ hL.loM i)

theorem const_ok (hL : LOk L) {m : Nat} {s0 : State} :
    WP isa (.block ((List.range L.k).flatMap fun j => li64 (L.A j) (L.lo j) (wordOf m j))) s0 (ConstInv L m s0 L.k) := by
  refine wp_range_flatMap (M := isa) (ConstInv L m s0) (fun n s hn h => ?_) L.k (Nat.le_refl _) s0
    ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [← List.append_nil (li64 _ _ _)]
  refine wp_li64 (hL.alo hn n) _ fun s1 e1 k1 => WP.block_nil ?_
  refine ⟨fun r hl hr => ?_, by rw [k1.2.1, h.mem], by rw [k1.2.2.1, h.rd], by rw [k1.2.2.2.1, h.wr],
    by rw [k1.2.2.2.2, h.sp], fun j hj => ?_⟩
  · rw [k1.1 r (by simp [ne_of_out hl (hL.loM n), ne_of_out hr (hL.am n hn)]), h.gpr r hl hr]
  · by_cases e : j = n
    · subst e; exact e1
    · obtain ne : L.A j ≠ L.A n := fun e' => e (hL.ai j (by omega_arith) n hn e')
      rw [k1.1 _ (by simp [hL.alo (by omega_arith : j < L.k) n, ne])]
      exact h.val j (by omega_arith)

theorem consts_ok (hL : LOk L) {b : Addr} {m : Nat} {s : State} (hc : Ctx b s) {is : List Instr} {Q : State → Prop}
    (h : ∀ s', (∀ r, r ∉ L.LO → r ∉ L.AL → r ≠ NI → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → MOk L b m s' → WP isa (.block is) s' Q) :
    WP isa (.block (consts L m ++ is)) s Q := by
  unfold consts
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (const_ok hL) fun s1 h1 => ?_)
  obtain nl : NI ≠ L.lo L.k := fun e => by
    have := hL.lo _ (hL.loM L.k); simp only [List.mem_append, not_or] at this; exact this.1 (by rw [← e]; decide)
  refine wp_li64 nl _ fun s2 v2 k2 => ?_
  obtain a3L : Reg.a3 ∉ L.LO := (out_iff.mp (hL.baseO (r := .a3) (by decide) (by decide))).2.1
  refine h s2 (fun r hl ha hn => ?_) (by rw [k2.2.1, h1.mem]) (by rw [k2.2.2.1, h1.rd]) (by rw [k2.2.2.2.1, h1.wr])
    (by rw [k2.2.2.2.2, h1.sp]) ⟨ctx_of hc ?_ (by rw [k2.2.2.2.1, h1.wr]), fun j hj => ?_, v2⟩
  · rw [k2.1 r (by simp [hn, ne_of_out hl (hL.loM _)]), h1.gpr r hl ha]
  · rw [k2.1 _ (by simp [ne_of_out a3L (hL.loM _)]), h1.gpr _ a3L (hL.aB (by decide))]
  · obtain ne : L.A j ≠ NI := fun e => hL.aB (r := NI) (by decide) (by rw [← e]; exact hL.am j hj)
    rw [k2.1 _ (by simp [hL.alo hj, ne])]
    exact h1.val j hj

theorem MOk.of {b : Addr} {m : Nat} {s s' : State} (h : MOk L b m s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (hA : ∀ j < L.k, s'.gpr (L.A j) = s.gpr (L.A j)) (hn : s'.gpr NI = s.gpr NI) (hwr : s'.wr = s.wr) : MOk L b m s' :=
  ⟨ctx_of h.ctx h3 hwr, fun j hj => (hA j hj).trans (h.regs j hj), hn.trans h.ni⟩

/-! ## A round of the reduction -/

private theorem mont_mod {m0 ni : Nat} (hi : (m0 * ni + 1) % 2 ^ 64 = 0) (w : Nat) :
    (w + (w * ni % 2 ^ 64) * m0) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod,
    show w + w * ni * m0 = w * (m0 * ni + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m0, Nat.mul_assoc,
      Nat.add_comm],
    Nat.mul_mod, hi, Nat.mul_zero, Nat.zero_mod]

/-- The carry out of `w + q m₀`, for the quotient word `q = w m' mod 2⁶⁴`, is `q ≠ 0`. -/
private theorem mont_carry {m0 ni w : Nat} (hi : (m0 * ni + 1) % 2 ^ 64 = 0) (hw : w < 2 ^ 64) :
    w + (w * ni % 2 ^ 64) * m0 =
      2 ^ 64 * ((w * ni % 2 ^ 64) * m0 / 2 ^ 64 + if 0 < w * ni % 2 ^ 64 then 1 else 0) := by
  obtain h0 := mont_mod hi w
  obtain hz : w = 0 → w * ni % 2 ^ 64 = 0 := by rintro rfl; simp
  generalize w * ni % 2 ^ 64 = q at *
  obtain hd := Nat.div_add_mod (q * m0) (2 ^ 64)
  obtain hl := Nat.mod_lt (q * m0) (show 0 < 2 ^ 64 by decide)
  obtain hq0 : q = 0 → q * m0 = 0 := by rintro rfl; simp
  generalize q * m0 / 2 ^ 64 = H at *
  generalize q * m0 % 2 ^ 64 = L at *
  generalize q * m0 = X at *
  split <;> omega_arith

theorem quot_ok (hL : LOk L) {b : Addr} {m i : Nat} {s : State} (h : MOk L b m s)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    WP isa (.block (quot L i)) s fun s' =>
      (s.gpr (L.V i)).toNat + (s'.gpr (L.V i)).toNat * (wordOf m 0).toNat = 2 ^ 64 * (s'.gpr C).toNat ∧
      Keeps [L.V i, L.lo 0, C] s s' := by
  have k4 := hL.k4
  obtain vo := hL.vt i 0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  obtain ol := hL.lo _ (hL.loM 0)
  simp only [List.mem_append, not_or] at ol
  obtain lC : L.lo 0 ≠ C := ne_of_out ol.1 (by decide)
  obtain va : L.A 0 ≠ L.V i := ne_of_out (out_iff.mp (hL.aO (hL.am 0 (by omega_arith)))).2.2.2 (hL.vM i)
  unfold quot
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => wp_li (imm := 0) (by decide) fun s4 u4 => wp_sltu fun s5 u5 =>
    wp_add fun s6 u6 => WP.block_nil ?_
  obtain q2 : (s2.gpr (L.V i)).toNat = (s.gpr (L.V i)).toNat * (negInv m % 2 ^ 64) % 2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, h.ni, BitVec.toNat_ofNat]
  obtain m2 : s2.gpr (L.A 0) = wordOf m 0 := by rw [u2.other _ va, h.regs 0 (by omega_arith)]
  obtain q5 : s5.gpr (L.V i) = s2.gpr (L.V i) := by rw [u5.other _ vo.1, u4.other _ vo.1, u3.other _ vo.2.2]
  obtain q6 : s6.gpr (L.V i) = s2.gpr (L.V i) := by rw [u6.other _ vo.2.2, q5]
  obtain c3 : s3.gpr C = BitVec.ofNat 64 ((s2.gpr (L.V i)).toNat * (wordOf m 0).toNat / 2 ^ 64) := by rw [u3.gpr, m2]
  obtain c5 : s5.gpr C = s3.gpr C := by rw [u5.other _ (Ne.symm lC), u4.other _ (Ne.symm lC)]
  obtain l5 : (s5.gpr (L.lo 0)).toNat = if 0 < (s2.gpr (L.V i)).toNat then 1 else 0 := by
    rw [u5.gpr, sltu_toNat, u4.gpr, u4.other _ vo.1, u3.other _ vo.2.2]; rfl
  obtain pl : (s2.gpr (L.V i)).toNat * (wordOf m 0).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (s2.gpr (L.V i)).isLt; omega_arith) (by have := (wordOf m 0).isLt; omega_arith)
  obtain c6 : (s6.gpr C).toNat = (s2.gpr (L.V i)).toNat * (wordOf m 0).toNat / 2 ^ 64 +
      if 0 < (s2.gpr (L.V i)).toNat then 1 else 0 := by
    obtain bl : (if 0 < (s2.gpr (L.V i)).toNat then 1 else 0) ≤ 1 := by split <;> decide
    obtain bd : (s2.gpr (L.V i)).toNat * (wordOf m 0).toNat / 2 ^ 64 < 2 ^ 64 - 1 :=
      Nat.div_lt_of_lt_mul (by omega_using [pl])
    rw [u6.gpr, BitVec.toNat_add, l5, c5, c3, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := _ / _) (by omega_using [bd]), Nat.mod_eq_of_lt (by omega_using [bd, bl])]
  obtain mc := mont_carry hinv (s.gpr (L.V i)).isLt
  rw [← q2] at mc
  refine ⟨by rw [q6, c6]; exact mc, ?_⟩
  exact ((((upd_keeps u2).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
    (upd_keeps u5)).trans (upd_keeps u6) |>.mono (by simp)

theorem top_ok (hL : LOk L) {b : Addr} {i : Nat} (hi : i < L.k) {s : State} (hc : Ctx b s) :
    WP isa (.block (top L i)) s fun s' =>
      (s'.gpr (L.V i)).toNat + 2 ^ 64 * (s'.gpr TOP).toNat =
        dw s.mem b (L.P (L.k + i)) + (s.gpr C).toNat + (s.gpr TOP).toNat ∧ Keeps [L.V i, L.lo 0, TOP] s s' := by
  obtain ⟨p1, p2⟩ := hL.p (j := L.k + i) (by omega_arith)
  obtain vt := hL.vt i 0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vt
  obtain vB : L.V i ∉ base := fun hm => by
    have := hL.vo _ (hL.vM i); simp only [List.mem_append, not_or] at this; exact this.1.1.1 hm
  obtain vT : L.V i ≠ TOP := ne_of_out vB (by decide)
  obtain ol := hL.lo _ (hL.loM 0)
  simp only [List.mem_append, not_or] at ol
  obtain lC : L.lo 0 ≠ C := ne_of_out ol.1 (by decide)
  obtain lT : L.lo 0 ≠ TOP := ne_of_out ol.1 (by decide)
  unfold top
  refine ld_ok hc p1 p2 fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => wp_add fun s4 u4 => wp_sltu fun s5 u5 =>
    wp_add fun s6 u6 => WP.block_nil ?_
  obtain v1 : (s1.gpr (L.V i)).toNat = dw s.mem b (L.P (L.k + i)) := by rw [u1.gpr]; rfl
  obtain c1 : s1.gpr C = s.gpr C := u1.other _ (Ne.symm vt.2.2)
  obtain e1 := carry (s1.gpr (L.V i)) (s1.gpr C)
  obtain l1 := carry_le (s1.gpr (L.V i) + s1.gpr C < s1.gpr C)
  obtain l3 : s3.gpr (L.lo 0) = if s1.gpr (L.V i) + s1.gpr C < s1.gpr C then 1 else 0 := by
    rw [u3.gpr, u2.gpr, u2.other _ (Ne.symm vt.2.2)]
  obtain v3 : s3.gpr (L.V i) = s1.gpr (L.V i) + s1.gpr C := by rw [u3.other _ vt.1, u2.gpr]
  rw [← l3, ← v3, v1, c1] at e1
  rw [← l3] at l1
  obtain t3 : s3.gpr TOP = s.gpr TOP := by
    rw [u3.other _ (Ne.symm lT), u2.other _ (Ne.symm vT), u1.other _ (Ne.symm vT)]
  obtain e2 := carry (s3.gpr (L.V i)) (s3.gpr TOP)
  obtain l2 := carry_le (s3.gpr (L.V i) + s3.gpr TOP < s3.gpr TOP)
  obtain t5 : s5.gpr TOP = if s3.gpr (L.V i) + s3.gpr TOP < s3.gpr TOP then 1 else 0 := by
    rw [u5.gpr, u4.gpr, u4.other _ (Ne.symm vT)]
  obtain v5 : s5.gpr (L.V i) = s3.gpr (L.V i) + s3.gpr TOP := by rw [u5.other _ vT, u4.gpr]
  rw [← t5, ← v5, t3] at e2
  rw [← t5] at l2
  obtain l5 : s5.gpr (L.lo 0) = s3.gpr (L.lo 0) := by rw [u5.other _ lT, u4.other _ (Ne.symm vt.1)]
  obtain t6 : (s6.gpr TOP).toNat = (s5.gpr TOP).toNat + (s3.gpr (L.lo 0)).toNat := by
    rw [u6.gpr, BitVec.toNat_add, l5, Nat.mod_eq_of_lt (by omega_using [l1, l2])]
  refine ⟨?_, ?_⟩
  · rw [u6.other _ vT, t6]; omega_using [e1, e2]
  · exact (((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
      (upd_keeps u5)).trans (upd_keeps u6) |>.mono (by simp)

/-! ## The rounds -/

/-- The words of the product above round `i`'s window. -/
abbrev up (L : Lay) (m : Mem) (b : Addr) (i : Nat) : Nat := colsV (fun j => dw m b (L.P (L.k + i + j))) (L.k - i)

/-- After `i` rounds. -/
structure RedInv (L : Lay) (b : Addr) (m : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ TOP :: clobR L → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∃ Q < (2 ^ 64) ^ i, (2 ^ 64) ^ i * (rv L s i L.k + (2 ^ 64) ^ L.k * ((s.gpr TOP).toNat + up L s0.mem b i)) =
    pw L s0.mem b + Q * m

private theorem round_alg {B E X R v R1 q M0 M1 m c1 c2 p w t t' u P Q E8 X' W W' U : Nat}
    (h8 : E8 = E * B) (hX : X' = X * B) (hW : W = v + B * R1) (hW' : W' = R + E * w) (hU : U = p + B * u)
    (hq : v + q * M0 = B * c1) (hr : R + E * c2 = R1 + c1 + M1 * q) (ht : w + B * t' = p + c2 + t)
    (hm : m = M0 + B * M1) (hv : X * (W + E8 * (t + U)) = P + Q * m) :
    X' * (W' + E8 * (t' + u)) = P + (Q + X * q) * m := by
  subst h8 hX hW hW' hU
  calc X * B * ((R + E * w) + E * B * (t' + u))
      = X * (B * R + B * E * (w + B * t') + E * B * (B * u)) := by grind
    _ = X * (B * (R + E * c2) + E * B * (p + t) + E * B * (B * u)) := by rw [ht]; grind
    _ = X * (B * c1 + B * R1 + B * (M1 * q) + E * B * (p + t) + E * B * (B * u)) := by rw [hr]; grind
    _ = X * ((v + B * R1) + E * B * (t + (p + B * u))) + X * q * (M0 + B * M1) := by rw [← hq]; grind
    _ = _ := by rw [hv, hm]; grind

theorem up_succ (m : Mem) (b : Addr) {i : Nat} (hi : i < L.k) :
    up L m b i = dw m b (L.P (L.k + i)) + 2 ^ 64 * up L m b (i + 1) := by
  obtain ⟨l, hl⟩ : ∃ l, L.k - i = l + 1 := ⟨L.k - 1 - i, by omega_arith⟩
  rw [up, up, hl, show L.k - (i + 1) = l by omega_arith, colsV_shift, Nat.add_zero,
    colsV_congr (f := fun j => dw m b (L.P (L.k + i + (j + 1)))) (g := fun j => dw m b (L.P (L.k + (i + 1) + j)))
      fun j _ => by rw [show L.k + i + (j + 1) = L.k + (i + 1) + j by omega_arith]]

theorem top_iff {r : Reg} : r ∉ TOP :: clobR L ↔ r ≠ TOP ∧ r ∉ clobR L := by
  simp only [List.mem_cons (b := TOP), not_or, ne_eq]

theorem LOk.aT (hL : LOk L) {r : Reg} (hr : r ∈ L.AL) : r ∉ TOP :: clobR L :=
  top_iff.mpr ⟨fun e => hL.aB (r := TOP) (by decide) (e ▸ hr), hL.aO hr⟩

theorem round_ok (hL : LOk L) {b : Addr} {m : Nat} {s0 : State} (h0 : MOk L b m s0)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (hm : m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) (L.k - 1))
    {i : Nat} (hi : i < L.k) {s : State} (h : RedInv L b m s0 i s) :
    WP isa (.block (redRound L i)) s (RedInv L b m s0 (i + 1)) := by
  have k4 := hL.k4
  obtain ⟨l, hl⟩ : ∃ l, L.k = l + 1 := ⟨L.k - 1, by omega_arith⟩
  have hl' : L.k - 1 = l := by omega_arith
  rw [hl'] at hm
  obtain a3 : Reg.a3 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain ni : NI ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain hM : MOk L b m s := h0.of (h.gpr _ (top_iff.mpr ⟨by decide, a3⟩)) (fun j hj => h.gpr _ (hL.aT (hL.am j hj)))
    (h.gpr _ (top_iff.mpr ⟨by decide, ni⟩)) h.wr
  unfold redRound
  refine WP.block_append (WP.mono (quot_ok hL (i := i) hM hinv) fun s1 ⟨e1, k1⟩ => ?_)
  obtain tO : TOP ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain g1 : ∀ r, r ∉ clobR L → s1.gpr r = s.gpr r := fun r hr => by
    obtain o := out_iff.mp hr
    exact k1.1 r (by simp [ne_of_out o.2.2.2 (hL.vM i), ne_of_out o.2.1 (hL.loM 0), o.1])
  obtain hM1 : MOk L b m s1 := hM.of (g1 _ a3) (fun j hj => g1 _ (hL.aO (hL.am j hj))) (g1 _ ni) k1.2.2.2.1
  obtain dis : ∀ j < l, L.V i ≠ L.V (i + 1 + j) := fun j hj => hL.vne (by omega_arith) (by omega_arith)
  obtain vv := hL.vo _ (hL.vM i)
  simp only [List.mem_append, not_or] at vv
  rw [hl']
  refine WP.block_append (WP.mono (row_ok hL (acc := true) (x := fun j => L.A (j + 1)) (y := L.V i) (i := i + 1) (n := l)
    (fun j hj => hL.aO (hL.am _ (by omega_arith))) (by omega_arith) ⟨vv.1.1.2, vv.1.2, ne_of_out vv.1.1.1 (by decide)⟩ dis l
    (Nat.le_refl _)) fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hM1.ctx (h2.out hL _ a3) h2.wr
  refine WP.mono (top_ok hL hi hc2) fun s3 ⟨e3, k3⟩ => ?_
  obtain m2 : s2.mem = s0.mem := by rw [h2.mem, k1.2.1, h.mem]
  refine ⟨fun r hr => ?_, by rw [k3.2.1, m2], by rw [k3.2.2.1, h2.rd, k1.2.2.1, h.rd],
    by rw [k3.2.2.2.1, h2.wr, k1.2.2.2.1, h.wr], by rw [k3.2.2.2.2, h2.sp, k1.2.2.2.2, h.sp], ?_⟩
  · obtain ⟨a, d⟩ := top_iff.mp hr
    obtain o := out_iff.mp d
    rw [k3.1 r (by simp [a, ne_of_out o.2.2.2 (hL.vM i), ne_of_out o.2.1 (hL.loM 0)]), h2.out hL r d, g1 r d, h.gpr r hr]
  · obtain ⟨Q, hQ, hv⟩ := h.val
    have e2 := h2.val
    simp only [↓reduceIte] at e2
    obtain t2 : s2.gpr TOP = s.gpr TOP := by rw [h2.out hL _ tO, g1 _ tO]
    rw [m2, t2] at e3
    obtain xA : colsV (fun j => (s1.gpr (L.A (j + 1))).toNat) l = colsV (fun j => (wordOf m (j + 1)).toNat) l :=
      colsV_congr fun j hj => by rw [hM1.regs _ (by omega_arith)]
    obtain vt : ∀ j, L.V j ≠ L.lo 0 ∧ L.V j ≠ C ∧ L.V j ≠ TOP := fun j => by
      obtain a := hL.vt j 0
      obtain b := hL.vo _ (hL.vM j)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at a
      simp only [List.mem_append, not_or] at b
      exact ⟨a.1, a.2.2, ne_of_out b.1.1.1 (by decide)⟩
    obtain w1 : rv L s1 (i + 1) l = colsV (fun j => (s.gpr (L.V (i + (j + 1)))).toNat) l := colsV_congr fun j hj => by
      rw [k1.1 _ (by simp [Ne.symm (dis j hj), (vt (i + 1 + j)).1, (vt (i + 1 + j)).2.1]),
        show i + 1 + j = i + (j + 1) by omega_arith]
    obtain w3 : rv L s3 (i + 1) L.k = rv L s2 (i + 1) l + (2 ^ 64) ^ l * (s3.gpr (L.V i)).toNat := by
      rw [rv, hl, colsV_succ, show i + 1 + l = i + L.k by omega_arith, Lay.V_add,
        colsV_congr (g := fun j => (s2.gpr (L.V (i + 1 + j))).toNat) fun j hj => by
          rw [k3.1 _ (by simp [Ne.symm (dis j hj), (vt (i + 1 + j)).1, (vt (i + 1 + j)).2.2])]]
    obtain hu := up_succ (L := L) s0.mem b hi
    obtain hq := (s1.gpr (L.V i)).isLt
    refine ⟨Q + (2 ^ 64) ^ i * (s1.gpr (L.V i)).toNat, ?_, ?_⟩
    · obtain hle : (2 ^ 64) ^ i * ((s1.gpr (L.V i)).toNat + 1) ≤ (2 ^ 64) ^ i * 2 ^ 64 :=
        Nat.mul_le_mul_left _ (by omega_using [hq])
      rw [show ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 from Nat.pow_succ ..]
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega_using [hQ, hle]
    · rw [w1, xA] at e2
      refine round_alg (E := (2 ^ 64) ^ l) (by rw [hl]; exact Nat.pow_succ ..) (Nat.pow_succ ..) ?_ w3 hu e1 e2 e3 hm hv
      rw [rv, hl, colsV_shift, Nat.add_zero]

/-- After `n` words of the product loaded. -/
structure LdInv (L : Lay) (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ L.VL → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, (s.gpr (L.V j)).toNat = dw s0.mem b (L.P j)

theorem ldP_ok (hL : LOk L) {b : Addr} {s0 : State} (hc : Ctx b s0) :
    WP isa (.block ((List.range L.k).flatMap fun j => [.load .d (L.V j) .a3 (L.P j)])) s0 (LdInv L b s0 L.k) := by
  obtain a3 := (out_iff.mp (hL.baseO (r := .a3) (by decide) (by decide))).2.2.2
  refine wp_range_flatMap (M := isa) (LdInv L b s0) (fun n s hn h => ?_) L.k (Nat.le_refl _) s0
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨p1, p2⟩ := hL.p (j := n) (by omega_arith)
  refine ld_ok (ctx_of hc (h.gpr _ a3) h.wr) p1 p2 fun s1 u1 => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u1.other r (ne_of_out hr (hL.vM n)), h.gpr r hr], by rw [u1.mem, h.mem],
    by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], fun j hj => ?_⟩
  by_cases e : j = n
  · subst e; rw [u1.gpr, h.mem]; rfl
  · rw [u1.other _ (hL.vne (by omega_arith) (by omega_arith))]; exact h.val j (by omega_arith)

private theorem red_start {f : Nat → Nat} {R t m k n : Nat} (hR : R = colsV f k) (ht : t = 0) (hn : n = k + k) :
    (2 ^ 64) ^ 0 * (R + (2 ^ 64) ^ k * (t + colsV (fun j => f (k + 0 + j)) (k - 0))) = colsV f n + 0 * m := by
  subst hn hR ht
  rw [colsV_split, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.add_zero]

theorem red_ok (hL : LOk L) {b : Addr} {m : Nat} {s : State} (h : MOk L b m s)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (hm : m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) (L.k - 1)) :
    WP isa (.block (red L)) s (RedInv L b m s L.k) := by
  unfold red
  refine WP.block_append (WP.mono (ldP_ok hL h.ctx) fun s1 h1 => ?_)
  refine wp_li (imm := 0) (by decide) fun s2 u2 => ?_
  obtain vT : ∀ j, L.V j ≠ TOP := fun j => by
    obtain b := hL.vo _ (hL.vM j); simp only [List.mem_append, not_or] at b; exact ne_of_out b.1.1.1 (by decide)
  refine wp_range_flatMap (M := isa) (RedInv L b m s) (fun i s' hi h' => round_ok hL h hinv hm hi h') L.k (Nat.le_refl _) s2
    ⟨fun r hr => ?_, by rw [u2.mem, h1.mem], by rw [u2.rd, h1.rd], by rw [u2.wr, h1.wr], by rw [u2.sp, h1.sp], 0,
      by decide, ?_⟩
  · obtain ⟨a, d⟩ := top_iff.mp hr
    rw [u2.other r a, h1.gpr r (out_iff.mp d).2.2.2]
  · refine red_start (f := fun j => dw s.mem b (L.P j)) (R := rv L s2 0 L.k) (t := (s2.gpr TOP).toNat) ?_
      (by rw [u2.gpr]; rfl) (Nat.two_mul _)
    exact colsV_congr fun j hj => by
      rw [Nat.zero_add, u2.other _ (vT j)]
      exact h1.val j hj

/-! ## The final subtraction -/

open VG.Proof.Weierstrass.RISCV64.P256Field (sbb_ok)
open VG.Proof.X25519.RISCV64 (wp_and)
open VG.Proof.Weierstrass.RISCV64.GenWide (csub_nat toNat_sub_bits ov wp_xor' IsMask sel_mask)

/-- After `j` words of the difference. -/
structure SubInv (L : Lay) (m : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ L.LO → r ∉ L.HI → r ≠ C → r ∉ L.AL → s.gpr r = s0.gpr r
  ar : ∀ l, j ≤ l → l < L.k → s.gpr (L.A l) = wordOf m l
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  cy : (s.gpr C).toNat ≤ 1
  val : colsV (fun i => (s.gpr (L.A i)).toNat) j + colsV (fun i => (wordOf m i).toNat) j =
    colsV (fun i => (s0.gpr (L.V i)).toNat) j + (2 ^ 64) ^ j * (s.gpr C).toNat

private theorem sub_alg {L M V E d c x c' dw' E' : Nat} (hv : L + M = V + E * c) (e : d + dw' + c = x + 2 ^ 64 * c')
    (hE : E' = E * 2 ^ 64) : L + E * d + (M + E * dw') = V + E * x + E' * c' := by
  subst hE
  obtain key : E * d + E * dw' + E * c = E * x + E * 2 ^ 64 * c' := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e]
  omega_using [hv, key]

theorem subStep_ok (hL : LOk L) {m : Nat} {s0 : State} {j : Nat} (hj : j < L.k) {s : State}
    (h : SubInv L m s0 j s) : WP isa (.block (subStep L j)) s (SubInv L m s0 (j + 1)) := by
  obtain lM := hL.loM j
  obtain hM := hL.hiM j
  obtain ol := hL.lo _ lM
  simp only [List.mem_append, not_or] at ol
  obtain oh := hL.hi _ hM
  obtain aM := hL.am j hj
  obtain oa := hL.ao _ aM
  simp only [List.mem_append, not_or] at oa
  obtain vv := hL.vo _ (hL.vM j)
  simp only [List.mem_append, not_or] at vv
  obtain lC : L.lo j ≠ C := ne_of_out ol.1 (by decide)
  obtain hC : L.hi j ≠ C := ne_of_out oh (by decide)
  obtain aC : L.A j ≠ C := ne_of_out oa.1.1 (by decide)
  obtain la : L.lo j ≠ L.A j := Ne.symm (ne_of_out oa.1.2 lM)
  unfold subStep
  refine WP.mono (sbb_ok (d := L.A j) (x := L.V j) (y := L.A j) (c := C) (u := L.lo j) (v := L.hi j) (hdc := aC)
    (hud := la) (huc := lC) (hvd := Ne.symm (ne_of_out oa.2 hM)) (hvc := hC) (huv := ne_of_out ol.2 hM)
    (hux := Ne.symm (ne_of_out vv.1.1.2 lM)) (huy := la)) fun s2 ⟨e2', k2⟩ => ?_
  obtain v1 : s.gpr (L.V j) = s0.gpr (L.V j) := h.gpr _ vv.1.1.2 vv.1.2 (ne_of_out vv.1.1.1 (by decide)) vv.2
  obtain ⟨ev, ec⟩ := e2' h.cy
  rw [h.ar j (Nat.le_refl _) hj, v1] at ev
  refine ⟨fun r hl hh hc ha => ?_, fun l hl hl7 => ?_, by rw [k2.2.1, h.mem], by rw [k2.2.2.1, h.rd],
    by rw [k2.2.2.2.1, h.wr], by rw [k2.2.2.2.2, h.sp], ec, ?_⟩
  · rw [k2.1 r (by simp [ne_of_out ha aM, ne_of_out hl lM, ne_of_out hh hM, hc]), h.gpr r hl hh hc ha]
  · obtain o := hL.ao _ (hL.am l hl7)
    simp only [List.mem_append, not_or] at o
    obtain ne : L.A l ≠ L.A j := fun e => absurd (hL.ai l hl7 j hj e) (by omega_arith)
    rw [k2.1 _ (by simp [ne, ne_of_out o.1.2 lM, ne_of_out o.2 hM, ne_of_out o.1.1 (by decide : C ∈ base)])]
    exact h.ar l (by omega_arith) hl7
  · obtain low : colsV (fun i => (s2.gpr (L.A i)).toNat) j = colsV (fun i => (s.gpr (L.A i)).toNat) j :=
      colsV_congr fun i hi => by
        obtain o := hL.ao _ (hL.am i (by omega_arith))
        simp only [List.mem_append, not_or] at o
        obtain ne : L.A i ≠ L.A j := fun e => absurd (hL.ai i (by omega_arith) j hj e) (by omega_arith)
        rw [k2.1 _ (by simp [ne, ne_of_out o.1.2 lM, ne_of_out o.2 hM, ne_of_out o.1.1 (by decide : C ∈ base)])]
    rw [colsV_succ, colsV_succ, colsV_succ, low]
    exact sub_alg h.val ev (Nat.pow_succ ..)

/-- After `j` words of the selection. -/
structure SelInv (L : Lay) (O : Addr) (sel : Prop) [Decidable sel] (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ L.VL → s.gpr r = s0.gpr r
  vr : ∀ l, j ≤ l → l < L.k → s.gpr (L.V l) = s0.gpr (L.V l)
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 8 * L.k⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = if sel then (s0.gpr (L.V i)).toNat else (s0.gpr (L.A i)).toNat

theorem selStep_ok (hL : LOk L) {O : Addr} {s0 : State} (h2 : s0.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < L.k, InRegions s0.wr (O + BitVec.ofNat 64 (8 * i)) 8) (hm : IsMask (s0.gpr TOP))
    {j : Nat} (hj : j < L.k) {s : State} (h : SelInv L O (s0.gpr TOP = BitVec.allOnes 64) s0 j s) :
    WP isa (.block (selStep L j)) s (SelInv L O (s0.gpr TOP = BitVec.allOnes 64) s0 (j + 1)) := by
  have k8 := hL.k8
  obtain vM := hL.vM j
  obtain vv := hL.vo _ vM
  simp only [List.mem_append, not_or] at vv
  obtain vT : L.V j ≠ TOP := ne_of_out vv.1.1.1 (by decide)
  obtain v2 : L.V j ≠ .t2 := ne_of_out vv.1.1.1 (by decide)
  obtain oA := (out_iff.mp (hL.aO (hL.am j hj))).2.2.2
  obtain va : L.A j ≠ L.V j := ne_of_out oA vM
  obtain t2V : Reg.t2 ∉ L.VL := (out_iff.mp (hL.baseO (r := .t2) (by decide) (by decide))).2.2.2
  obtain tV : TOP ∉ L.VL := (out_iff.mp (hL.baseO (r := TOP) (by decide) (by decide))).2.2.2
  unfold selStep
  refine wp_xor' fun s2 u2 => wp_and fun s3 u3 => wp_xor' fun s4 u4 => ?_
  refine wp_sd (by omega_arith) (by rw [u4.other _ (Ne.symm v2), u3.other _ (Ne.symm v2), u2.other _ (Ne.symm v2),
    h.gpr _ t2V, h2]) (al8 oal (by omega_arith))
    (by rw [u4.wr, u3.wr, u2.wr, h.wr]; exact ow j hj) fun s5 u5 => WP.block_nil ?_
  obtain v4 : s4.gpr (L.V j) = s0.gpr (L.A j) ^^^ ((s0.gpr (L.V j) ^^^ s0.gpr (L.A j)) &&& s0.gpr TOP) := by
    rw [u4.gpr, u3.gpr, u3.other _ va, u2.other _ va, u2.gpr, u2.other TOP (Ne.symm vT), h.gpr _ oA, h.gpr _ tV,
      h.vr j (Nat.le_refl _) hj, BitVec.xor_comm]
  rw [sel_mask hm] at v4
  have hm5 : s5.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s4.gpr (L.V j)) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem]
  refine ⟨fun r hr => ?_, fun l hl hl' => ?_, by rw [u5.rd, u4.rd, u3.rd, u2.rd, h.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, h.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, h.sp], ?_, fun i hi => ?_⟩
  · have nr := ne_of_out hr vM
    rw [u5.gpr, u4.other r nr, u3.other r nr, u2.other r nr, h.gpr r hr]
  · have nr : L.V l ≠ L.V j := Ne.symm (hL.vne (by omega_arith) (by omega_arith))
    rw [u5.gpr, u4.other _ nr, u3.other _ nr, u2.other _ nr, h.vr l (by omega_arith) hl']
  · rw [hm5]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [show (⟨O, 8 * L.k⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 8 * L.k⟩ by simp]
    exact Offset.contains O (by omega_arith) (by omega_arith) (by omega_arith)
  · rw [hm5]
    by_cases e : i = j
    · subst e
      rw [dw_write_self, v4]
      split <;> rfl
    · rw [dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.val i (by omega_arith)

private theorem csub_out {D' Mv L E Tk c V R m' : Nat} (hD : D' < E) (hM : Mv < E) (hV : V = L + E * Tk) (hV2 : V < 2 * Mv)
    (hs : D' + Mv = L + E * c) (hc : c ≤ 1) {sel : Prop} (hsel : sel ↔ Tk = 0 ∧ c = 1)
    (h1 : sel → R = L) (h0 : ¬ sel → R = D') (hm : m' = Mv) : R = V % m' := by
  obtain ⟨-, -, a, b⟩ := csub_nat hD hM hV hV2 hs hc
  subst hm
  by_cases h : sel
  · rw [h1 h, a (hsel.mp h)]
  · rw [h0 h, b (fun h' => h (hsel.mpr h'))]

theorem csub_ok (hL : LOk L) {b O : Addr} {m : Nat} {s : State} (h : MOk L b m s) (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < L.k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8)
    (hm : m = colsV (fun i => (wordOf m i).toNat) L.k)
    (hV : rv L s 0 L.k + (2 ^ 64) ^ L.k * (s.gpr TOP).toNat < 2 * m) :
    WP isa (.block (csub L)) s fun s' =>
      (∀ r, r ∉ TOP :: clobR L → r ∉ L.AL → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨O, 8 * L.k⟩] s.mem s'.mem ∧
      ov s'.mem O L.k = (rv L s 0 L.k + (2 ^ 64) ^ L.k * (s.gpr TOP).toNat) % m := by
  unfold csub
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s1 u1 => ?_
  obtain aC : ∀ j < L.k, L.A j ≠ C := fun j hj => (out_iff.mp (hL.aO (hL.am j hj))).1
  obtain vB : ∀ j, L.V j ∉ base ∧ L.V j ∉ L.LO ∧ L.V j ∉ L.HI ∧ L.V j ∉ L.AL := fun j => by
    obtain b := hL.vo _ (hL.vM j); simp only [List.mem_append, not_or] at b; exact ⟨b.1.1.1, b.1.1.2, b.1.2, b.2⟩
  obtain vC : ∀ j, L.V j ≠ C := fun j => ne_of_out (vB j).1 (by decide)
  obtain c1 : (s1.gpr C).toNat = 0 := by rw [u1.gpr]; rfl
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SubInv L m s1) (fun j s' hj h' => subStep_ok hL hj h') L.k
    (Nat.le_refl _) s1 ⟨fun _ _ _ _ _ => rfl, fun l _ hl => by rw [u1.other _ (aC l hl)]; exact h.regs l hl, rfl, rfl, rfl,
      rfl, by rw [c1]; decide, by rw [c1]; rfl⟩) fun s3 h3 => ?_)
  refine wp_sub fun s4 u4 => ?_
  obtain tO := out_iff.mp (hL.baseO (r := TOP) (by decide) (by decide))
  obtain t3 : s3.gpr TOP = s.gpr TOP := by
    rw [h3.gpr _ tO.2.1 tO.2.2.1 tO.1 (hL.aB (by decide)), u1.other _ (by decide)]
  obtain v1 : ∀ j, s1.gpr (L.V j) = s.gpr (L.V j) := fun j => u1.other _ (vC j)
  have hs := h3.val
  obtain hLv : colsV (fun i => (s1.gpr (L.V i)).toNat) L.k = rv L s 0 L.k :=
    colsV_congr fun j _ => by rw [v1, Nat.zero_add]
  rw [hLv, ← hm] at hs
  obtain hD : colsV (fun i => (s3.gpr (L.A i)).toNat) L.k < (2 ^ 64) ^ L.k := colsV_lt _ (fun i => (s3.gpr (L.A i)).isLt) L.k
  obtain hMl : m < (2 ^ 64) ^ L.k := by
    rw [hm]; exact colsV_lt _ (fun i => (wordOf m i).isLt) L.k
  obtain ⟨hT1, hno, -, -⟩ := csub_nat (V := rv L s 0 L.k + (2 ^ 64) ^ L.k * (s.gpr TOP).toNat) hD hMl rfl hV hs h3.cy
  obtain ⟨hmask, hall⟩ := toNat_sub_bits (x := s3.gpr TOP) (c := s3.gpr C) (by rw [t3]; exact hT1) h3.cy
    (by rw [t3]; exact hno)
  rw [← u4.gpr] at hmask hall
  rw [t3] at hall
  obtain g4 : ∀ r, r ∉ TOP :: clobR L → r ∉ L.AL → s4.gpr r = s.gpr r := fun r hr ha => by
    obtain ⟨a, d⟩ := top_iff.mp hr
    obtain o := out_iff.mp d
    rw [u4.other r a, h3.gpr r o.2.1 o.2.2.1 o.1 ha, u1.other r o.1]
  obtain wr4 : s4.wr = s.wr := by rw [u4.wr, h3.wr, u1.wr]
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv L O (s4.gpr TOP = BitVec.allOnes 64) s4)
    (fun j s' hj h' => selStep_ok hL (by
      rw [g4 _ (top_iff.mpr ⟨by decide, hL.baseO (by decide) (by decide)⟩) (hL.aB (by decide)), h2]) oal
      (by rw [wr4]; exact ow) hmask hj h') L.k (Nat.le_refl _) s4
    ⟨fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s5 h5 => ?_
  refine ⟨fun r hr ha => ?_, by rw [h5.rd, u4.rd, h3.rd, u1.rd], by rw [h5.wr, wr4],
    by rw [h5.sp, u4.sp, h3.sp, u1.sp], ?_, ?_⟩
  · rw [h5.gpr r (out_iff.mp (top_iff.mp hr).2).2.2.2, g4 r hr ha]
  · rw [← u1.mem, ← h3.mem, ← u4.mem]; exact h5.frame
  · refine csub_out hD hMl rfl hV hs h3.cy hall (fun hsel => ?_) (fun hsel => ?_) rfl
    · exact colsV_congr fun j hj => by
        rw [h5.val j hj, ite_eq_left hsel, u4.other _ (ne_of_out (vB j).1 (by decide)),
          h3.gpr _ (vB j).2.1 (vB j).2.2.1 (vC j) (vB j).2.2.2, v1, Nat.zero_add]
    · exact colsV_congr fun j hj => by
        rw [h5.val j hj, ite_eq_right hsel, u4.other _ fun e => hL.aB (r := TOP) (by decide) (e ▸ hL.am j hj)]

/-! ## The registers kept -/

/-- Where they are kept. -/
abbrev SR (L : Lay) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 L.sv, 8 * L.KR.length⟩

/-- After `n` registers kept. -/
structure SvInv (L : Lay) (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [SR L b] s0.mem s.mem
  saved : ∀ i < n, s.mem.readW (b + BitVec.ofNat 64 (L.sv + 8 * i)) 64 = s0.gpr (L.KR.getD i .s6)

theorem save_ok (hL : LOk L) {b : Addr} {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (save L)) s0 (SvInv L b s0 L.KR.length) := by
  have := hL.sv8; have := hL.svp; have := hL.pp2
  refine wp_range_flatMap (M := isa) (SvInv L b s0) (fun n s hn h => ?_) _ (Nat.le_refl _) s0
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine sd_ok (ctx_of hc (by rw [h.gpr]) h.wr) (by omega_arith) (by omega_arith) fun s1 u1 => WP.block_nil ?_
  refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], ?_, fun i hi => ?_⟩
  · rw [u1.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))
  · rw [u1.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- After `n` registers loaded back, to `v`. -/
structure RsInv (L : Lay) (v : Nat → BitVec 64) (s0 : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (L.KR.getD i .s6) = v i
  others : ∀ r, r ∉ L.KR → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp

theorem restore_ok (hL : LOk L) {b : Addr} {v : Nat → BitVec 64} {s0 : State} (hc : Ctx b s0)
    (hs : ∀ i < L.KR.length, s0.mem.readW (b + BitVec.ofNat 64 (L.sv + 8 * i)) 64 = v i) :
    WP isa (.block (restore L)) s0 (RsInv L v s0 L.KR.length) := by
  have := hL.sv8; have := hL.svp; have := hL.pp2
  refine wp_range_flatMap (M := isa) (RsInv L v s0) (fun n s hn h => ?_) _ (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine ld_ok (ctx_of hc (h.others _ fun hk => hL.ko _ hk (by decide)) h.wr) (by omega_arith)
    (by omega_arith) fun s1 u1 => WP.block_nil ?_
  rw [h.mem, hs n hn] at u1
  refine ⟨fun i hi => ?_, fun r hr => ?_, by rw [u1.mem, h.mem], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr],
    by rw [u1.sp, h.sp]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [u1.other _ fun e => absurd (hL.ki i (by omega_arith) n hn e) (by omega_arith)]
      exact h.restored i hi
    · exact u1.gpr
  · rw [u1.other _ (ne_of_out hr (getD_mem hn _))]; exact h.others r hr

/-! ## The operation -/

theorem colsV_wordOf (m n : Nat) : colsV (fun j => (wordOf m j).toNat) n = m % (2 ^ 64) ^ n :=
  GenWide.colsV_wordOf m n

theorem wordOf_split {m k : Nat} (hk : 0 < k) (hm : m < (2 ^ 64) ^ k) :
    m = colsV (fun i => (wordOf m i).toNat) k ∧
    m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) (k - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega_arith⟩
  obtain h : m = colsV (fun i => (wordOf m i).toNat) (l + 1) := by
    rw [colsV_wordOf, Nat.mod_eq_of_lt hm]
  exact ⟨h, h.trans (colsV_shift _ _)⟩

/-- The value after the rounds is Montgomery's. -/
private theorem red_out {V X B Q P m R E : Nat} (hP : P = X * B) (hv : E * V = P + Q * m) (hE : E = R) (hX : X < R)
    (hB : B < m) (hQ : Q < E) : V < 2 * m ∧ V % m * R % m = X * B % m := by
  subst hP hE
  exact GenWide.mont_nat (by rw [Nat.mul_comm]; exact hv) hX hB hQ

/-- The operation's own working space. -/
abbrev own (L : Lay) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 L.sv, L.pp + 16 * L.k - L.sv⟩

/-- What a tail does: `[O] = P R⁻¹ mod m` for the product `P` of a number below `R` and one below `m`. -/
def TailOk (L : Lay) (m : Nat) (tail : List Instr) : Prop :=
  ∀ {b O : Addr} {s : State} {X Z : Nat}, Ctx b s → s.gpr .t2 = O → O.toNat % 8 = 0 →
    (∀ i < L.k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8) → Region.Disjoint ⟨O, 8 * L.k⟩ (own L b) →
    X < (2 ^ 64) ^ L.k → Z < m → pw L s.mem b = X * Z →
    WP isa (.block tail) s fun s' =>
      (∀ r, r ∉ clobP L → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [PR L b, ⟨O, 8 * L.k⟩] s.mem s'.mem ∧ ov s'.mem O L.k < m ∧
      ov s'.mem O L.k * (2 ^ 64) ^ L.k % m = X * Z % m

/-- `[O] = [A] [B] R⁻¹ mod m`, for operands and a result apart from the own working space. -/
theorem fastWith_ok (hL : LOk L) {m : Nat} {tail : List Instr} (o : Order) (ht : TailOk L m tail) {b A B O : Addr} {s : State}
    (hc : Ctx b s) (h4 : s.gpr .t4 = A) (h5 : s.gpr .t5 = B) (ht2 : s.gpr .t2 = O) (aal : A.toNat % 8 = 0)
    (bal : B.toNat % 8 = 0) (oal : O.toNat % 8 = 0)
    (ain : ∀ i < L.k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (bin : ∀ i < L.k, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8)
    (ow : ∀ i < L.k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8)
    (hA : ∀ i < L.k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (own L b))
    (hB : ∀ i < L.k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (own L b))
    (hO : Region.Disjoint ⟨O, 8 * L.k⟩ (own L b)) (hp : xv s.mem B L.k < m) :
    WP isa (fastWith L tail o) s fun s' =>
      ov s'.mem O L.k < m ∧ ov s'.mem O L.k * (2 ^ 64) ^ L.k % m = xv s.mem A L.k * xv s.mem B L.k % m ∧
      Frame [own L b, ⟨O, 8 * L.k⟩] s.mem s'.mem ∧
      (∀ r, r ∉ clobP L ∨ r ∈ L.KR → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain sv8 := hL.sv8; obtain svp := hL.svp; obtain pp2 := hL.pp2
  unfold fastWith
  refine WP.seq (WP.mono (save_ok hL hc) fun s1 h1 => ?_)
  obtain hc1 : Ctx b s1 := ctx_of hc (by rw [h1.gpr]) h1.wr
  obtain sR : Region.Sub (SR L b) (own L b) := Offset.sub b (Nat.le_refl _) (by omega_arith)
  obtain sP : Region.Sub (PR L b) (own L b) := Offset.sub b (by omega_arith) (by omega_arith)
  obtain xA : xv s1.mem A L.k = xv s.mem A L.k := colsV_congr fun i hi => dw_frame h1.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hA i hi) sR
  obtain xB : xv s1.mem B L.k = xv s.mem B L.k := colsV_congr fun i hi => dw_frame h1.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hB i hi) sR
  -- The product.
  refine WP.seq (WP.mono (Q := fun s' : State =>
      (∀ r, r ∉ clobP L → s'.gpr r = s1.gpr r) ∧ s'.rd = s1.rd ∧ s'.wr = s1.wr ∧ s'.sp = s1.sp ∧
      Frame [PR L b] s1.mem s'.mem ∧ pw L s'.mem b = xv s1.mem A L.k * xv s1.mem B L.k) ?_
    fun s2 ⟨g2, rd2, wr2, sp2, f2, v2⟩ => ?_)
  · refine WP.ite (s1.gpr .t4 == s1.gpr .t5) rfl (fun he => ?_) (fun _ => ?_)
    · obtain hAB : A = B := by rw [← h4, ← h5, ← h1.gpr]; exact beq_iff_eq.mp he
      subst hAB
      exact WP.sched (sqrProd_ok hL hc1 (by rw [h1.gpr, h4]) aal (by rw [h1.rd, h1.wr]; exact ain))
    · exact WP.sched (mulProd_ok hL hc1 (by rw [h1.gpr, h4]) (by rw [h1.gpr, h5]) aal bal
        (by rw [h1.rd, h1.wr]; exact ain) (by rw [h1.rd, h1.wr]; exact bin) fun i hi => disj_sub (hB i hi) sP)
  obtain a3 : Reg.a3 ∉ clobP L :=
    clobP_iff.mpr ⟨by decide, by decide, hL.aB (by decide), hL.baseO (by decide) (by decide)⟩
  obtain t2 : Reg.t2 ∉ clobP L :=
    clobP_iff.mpr ⟨by decide, by decide, hL.aB (by decide), hL.baseO (by decide) (by decide)⟩
  -- The reduction.
  refine WP.seq (WP.mono (WP.sched (ht (O := O) (X := xv s.mem A L.k) (Z := xv s.mem B L.k) (ctx_of hc1 (g2 _ a3) wr2) (by rw [g2 _ t2, h1.gpr, ht2]) oal
    (by rw [wr2, h1.wr]; exact ow) hO (colsV_lt _ (fun _ => dw_lt _ _ _) L.k) hp (by rw [v2, xA, xB])))
    fun s5 ⟨g5, rd5, wr5, sp5, f5, v5, v5'⟩ => ?_)
  -- The registers back.
  obtain hc5 : Ctx b s5 := ctx_of hc1 (by rw [g5 _ a3, g2 _ a3]) (by rw [wr5, wr2])
  obtain dP : ∀ i < L.KR.length, Region.Disjoint ⟨b + BitVec.ofNat 64 (L.sv + 8 * i), 8⟩ (PR L b) := fun i hi =>
    Offset.disjoint b (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hsav : ∀ i < L.KR.length, s5.mem.readW (b + BitVec.ofNat 64 (L.sv + 8 * i)) 64 = s.gpr (L.KR.getD i .s6) :=
    fun i hi => by
      rw [← h1.saved i hi]
      obtain c : (⟨b + BitVec.ofNat 64 (L.sv + 8 * i), 8⟩ : Region).Contains (b + BitVec.ofNat 64 (L.sv + 8 * i)) 8 :=
        Region.contains_self _ _
      rw [f5.readW c (fun r hr => ?_) (by decide), f2.readW c (fun r hr => ?_) (by decide)]
      · rw [List.mem_singleton] at hr; subst hr; exact dP i hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dP i hi
        · exact disj_symm (disj_sub hO (Offset.sub b (by omega_arith) (by omega_arith)))
  refine WP.mono (restore_ok hL (v := fun i => s.gpr (L.KR.getD i .s6)) hc5 hsav) fun s6 h6 => ?_
  refine ⟨by rw [h6.mem]; exact v5, by rw [h6.mem]; exact v5', ?_, fun r hr => ?_, by rw [h6.rd, rd5, rd2, h1.rd],
    by rw [h6.wr, wr5, wr2, h1.wr], by rw [h6.sp, sp5, sp2, h1.sp]⟩
  · rw [h6.mem]
    refine ((h1.frame.sub fun r hr => ?_).trans (f2.sub fun r hr => ?_)).trans (f5.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sR⟩
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sP⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sP⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · by_cases hK : r ∈ L.KR
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hK
      have := h6.restored i hi
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, e] at this
    · rw [h6.others r hK, g5 r (hr.resolve_right hK), g2 r (hr.resolve_right hK), h1.gpr]

/-- The constants, the rounds and the final subtraction. -/
theorem tail_ok (hL : LOk L) {m : Nat} (hm : m < (2 ^ 64) ^ L.k)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0) : TailOk L m (tail L m) :=
  fun {b O s X Z} hc ht2 oal ow _ hX hZ hp => by
  obtain ⟨w8, w1⟩ := wordOf_split hL.k0 hm
  obtain a3 : Reg.a3 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain t2 : Reg.t2 ∉ clobR L := hL.baseO (by decide) (by decide)
  obtain ni : NI ∉ clobR L := hL.baseO (by decide) (by decide)
  unfold tail
  refine consts_ok hL (m := m) hc fun s3 g3 m3 rd3 wr3 sp3 hM3 => ?_
  refine WP.block_append (WP.mono (red_ok hL hM3 hinv w1) fun s4 h4' => ?_)
  obtain ⟨Q, hQ, hv⟩ := h4'.val
  obtain hup : up L s3.mem b L.k = 0 := by simp only [up, Nat.sub_self, colsV]
  obtain h08 : rv L s4 L.k L.k = rv L s4 0 L.k := colsV_congr fun j _ => by
    rw [Nat.add_comm L.k j, Lay.V_add, Nat.zero_add]
  rw [hup, Nat.add_zero, h08, m3] at hv
  obtain ⟨hV2, hVm⟩ := red_out hp hv rfl hX hZ hQ
  obtain hM4 : MOk L b m s4 := hM3.of (h4'.gpr _ (top_iff.mpr ⟨by decide, a3⟩))
    (fun j hj => h4'.gpr _ (hL.aT (hL.am j hj))) (h4'.gpr _ (top_iff.mpr ⟨by decide, ni⟩)) h4'.wr
  obtain g4 : ∀ r, r ∉ clobP L → s4.gpr r = s.gpr r := fun r hr => by
    obtain ⟨a, b', c, d⟩ := clobP_iff.mp hr
    rw [h4'.gpr r (top_iff.mpr ⟨a, d⟩), g3 r (out_iff.mp d).2.1 c b']
  obtain wr4 : s4.wr = s.wr := by rw [h4'.wr, wr3]
  refine WP.mono (csub_ok hL hM4 (by
    rw [g4 _ (clobP_iff.mpr ⟨by decide, by decide, hL.aB (by decide), t2⟩), ht2]) oal
    (by rw [wr4]; exact ow) w8 hV2) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [rd5, h4'.rd, rd3], by rw [wr5, wr4], by rw [sp5, h4'.sp, sp3],
    by rw [← m3, ← h4'.mem]; exact f5.mono (by simp), by rw [v5]; exact Nat.mod_lt _ (by omega_using [hZ]),
    by rw [v5]; exact hVm⟩
  obtain ⟨a, _, c, d⟩ := clobP_iff.mp hr
  rw [g5 r (top_iff.mpr ⟨a, d⟩) c, g4 r hr]

end VG.Proof.Weierstrass.RISCV64.Rows
