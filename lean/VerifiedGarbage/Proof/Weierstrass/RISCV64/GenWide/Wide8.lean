module

-- separate module: its proofs build in parallel with the field's code literal, which its importers'
-- constant time evaluates
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Wide8
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sqr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn

/-!
# Multiplication modulo a wide modulus of eight words on RISC-V, in registers: the proofs

`fast` (`Impl/Weierstrass/RISCV64/Wide8.lean`) meets GenWide's specification
of an operation on the pointers (`fast_spec`), so that the functions meet the
contract by register (`mul_rv`, `mulA_rv`), from the steps up:

* a multiply-accumulate step (`mac_ok`, `mac1_ok`) and a row of them
  (`row_ok`, `row1_ok`), for an operand's words however they are fetched
  (`OpsOk`);
* the product (`mulProd_ok`) and the square (`sqrProd_ok`, with GenWide's
  doubling, `diags_ok`) at `SQ`;
* the rounds of Montgomery's reduction (`round_ok`, `red_ok`): after `i`
  rounds, the window, `TOP` and the product's words above are `V` with
  `2^(64 i) V = P + Q m` for some `Q < 2^(64 i)`;
* the final subtraction (`csub_ok`), and the registers kept (`save_ok`,
  `restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Wide8

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Wide8
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv T N SQ)
open VG.Proof.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.Weierstrass.RISCV64.P256Field (upd_keeps sltu_toNat)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## The registers -/

theorem VR_mem (i : Nat) : VR i ∈ VL := by
  obtain h : ∀ k < 8, VL.getD k .t0 ∈ VL := by decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem VR_out {l : List Reg} (h : ∀ r ∈ VL, r ∉ l) (i : Nat) : VR i ∉ l := h _ (VR_mem i)

theorem VR_inj {i j : Nat} (h : VR i = VR j) : i % 8 = j % 8 := by
  obtain e : ∀ k < 8, ∀ l < 8, VL.getD k .t0 = VL.getD l .t0 → k = l := by decide
  exact e _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

theorem VR_add8 (i : Nat) : VR (i + 8) = VR i := by simp only [VR, Nat.add_mod_right]

theorem VR_ne {i j : Nat} (h : i % 8 ≠ j % 8) : VR i ≠ VR j := fun e => h (VR_inj e)

theorem AR_mem : ∀ j < 7, AR j ∈ AL := by decide

theorem AR_inj : ∀ i < 7, ∀ j < 7, AR i = AR j → i = j := by decide

/-! ## A step -/

private theorem mac1_nat {x y t lo hi c u : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (ht : t < 2 ^ 64)
    (hu : u < 2 ^ 64) (hp : lo + 2 ^ 64 * hi = x * y) (h : u + 2 ^ 64 * c = lo + t) :
    u + 2 ^ 64 * (hi + c) = x * y + t ∧ hi + c < 2 ^ 64 := by
  obtain hxy : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  constructor <;> omega_arith

set_option linter.unusedSimpArgs false in
/-- `v + 2⁶⁴ C := x y + v + C`, or without `v`. -/
theorem mac_ok {acc : Bool} {x y v : Reg} (hx : x ∉ [LO, C, v]) (hy : y ∉ [LO, HI, C, v])
    (hv : v ∉ [LO, HI, C]) {s : State} :
    WP isa (.block (mac acc x y v)) s fun s' =>
      (s'.gpr v).toNat + 2 ^ 64 * (s'.gpr C).toNat =
        (s.gpr x).toNat * (s.gpr y).toNat + (if acc then (s.gpr v).toNat else 0) + (s.gpr C).toNat ∧
      Keeps [v, LO, HI, C] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hy hv
  obtain ⟨xl, xc, xv⟩ := hx
  obtain ⟨yl, yh, yc, yv⟩ := hy
  obtain ⟨vl, vh, vc⟩ := hv
  cases acc
  · simp only [mac, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_add fun s3 u3 => wp_sltu fun s4 u4 => wp_add fun s5 u5 =>
      WP.block_nil ?_
    obtain hp := mul_words (s.gpr x) (s.gpr y)
    obtain a2 : s2.gpr v = s.gpr x * s.gpr y := by rw [u2.other _ vh, u1.gpr]
    obtain c2 : s2.gpr C = s.gpr C := by rw [u2.other _ (by decide), u1.other _ (Ne.symm vc)]
    obtain h2 : s2.gpr HI = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xv, u1.other _ yv]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr C := u3.gpr
    obtain l4 : s4.gpr LO = if s2.gpr v + s2.gpr C < s2.gpr C then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vc)]
    obtain e1 := carry (s2.gpr v) (s2.gpr C)
    rw [← l4, ← v3, a2, c2] at e1
    obtain h4 : s4.gpr HI = s2.gpr HI := by rw [u4.other _ (by decide), u3.other _ (Ne.symm vh)]
    obtain c5 : (s5.gpr C).toNat = ((s2.gpr HI).toNat + (s4.gpr LO).toNat) % 2 ^ 64 := by
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
    obtain hp := mul_words (s.gpr x) (s.gpr y)
    obtain a2 : s2.gpr LO = s.gpr x * s.gpr y := by rw [u2.other _ (by decide), u1.gpr]
    obtain h2 : s2.gpr HI = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xl, u1.other _ yl]
    obtain v2 : s2.gpr v = s.gpr v := by rw [u2.other _ vh, u1.other _ vl]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr LO := u3.gpr
    obtain l4 : s4.gpr LO = if s2.gpr v + s2.gpr LO < s2.gpr LO then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vl)]
    obtain e1 := carry (s2.gpr v) (s2.gpr LO)
    rw [← l4, ← v3, a2, v2] at e1
    obtain h4 : s4.gpr HI = s2.gpr HI := by rw [u4.other _ (by decide), u3.other _ (Ne.symm vh)]
    obtain v5 : s5.gpr v = s3.gpr v := by rw [u5.other _ vh, u4.other _ vl]
    obtain c5 : s5.gpr C = s.gpr C := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (Ne.symm vc), u2.other _ (by decide),
        u1.other _ (by decide)]
    obtain l7 : s7.gpr LO = if s5.gpr v + s5.gpr C < s5.gpr C then 1 else 0 := by
      rw [u7.gpr, u6.gpr, u6.other _ (Ne.symm vc)]
    obtain e2 := carry (s5.gpr v) (s5.gpr C)
    rw [← l7, v5, c5] at e2
    obtain h7 : s7.gpr HI = s5.gpr HI := by rw [u7.other _ (by decide), u6.other _ (Ne.symm vh)]
    obtain c8 : (s8.gpr C).toNat = (((s2.gpr HI).toNat + (s4.gpr LO).toNat) % 2 ^ 64 + (s7.gpr LO).toNat) % 2 ^ 64 := by
      rw [u8.gpr, BitVec.toNat_add, h7, u5.gpr, BitVec.toNat_add, h4]
    rw [← h2] at hp
    rw [Nat.add_comm (s.gpr v).toNat] at e1
    obtain ⟨n1, n2⟩ := mac_nat (s.gpr x).isLt (s.gpr y).isLt (s.gpr v).isLt (s.gpr C).isLt hp e1 e2
    refine ⟨?_, ?_⟩
    · rw [c8, Nat.mod_eq_of_lt (a := (s2.gpr HI).toNat + _) (by omega_using [n2]), Nat.mod_eq_of_lt n2,
        u8.other _ vc, u7.other _ vl, u6.gpr, v5, c5]
      exact n1
    · exact ((((((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
        (upd_keeps u5)).trans (upd_keeps u6)).trans (upd_keeps u7)).trans (upd_keeps u8)).mono (by simp)

/-- `v + 2⁶⁴ C := x y + v`, or without `v`. -/
theorem mac1_ok {acc : Bool} {x y v : Reg} (hx : x ∉ [LO, v]) (hy : y ∉ [LO, v])
    (hv : v ∉ [LO, HI, C]) {s : State} :
    WP isa (.block (mac1 acc x y v)) s fun s' =>
      (s'.gpr v).toNat + 2 ^ 64 * (s'.gpr C).toNat =
        (s.gpr x).toNat * (s.gpr y).toNat + (if acc then (s.gpr v).toNat else 0) ∧
      Keeps [v, LO, HI, C] s s' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hy hv
  obtain ⟨xl, xv⟩ := hx
  obtain ⟨yl, yv⟩ := hy
  obtain ⟨vl, vh, vc⟩ := hv
  cases acc
  · simp only [mac1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => WP.block_nil ?_
    obtain hp := mul_words (s.gpr x) (s.gpr y)
    refine ⟨?_, ((upd_keeps u1).trans (upd_keeps u2)).mono (by simp)⟩
    rw [u2.other _ vc, u1.gpr, u2.gpr, u1.other _ xv, u1.other _ yv]; exact hp
  · simp only [mac1, ↓reduceIte]
    refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_add fun s3 u3 => wp_sltu fun s4 u4 => wp_add fun s5 u5 =>
      WP.block_nil ?_
    obtain hp := mul_words (s.gpr x) (s.gpr y)
    obtain a2 : s2.gpr LO = s.gpr x * s.gpr y := by rw [u2.other _ (by decide), u1.gpr]
    obtain h2 : s2.gpr C = BitVec.ofNat 64 ((s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64) := by
      rw [u2.gpr, u1.other _ xl, u1.other _ yl]
    obtain v2 : s2.gpr v = s.gpr v := by rw [u2.other _ vc, u1.other _ vl]
    obtain v3 : s3.gpr v = s2.gpr v + s2.gpr LO := u3.gpr
    obtain l4 : s4.gpr LO = if s2.gpr v + s2.gpr LO < s2.gpr LO then 1 else 0 := by
      rw [u4.gpr, u3.gpr, u3.other _ (Ne.symm vl)]
    obtain e1 := carry (s2.gpr v) (s2.gpr LO)
    rw [← l4, ← v3, a2, v2] at e1
    obtain h4 : s4.gpr C = s2.gpr C := by rw [u4.other _ (by decide), u3.other _ (Ne.symm vc)]
    obtain c5 : (s5.gpr C).toNat = ((s2.gpr C).toNat + (s4.gpr LO).toNat) % 2 ^ 64 := by
      rw [u5.gpr, BitVec.toNat_add, h4]
    rw [← h2] at hp
    rw [Nat.add_comm (s.gpr v).toNat] at e1
    obtain ⟨n1, n2⟩ := mac1_nat (s.gpr x).isLt (s.gpr y).isLt (s.gpr v).isLt (s3.gpr v).isLt hp e1
    refine ⟨?_, ?_⟩
    · rw [c5, Nat.mod_eq_of_lt n2, u5.other _ vc, u4.other _ vl]; exact n1
    · exact ((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans (upd_keeps u5)
        |>.mono (by simp)

/-! ## A row -/

/-- The number in the `n` registers `VR i …`. -/
abbrev rv (s : State) (i n : Nat) : Nat := colsV (fun j => (s.gpr (VR (i + j))).toNat) n

/-- What a row may read of its operand's words `X j` through `f`, from `s0`. -/
structure OpsOk (f : Nat → Op) (X : Nat → Nat) (n : Nat) (s0 : State) : Prop where
  reg : ∀ j < n, (f j).2 ∉ LO :: C :: VL
  ok : ∀ j < n, ∀ s : State, (∀ r, r ∉ LO :: HI :: C :: VL → s.gpr r = s0.gpr r) → s.mem = s0.mem →
    s.rd = s0.rd → s.wr = s0.wr →
    WP isa (.block (f j).1) s fun s' => (s'.gpr (f j).2).toNat = X j ∧ Keeps [HI] s s'

/-- After `n` steps of a row from `VR i` from `s0`, its start value `V0`. -/
structure RowInv (X : Nat → Nat) (y V0 i n : Nat) (s0 s : State) : Prop where
  gpr : ∀ r, r ∉ [LO, HI, C] → (∀ j < n, r ≠ VR (i + j)) → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : rv s i n + (2 ^ 64) ^ n * (s.gpr C).toNat = V0 + colsV X n * y

theorem RowInv.out {X : Nat → Nat} {y V0 i n : Nat} {s0 s : State} (h : RowInv X y V0 i n s0 s) (r : Reg)
    (hr : r ∉ LO :: HI :: C :: VL) : s.gpr r = s0.gpr r := by
  simp only [List.mem_cons, not_or] at hr
  exact h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1]) fun j _ e => hr.2.2.2 (e ▸ VR_mem _)

private theorem row_alg {R E c v c' xy w Cin V0 S : Nat} (hv : R + E * c = V0 + S)
    (e : v + 2 ^ 64 * c' = xy + w + c) (hC : Cin = E * 2 ^ 64 * c') :
    R + E * v + Cin = V0 + E * w + (S + E * xy) := by
  obtain key : E * v + E * 2 ^ 64 * c' = E * xy + E * w + E * c := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e]
  omega_arith

/-- The row, its start value the registers' (`acc`) or zero, and the carry in. -/
theorem row_ok {acc : Bool} {f : Nat → Op} {X : Nat → Nat} {y : Reg} {i n : Nat} {s0 : State}
    (hf : OpsOk f X n s0) (hn : n ≤ 8) (hy : y ∉ [LO, HI, C]) (hyv : ∀ j < n, y ≠ VR (i + j)) :
    ∀ j ≤ n, WP isa (.block (row acc f y i j)) s0
      (RowInv X (s0.gpr y).toNat ((if acc then rv s0 i j else 0) + (s0.gpr C).toNat) i j s0)
  | 0, _ => WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, by simp [colsV]⟩
  | j + 1, hj => by
    unfold row
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (row_ok hf hn hy hyv j (by omega_arith)) fun s h => ?_)
    refine WP.block_append (WP.mono (hf.ok j (by omega_arith) s h.out h.mem h.rd h.wr) fun s1 ⟨x1, k1⟩ => ?_)
    obtain vo : VR (i + j) ∉ [LO, HI, C] := VR_out (by decide) _
    have vo' := vo
    obtain fr := hf.reg j (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at fr vo hy
    obtain vnx : VR (i + j) ≠ (f j).2 := fun e => fr.2.2 (e ▸ VR_mem _)
    refine WP.mono (mac_ok (acc := acc) (x := (f j).2) (y := y) (v := VR (i + j))
      (by simp [fr.1, fr.2.1, Ne.symm vnx]) (by simp [hy.1, hy.2.1, hy.2.2, hyv j (by omega_arith)]) vo')
      fun s2 ⟨e2, k2⟩ => ?_
    obtain dis : ∀ l < j, VR (i + l) ≠ VR (i + j) := fun l hl => VR_ne (by omega_arith)
    obtain y1 : s1.gpr y = s0.gpr y := by
      rw [k1.1 _ (by simp [hy.2.1]), h.gpr y (by simp [hy]) fun l hl => hyv l (by omega_arith)]
    obtain v1 : s1.gpr (VR (i + j)) = s0.gpr (VR (i + j)) := by
      rw [k1.1 _ (by simp [vo.2.1]), h.gpr _ vo' fun l hl => Ne.symm (dis l hl)]
    obtain c1 : s1.gpr C = s.gpr C := k1.1 _ (by decide)
    rw [x1, y1, v1, c1] at e2
    refine ⟨fun r hr hd => ?_, by rw [k2.2.1, k1.2.1, h.mem], by rw [k2.2.2.1, k1.2.2.1, h.rd],
      by rw [k2.2.2.2.1, k1.2.2.2.1, h.wr], by rw [k2.2.2.2.2, k1.2.2.2.2, h.sp], ?_⟩
    · have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k2.1 r (by simp [hr.1, hr.2.1, hr.2.2, hd j (by omega_arith)]), k1.1 r (by simp [hr.2.1]),
        h.gpr r hr' fun l hl => hd l (by omega_arith)]
    · have hv := h.val
      obtain low : rv s2 i j = rv s i j := colsV_congr fun l hl => by
        obtain vl : VR (i + l) ∉ [LO, HI, C] := VR_out (by decide) _
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vl
        rw [k2.1 _ (by simp [vl.1, vl.2.1, vl.2.2, dis l hl]), k1.1 _ (by simp [vl.2.1])]
      rw [show rv s2 i (j + 1) = rv s2 i j + (2 ^ 64) ^ j * (s2.gpr (VR (i + j))).toNat from rfl, low,
        colsV_succ, Nat.add_mul, Nat.mul_assoc]
      obtain alg := row_alg hv e2 (Cin := (2 ^ 64) ^ (j + 1) * (s2.gpr C).toNat) (by rw [Nat.pow_succ])
      rw [alg]
      cases acc
      · simp
      · simp only [↓reduceIte, rv, colsV_succ]; omega_arith

private theorem row1_alg {R W Xn y c' c E x v w B : Nat} (hv : R + E * c' = W + c + Xn * y)
    (e : v + B * c = x * y + w) : v + B * R + E * B * c' = w + B * W + (x + B * Xn) * y := by grind

/-- A row without the carry in. -/
theorem row1_ok {acc : Bool} {f : Nat → Op} {X : Nat → Nat} {y : Reg} {i n : Nat} {s0 : State}
    (hf : OpsOk f X (n + 1) s0) (hn : n < 8) (hy : y ∉ [LO, HI, C]) (hyv : ∀ j < n + 1, y ≠ VR (i + j)) :
    WP isa (.block (row1 acc f y i n)) s0
      (RowInv X (s0.gpr y).toNat (if acc then rv s0 i (n + 1) else 0) i (n + 1) s0) := by
  unfold row1
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (hf.ok 0 (by omega_arith) s0 (fun _ _ => rfl) rfl rfl rfl) fun s1 ⟨x1, k1⟩ => ?_)
  obtain vo : VR i ∉ [LO, HI, C] := VR_out (by decide) _
  have vo' := vo
  obtain fr := hf.reg 0 (by omega_arith)
  have hy' := hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at fr vo hy
  obtain vnx : VR i ≠ (f 0).2 := fun e => fr.2.2 (e ▸ VR_mem _)
  obtain yv0 : y ≠ VR i := hyv 0 (by omega_arith)
  refine WP.block_append (WP.mono (mac1_ok (acc := acc) (x := (f 0).2) (y := y) (v := VR i)
    (by simp [fr.1, Ne.symm vnx]) (by simp [hy.1, yv0]) vo') fun s2 ⟨e2, k2⟩ => ?_)
  obtain y1 : s1.gpr y = s0.gpr y := k1.1 _ (by simp [hy.2.1])
  obtain v1 : s1.gpr (VR i) = s0.gpr (VR i) := k1.1 _ (by simp [vo.2.1])
  rw [x1, y1, v1] at e2
  obtain g2 : ∀ r, r ∉ [LO, HI, C] → r ≠ VR i → s2.gpr r = s0.gpr r := fun r hr hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k2.1 r (by simp [hr.1, hr.2.1, hr.2.2, hi]), k1.1 r (by simp [hr.2.1])]
  obtain y2 : s2.gpr y = s0.gpr y := g2 y hy' yv0
  obtain m2 : s2.mem = s0.mem := by rw [k2.2.1, k1.2.1]
  obtain rd2 : s2.rd = s0.rd := by rw [k2.2.2.1, k1.2.2.1]
  obtain wr2 : s2.wr = s0.wr := by rw [k2.2.2.2.1, k1.2.2.2.1]
  obtain hf2 : OpsOk (fun j => f (j + 1)) (fun j => X (j + 1)) n s2 :=
    ⟨fun j hj => hf.reg (j + 1) (by omega_arith), fun j hj s hs hm hrd hwr =>
      hf.ok (j + 1) (by omega_arith) s (fun r hr => by
        rw [hs r hr]
        simp only [List.mem_cons, not_or] at hr
        exact g2 r (by simp [hr.1, hr.2.1, hr.2.2.1]) fun e => hr.2.2.2 (e ▸ VR_mem _)) (by rw [hm, m2])
        (by rw [hrd, rd2]) (by rw [hwr, wr2])⟩
  refine WP.mono (row_ok (acc := acc) (i := i + 1) hf2 (by omega_arith) hy'
    (fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact hyv _ (by omega_arith)) n (Nat.le_refl _))
    fun s3 h3 => ?_
  obtain nv : ∀ j < n, VR (i + (j + 1)) ≠ VR i := fun j hj => VR_ne (by omega_arith)
  obtain e3 : s3.gpr (VR i) = s2.gpr (VR i) := h3.gpr _ vo' fun j hj => by
    rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact Ne.symm (nv j hj)
  refine ⟨fun r hr hd => ?_, by rw [h3.mem, m2], by rw [h3.rd, rd2], by rw [h3.wr, wr2],
    by rw [h3.sp, k2.2.2.2.2, k1.2.2.2.2], ?_⟩
  · rw [h3.gpr r hr fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact hd _ (by omega_arith),
      g2 r hr (hd 0 (by omega_arith))]
  · have hv := h3.val
    rw [y2] at hv
    obtain idx : ∀ t : State, rv t (i + 1) n = colsV (fun j => (t.gpr (VR (i + (j + 1)))).toNat) n := fun t =>
      colsV_congr fun j _ => by rw [show i + 1 + j = i + (j + 1) by omega_arith]
    obtain r2 : rv s2 (i + 1) n = rv s0 (i + 1) n := colsV_congr fun j hj => by
      rw [g2 _ (VR_out (by decide) _) (by
        rw [show i + 1 + j = i + (j + 1) by omega_arith]; exact nv j hj)]
    rw [r2, idx s3, idx s0] at hv
    rw [rv, colsV_shift, colsV_shift X, rv, colsV_shift, Nat.add_zero, e3, Nat.pow_succ]
    refine (row1_alg hv e2).trans ?_
    cases acc
    · simp
    · simp only [↓reduceIte]

/-! ## The operand `[t4]` -/

/-- The operand's words `X` at `A`, the first `n` in registers too. -/
structure AOk (b A : Addr) (n : Nat) (X : Nat → Nat) (s : State) : Prop where
  ctx : Ctx b s
  a : s.gpr .t4 = A
  al : A.toNat % 8 = 0
  inR : ∀ i < 8, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  regs : ∀ j < n, (s.gpr (AR j)).toNat = X j
  mem : ∀ j < 8, dw s.mem A (8 * j) = X j

theorem AOk.of {b A : Addr} {n : Nat} {X : Nat → Nat} {s s' : State} (h : AOk b A n X s) (hn : n ≤ 7)
    (hg : ∀ r ∈ .a3 :: .t4 :: AL, (∀ j, n ≤ j → j < 7 → r ≠ AR j) → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hm : ∀ j < 8, dw s'.mem A (8 * j) = dw s.mem A (8 * j)) : AOk b A n X s' :=
  ⟨ctx_of h.ctx (hg _ (by decide) fun j _ => (by decide : ∀ j < 7, Reg.a3 ≠ AR j) j) hwr,
    (hg _ (by decide) fun j _ => (by decide : ∀ j < 7, Reg.t4 ≠ AR j) j).trans h.a, h.al,
    by rw [hrd, hwr]; exact h.inR, fun j hj => by
      rw [hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (AR_mem j (by omega_using [hj, hn]))))
        fun l hl hl7 e => absurd (AR_inj j (by omega_using [hj, hn]) l hl7 e) (by omega_using [hj, hl])]
      exact h.regs j hj,
    fun j hj => (hm j hj).trans (h.mem j hj)⟩

/-- The operand's words from word `e`. -/
theorem AOk.ops {b A : Addr} {n : Nat} {X : Nat → Nat} {s : State} (h : AOk b A n X s) (hn : n ≤ 7) {e c : Nat}
    (hc : e + c ≤ 8) : OpsOk (fun j => opA n (e + j)) (fun j => X (e + j)) c s := by
  refine ⟨fun j hj => ?_, fun j hj s' hg hm hrd hwr => ?_⟩
  · unfold opA
    split
    · exact (by decide : ∀ j < 7, AR j ∉ LO :: C :: VL) _ (by omega_arith)
    · show HI ∉ _; decide
  · unfold opA
    split
    · refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
      rw [hg _ ((by decide : ∀ j < 7, AR j ∉ LO :: HI :: C :: VL) _ (by omega_arith))]
      exact h.regs _ (by omega_arith)
    · refine wp_ld (by omega_arith) (by rw [hg _ (by decide), h.a]) (al8 h.al (by omega_arith))
        (by rw [hrd, hwr]; exact h.inR _ (by omega_arith)) fun s1 u1 => WP.block_nil ⟨?_, upd_keeps u1⟩
      rw [u1.gpr, hm]; exact h.mem _ (by omega_arith)

/-- After `n` words loaded. -/
structure LoadInv (A : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, (∀ j < n, r ≠ AR j) → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, (s.gpr (AR j)).toNat = dw s0.mem A (8 * j)

theorem loadA_ok {A : Addr} {s0 : State} (h4 : s0.gpr .t4 = A) (hal : A.toNat % 8 = 0)
    (hin : ∀ i < 8, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * i)) 8) :
    ∀ n ≤ 7, WP isa (.block (loadA n)) s0 (LoadInv A s0 n)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    unfold loadA
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (loadA_ok h4 hal hin n (by omega_arith)) fun s h => ?_)
    refine wp_ld (by omega_arith) (by
        rw [h.gpr _ fun j hj => (by decide : ∀ j < 7, Reg.t4 ≠ AR j) j (by omega_arith), h4])
      (al8 hal (by omega_arith)) (by rw [h.rd, h.wr]; exact hin n (by omega_arith)) fun s1 u1 => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u1.other r (hr n (by omega_arith)), h.gpr r fun j hj => hr j (by omega_arith)],
      by rw [u1.mem, h.mem], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], fun j hj => ?_⟩
    by_cases e : j = n
    · subst e; rw [u1.gpr, h.mem]; rfl
    · rw [u1.other _ fun e' => e (AR_inj j (by omega_arith) n (by omega_arith) e')]; exact h.val j (by omega_arith)

theorem P_facts {j : Nat} (hj : j < 16) : P j + 8 ≤ 2048 ∧ P j % 8 = 0 ∧ T 8 + 64 ≤ P j := by
  unfold P; unfold SQ Impl.Weierstrass.RISCV64.GenWide.SO Impl.Weierstrass.RISCV64.GenWide.SB
    Impl.Weierstrass.RISCV64.GenWide.SA N T; omega_arith

/-- A word of the product stored. -/
theorem PR_store {b : Addr} {m m' : Mem} {j : Nat} (hj : j < 16) (h : Frame [PR 8 b] m m') (v : BitVec 64) :
    Frame [PR 8 b] m (m'.writeW (b + BitVec.ofNat 64 (P j)) v) := by
  obtain ⟨h1, -, -⟩ := P_facts hj
  simp only [P] at h1 ⊢
  exact h.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))

theorem P_write {m : Mem} {b : Addr} {i j : Nat} (hi : i < 16) (hj : j < 16) (v : BitVec 64) :
    dw (m.writeW (b + BitVec.ofNat 64 (P j)) v) b (P i) = if i = j then v.toNat else dw m b (P i) := by
  obtain ⟨h1, -, -⟩ := P_facts hi
  obtain ⟨h2, -, -⟩ := P_facts hj
  simp only [P] at h1 h2 ⊢
  split
  · rename_i e; subst e; exact dw_write_self ..
  · exact dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)

/-! ## The product -/

abbrev clobM : List Reg := Y :: LO :: HI :: C :: VL

/-- The start value of row `i`. -/
abbrev W (i : Nat) (s : State) (j n : Nat) : Nat := if decide (0 < i) then rv s j n else 0

/-- What the product needs. -/
structure MulOk8 (b A B : Addr) (s : State) : Prop where
  ao : AOk b A 5 (fun j => dw s.mem A (8 * j)) s
  adis : ∀ i < 8, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b)
  b' : s.gpr .t5 = B
  bal : B.toNat % 8 = 0
  bin : ∀ i < 8, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  bdis : ∀ i < 8, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b)

/-- After `i` rows of the product. -/
structure MulInv (b A B : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobM → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR 8 b] s0.mem s.mem
  val : colsV (fun j => dw s.mem b (P j)) i + (2 ^ 64) ^ i * W i s i 8 = xv s0.mem A 8 * bv s0.mem B i

private theorem mulRow_alg {L E w v R y bv X S B : Nat} (hv : L + E * w = X * bv)
    (e : v + B * R = w + S) (hS : S = X * y) : L + E * v + E * B * R = X * (bv + E * y) := by
  subst hS
  calc L + E * v + E * B * R = L + E * (v + B * R) := by grind
    _ = (L + E * w) + E * (X * y) := by rw [e]; grind
    _ = _ := by rw [hv]; grind

theorem mulRow_ok {b A B : Addr} {s0 : State} (h0 : MulOk8 b A B s0) {i : Nat} (hi : i < 8) {s : State}
    (h : MulInv b A B s0 i s) : WP isa (.block (mulRow i)) s (MulInv b A B s0 (i + 1)) := by
  obtain ⟨p1, p2, -⟩ := P_facts (j := i) (by omega_arith)
  unfold mulRow
  refine wp_ld (by omega_arith) (by rw [h.gpr _ (by decide), h0.b']) (al8 h0.bal (by omega_arith))
    (by rw [h.rd, h.wr]; exact h0.bin i hi) fun s1 u1 => ?_
  obtain hA : ∀ j < 8, dw s.mem A (8 * j) = dw s0.mem A (8 * j) := fun j hj =>
    dwA_frame h.frame (by decide) (by decide) h0.adis hj
  obtain hB : dw s.mem B (8 * i) = dw s0.mem B (8 * i) :=
    dwA_frame h.frame (by decide) (by decide) h0.bdis hi
  obtain ao1 : AOk b A 5 (fun j => dw s0.mem A (8 * j)) s1 :=
    h0.ao.of (by decide) (fun r hr hn => by
      have h5 := hn 5 (by decide) (by decide)
      have h6 := hn 6 (by decide) (by decide)
      rw [u1.other r h5, h.gpr r (by
        clear hn; revert hr h5 h6; cases r <;> decide)])
      (by rw [u1.rd, h.rd]) (by rw [u1.wr, h.wr]) (fun j hj => by rw [u1.mem]; exact hA j hj)
  obtain ops := ao1.ops (by decide) (e := 0) (c := 8) (by decide)
  simp only [Nat.zero_add] at ops
  refine WP.block_append (WP.mono (row1_ok (acc := decide (0 < i)) (i := i) (n := 7) ops (by decide) (by decide)
    fun j _ e => absurd e (Ne.symm fun e' => (VR_out (by decide) _ : VR (i + j) ∉ [Y]) (by rw [e']; simp)))
    fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of ao1.ctx (h2.out _ (by decide)) h2.wr
  refine sd_ok hc2 p1 p2 fun s3 u3 => wp_mv fun s4 u4 => WP.block_nil ?_
  obtain hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (P i)) (s2.gpr (VR i)) := by
    rw [u4.mem, u3.mem, h2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, h2.rd, u1.rd, h.rd], by rw [u4.wr, u3.wr, h2.wr, u1.wr, h.wr],
    by rw [u4.sp, u3.sp, h2.sp, u1.sp, h.sp], by rw [hm4]; exact PR_store (by omega_arith) h.frame _, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, not_or] at hr
    rw [u4.other r (fun e => hr.2.2.2.2 (e ▸ VR_mem _)), u3.gpr, h2.out r (by simp only [List.mem_cons, not_or]; exact hr.2),
      u1.other r hr.1, h.gpr r hr']
  · have hv := h.val
    have e := h2.val
    obtain y1 : (s1.gpr Y).toNat = dw s0.mem B (8 * i) := by rw [u1.gpr, ← hB]; rfl
    obtain rv1 : rv s1 i 8 = rv s i 8 := colsV_congr fun j _ => by
      rw [u1.other _ (fun e' => (VR_out (by decide) _ : VR (i + j) ∉ [Y]) (by rw [e']; simp))]
    rw [rv1, y1] at e
    obtain hw : W (i + 1) s4 (i + 1) 8 = colsV (fun j => (s2.gpr (VR (i + (j + 1)))).toNat) 7 +
        (2 ^ 64) ^ 7 * (s2.gpr C).toNat := by
      simp only [W, Nat.succ_pos, decide_true, ↓reduceIte]
      show colsV _ 7 + (2 ^ 64) ^ 7 * (s4.gpr (VR (i + 1 + 7))).toNat = _
      rw [show i + 1 + 7 = i + 8 by omega_arith, VR_add8, u4.gpr, u3.gpr]
      congr 1
      refine colsV_congr fun j hj => ?_
      rw [show i + 1 + j = i + (j + 1) by omega_arith, u4.other _ (VR_ne (by omega_arith)), u3.gpr]
    obtain low : colsV (fun j => dw s4.mem b (P j)) i = colsV (fun j => dw s.mem b (P j)) i :=
      colsV_congr fun j hj => by rw [hm4, P_write (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    obtain nw : dw s4.mem b (P i) = (s2.gpr (VR i)).toNat := by rw [hm4]; exact dw_write_self ..
    rw [rv, colsV_shift, Nat.add_zero] at e
    rw [colsV_succ, low, nw, hw, Nat.pow_succ, show bv s0.mem B (i + 1) = bv s0.mem B i + (2 ^ 64) ^ i * dw s0.mem B (8 * i)
      from rfl]
    refine mulRow_alg hv (S := xv s0.mem A 8 * dw s0.mem B (8 * i)) ?_ rfl
    rw [← e, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ', Nat.add_assoc]

/-- After `j` words of the window stored. -/
structure HiInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR 8 b] s0.mem s.mem
  low : ∀ i < 8, dw s.mem b (P i) = dw s0.mem b (P i)
  val : ∀ i < j, dw s.mem b (P (8 + i)) = (s0.gpr (VR (8 + i))).toNat

theorem hi_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ j ≤ 8, WP isa (.block ((List.range j).flatMap fun j => [.store .d (VR (8 + j)) .a3 (P (8 + j))])) s0
      (HiInv b s0 j)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨p1, p2, -⟩ := P_facts (j := 8 + j) (by omega_arith)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (hi_ok hc j (by omega_arith)) fun s h => ?_)
    refine sd_ok (ctx_of hc (by rw [h.gpr]) h.wr) p1 p2 fun s1 u1 => WP.block_nil ?_
    refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp],
      by rw [u1.mem]; exact PR_store (by omega_arith) h.frame _, fun i hi => ?_, fun i hi => ?_⟩
    · rw [u1.mem, P_write (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), h.low i hi]
    · rw [u1.mem, P_write (by omega_arith) (by omega_arith)]
      by_cases e : i = j
      · subst e; rw [ite_eq_left rfl, h.gpr]
      · rw [ite_eq_right (by omega_arith), h.val i (by omega_arith)]

/-- The sixteen words of the product. -/
abbrev pw (m : Mem) (b : Addr) : Nat := colsV (fun j => dw m b (P j)) 16

/-- The registers the products write. -/
abbrev clobP : List Reg := AL ++ LO :: HI :: C :: VL

theorem mulProd_ok {b A B : Addr} {s : State} (hc : Ctx b s) (h4 : s.gpr .t4 = A) (h5 : s.gpr .t5 = B)
    (hal : A.toNat % 8 = 0) (hbl : B.toNat % 8 = 0)
    (ain : ∀ i < 8, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (bin : ∀ i < 8, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8)
    (adis : ∀ i < 8, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b))
    (bdis : ∀ i < 8, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b)) :
    WP isa (.block mulProd) s fun s' =>
      (∀ r, r ∉ clobP → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [PR 8 b] s.mem s'.mem ∧ pw s'.mem b = xv s.mem A 8 * xv s.mem B 8 := by
  unfold mulProd
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadA_ok h4 hal ain 5 (by decide)) fun s1 h1 => ?_)
  obtain g1 : ∀ r, r ∉ AL → s1.gpr r = s.gpr r := fun r hr =>
    h1.gpr r fun j hj e => hr (e ▸ AR_mem j (by omega_arith))
  obtain hc1 : Ctx b s1 := ctx_of hc (g1 _ (by decide)) h1.wr
  obtain hM : MulOk8 b A B s1 :=
    { ao := ⟨hc1, by rw [g1 _ (by decide), h4], hal, by rw [h1.rd, h1.wr]; exact ain,
        fun j hj => by rw [h1.val j hj, h1.mem], fun _ _ => rfl⟩
      adis := adis
      b' := by rw [h1.gpr _ (fun j hj => (by decide : ∀ j < 5, Reg.t5 ≠ AR j) j hj), h5]
      bal := hbl
      bin := by rw [h1.rd, h1.wr]; exact bin
      bdis := bdis }
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (MulInv b A B s1) (fun i s' hi h => mulRow_ok hM hi h) 8
    (Nat.le_refl _) s1 ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, by simp [colsV]⟩) fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by decide)) h2.wr
  refine WP.mono (hi_ok hc2 8 (Nat.le_refl _)) fun s3 h3 => ?_
  refine ⟨fun r hr => ?_, by rw [h3.rd, h2.rd, h1.rd], by rw [h3.wr, h2.wr, h1.wr], by rw [h3.sp, h2.sp, h1.sp],
    by rw [← h1.mem]; exact h2.frame.trans h3.frame, ?_⟩
  · obtain ⟨ha, hb⟩ : r ∉ AL ∧ r ∉ clobM := by revert hr; cases r <;> decide
    rw [h3.gpr, h2.gpr r hb, g1 r ha]
  · have hv := h2.val
    simp only [W, Nat.reduceLT, decide_true, ↓reduceIte] at hv
    show colsV (fun j => dw s3.mem b (P j)) (8 + 8) = _
    rw [colsV_split, colsV_congr (g := fun j => dw s2.mem b (P j)) fun j hj => h3.low j hj,
      colsV_congr (f := fun j => dw s3.mem b (P (8 + j))) (g := fun j => (s2.gpr (VR (8 + j))).toNat) fun j hj => h3.val j hj]
    refine hv.trans ?_
    rw [h1.mem]

/-! ## The square -/

/-- The registers the square's rows write. -/
abbrev clobR : List Reg := LO :: HI :: C :: VL

/-- What the square's rows need. -/
structure SqOk8 (b A : Addr) (s : State) : Prop where
  ao : AOk b A 7 (fun j => dw s.mem A (8 * j)) s
  adis : ∀ i < 8, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b)

/-- After `i` rows of the square's products. -/
structure SqInv (b A : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobR → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR 8 b] s0.mem s.mem
  val : 2 ^ 64 * (colsV (fun j => dw s.mem b (P (1 + j))) (2 * i) +
    (2 ^ 64) ^ (2 * i) * W i s (2 * i + 1) (7 - i)) = sumN (rowTerm (fun j => dw s0.mem A (8 * j)) 8) i

private theorem sqrRow_alg {L E w v0 v1 R S a X B t : Nat} (hv : B * (L + E * w) = S)
    (e : v0 + B * (v1 + B * R) = w + X * a) (ht : t = a * (E * B) * X) :
    B * (L + E * v0 + E * B * v1 + E * B * B * R) = S + t := by
  subst ht
  calc B * (L + E * v0 + E * B * v1 + E * B * B * R) = B * (L + E * (v0 + B * (v1 + B * R))) := by grind
    _ = B * (L + E * w) + B * (E * (X * a)) := by rw [e]; grind
    _ = _ := by rw [hv]; grind

theorem sqrRow_ok {b A : Addr} {s0 : State} (h0 : SqOk8 b A s0) {i : Nat} (hi : i < 7) {s : State}
    (h : SqInv b A s0 i s) : WP isa (.block (sqrRow i)) s (SqInv b A s0 (i + 1)) := by
  obtain ⟨p1, p2, -⟩ := P_facts (j := 2 * i + 1) (by omega_arith)
  obtain ⟨q1, q2, -⟩ := P_facts (j := 2 * i + 2) (by omega_arith)
  unfold sqrRow
  obtain hA : ∀ j < 8, dw s.mem A (8 * j) = dw s0.mem A (8 * j) := fun j hj =>
    dwA_frame h.frame (by decide) (by decide) h0.adis hj
  obtain gA : ∀ r ∈ .a3 :: .t4 :: AL, s.gpr r = s0.gpr r := fun r hr => h.gpr r (by revert hr; cases r <;> decide)
  obtain ao : AOk b A 7 (fun j => dw s0.mem A (8 * j)) s :=
    h0.ao.of (by decide) (fun r hr _ => gA r hr) h.rd h.wr hA
  obtain ops := ao.ops (by decide) (e := i + 1) (c := 6 - i + 1) (by omega_arith)
  obtain ay : AR i ∉ clobR := (by decide : ∀ j < 7, AR j ∉ clobR) i hi
  refine WP.block_append (WP.mono (row1_ok (acc := decide (0 < i)) (y := AR i) (i := 2 * i + 1) (n := 6 - i) ops
    (by omega_arith) ((by decide : ∀ j < 7, AR j ∉ [LO, HI, C]) i hi)
    fun j _ e => ay (by rw [e]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (VR_mem _)))))
    fun s2 h2 => ?_)
  refine wp_mv fun s3 u3 => ?_
  obtain hc2 : Ctx b s2 := ctx_of ao.ctx (h2.out _ (by decide)) h2.wr
  obtain hc3 : Ctx b s3 := ctx_of hc2 (u3.other _ fun e => (VR_out (by decide) _ : VR (i + 8) ∉ [Reg.a3]) (by rw [e]; simp)) u3.wr
  refine sd_ok hc3 p1 p2 fun s4 u4 => ?_
  refine sd_ok (ctx_of hc3 (by rw [u4.gpr]) u4.wr) q1 q2 fun s5 u5 => WP.block_nil ?_
  obtain hm5 : s5.mem = (s.mem.writeW (b + BitVec.ofNat 64 (P (2 * i + 1))) (s3.gpr (VR (2 * i + 1)))).writeW
      (b + BitVec.ofNat 64 (P (2 * i + 2))) (s3.gpr (VR (2 * i + 2))) := by
    rw [u5.mem, u4.mem, u4.gpr, u3.mem, h2.mem]
  refine ⟨fun r hr => ?_, by rw [u5.rd, u4.rd, u3.rd, h2.rd, h.rd], by rw [u5.wr, u4.wr, u3.wr, h2.wr, h.wr],
    by rw [u5.sp, u4.sp, u3.sp, h2.sp, h.sp],
    by rw [hm5]; exact PR_store (by omega_arith) (PR_store (by omega_arith) h.frame _) _, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, not_or] at hr
    rw [u5.gpr, u4.gpr, u3.other r (fun e => hr.2.2.2 (e ▸ VR_mem _)), h2.out r hr', h.gpr r hr']
  · have hv := h.val
    have e := h2.val
    obtain a1 : (s.gpr (AR i)).toNat = dw s0.mem A (8 * i) := ao.regs i hi
    rw [a1, show 6 - i + 1 = 7 - i by omega_arith] at e
    -- The row and its carry, as `8 - i` registers.
    obtain hR : rv s3 (2 * i + 1) (7 - i + 1) = rv s2 (2 * i + 1) (7 - i) + (2 ^ 64) ^ (7 - i) * (s2.gpr C).toNat := by
      rw [rv, colsV_succ, show 2 * i + 1 + (7 - i) = i + 8 by omega_arith, u3.gpr]
      congr 1
      exact colsV_congr fun j hj => by rw [u3.other _ (VR_ne (by omega_arith))]
    rw [← hR, rv, colsV_shift, show 7 - i = 6 - i + 1 by omega_arith, colsV_shift] at e
    obtain hg : s5.gpr = s3.gpr := by rw [u5.gpr, u4.gpr]
    obtain hw : W (i + 1) s5 (2 * (i + 1) + 1) (7 - (i + 1)) =
        colsV (fun j => (s3.gpr (VR (2 * i + 1 + (j + 1 + 1)))).toNat) (6 - i) := by
      simp only [W, Nat.succ_pos, decide_true, ↓reduceIte]
      rw [show 7 - (i + 1) = 6 - i by omega_arith]
      exact colsV_congr fun j _ => by rw [hg, show 2 * (i + 1) + 1 + j = 2 * i + 1 + (j + 1 + 1) by omega_arith]
    obtain low : colsV (fun j => dw s5.mem b (P (1 + j))) (2 * i) = colsV (fun j => dw s.mem b (P (1 + j))) (2 * i) :=
      colsV_congr fun j hj => by
        rw [hm5, P_write (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
          P_write (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    obtain n0 : dw s5.mem b (P (1 + 2 * i)) = (s3.gpr (VR (2 * i + 1))).toNat := by
      rw [hm5, P_write (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith),
        P_write (by omega_arith) (by omega_arith), ite_eq_left (by omega_arith)]
    obtain n1 : dw s5.mem b (P (1 + (2 * i + 1))) = (s3.gpr (VR (2 * i + 2))).toNat := by
      rw [hm5, P_write (by omega_arith) (by omega_arith), ite_eq_left (by omega_arith)]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith] at hw ⊢
    rw [colsV_succ, colsV_succ, low, n0, n1, hw, Nat.pow_succ, Nat.pow_succ]
    show _ = sumN _ i + rowTerm _ 8 i
    refine sqrRow_alg hv (w := W i s (2 * i + 1) (7 - i))
      (X := colsV (fun j => dw s0.mem A (8 * (i + 1 + j))) (7 - i)) (a := dw s0.mem A (8 * i)) ?_ ?_
    · rw [show 7 - i = 6 - i + 1 by omega_arith]
      simp only [Nat.add_zero, Nat.zero_add] at e
      exact e
    · rw [rowTerm, Nat.pow_succ, show 8 - 1 - i = 7 - i by omega_arith]

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

/-- Sixteen words of which the first and the last are zero. -/
private theorem cols_ends {f : Nat → Nat} {n l k : Nat} (hl : l = n + 1) (hk : k = l + 1) (h0 : f 0 = 0) (hn : f l = 0) :
    colsV f k = 2 ^ 64 * colsV (fun j => f (1 + j)) n := by
  subst hk hl
  rw [colsV_succ, hn, Nat.mul_zero, Nat.add_zero, colsV_shift, h0, Nat.zero_add,
    colsV_congr (g := fun j => f (1 + j)) fun j _ => by rw [Nat.add_comm]]

/-- The last row's window is empty. -/
private theorem W_last (s : State) : W 7 s 15 0 = 0 := by simp only [W, rv, colsV, ite_self]

theorem sqrProd_ok {b A : Addr} {s : State} (hc : Ctx b s) (hnw : b.toNat + 2048 ≤ 2 ^ 64) (h4 : s.gpr .t4 = A)
    (hal : A.toNat % 8 = 0)
    (ain : ∀ i < 8, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (adis : ∀ i < 8, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA 8 b)) :
    WP isa (.block sqrProd) s fun s' =>
      (∀ r, r ∉ clobP → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [PR 8 b] s.mem s'.mem ∧ pw s'.mem b = xv s.mem A 8 * xv s.mem A 8 := by
  obtain ⟨p1, p2, -⟩ := P_facts (j := 0) (by decide)
  obtain ⟨q1, q2, -⟩ := P_facts (j := 15) (by decide)
  unfold sqrProd
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (loadA_ok h4 hal ain 7 (by decide)) fun s1 h1 => ?_)
  obtain g1 : ∀ r, r ∉ AL → s1.gpr r = s.gpr r := fun r hr => h1.gpr r fun j hj e => hr (e ▸ AR_mem j hj)
  obtain hc1 : Ctx b s1 := ctx_of hc (g1 _ (by decide)) h1.wr
  obtain hM : SqOk8 b A s1 :=
    { ao := ⟨hc1, by rw [g1 _ (by decide), h4], hal, by rw [h1.rd, h1.wr]; exact ain,
        fun j hj => by rw [h1.val j hj, h1.mem], fun _ _ => rfl⟩
      adis := adis }
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SqInv b A s1) (fun i s' hi h => sqrRow_ok hM hi h) 7
    (Nat.le_refl _) s1 ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, by simp [colsV, sumN, W]⟩) fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by decide)) h2.wr
  refine wp_li (by decide) fun s3 u3 => ?_
  obtain hc3 : Ctx b s3 := ctx_of hc2 (u3.other _ (by decide)) u3.wr
  refine sd_ok hc3 p1 p2 fun s4 u4 => ?_
  obtain hc4 : Ctx b s4 := ctx_of hc3 (by rw [u4.gpr]) u4.wr
  refine sd_ok hc4 q1 q2 fun s5 u5 => wp_li (by decide) fun s6 u6 => ?_
  obtain g6 : ∀ r, r ≠ .a2 → r ≠ .a5 → s6.gpr r = s2.gpr r := fun r h2 h5 => by
    rw [u6.other r h5, u5.gpr, u4.gpr, u3.other r h2]
  obtain rd6 : s6.rd = s.rd := by rw [u6.rd, u5.rd, u4.rd, u3.rd, h2.rd, h1.rd]
  obtain wr6 : s6.wr = s.wr := by rw [u6.wr, u5.wr, u4.wr, u3.wr, h2.wr, h1.wr]
  obtain a2 : s6.gpr .a2 = 0 := by rw [u6.other _ (by decide), u5.gpr, u4.gpr, u3.gpr]; rfl
  obtain hm6 : s6.mem = (s2.mem.writeW (b + BitVec.ofNat 64 (P 0)) (0 : BitVec 64)).writeW
      (b + BitVec.ofNat 64 (P 15)) (0 : BitVec 64) := by
    rw [u6.mem, u5.mem, u4.mem, u4.gpr, u3.mem, u3.gpr]; rfl
  obtain hS : SqOk 8 b A s6 :=
    ⟨ctx_of hc (by rw [g6 _ (by decide) (by decide), h2.gpr _ (by decide), g1 _ (by decide)]) wr6, hnw,
      by rw [g6 _ (by decide) (by decide), h2.gpr _ (by decide), g1 _ (by decide), h4], hal,
      by rw [rd6, wr6]; exact ain, adis, by decide, by decide⟩
  refine WP.mono (diags_ok hS a2 (by rw [u6.gpr]; rfl) 8 (Nat.le_refl _)) fun s7 h7 => ?_
  obtain f6 : Frame [PR 8 b] s.mem s6.mem := by
    rw [hm6, ← h1.mem]; exact PR_store (by decide) (PR_store (by decide) h2.frame _) _
  refine ⟨fun r hr => ?_, by rw [h7.rd, rd6], by rw [h7.wr, wr6],
    by rw [h7.sp, u6.sp, u5.sp, u4.sp, u3.sp, h2.sp, h1.sp], f6.trans h7.frame, ?_⟩
  · obtain ⟨ha, hb, hd, h2', h5'⟩ : r ∉ AL ∧ r ∉ clobR ∧ r ∉ [Reg.t0, .a1, .a2, .a4, .a5, .a6, .a7] ∧ r ≠ .a2 ∧ r ≠ .a5 := by
      revert hr; cases r <;> decide
    rw [h7.gpr r hd, g6 r h2' h5', h2.gpr r hb, g1 r ha]
  · have hv := h7.val
    have hr := h2.val
    -- The rows' words, with zeros below and above.
    obtain e15 : dw s6.mem b (P 15) = 0 := by
      rw [hm6, P_write (by decide) (by decide), ite_eq_left rfl]; decide
    obtain e0 : dw s6.mem b (P 0) = 0 := by
      rw [hm6, P_write (by decide) (by decide), ite_eq_right (by decide), P_write (by decide) (by decide),
        ite_eq_left rfl]; decide
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hr hv
    rw [W_last, Nat.mul_zero, Nat.add_zero] at hr
    obtain hp : pw s6.mem b = sumN (rowTerm (fun j => dw s1.mem A (8 * j)) 8) 7 := by
      refine (cols_ends (f := fun j => dw s6.mem b (P j)) (n := 14) (l := 15) (k := 16) rfl rfl e0 e15).trans ?_
      rw [← hr]
      refine congrArg (2 ^ 64 * ·) (colsV_congr fun j hj => ?_)
      rw [hm6, P_write (by omega_arith) (by decide), ite_eq_right (by omega_arith),
        P_write (by omega_arith) (by decide), ite_eq_right (by omega_arith)]
    obtain hA6 : ∀ j < 8, dw s6.mem A (8 * j) = dw s.mem A (8 * j) := fun j hj =>
      dwA_frame f6 (by decide) (by decide) adis hj
    simp only [pv, Nat.zero_add] at hv
    have hv' : pw s7.mem b + (2 ^ 64) ^ 16 * ((s7.gpr .a2).toNat + (s7.gpr .a5).toNat) = 2 * pw s6.mem b +
        sumN (fun j => dw s6.mem A (8 * j) * dw s6.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) 8 := hv
    obtain hd : sumN (fun j => dw s6.mem A (8 * j) * dw s6.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) 8 =
        sumN (fun j => dw s.mem A (8 * j) * dw s.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) 8 :=
      sumN_congr fun j hj => by rw [hA6 j hj]
    rw [h1.mem] at hp
    exact sq_final (a := fun j => dw s.mem A (8 * j)) (k := 8) (l := 7) (n := 16) (fun _ => dw_lt _ _ _) rfl rfl hp hd hv'

/-! ## The constants -/

open VG.Impl.Words.RISCV64 (li64)

theorem lay : T 8 = 1536 ∧ N 8 = 1616 := by unfold N T; decide

/-- The modulus's words and `m'` where the reduction reads them. -/
structure MOk (b : Addr) (m : Nat) (s : State) : Prop where
  ctx : Ctx b s
  regs : ∀ j < 7, s.gpr (AR j) = wordOf m j
  m7 : dw s.mem b M7 = (wordOf m 7).toNat
  ni : s.mem.readW (b + BitVec.ofNat 64 NI) 64 = BitVec.ofNat 64 (negInv m)

/-- After `n` words of the modulus. -/
structure ConstInv (m : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ LO → r ∉ AL → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, s.gpr (AR j) = wordOf m j

theorem const_ok {m : Nat} {s0 : State} :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap fun j => li64 (AR j) LO (wordOf m j))) s0 (ConstInv m s0 n)
  | 0, _ => WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (const_ok n (by omega_arith)) fun s h => ?_)
    obtain ne : AR n ≠ LO := (by decide : ∀ j < 7, AR j ≠ LO) n (by omega_arith)
    rw [← List.append_nil (li64 _ _ _)]
    refine wp_li64 ne _ fun s1 e1 k1 => WP.block_nil ?_
    refine ⟨fun r hl hr => ?_, by rw [k1.2.1, h.mem], by rw [k1.2.2.1, h.rd], by rw [k1.2.2.2.1, h.wr],
      by rw [k1.2.2.2.2, h.sp], fun j hj => ?_⟩
    · obtain nr : r ≠ AR n := fun e => hr (e ▸ AR_mem n (by omega_arith))
      rw [k1.1 r (by simp [hl, nr]), h.gpr r hl hr]
    · by_cases e : j = n
      · subst e; exact e1
      · obtain nl : AR j ≠ LO := (by decide : ∀ j < 7, AR j ≠ LO) j (by omega_arith)
        obtain nj : AR j ≠ AR n := fun e' => e (AR_inj j (by omega_arith) n (by omega_arith) e')
        rw [k1.1 _ (by simp [nl, nj])]
        exact h.val j (by omega_arith)

/-- The words kept, the last word of the modulus and `m'`. -/
abbrev CR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 M7, 16⟩

theorem consts_ok {b : Addr} {m : Nat} {s : State} (hc : Ctx b s) {is : List Instr} {Q : State → Prop}
    (h : ∀ s', (∀ r, r ∉ LO :: HI :: AL → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [CR b] s.mem s'.mem → MOk b m s' → WP isa (.block is) s' Q) :
    WP isa (.block (consts m ++ is)) s Q := by
  obtain ⟨e1, e2⟩ := lay
  unfold consts
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (const_ok 7 (Nat.le_refl _)) fun s1 h1 => ?_)
  obtain hc1 : Ctx b s1 := ctx_of hc (h1.gpr _ (by decide) (by decide)) h1.wr
  refine wp_li64 (by decide) _ fun s2 v2 k2 => ?_
  obtain hc2 : Ctx b s2 := ctx_of hc1 (k2.1 _ (by decide)) k2.2.2.2.1
  refine sd_ok hc2 (by simp only [M7]; omega_arith) (by simp only [M7]; omega_arith) fun s3 u3 => ?_
  refine wp_li64 (by decide) _ fun s4 v4 k4 => ?_
  obtain hc4 : Ctx b s4 := ctx_of hc2 (by rw [k4.1 _ (by decide), u3.gpr]) (by rw [k4.2.2.2.1, u3.wr])
  refine sd_ok hc4 (by simp only [NI]; omega_arith) (by simp only [NI]; omega_arith) fun s5 u5 => ?_
  obtain g5 : ∀ r, r ∉ [HI, LO] → s5.gpr r = s1.gpr r := fun r hr => by
    rw [u5.gpr, k4.1 r hr, u3.gpr, k2.1 r hr]
  obtain hm : s5.mem = (s.mem.writeW (b + BitVec.ofNat 64 M7) (wordOf m 7)).writeW (b + BitVec.ofNat 64 NI)
      (BitVec.ofNat 64 (negInv m)) := by
    rw [u5.mem, k4.2.1, u3.mem, k2.2.1, h1.mem, v4, v2]
  refine h s5 (fun r hr => ?_) (by rw [u5.rd, k4.2.2.1, u3.rd, k2.2.2.1, h1.rd])
    (by rw [u5.wr, k4.2.2.2.1, u3.wr, k2.2.2.2.1, h1.wr]) (by rw [u5.sp, k4.2.2.2.2, u3.sp, k2.2.2.2.2, h1.sp]) ?_
    ⟨ctx_of hc1 (g5 _ (by decide)) (by rw [u5.wr, k4.2.2.2.1, u3.wr, k2.2.2.2.1]), fun j hj => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [g5 r (by simp [hr.1, hr.2.1]), h1.gpr r hr.1 hr.2.2]
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by simp only [M7]; omega_arith)
      (by simp only [M7]; omega_arith) (by simp only [M7]; omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains b (by simp only [M7, NI]; omega_arith) (by simp only [M7, NI]; omega_arith)
        (by simp only [M7]; omega_arith))
  · rw [g5 _ ((by decide : ∀ j < 7, AR j ∉ [HI, LO]) j hj)]; exact h1.val j hj
  · rw [hm, dw_write_other _ _ _ (by simp only [M7, NI]; omega_arith) (by simp only [M7]; omega_arith)
      (by simp only [NI]; omega_arith), dw_write_self]
  · rw [hm, Mem.readW_writeW_self64]

theorem MOk.of {b : Addr} {m : Nat} {s s' : State} (h : MOk b m s) (hg : ∀ r ∈ .a3 :: AL, s'.gpr r = s.gpr r)
    (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) : MOk b m s' :=
  ⟨ctx_of h.ctx (hg _ (by decide)) hwr, fun j hj => by
    rw [hg _ (List.mem_cons_of_mem _ (AR_mem j hj))]; exact h.regs j hj, by rw [hm]; exact h.m7, by rw [hm]; exact h.ni⟩

/-- The modulus's words from the second. -/
theorem MOk.ops {b : Addr} {m : Nat} {s : State} (h : MOk b m s) :
    OpsOk (fun j => opM (j + 1)) (fun j => (wordOf m (j + 1)).toNat) 7 s := by
  obtain ⟨e1, e2⟩ := lay
  refine ⟨fun j hj => ?_, fun j hj s' hg hm hrd hwr => ?_⟩
  · unfold opM
    split
    · exact (by decide : ∀ j < 7, AR j ∉ LO :: C :: VL) _ (by omega_arith)
    · show HI ∉ _; decide
  · unfold opM
    split
    · refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
      rw [hg _ ((by decide : ∀ j < 7, AR j ∉ LO :: HI :: C :: VL) _ (by omega_arith)), h.regs _ (by omega_arith)]
    · obtain rfl : j = 6 := by omega_arith
      refine ld_ok (ctx_of h.ctx (hg _ (by decide)) hwr) (by simp only [M7]; omega_arith) (by simp only [M7]; omega_arith)
        fun s1 u1 => WP.block_nil ⟨?_, upd_keeps u1⟩
      rw [u1.gpr, hm]; exact h.m7

/-! ## A round of the reduction -/

theorem quot_ok {b : Addr} {m i : Nat} {s : State} (h : MOk b m s)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0) :
    WP isa (.block (quot i)) s fun s' =>
      (s.gpr (VR i)).toNat + (s'.gpr (VR i)).toNat * (wordOf m 0).toNat = 2 ^ 64 * (s'.gpr C).toNat ∧
      Keeps [VR i, LO, C] s s' := by
  obtain ⟨e1, e2⟩ := lay
  obtain vo : VR i ∉ [LO, HI, C] := VR_out (by decide) _
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  obtain va : AR 0 ≠ VR i := fun e => (by decide : AR 0 ∉ VL) (e ▸ VR_mem i)
  unfold quot
  refine ld_ok h.ctx (by simp only [NI]; omega_arith) (by simp only [NI]; omega_arith) fun s1 u1 =>
    wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => wp_li (imm := 0) (by decide) fun s4 u4 => wp_sltu fun s5 u5 =>
    wp_add fun s6 u6 => WP.block_nil ?_
  obtain ni1 : s1.gpr LO = BitVec.ofNat 64 (negInv m) := by rw [u1.gpr, h.ni]
  obtain v1 : s1.gpr (VR i) = s.gpr (VR i) := u1.other _ vo.1
  obtain q2 : (s2.gpr (VR i)).toNat = (s.gpr (VR i)).toNat * (negInv m % 2 ^ 64) % 2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, v1, ni1, BitVec.toNat_ofNat]
  obtain m2 : s2.gpr (AR 0) = wordOf m 0 := by
    rw [u2.other _ va, u1.other _ (by decide), h.regs 0 (by decide)]
  obtain q5 : s5.gpr (VR i) = s2.gpr (VR i) := by
    rw [u5.other _ vo.1, u4.other _ vo.1, u3.other _ vo.2.2]
  obtain q6 : s6.gpr (VR i) = s2.gpr (VR i) := by rw [u6.other _ vo.2.2, q5]
  obtain c3 : s3.gpr C = BitVec.ofNat 64 ((s2.gpr (VR i)).toNat * (wordOf m 0).toNat / 2 ^ 64) := by rw [u3.gpr, m2]
  obtain c5 : s5.gpr C = s3.gpr C := by rw [u5.other _ (by decide), u4.other _ (by decide)]
  obtain l5 : (s5.gpr LO).toNat = if 0 < (s2.gpr (VR i)).toNat then 1 else 0 := by
    rw [u5.gpr, sltu_toNat, u4.gpr, u4.other _ vo.1, u3.other _ vo.2.2]; rfl
  obtain pl : (s2.gpr (VR i)).toNat * (wordOf m 0).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (s2.gpr (VR i)).isLt; omega_arith) (by have := (wordOf m 0).isLt; omega_arith)
  obtain c6 : (s6.gpr C).toNat = (s2.gpr (VR i)).toNat * (wordOf m 0).toNat / 2 ^ 64 +
      if 0 < (s2.gpr (VR i)).toNat then 1 else 0 := by
    obtain bl : (if 0 < (s2.gpr (VR i)).toNat then 1 else 0) ≤ 1 := by split <;> decide
    obtain bd : (s2.gpr (VR i)).toNat * (wordOf m 0).toNat / 2 ^ 64 < 2 ^ 64 - 1 :=
      Nat.div_lt_of_lt_mul (by omega_using [pl])
    rw [u6.gpr, BitVec.toNat_add, l5, c5, c3, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := _ / _) (by omega_using [bd]), Nat.mod_eq_of_lt (by omega_using [bd, bl])]
  obtain mc := VG.Proof.Weierstrass.RISCV64.Gen4.mont_carry hinv (s.gpr (VR i)).isLt
  rw [← q2] at mc
  refine ⟨by rw [q6, c6]; exact mc, ?_⟩
  exact (((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
    (upd_keeps u5)).trans (upd_keeps u6) |>.mono (by simp)

theorem top_ok {b : Addr} {i : Nat} (hi : i < 8) {s : State} (hc : Ctx b s) :
    WP isa (.block (top i)) s fun s' =>
      (s'.gpr (VR i)).toNat + 2 ^ 64 * (s'.gpr TOP).toNat =
        dw s.mem b (P (8 + i)) + (s.gpr C).toNat + (s.gpr TOP).toNat ∧ Keeps [VR i, LO, TOP] s s' := by
  obtain ⟨p1, p2, -⟩ := P_facts (j := 8 + i) (by omega_arith)
  obtain vo : VR i ∉ [LO, TOP, C] := VR_out (by decide) _
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  unfold top
  refine ld_ok hc p1 p2 fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => wp_add fun s4 u4 => wp_sltu fun s5 u5 =>
    wp_add fun s6 u6 => WP.block_nil ?_
  obtain v1 : (s1.gpr (VR i)).toNat = dw s.mem b (P (8 + i)) := by rw [u1.gpr]; rfl
  obtain c1 : s1.gpr C = s.gpr C := u1.other _ (Ne.symm vo.2.2)
  obtain e1 := carry (s1.gpr (VR i)) (s1.gpr C)
  obtain l1 := carry_le (s1.gpr (VR i) + s1.gpr C < s1.gpr C)
  obtain l3 : s3.gpr LO = if s1.gpr (VR i) + s1.gpr C < s1.gpr C then 1 else 0 := by
    rw [u3.gpr, u2.gpr, u2.other _ (Ne.symm vo.2.2)]
  obtain v3 : s3.gpr (VR i) = s1.gpr (VR i) + s1.gpr C := by rw [u3.other _ vo.1, u2.gpr]
  rw [← l3, ← v3, v1, c1] at e1
  rw [← l3] at l1
  obtain t3 : s3.gpr TOP = s.gpr TOP := by
    rw [u3.other _ (by decide), u2.other _ (Ne.symm vo.2.1), u1.other _ (Ne.symm vo.2.1)]
  obtain e2 := carry (s3.gpr (VR i)) (s3.gpr TOP)
  obtain l2 := carry_le (s3.gpr (VR i) + s3.gpr TOP < s3.gpr TOP)
  obtain t5 : s5.gpr TOP = if s3.gpr (VR i) + s3.gpr TOP < s3.gpr TOP then 1 else 0 := by
    rw [u5.gpr, u4.gpr, u4.other _ (Ne.symm vo.2.1)]
  obtain v5 : s5.gpr (VR i) = s3.gpr (VR i) + s3.gpr TOP := by rw [u5.other _ vo.2.1, u4.gpr]
  rw [← t5, ← v5, t3] at e2
  rw [← t5] at l2
  obtain l5 : s5.gpr LO = s3.gpr LO := by rw [u5.other _ (by decide), u4.other _ (Ne.symm vo.1)]
  obtain t6 : (s6.gpr TOP).toNat = (s5.gpr TOP).toNat + (s3.gpr LO).toNat := by
    rw [u6.gpr, BitVec.toNat_add, l5, Nat.mod_eq_of_lt (by omega_using [l1, l2])]
  refine ⟨?_, ?_⟩
  · rw [u6.other _ vo.2.1, t6]; omega_using [e1, e2]
  · exact (((((upd_keeps u1).trans (upd_keeps u2)).trans (upd_keeps u3)).trans (upd_keeps u4)).trans
      (upd_keeps u5)).trans (upd_keeps u6) |>.mono (by simp)

/-! ## The rounds -/

/-- The words of the product above round `i`'s window. -/
abbrev up (m : Mem) (b : Addr) (i : Nat) : Nat := colsV (fun j => dw m b (P (8 + i + j))) (8 - i)

/-- The registers the reduction writes. -/
abbrev clobD : List Reg := TOP :: LO :: HI :: C :: VL

/-- After `i` rounds. -/
structure RedInv (b : Addr) (m : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobD → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∃ Q < (2 ^ 64) ^ i, (2 ^ 64) ^ i * (rv s i 8 + (2 ^ 64) ^ 8 * ((s.gpr TOP).toNat + up s0.mem b i)) =
    pw s0.mem b + Q * m

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

theorem rv_next {s s' : State} {i : Nat} (h : ∀ j < 7, s'.gpr (VR (i + 1 + j)) = s.gpr (VR (i + 1 + j))) :
    rv s' (i + 1) 8 = rv s (i + 1) 7 + (2 ^ 64) ^ 7 * (s'.gpr (VR i)).toNat := by
  rw [rv, colsV_succ, show i + 1 + 7 = i + 8 by omega_arith, VR_add8,
    colsV_congr (g := fun j => (s.gpr (VR (i + 1 + j))).toNat) fun j hj => by rw [h j hj]]

theorem up_succ (m : Mem) (b : Addr) {i : Nat} (hi : i < 8) :
    up m b i = dw m b (P (8 + i)) + 2 ^ 64 * up m b (i + 1) := by
  obtain ⟨l, hl⟩ : ∃ l, 8 - i = l + 1 := ⟨7 - i, by omega_arith⟩
  rw [up, up, hl, show 8 - (i + 1) = l by omega_arith, colsV_shift, Nat.add_zero,
    colsV_congr (f := fun j => dw m b (P (8 + i + (j + 1)))) (g := fun j => dw m b (P (8 + (i + 1) + j)))
      fun j _ => by rw [show 8 + i + (j + 1) = 8 + (i + 1) + j by omega_arith]]

theorem round_ok {b : Addr} {m : Nat} {s0 : State} (h0 : MOk b m s0)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (hm : m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) 7)
    {i : Nat} (hi : i < 8) {s : State} (h : RedInv b m s0 i s) :
    WP isa (.block (redRound i)) s (RedInv b m s0 (i + 1)) := by
  obtain gM : ∀ r ∈ .a3 :: AL, s.gpr r = s0.gpr r := fun r hr => h.gpr r (by revert hr; cases r <;> decide)
  obtain hM : MOk b m s := h0.of gM h.wr h.mem
  unfold redRound
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (quot_ok (i := i) hM hinv) fun s1 ⟨e1, k1⟩ => ?_)
  obtain vo : VR i ∉ [LO, HI, C, TOP] := VR_out (by decide) _
  have vo' : VR i ∉ [LO, HI, C] := VR_out (by decide) _
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  obtain g1 : ∀ r, r ∉ clobD → s1.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, not_or] at hr
    obtain nr : r ≠ VR i := fun e => hr.2.2.2.2 (e ▸ VR_mem i)
    exact k1.1 r (by simp [hr.2.1, hr.2.2.2.1, nr])
  obtain hM1 : MOk b m s1 := hM.of (fun r hr => g1 r (by revert hr; cases r <;> decide)) k1.2.2.2.1 k1.2.1
  obtain dis : ∀ j < 7, VR (i + 1 + j) ≠ VR i := fun j hj => VR_ne (by omega_arith)
  refine WP.block_append (WP.mono (row_ok (acc := true) (y := VR i) (i := i + 1) hM1.ops (by decide) vo'
    (fun j hj => Ne.symm (dis j hj)) 7 (Nat.le_refl _)) fun s2 h2 => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hM1.ctx (h2.out _ (by decide)) h2.wr
  refine WP.mono (top_ok hi hc2) fun s3 ⟨e3, k3⟩ => ?_
  obtain m2 : s2.mem = s0.mem := by rw [h2.mem, k1.2.1, h.mem]
  refine ⟨fun r hr => ?_, by rw [k3.2.1, m2], by rw [k3.2.2.1, h2.rd, k1.2.2.1, h.rd],
    by rw [k3.2.2.2.1, h2.wr, k1.2.2.2.1, h.wr], by rw [k3.2.2.2.2, h2.sp, k1.2.2.2.2, h.sp], ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, not_or] at hr
    obtain nr : r ≠ VR i := fun e => hr.2.2.2.2 (e ▸ VR_mem i)
    rw [k3.1 r (by simp [hr.1, hr.2.1, nr]),
      h2.out r (by simp only [List.mem_cons, not_or]; exact hr.2), g1 r hr', h.gpr r hr']
  · obtain ⟨Q, hQ, hv⟩ := h.val
    have e2 := h2.val
    simp only [↓reduceIte] at e2
    obtain t2 : s2.gpr TOP = s.gpr TOP := by
      rw [h2.out _ (by decide), k1.1 _ (by simp [Ne.symm vo.2.2.2])]
    rw [m2, t2] at e3
    obtain w1 : rv s1 (i + 1) 7 = colsV (fun j => (s.gpr (VR (i + (j + 1)))).toNat) 7 := colsV_congr fun j hj => by
      obtain vj : VR (i + 1 + j) ∉ [LO, HI, C] := VR_out (by decide) _
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vj
      rw [k1.1 _ (by simp [dis j hj, vj.1, vj.2.2]), show i + 1 + j = i + (j + 1) by omega_arith]
    obtain w3 : rv s3 (i + 1) 8 = rv s2 (i + 1) 7 + (2 ^ 64) ^ 7 * (s3.gpr (VR i)).toNat :=
      rv_next fun j hj => by
        obtain vj : VR (i + 1 + j) ∉ [LO, TOP] := VR_out (by decide) _
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vj
        exact k3.1 _ (by simp [dis j hj, vj.1, vj.2])
    obtain hu := up_succ s0.mem b hi
    obtain hq := (s1.gpr (VR i)).isLt
    refine ⟨Q + (2 ^ 64) ^ i * (s1.gpr (VR i)).toNat, ?_, ?_⟩
    · obtain hle : (2 ^ 64) ^ i * ((s1.gpr (VR i)).toNat + 1) ≤ (2 ^ 64) ^ i * 2 ^ 64 :=
        Nat.mul_le_mul_left _ (by omega_using [hq])
      rw [show ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 from Nat.pow_succ ..]
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega_using [hQ, hle]
    · rw [w1] at e2
      refine round_alg (E := (2 ^ 64) ^ 7) (Nat.pow_succ ..) (Nat.pow_succ ..) ?_ w3 hu e1 e2 e3 hm hv
      rw [rv, colsV_shift, Nat.add_zero]

/-- After `n` words of the product loaded. -/
structure LdInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ VL → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : ∀ j < n, (s.gpr (VR j)).toNat = dw s0.mem b (P j)

theorem ld8_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j => [.load .d (VR j) .a3 (P j)])) s0 (LdInv b s0 n)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨p1, p2, -⟩ := P_facts (j := n) (by omega_arith)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ld8_ok hc n (by omega_arith)) fun s h => ?_)
    refine ld_ok (ctx_of hc (h.gpr _ (by decide)) h.wr) p1 p2 fun s1 u1 => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u1.other r (fun e => hr (e ▸ VR_mem n)), h.gpr r hr], by rw [u1.mem, h.mem],
      by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], fun j hj => ?_⟩
    by_cases e : j = n
    · subst e; rw [u1.gpr, h.mem]; rfl
    · rw [u1.other _ (VR_ne (by omega_arith))]; exact h.val j (by omega_arith)

private theorem red_start {f : Nat → Nat} {R t m : Nat} (hR : R = colsV f 8) (ht : t = 0) {n : Nat} (hn : n = 8 + 8) :
    (2 ^ 64) ^ 0 * (R + (2 ^ 64) ^ 8 * (t + colsV (fun j => f (8 + 0 + j)) (8 - 0))) = colsV f n + 0 * m := by
  subst hn hR ht
  rw [colsV_split, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.add_zero]

theorem red_ok {b : Addr} {m : Nat} {s : State} (h : MOk b m s)
    (hinv : ((wordOf m 0).toNat * (negInv m % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    (hm : m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) 7) :
    WP isa (.block red) s (RedInv b m s 8) := by
  unfold red
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (ld8_ok h.ctx 8 (Nat.le_refl _)) fun s1 h1 => ?_)
  refine wp_li (imm := 0) (by decide) fun s2 u2 => ?_
  refine wp_range_flatMap (M := isa) (RedInv b m s) (fun i s' hi h' => round_ok h hinv hm hi h') 8 (Nat.le_refl _) s2
    ⟨fun r hr => ?_, by rw [u2.mem, h1.mem], by rw [u2.rd, h1.rd], by rw [u2.wr, h1.wr], by rw [u2.sp, h1.sp], 0,
      by decide, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [u2.other r hr.1, h1.gpr r hr.2.2.2.2]
  · refine red_start (f := fun j => dw s.mem b (P j)) (R := rv s2 0 8) (t := (s2.gpr TOP).toNat) ?_
      (by rw [u2.gpr]; rfl) rfl
    exact colsV_congr fun j hj => by
      rw [Nat.zero_add, u2.other _ (fun e => (VR_out (by decide) _ : VR j ∉ [TOP]) (by rw [e]; simp))]
      exact h1.val j hj

/-! ## The final subtraction -/

open VG.Proof.Weierstrass.RISCV64.P256Field (sbb_ok)
open VG.Proof.X25519.RISCV64 (wp_and)

/-- After `j` words of the difference. -/
structure SubInv (b : Addr) (m : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ LO :: HI :: C :: AL → s.gpr r = s0.gpr r
  ar : ∀ l, j ≤ l → l < 7 → s.gpr (AR l) = wordOf m l
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 D, 64⟩] s0.mem s.mem
  cy : (s.gpr C).toNat ≤ 1
  val : colsV (fun i => dw s.mem b (D + 8 * i)) j + colsV (fun i => (wordOf m i).toNat) j =
    colsV (fun i => (s0.gpr (VR i)).toNat) j + (2 ^ 64) ^ j * (s.gpr C).toNat

private theorem sub_alg {L M V E d c x c' dw' E' : Nat} (hv : L + M = V + E * c) (e : d + dw' + c = x + 2 ^ 64 * c')
    (hE : E' = E * 2 ^ 64) : L + E * d + (M + E * dw') = V + E * x + E' * c' := by
  subst hE
  obtain key : E * d + E * dw' + E * c = E * x + E * 2 ^ 64 * c' := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e]
  omega_using [hv, key]

theorem MR_facts : ∀ j < 8, MR j ∉ [LO, HI, C, .a3] ∧ MR j ∈ AL ∧ ∀ l < 7, j < l → AR l ≠ MR j := by decide

theorem subStep_ok {b : Addr} {m : Nat} {s0 : State} (h0 : MOk b m s0) {j : Nat} (hj : j < 8) {s : State}
    (h : SubInv b m s0 j s) : WP isa (.block (subStep j)) s (SubInv b m s0 (j + 1)) := by
  obtain ⟨e1, e2⟩ := lay
  obtain ⟨mr, mal, mne⟩ := MR_facts j hj
  obtain hcs : Ctx b s := ctx_of h0.ctx (h.gpr _ (by decide)) h.wr
  obtain vo : VR j ∉ LO :: HI :: C :: AL := VR_out (by decide) _
  unfold subStep
  -- The modulus's word.
  refine WP.block_append (WP.mono (Q := fun s1 : State => (s1.gpr (MR j)) = wordOf m j ∧
    (∀ r, r ≠ MR j → s1.gpr r = s.gpr r) ∧ s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.sp = s.sp) ?_
    fun s1 ⟨w1, g1, m1, rd1, wr1, sp1⟩ => ?_)
  · split
    · rename_i hl
      refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [MR, ite_eq_left hl]; exact h.ar j (Nat.le_refl _) hl
    · rename_i hl
      obtain rfl : j = 7 := by omega_using [hj, hl]
      refine ld_ok hcs (by simp only [M7]; omega_arith) (by simp only [M7]; omega_arith) fun s1 u1 =>
        WP.block_nil ⟨?_, fun r hr => u1.other r hr, u1.mem, u1.rd, u1.wr, u1.sp⟩
      show s1.gpr .a0 = _
      rw [u1.gpr]
      refine BitVec.eq_of_toNat_eq ?_
      rw [← h0.m7]
      exact dw_frame h.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint b (by simp only [M7, D]; omega_arith) (by simp only [M7]; omega_arith)
          (by simp only [D]; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at mr
  have vo' := vo
  simp only [List.mem_cons, not_or] at vo
  obtain vm : VR j ≠ MR j := fun e => vo.2.2.2 (e ▸ mal)
  show WP isa (.block ([.sltu LO (VR j) (MR j), .sub HI (VR j) (MR j), .sltu (MR j) HI C, .sub HI HI C,
    .add C LO (MR j)] ++ [Instr.store .d HI .a3 (D + 8 * j)])) s1 _
  refine WP.block_append (WP.mono (sbb_ok (d := HI) (x := VR j) (y := MR j) (c := C) (u := LO) (v := MR j)
    (hvd := mr.2.1) (hvc := mr.2.2.1) (huv := Ne.symm mr.1) (hux := Ne.symm vo.1) (huy := Ne.symm mr.1))
    fun s2 ⟨e2', k2⟩ => ?_)
  obtain hc2 : Ctx b s2 := ctx_of hcs (by rw [k2.1 _ (by simp [Ne.symm mr.2.2.2]), g1 _ (Ne.symm mr.2.2.2)])
    (by rw [k2.2.2.2.1, wr1])
  refine sd_ok hc2 (by simp only [D]; omega_arith) (by simp only [D]; omega_arith) fun s3 u3 => WP.block_nil ?_
  obtain c1 : s1.gpr C = s.gpr C := g1 _ (Ne.symm mr.2.2.1)
  obtain v1 : s1.gpr (VR j) = s0.gpr (VR j) := by rw [g1 _ vm, h.gpr _ vo']
  obtain ⟨ev, ec⟩ := e2' (by rw [c1]; exact h.cy)
  rw [w1, c1, v1] at ev
  have hm3 : s3.mem = s.mem.writeW (b + BitVec.ofNat 64 (D + 8 * j)) (s2.gpr HI) := by rw [u3.mem, k2.2.1, m1]
  refine ⟨fun r hr => ?_, fun l hl hl7 => ?_, by rw [u3.rd, k2.2.2.1, rd1, h.rd], by rw [u3.wr, k2.2.2.2.1, wr1, h.wr],
    by rw [u3.sp, k2.2.2.2.2, sp1, h.sp], ?_, by rw [u3.gpr]; exact ec, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, not_or] at hr
    obtain nr : r ≠ MR j := fun e => hr.2.2.2 (e ▸ mal)
    rw [u3.gpr, k2.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, nr]), g1 r nr, h.gpr r hr']
  · obtain nl := mne l hl7 hl
    obtain nc := (by decide : ∀ l < 7, AR l ∉ [LO, HI, C]) l hl7
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at nc
    rw [u3.gpr, k2.1 _ (by simp [nc.1, nc.2.1, nc.2.2, nl]), g1 _ nl]
    exact h.ar l (by omega_arith) hl7
  · rw [hm3]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_arith) (by omega_arith)
      (by simp only [D]; omega_arith))
  · obtain low : colsV (fun i => dw s3.mem b (D + 8 * i)) j = colsV (fun i => dw s.mem b (D + 8 * i)) j :=
      colsV_congr fun i hi => by
        rw [hm3, dw_write_other _ _ _ (by omega_arith) (by simp only [D]; omega_arith) (by simp only [D]; omega_arith)]
    rw [colsV_succ, colsV_succ, colsV_succ, low, hm3, dw_write_self, u3.gpr]
    exact sub_alg h.val ev (Nat.pow_succ ..)

/-- After `j` words of the selection. -/
structure SelInv8 (b O : Addr) (sel : Prop) [Decidable sel] (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [LO, HI] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 64⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = if sel then (s0.gpr (VR i)).toNat else dw s0.mem b (D + 8 * i)

theorem selStep_ok {b O : Addr} {s0 : State} (hc : Ctx b s0) (h2 : s0.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 8, InRegions s0.wr (O + BitVec.ofNat 64 (8 * i)) 8)
    (odis : ∀ i < 8, Region.Disjoint ⟨b + BitVec.ofNat 64 (D + 8 * i), 8⟩ ⟨O, 64⟩) (hm : IsMask (s0.gpr TOP))
    {j : Nat} (hj : j < 8) {s : State} (h : SelInv8 b O (s0.gpr TOP = BitVec.allOnes 64) s0 j s) :
    WP isa (.block (selStep j)) s (SelInv8 b O (s0.gpr TOP = BitVec.allOnes 64) s0 (j + 1)) := by
  obtain ⟨e1, e2⟩ := lay
  obtain vo : VR j ∉ [LO, HI] := VR_out (by decide) _
  have vo' := vo
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at vo
  obtain hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold selStep
  refine ld_ok hcs (by simp only [D]; omega_arith) (by simp only [D]; omega_arith) fun s1 u1 =>
    wp_xor' fun s2 u2 => wp_and fun s3 u3 => wp_xor' fun s4 u4 => ?_
  refine wp_sd (by omega_arith) (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
    u1.other _ (by decide), h.gpr _ (by decide), h2]) (al8 oal (by omega_arith))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr]; exact ow j hj) fun s5 u5 => WP.block_nil ?_
  obtain v4 : s4.gpr LO = s1.gpr LO ^^^ ((s0.gpr (VR j) ^^^ s1.gpr LO) &&& s0.gpr TOP) := by
    rw [u4.gpr, u3.gpr, u3.other _ (by decide), u2.other LO (by decide), u2.gpr, u2.other TOP (by decide),
      u1.other TOP (by decide), u1.other _ vo.1, h.gpr _ vo', h.gpr TOP (by decide)]
  rw [sel_mask hm] at v4
  have hm5 : s5.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s4.gpr LO) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain d1 : (s1.gpr LO).toNat = dw s0.mem b (D + 8 * j) := by
    rw [u1.gpr]
    exact dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact odis j hj
  refine ⟨fun r hr => ?_, by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_, fun i hi => ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.gpr, u4.other r hr.1, u3.other r hr.2, u2.other r hr.2, u1.other r hr.1, h.gpr r hr']
  · rw [hm5]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [show (⟨O, 64⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 64⟩ by simp]
    exact Offset.contains O (by omega_arith) (by omega_arith) (by omega_arith)
  · rw [hm5]
    by_cases e : i = j
    · subst e
      rw [dw_write_self, v4]
      split
      · rfl
      · exact d1
    · rw [dw_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.val i (by omega_arith)

private theorem csub_out {D' Mv L E Tk c V R m' : Nat} (hD : D' < E) (hM : Mv < E) (hV : V = L + E * Tk) (hV2 : V < 2 * Mv)
    (hs : D' + Mv = L + E * c) (hc : c ≤ 1) {sel : Prop} (hsel : sel ↔ Tk = 0 ∧ c = 1)
    (h1 : sel → R = L) (h0 : ¬ sel → R = D') (hm : m' = Mv) : R = V % m' := by
  obtain ⟨-, -, a, b⟩ := csub_nat hD hM hV hV2 hs hc
  subst hm
  by_cases h : sel
  · rw [h1 h, a (hsel.mp h)]
  · rw [h0 h, b (fun h' => h (hsel.mpr h'))]

/-- The registers the final subtraction writes. -/
abbrev clobC : List Reg := TOP :: LO :: HI :: C :: AL

theorem csub_ok {b O : Addr} {m : Nat} {s : State} (h : MOk b m s) (h2 : s.gpr .t2 = O) (oal : O.toNat % 8 = 0)
    (ow : ∀ i < 8, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8)
    (odis : ∀ i < 8, Region.Disjoint ⟨b + BitVec.ofNat 64 (D + 8 * i), 8⟩ ⟨O, 64⟩)
    (hm : m = colsV (fun i => (wordOf m i).toNat) 8)
    (hV : rv s 0 8 + (2 ^ 64) ^ 8 * (s.gpr TOP).toNat < 2 * m) :
    WP isa (.block csub) s fun s' =>
      (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 D, 64⟩, ⟨O, 64⟩] s.mem s'.mem ∧
      ov s'.mem O 8 = (rv s 0 8 + (2 ^ 64) ^ 8 * (s.gpr TOP).toNat) % m := by
  unfold csub
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s1 u1 => ?_
  obtain gA : ∀ r ∈ .a3 :: AL, s1.gpr r = s.gpr r := fun r hr => u1.other r (by revert hr; cases r <;> decide)
  obtain hM1 : MOk b m s1 := h.of gA u1.wr u1.mem
  obtain c1 : (s1.gpr C).toNat = 0 := by rw [u1.gpr]; rfl
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SubInv b m s1) (fun j s' hj h' => subStep_ok hM1 hj h') 8
    (Nat.le_refl _) s1 ⟨fun _ _ => rfl, fun l _ hl => hM1.regs l hl, rfl, rfl, rfl, Frame.refl _ _,
      by rw [c1]; decide, by rw [c1]; rfl⟩) fun s3 h3 => ?_)
  refine wp_sub fun s4 u4 => ?_
  obtain t3 : s3.gpr TOP = s.gpr TOP := by rw [h3.gpr _ (by decide), u1.other _ (by decide)]
  obtain v1 : ∀ j, s1.gpr (VR j) = s.gpr (VR j) := fun j =>
    u1.other _ fun e => (VR_out (by decide) _ : VR j ∉ [C]) (by rw [e]; simp)
  have hs := h3.val
  obtain hL : colsV (fun i => (s1.gpr (VR i)).toNat) 8 = rv s 0 8 :=
    colsV_congr fun j _ => by rw [v1, Nat.zero_add]
  rw [hL, ← hm] at hs
  obtain hD : colsV (fun i => dw s3.mem b (D + 8 * i)) 8 < (2 ^ 64) ^ 8 := colsV_lt _ (fun _ => dw_lt _ _ _) 8
  obtain hMl : m < (2 ^ 64) ^ 8 := by
    rw [hm]; exact colsV_lt _ (fun _ => (wordOf m _).isLt) 8
  obtain ⟨hT1, hno, -, -⟩ := csub_nat (V := rv s 0 8 + (2 ^ 64) ^ 8 * (s.gpr TOP).toNat) hD hMl rfl hV hs h3.cy
  obtain ⟨hmask, hall⟩ := toNat_sub_bits (x := s3.gpr TOP) (c := s3.gpr C) (by rw [t3]; exact hT1) h3.cy
    (by rw [t3]; exact hno)
  rw [← u4.gpr] at hmask hall
  rw [t3] at hall
  obtain g4 : ∀ r, r ∉ clobC → s4.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, not_or] at hr
    rw [u4.other r hr.1, h3.gpr r (by simp only [List.mem_cons, not_or]; exact hr.2), u1.other r hr.2.2.2.1]
  obtain wr4 : s4.wr = s.wr := by rw [u4.wr, h3.wr, u1.wr]
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv8 b O (s4.gpr TOP = BitVec.allOnes 64) s4)
    (fun j s' hj h' => selStep_ok (ctx_of h.ctx (g4 _ (by decide)) wr4) (by rw [g4 _ (by decide), h2]) oal
      (by rw [wr4]; exact ow) odis hmask hj h') 8 (Nat.le_refl _) s4
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s5 h5 => ?_
  refine ⟨fun r hr => ?_, by rw [h5.rd, u4.rd, h3.rd, u1.rd], by rw [h5.wr, wr4],
    by rw [h5.sp, u4.sp, h3.sp, u1.sp], ?_, ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, not_or] at hr
    rw [h5.gpr r (by simp [hr.2.1, hr.2.2.1]), g4 r hr']
  · rw [← u1.mem]
    refine (h3.frame.mono (by simp)).trans ?_
    rw [← u4.mem]
    exact h5.frame.mono (by simp)
  · refine csub_out hD hMl rfl hV hs h3.cy hall (fun hsel => ?_) (fun hsel => ?_) rfl
    · exact colsV_congr fun j hj => by
        rw [h5.val j hj, ite_eq_left hsel, u4.other _ (fun e => (VR_out (by decide) _ : VR j ∉ [TOP]) (by rw [e]; simp)),
          h3.gpr _ (VR_out (by decide) _), v1, Nat.zero_add]
    · exact colsV_congr fun j hj => by rw [h5.val j hj, ite_eq_right hsel, u4.mem]

/-! ## The registers kept -/

theorem KR_inj : ∀ i < 6, ∀ j < 6, KR.getD i .s6 = KR.getD j .s6 → i = j := by decide
theorem KR_idx : ∀ r ∈ KR, ∃ i < 6, KR.getD i .s6 = r := by decide
theorem KR_mem : ∀ i < 6, KR.getD i .s6 ∈ KR := by decide

/-- Where they are kept. -/
abbrev SR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SV, 48⟩

/-- After `n` registers kept. -/
structure SvInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [SR b] s0.mem s.mem
  saved : ∀ i < n, s.mem.readW (b + BitVec.ofNat 64 (SV + 8 * i)) 64 = s0.gpr (KR.getD i .s6)

theorem save_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ n ≤ 6, WP isa (.block ((List.range n).flatMap fun j => [.store .d (KR.getD j .s6) .a3 (SV + 8 * j)])) s0
      (SvInv b s0 n)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨e1, e2⟩ := lay
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (save_ok hc n (by omega_arith)) fun s h => ?_)
    refine sd_ok (ctx_of hc (by rw [h.gpr]) h.wr) (by simp only [SV]; omega_arith) (by simp only [SV]; omega_arith)
      fun s1 u1 => WP.block_nil ?_
    refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], ?_, fun i hi => ?_⟩
    · rw [u1.mem]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_arith) (by omega_arith)
        (by simp only [SV]; omega_arith))
    · rw [u1.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by simp only [SV]; omega_arith)
          (by simp only [SV]; omega_arith)) (by decide)]
        exact h.saved i hi
      · rw [Mem.readW_writeW_self64, h.gpr]

/-- After `n` registers loaded back, to `v`. -/
structure RsInv (v : Nat → BitVec 64) (s0 : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (KR.getD i .s6) = v i
  others : ∀ r, r ∉ KR → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp

theorem restore_ok {b : Addr} {v : Nat → BitVec 64} {s0 : State} (hc : Ctx b s0)
    (hs : ∀ i < 6, s0.mem.readW (b + BitVec.ofNat 64 (SV + 8 * i)) 64 = v i) :
    ∀ n ≤ 6, WP isa (.block ((List.range n).flatMap fun j => [.load .d (KR.getD j .s6) .a3 (SV + 8 * j)])) s0
      (RsInv v s0 n)
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨e1, e2⟩ := lay
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (restore_ok hc hs n (by omega_arith)) fun s h => ?_)
    refine ld_ok (ctx_of hc (h.others _ (by decide)) h.wr) (by simp only [SV]; omega_arith)
      (by simp only [SV]; omega_arith) fun s1 u1 => WP.block_nil ?_
    rw [h.mem, hs n (by omega_arith)] at u1
    refine ⟨fun i hi => ?_, fun r hr => ?_, by rw [u1.mem, h.mem], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr],
      by rw [u1.sp, h.sp]⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [u1.other _ fun e => absurd (KR_inj i (by omega_arith) n (by omega_arith) e) (by omega_arith)]
        exact h.restored i hi
      · exact u1.gpr
    · rw [u1.other _ fun e => hr (by rw [e]; exact KR_mem n (by omega_arith))]; exact h.others r hr

/-! ## The operation -/

theorem wordOf_split {m : Nat} (hm : m < 2 ^ (64 * 8)) :
    m = colsV (fun i => (wordOf m i).toNat) 8 ∧
    m = (wordOf m 0).toNat + 2 ^ 64 * colsV (fun j => (wordOf m (j + 1)).toNat) 7 := by
  obtain h : m = colsV (fun i => (wordOf m i).toNat) 8 := by
    rw [colsV_wordOf, Nat.mod_eq_of_lt (by rw [← Nat.pow_mul]; exact hm)]
  exact ⟨h, h.trans (colsV_shift _ _)⟩

private theorem inv_form {a b : Nat} (h : a * b % 2 ^ 64 = 2 ^ 64 - 1) : (a * (b % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod_mod, h]

/-- The value after the rounds is Montgomery's. -/
private theorem red_out {V X B Q P m R E : Nat} (hP : P = X * B) (hv : E * V = P + Q * m) (hE : E = R) (hX : X < R)
    (hB : B < m) (hQ : Q < E) : V < 2 * m ∧ V % m * R % m = X * B % m := by
  subst hP hE
  exact mont_nat (by rw [Nat.mul_comm]; exact hv) hX hB hQ

/-- The part of the own working space the operation writes. -/
theorem sub_own8 {b O : Addr} {d n : Nat} (hd : T 8 ≤ d) (hn : d + n ≤ T 8 + 64 * 8) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 d, n⟩ : Region)], ∃ r' ∈ [ownA 8 b, ⟨O, 8 * 8⟩], Region.Sub r r' := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., ownA_sub b hd hn⟩

theorem fast_spec {m : Nat} (hm : m < 2 ^ (64 * 8)) (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1) :
    FastSpec 8 (fast m) (fun _ B => B < m) (fun A B r => r < m ∧ r * 2 ^ (64 * 8) % m = A * B % m) := by
  intro b A B O s hC hA hB hO hp
  obtain ⟨e1, e2⟩ := lay
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts 8 (by decide) (by decide)
  obtain ⟨w8, w1⟩ := wordOf_split hm
  have hc := hC.ctx
  unfold fast
  refine WP.seq (WP.mono (save_ok hc 6 (Nat.le_refl _)) fun s1 h1 => ?_)
  obtain hc1 : Ctx b s1 := ctx_of hc (by rw [h1.gpr]) h1.wr
  obtain sR : Region.Sub (SR b) (ownA 8 b) := ownA_sub b (Nat.le_refl _) (by simp only [SV]; omega_arith)
  obtain xA : xv s1.mem A 8 = xv s.mem A 8 := colsV_congr fun i hi => dw_frame h1.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hA i hi) sR
  obtain xB : xv s1.mem B 8 = xv s.mem B 8 := colsV_congr fun i hi => dw_frame h1.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hB i hi) sR
  obtain ain : ∀ i < 8, InRegions (s1.rd ++ s1.wr) (A + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [h1.rd, h1.wr]; exact hC.ain
  obtain bin : ∀ i < 8, InRegions (s1.rd ++ s1.wr) (B + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [h1.rd, h1.wr]; exact hC.bin
  obtain h4 : s1.gpr .t4 = A := by rw [h1.gpr, hC.a]
  obtain h5 : s1.gpr .t5 = B := by rw [h1.gpr, hC.b']
  -- The product.
  refine WP.seq (WP.mono (Q := fun s' : State =>
      (∀ r, r ∉ clobP → s'.gpr r = s1.gpr r) ∧ s'.rd = s1.rd ∧ s'.wr = s1.wr ∧ s'.sp = s1.sp ∧
      Frame [PR 8 b] s1.mem s'.mem ∧ pw s'.mem b = xv s1.mem A 8 * xv s1.mem B 8) ?_
    fun s2 ⟨g2, rd2, wr2, sp2, f2, v2⟩ => ?_)
  · refine WP.ite (s1.gpr .t4 == s1.gpr .t5) rfl (fun he => ?_) (fun _ => ?_)
    · obtain hAB : A = B := by rw [← h4, ← h5]; exact beq_iff_eq.mp he
      subst hAB
      exact sqrProd_ok hc1 hC.nowrap h4 hC.aal ain hA
    · exact mulProd_ok hc1 h4 h5 hC.aal hC.bal ain bin hA hB
  obtain hc2 : Ctx b s2 := ctx_of hc1 (g2 _ (by decide)) wr2
  -- The reduction.
  refine consts_ok (m := m) hc2 fun s3 g3 rd3 wr3 sp3 f3 hM3 => ?_
  refine WP.block_append (WP.mono (red_ok hM3 (inv_form hinv) w1) fun s4 h4' => ?_)
  obtain ⟨Q, hQ, hv⟩ := h4'.val
  obtain p3 : pw s3.mem b = pw s2.mem b := colsV_congr fun j hj => by
    obtain ⟨-, -, p⟩ := P_facts hj
    obtain ⟨p', -, -⟩ := P_facts hj
    exact dw_frame f3 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (by simp only [M7]; omega_arith) (by omega_arith) (by simp only [M7]; omega_arith)
  obtain hAlt : xv s.mem A 8 < (2 ^ 64) ^ 8 := colsV_lt _ (fun _ => dw_lt _ _ _) 8
  obtain hup : up s3.mem b 8 = 0 := by simp only [up, Nat.sub_self, colsV]
  obtain h08 : rv s4 8 8 = rv s4 0 8 := colsV_congr fun j _ => by
    rw [Nat.add_comm 8 j, VR_add8, Nat.zero_add]
  rw [hup, Nat.add_zero, h08, p3] at hv
  obtain hR : ((2 : Nat) ^ 64) ^ 8 = 2 ^ (64 * 8) := (Nat.pow_mul ..).symm
  obtain ⟨hV2, hVm⟩ := red_out (X := xv s.mem A 8) (B := xv s.mem B 8) (by rw [v2, xA, xB]) hv hR
    (by rw [← hR]; exact hAlt) hp hQ
  -- The final subtraction.
  obtain gM : ∀ r ∈ .a3 :: AL, s4.gpr r = s3.gpr r := fun r hr => h4'.gpr r (by revert hr; cases r <;> decide)
  obtain hM4 : MOk b m s4 := hM3.of gM h4'.wr h4'.mem
  obtain g4 : ∀ r, r ∉ [TOP] ++ clobP → s4.gpr r = s1.gpr r := fun r hr => by
    obtain ⟨a, b', c⟩ : r ∉ clobD ∧ r ∉ LO :: HI :: AL ∧ r ∉ clobP := by revert hr; cases r <;> decide
    rw [h4'.gpr r a, g3 r b', g2 r c]
  obtain wr4 : s4.wr = s.wr := by rw [h4'.wr, wr3, wr2, h1.wr]
  obtain odis : ∀ i < 8, Region.Disjoint ⟨b + BitVec.ofNat 64 (D + 8 * i), 8⟩ ⟨O, 64⟩ := fun i hi =>
    disj_symm (disj_sub hO (ownA_sub b (by simp only [D]; omega_arith) (by simp only [D]; omega_arith)))
  refine WP.block_append (WP.mono (csub_ok hM4 (by rw [g4 _ (by decide), h1.gpr, hC.o]) hC.oal
    (by rw [wr4]; exact hC.ow) odis w8 hV2) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_)
  obtain hc5 : Ctx b s5 := ctx_of hc1 (by rw [g5 _ (by decide), g4 _ (by decide)]) (by rw [wr5, wr4, h1.wr])
  -- The registers back.
  obtain hsav : ∀ i < 6, s5.mem.readW (b + BitVec.ofNat 64 (SV + 8 * i)) 64 = s.gpr (KR.getD i .s6) := fun i hi => by
    rw [← h1.saved i hi]
    obtain c : (⟨b + BitVec.ofNat 64 (SV + 8 * i), 8⟩ : Region).Contains (b + BitVec.ofNat 64 (SV + 8 * i)) 8 :=
      Region.contains_self _ _
    rw [f5.readW c (fun r hr => ?_) (by decide), h4'.mem, f3.readW c (fun r hr => ?_) (by decide),
      f2.readW c (fun r hr => ?_) (by decide)]
    · rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inl (by simp only [SV]; omega_arith)) (by simp only [SV]; omega_arith) (by omega_arith)
    · rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inl (by simp only [SV, M7]; omega_arith)) (by simp only [SV]; omega_arith)
        (by simp only [M7]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (.inl (by simp only [SV, D]; omega_arith)) (by simp only [SV]; omega_arith)
          (by simp only [D]; omega_arith)
      · exact disj_symm (disj_sub hO (ownA_sub b (by simp only [SV]; omega_arith) (by simp only [SV]; omega_arith)))
  refine WP.mono (restore_ok (v := fun i => s.gpr (KR.getD i .s6)) hc5 hsav 6 (Nat.le_refl _)) fun s6 h6 => ?_
  refine ⟨⟨?_, ?_⟩, ?_, fun r hr => ?_, by rw [h6.rd, rd5, h4'.rd, rd3, rd2, h1.rd], by rw [h6.wr, wr5, wr4],
    by rw [h6.sp, sp5, h4'.sp, sp3, sp2, h1.sp]⟩
  · rw [h6.mem, v5]; exact Nat.mod_lt _ (by omega_using [hp])
  · rw [h6.mem, v5]; exact hVm
  · rw [h6.mem]
    refine ((h1.frame.sub (sub_own8 (Nat.le_refl _) (by simp only [SV]; omega_arith))).trans
      (f2.sub (sub_own8 (by omega_arith) (by omega_arith)))).trans ?_
    refine (f3.sub (sub_own8 (by simp only [M7]; omega_arith) (by simp only [M7]; omega_arith))).trans ?_
    rw [← h4'.mem]
    refine f5.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_own8 (by simp only [D]; omega_arith) (by simp only [D]; omega_arith) _ (List.mem_singleton_self _)
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · by_cases hK : r ∈ KR
    · obtain ⟨i, hi, rfl⟩ := KR_idx r hK
      exact h6.restored i hi
    · obtain ⟨a, c⟩ : r ∉ clobC ∧ r ∉ [TOP] ++ clobP := by revert hr hK; cases r <;> decide
      rw [h6.others r hK, g5 r a, g4 r c, h1.gpr]

/-! ## The contract by register -/

open VG.Impl.Weierstrass.Mont (Modulus)
open VG.Proof.Weierstrass.RISCV64 (mulRV alignedC)

theorem mul_rv {S : Modulus} (hS : WideOk S) (h8 : S.k = 8) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain hf : FastSpec S.k (fast S.m) (fun _ B => B < S.m)
      (fun A B r => r < S.m ∧ r * 2 ^ (64 * S.k) % S.m = A * B % S.m) := by
    rw [h8]; exact fast_spec (h8 ▸ hS.lt) hS.inv
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnWith_rv hS.k7 hS.k30 @hf (@mulCore_spec S.k S.m hS.lt hS.inv) hs.1 hs.2
  rw [h8] at he
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem mulA_rv {S : Modulus} (hS : WideOk S) (h8 : S.k = 8) (s : State) (hs : (alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa (mulFnA S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain hf : FastSpec S.k (fast S.m) (fun _ B => B < S.m)
      (fun A B r => r < S.m ∧ r * 2 ^ (64 * S.k) % S.m = A * B % S.m) := by
    rw [h8]; exact fast_spec (h8 ▸ hS.lt) hS.inv
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv hS.k7 hS.k30 @hf hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, v1, v2, k⟩

end VG.Proof.Weierstrass.RISCV64.Wide8
