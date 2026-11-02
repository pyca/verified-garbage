module

-- separate module: its proofs (about 8 s) build in parallel with the code's literal, which its importer's
-- constant time evaluates
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Mersenne
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words

/-!
# Montgomery's multiplication modulo P-521's prime by its Mersenne form, on RISC-V: the proofs

`mulCore` (`Impl/Weierstrass/RISCV64/P521Mersenne.lean`) meets GenWide's
specification of a multiplication (`GenWide.CoreSpec`) for `p = 2⁵²¹ - 1`
and `R = 2⁵⁷⁶` (`mulCore_spec`), so that GenWide's entry and copies make it
the function of the contract by register (`mul_rv`):

* the rows of the product, each GenWide's multiply-accumulate step at the
  row's words (`row_ok`, a row of GenWide's `row_ok` at any offset);
* the folds, the correction and the rotation, word by word.
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1200

namespace VG.Proof.Weierstrass.RISCV64.P521Mersenne

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Mersenne
open VG.Impl.Weierstrass.RISCV64.GenWide (T macStep adcCore)
open VG.Proof.Weierstrass.RISCV64.GenWide (clobS colsV_congr ctx_of mac_ok colsV_add' colsV_mul)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## A row at any offset -/

/-- After `j` steps of a row at the offset `u` from `s0`. -/
structure RowInv (b X : Addr) (u : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 u, 8 * j⟩] s0.mem s.mem
  val : colsV (fun i => dw s.mem b (u + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem b (u + 8 * i) + dw s0.mem X (8 * i) * (s0.gpr .a4).toNat) j +
      (s0.gpr .a5).toNat

/-- What a row needs of its operands. -/
structure RowOk (b X : Addr) (u n : Nat) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  hx : s0.gpr .t4 = X
  xal : X.toNat % 8 = 0
  xin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (8 * i)) 8
  xdis : ∀ i < n, ∀ j ≤ n, Region.Disjoint ⟨X + BitVec.ofNat 64 (8 * i), 8⟩ ⟨b + BitVec.ofNat 64 u, 8 * j⟩
  top : u + 8 * n ≤ 2048
  u8 : u % 8 = 0
  n2 : 8 * n < 2048

set_option linter.unusedSimpArgs false in
/-- Step `j` of a row. -/
theorem rowStep_ok {b X : Addr} {u n : Nat} {s0 : State} (hR : RowOk b X u n s0)
    {j : Nat} (hj : j < n) {s : State} (h : RowInv b X u s0 j s) :
    WP isa (.block (macStep .t4 (8 * j) (u + 8 * j) (u + 8 * j))) s (RowInv b X u s0 (j + 1)) := by
  have hc : Ctx b s := ctx_of hR.ctx (h.gpr _ (by decide)) h.wr
  have hT := hR.top
  have ht8 := hR.u8
  have hb := hR.nowrap
  have hn2 := hR.n2
  unfold macStep
  refine wp_ld (by omega) (by rw [h.gpr _ (by decide), hR.hx]) (al8 hR.xal (by omega))
    (by rw [h.rd, h.wr]; exact hR.xin j hj) fun s1 u1 => ?_
  refine ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 => ?_
  show WP isa (.block ([.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
    .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3] ++
    [Instr.store .d .t0 .a3 (u + 8 * j)])) s2 _
  refine WP.block_append (WP.mono mac_ok fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hc (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have m3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have g3 : ∀ r, r ∉ clobS → s3.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1]
  have a6 : s2.gpr .a6 = s.mem.readW (X + BitVec.ofNat 64 (8 * j)) 64 := by
    rw [u2.other _ (by decide), u1.gpr]
  have a7 : s2.gpr .a7 = s.mem.readW (b + BitVec.ofNat 64 (u + 8 * j)) 64 := by
    rw [u2.gpr, u1.mem]
  have a4 : s2.gpr .a4 = s.gpr .a4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (u + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, m3]
  have hX0 : dw s.mem X (8 * j) = dw s0.mem X (8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hR.xdis j hj j (by omega)
  have hT0 : dw s.mem b (u + 8 * j) = dw s0.mem b (u + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  refine ⟨fun r hr => by rw [u4.gpr, g3 r hr, h.gpr r hr], by rw [u4.rd, k3.2.2.1, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, k3.2.2.2.1, u2.wr, u1.wr, h.wr], by rw [u4.sp, k3.2.2.2.2, u2.sp, u1.sp, h.sp], ?_, ?_⟩
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s4.mem b (u + 8 * i)) j = colsV (fun i => dw s.mem b (u + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have e3' : (s3.gpr .t0).toNat + 2 ^ 64 * (s3.gpr .a5).toNat =
        dw s0.mem X (8 * j) * (s0.gpr .a4).toNat + dw s0.mem b (u + 8 * j) + (s.gpr .a5).toNat := by
      rw [e3, a6, a7, a4, a5, ← hX0, ← hT0, h.gpr _ (by decide)]; rfl
    show colsV (fun i => dw s4.mem b (u + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (u + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      colsV (fun i => dw s0.mem b (u + 8 * i) + dw s0.mem X (8 * i) * (s0.gpr .a4).toNat) j +
        (2 ^ 64) ^ j * (dw s0.mem b (u + 8 * j) + dw s0.mem X (8 * j) * (s0.gpr .a4).toNat) +
        (s0.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun i => dw s.mem b (u + 8 * i)) j = C at *
    have key : E * (s3.gpr .t0).toNat + E * 2 ^ 64 * (s3.gpr .a5).toNat =
        E * (s.gpr .a5).toNat + E * (dw s0.mem b (u + 8 * j) + dw s0.mem X (8 * j) * (s0.gpr .a4).toNat) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e3']; congr 1; omega
    omega

/-- The row. -/
theorem row_ok {b X : Addr} {u n : Nat} {s0 : State} (hR : RowOk b X u n s0) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap fun i => macStep .t4 (8 * i) (u + 8 * i) (u + 8 * i))) s0
      (RowInv b X u s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (row_ok hR j (by omega)) fun s h => rowStep_ok hR (j := j) (by omega) h)

/-! ## The product -/

/-- The own working space GenWide's operations may write. -/
abbrev own (b : Addr) : Region := ⟨b + BitVec.ofNat 64 P, 160⟩

theorem P_eq : P = 1472 := rfl

/-- What the product needs. -/
structure PCtx (b A B : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  bb : s.gpr .t5 = B
  aal : A.toNat % 8 = 0
  bal : B.toNat % 8 = 0
  ain : ∀ i < 9, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  bin : ∀ i < 9, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < 9, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (own b)
  bdis : ∀ i < 9, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (own b)

theorem PCtx.of {b A B : Addr} {s s' : State} (h : PCtx b A B s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (h4 : s'.gpr .t4 = s.gpr .t4) (h5 : s'.gpr .t5 = s.gpr .t5) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    PCtx b A B s' :=
  ⟨ctx_of h.ctx h3 hwr, h.nowrap, h4.trans h.a, h5.trans h.bb, h.aal, h.bal, by rw [hrd, hwr]; exact h.ain,
    by rw [hrd, hwr]; exact h.bin, h.adis, h.bdis⟩

/-- A part of the own working space within it. -/
theorem own_sub {b : Addr} {d n : Nat} (hd : P ≤ d) (hn : d + n ≤ P + 160) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (own b) :=
  Offset.sub b hd hn

/-- The `n` words of the product from word `i`. -/
abbrev pw (m : Mem) (b : Addr) (i n : Nat) : Nat := colsV (fun j => dw m b (P + 8 * i + 8 * j)) n

theorem colsV_split (f : Nat → Nat) (i : Nat) : ∀ n, colsV f (i + n) = colsV f i + (2 ^ 64) ^ i * colsV (fun j => f (i + j)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    rw [← Nat.add_assoc, colsV, colsV_split f i n, colsV, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]; omega

/-- Row `i`: the ten words from word `i` become the nine before plus `a bᵢ`. -/
theorem prodRow_ok {b A B : Addr} {i : Nat} {s : State} (h : PCtx b A B s) (hi : i < 9) :
    WP isa (.block (prodRow i)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (P + 8 * i), 80⟩] s.mem s'.mem ∧
      pw s'.mem b i 10 = pw s.mem b i 9 + colsV (fun j => dw s.mem A (8 * j)) 9 * dw s.mem B (8 * i) := by
  have hb := h.nowrap
  have hP := P_eq
  unfold prodRow
  refine wp_ld (by omega) (by rw [h.bb]) (al8 h.bal (by omega)) (h.bin i hi) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  simp only
  have hR : RowOk b A (P + 8 * i) 9 s2 :=
    { ctx := ctx_of h.ctx (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr])
      nowrap := hb
      hx := by rw [u2.other _ (by decide), u1.other _ (by decide), h.a]
      xal := h.aal
      xin := fun j hj => by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact h.ain j hj
      xdis := fun j hj n hn => GenWide.disj_sub (h.adis j hj) (own_sub (by omega) (by omega))
      top := by omega
      u8 := by omega
      n2 := by omega }
  refine WP.block_append (WP.mono (row_ok hR 9 (Nat.le_refl _)) fun s3 h3 => ?_)
  have hc3 : Ctx b s3 := ctx_of hR.ctx (h3.gpr _ (by decide)) h3.wr
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hm4 : s4.mem = s3.mem.writeW (b + BitVec.ofNat 64 (P + 8 * i + 8 * 9)) (s3.gpr .a5) := u4.mem
  refine ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u4.gpr, h3.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
        u2.other r hr.2.2.2.2.1, u1.other r hr.1],
    by rw [u4.rd, h3.rd, u2.rd, u1.rd], by rw [u4.wr, h3.wr, u2.wr, u1.wr], by rw [u4.sp, h3.sp, u2.sp, u1.sp],
    ?_, ?_⟩
  · rw [hm4, ← m2]
    refine (h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h3.val
    have hlow : colsV (fun j => dw s4.mem b (P + 8 * i + 8 * j)) 9 = colsV (fun j => dw s3.mem b (P + 8 * i + 8 * j)) 9 :=
      colsV_congr fun j hj => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have htop : dw s4.mem b (P + 8 * i + 8 * 9) = (s3.gpr .a5).toNat := by rw [hm4, dw_write_self]
    have hrow : colsV (fun j => dw s2.mem b (P + 8 * i + 8 * j) + dw s2.mem A (8 * j) * (s2.gpr .a4).toNat) 9 =
        pw s.mem b i 9 + colsV (fun j => dw s.mem A (8 * j)) 9 * dw s.mem B (8 * i) := by
      rw [colsV_add', colsV_mul, m2, u2.other _ (by decide), u1.gpr]; rfl
    have a50 : (s2.gpr .a5).toNat = 0 := by rw [u2.gpr]; rfl
    rw [hrow, a50, Nat.add_zero] at hv
    show colsV (fun j => dw s4.mem b (P + 8 * i + 8 * j)) 9 + (2 ^ 64) ^ 9 * dw s4.mem b (P + 8 * i + 8 * 9) = _
    rw [hlow, htop]; exact hv

/-- After `i` rows: `T`'s `i + 9` words are `a (b mod 2^(64 i))`. -/
structure RowsInv (b A B : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ .a4 :: clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * 18⟩] s0.mem s.mem
  val : pw s.mem b 0 (i + 9) = colsV (fun j => dw s0.mem A (8 * j)) 9 * colsV (fun j => dw s0.mem B (8 * j)) i

theorem rows_ok {b A B : Addr} {s0 : State} (h : PCtx b A B s0) (hz : ∀ j < 9, dw s0.mem b (P + 8 * j) = 0) :
    ∀ i ≤ 9, WP isa (.block ((List.range i).flatMap prodRow)) s0 (RowsInv b A B s0 i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by
      show colsV _ 9 = _ * 0
      rw [Nat.mul_zero]
      exact (colsV_congr (g := fun _ => 0) fun j hj => by simp only [Nat.add_zero]; exact hz j hj).trans
        (by simp [colsV])⟩
  | i + 1, hi => by
    have hP := P_eq
    have hb := h.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (rows_ok h hz i (by omega)) fun s hs => ?_)
    have hc : PCtx b A B s := h.of (hs.gpr _ (by decide)) (hs.gpr _ (by decide)) (hs.gpr _ (by decide)) hs.rd hs.wr
    refine WP.mono (prodRow_ok hc (by omega)) fun s' ⟨g, rd, wr, sp, f, v⟩ => ?_
    have hA : ∀ j < 9, dw s.mem A (8 * j) = dw s0.mem A (8 * j) := fun j hj =>
      dw_frame hs.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact GenWide.disj_sub (h.adis j hj) (own_sub (by omega) (by omega))
    have hB : dw s.mem B (8 * i) = dw s0.mem B (8 * i) :=
      dw_frame hs.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact GenWide.disj_sub (h.bdis i (by omega)) (own_sub (by omega) (by omega))
    refine ⟨fun r hr => (g r hr).trans (hs.gpr r hr), rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
    · exact hs.frame.trans (f.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega) (by omega)⟩)
    · have hlo : colsV (fun j => dw s'.mem b (P + 8 * 0 + 8 * j)) i = colsV (fun j => dw s.mem b (P + 8 * 0 + 8 * j)) i :=
        colsV_congr fun j hj => dw_frame f fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)
      have e1 := colsV_split (fun j => dw s'.mem b (P + 8 * 0 + 8 * j)) i 10
      have e0 := colsV_split (fun j => dw s.mem b (P + 8 * 0 + 8 * j)) i 9
      have hv := hs.val
      have hpw : ∀ (m : Mem) (n : Nat), colsV (fun j => dw m b (P + 8 * 0 + 8 * (i + j))) n = pw m b i n :=
        fun m n => colsV_congr fun j _ => by congr 1; omega
      rw [hpw] at e1 e0
      rw [colsV_congr (g := fun j => dw s0.mem A (8 * j)) hA, hB] at v
      show colsV (fun j => dw s'.mem b (P + 8 * 0 + 8 * j)) (i + 1 + 9) = _
      rw [show i + 1 + 9 = i + 10 by omega, e1, hlo, v, Nat.mul_add, ← Nat.add_assoc, ← e0]
      change colsV (fun j => dw s.mem b (P + 8 * 0 + 8 * j)) (i + 9) + _ = _ 
      rw [show colsV (fun j => dw s.mem b (P + 8 * 0 + 8 * j)) (i + 9) = _ from hv]
      show _ = colsV (fun j => dw s0.mem A (8 * j)) 9 * (colsV (fun j => dw s0.mem B (8 * j)) i +
        (2 ^ 64) ^ i * dw s0.mem B (8 * i))
      rw [Nat.mul_add]
      generalize colsV (fun j => dw s0.mem A (8 * j)) 9 = a
      rw [Nat.mul_left_comm]

/-! ## Bits of words -/

theorem wp_srl {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

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

/-- `x &&& 511` is `x mod 2^9`. -/
theorem and511 (x : BitVec 64) : (x &&& BitVec.ofInt 64 0x1ff).toNat = x.toNat % 2 ^ 9 := by
  rw [show BitVec.ofInt 64 0x1ff = BitVec.ofNat 64 (2 ^ 9 - 1) from rfl, BitVec.toNat_and,
    BitVec.toNat_ofNat, show (2 ^ 9 - 1) % 2 ^ 64 = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The words of a number shifted right by `s` bits: `2^s` times their
number, plus the low bits, is the number plus the low bits of the next word. -/
theorem shr_cols (w : Nat → Nat) {s : Nat} (hs : s ≤ 64) : ∀ n,
    2 ^ s * colsV (fun i => w i / 2 ^ s + w (i + 1) % 2 ^ s * 2 ^ (64 - s)) n + w 0 % 2 ^ s =
      colsV w n + (2 ^ 64) ^ n * (w n % 2 ^ s)
  | 0 => by simp [colsV]
  | n + 1 => by
    have ih := shr_cols w hs n
    have e : (2 : Nat) ^ s * 2 ^ (64 - s) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
    simp only [colsV]
    have h1 := Nat.div_add_mod (w n) (2 ^ s)
    rw [show (2 ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ n = E at *
    generalize w n / 2 ^ s = A at *
    generalize w (n + 1) % 2 ^ s = Bq
    generalize hS : 2 ^ s = S at *
    generalize 2 ^ (64 - s) = U at *
    have h3 : S * (E * (A + Bq * U)) = E * (S * A) + E * (S * U) * Bq := by
      rw [Nat.mul_add E, Nat.mul_add S]; ac_rfl
    rw [e] at h3
    have h2 : E * (S * A) + E * (w n % S) = E * w n := by rw [← Nat.mul_add, h1]
    rw [Nat.mul_add, h3]
    omega

/-! ## Carries through the words -/

/-- After `j` steps of `+ a5` from `s0`. -/
structure CarryInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a5] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * j⟩] s0.mem s.mem
  cy : 0 < j → (s.gpr .a5).toNat ≤ 1
  val : pw s.mem b 0 j + (2 ^ 64) ^ j * (s.gpr .a5).toNat = pw s0.mem b 0 j + (s0.gpr .a5).toNat

set_option linter.unusedSimpArgs false in
theorem carryStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 9) {s : State}
    (h : CarryInv b s0 j s) : WP isa (.block (carryStep j)) s (CarryInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  have hal := hc.al
  unfold carryStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ctx_of hcs (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [u3.wr, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have t0 : s3.gpr .t0 = s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 := by
    rw [u3.other _ (by decide), u2.gpr, u1.gpr, u1.other _ (by decide)]
  have a5 : s3.gpr .a5 = if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5 then 1 else 0 := by
    rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have e := carry (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64) (s.gpr .a5)
  have hw0 : dw s.mem b (P + 8 * j) = dw s0.mem b (P + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd], by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr],
    by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_, fun _ => by rw [u4.gpr, a5]; exact carry_le _, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.gpr, u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.1, h.gpr r (by simp [hr.1, hr.2])]
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : pw s4.mem b 0 j = pw s.mem b 0 j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    show pw s4.mem b 0 j + (2 ^ 64) ^ j * dw s4.mem b (P + 8 * 0 + 8 * j) + (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      pw s0.mem b 0 j + (2 ^ 64) ^ j * dw s0.mem b (P + 8 * 0 + 8 * j) + (s0.gpr .a5).toNat
    rw [hcw, show P + 8 * 0 + 8 * j = P + 8 * j by omega, hm4, dw_write_self, u4.gpr, t0, a5, ← hw0,
      show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5).toNat +
        E * 2 ^ 64 * (if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5
          then (1 : BitVec 64) else 0).toNat =
        E * dw s.mem b (P + 8 * j) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, e, Nat.mul_add]; rfl
    omega

theorem carry_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ j ≤ 9, WP isa (.block ((List.range j).flatMap carryStep)) s0 (CarryInv b s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun h => absurd h (Nat.lt_irrefl _),
      by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (carry_ok hc j (by omega)) fun s h => carryStep_ok hc (by omega) h)

/-! ## The first fold -/

/-- Word `j` of `T >> 521` into `a7`. -/
theorem hiWord_ok {b : Addr} {s : State} (hc : Ctx b s) {j : Nat} (hj : j ≤ 8) :
    WP isa (.block (hiWord j)) s fun s' =>
      (s'.gpr .a7).toNat = dw s.mem b (P + 8 * (8 + j)) / 2 ^ 9 + dw s.mem b (P + 8 * (9 + j)) % 2 ^ 9 * 2 ^ 55 ∧
      (∀ r, r ∉ [Reg.t0, .a7] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have hP := P_eq
  unfold hiWord
  refine ld_ok hc (by omega) (by omega) fun s1 u1 =>
    ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_srl (by decide) fun s3 u3 => wp_sll (by decide) fun s4 u4 => wp_or fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u5.gpr, u4.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u2.gpr, u1.mem, shr_or_shl _ _ (by decide : 9 + 55 = 64)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.other _ hr.2, u4.other _ hr.1, u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.2]

/-- The registers the fold writes. -/
abbrev clobF : List Reg := [.t0, .t3, .a5, .a6, .a7]

/-- Word `i` of `T >> 521`, from the words of `T` at `s0`. -/
abbrev hw (m : Mem) (b : Addr) (i : Nat) : Nat :=
  dw m b (P + 8 * (8 + i)) / 2 ^ 9 + dw m b (P + 8 * (9 + i)) % 2 ^ 9 * 2 ^ 55

/-- Word `i` of `T mod 2⁵²¹`. -/
abbrev lw (m : Mem) (b : Addr) (i : Nat) : Nat :=
  if i < 8 then dw m b (P + 8 * i) else dw m b (P + 8 * i) % 2 ^ 9

/-- After `j` words of the fold from `s0`. -/
structure FoldInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobF → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 P, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : pw s.mem b 0 j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => lw s0.mem b i + hw s0.mem b i) j + (s0.gpr .a5).toNat


set_option linter.unusedSimpArgs false in
/-- The end of a word of the fold: `a6 + a7 + a5`, for `a6` the low word and
`a7` `T >> 521`'s, into word `j`. -/
theorem foldTail_ok {b : Addr} {s0 s : State} (hc : Ctx b s0) {j : Nat} (hj : j ≤ 8) (h : FoldInv b s0 j s)
    {s1 : State} (m1 : s1.mem = s.mem) (rd1 : s1.rd = s.rd) (wr1 : s1.wr = s.wr) (sp1 : s1.sp = s.sp)
    (g1 : ∀ r, r ∉ [Reg.t0, .a6, .a7] → s1.gpr r = s.gpr r)
    (a6 : (s1.gpr .a6).toNat = lw s0.mem b j) (a7 : (s1.gpr .a7).toNat = hw s0.mem b j) :
    WP isa (.block (adcCore ++ ([.store .d .t0 .a3 (P + 8 * j)] : List Instr))) s1 (FoldInv b s0 (j + 1)) := by
  have hP := P_eq
  have hal := hc.al
  have hc1 : Ctx b s1 := ctx_of hc (by rw [g1 _ (by decide), h.gpr _ (by decide)]) (by rw [wr1, h.wr])
  refine WP.block_append (WP.mono (adc_ok (d := .t0) (x := .a6) (y := .a7) (c := .a5) (u := .t3))
    fun s4 ⟨e4, k4⟩ => ?_)
  have hc4 : Ctx b s4 := ctx_of hc1 (k4.1 _ (by decide)) k4.2.2.2.1
  refine sd_ok hc4 (by omega) (by omega) fun s5 u5 => WP.block_nil ?_
  have a5 : s1.gpr .a5 = s.gpr .a5 := g1 _ (by decide)
  have e4v := e4 (by rw [a5]; exact h.cy)
  have hm5 : s5.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 8 * j)) (s4.gpr .t0) := by
    rw [u5.mem, k4.2.1, m1]
  refine ⟨fun r hr => ?_, by rw [u5.rd, k4.2.2.1, rd1, h.rd], by rw [u5.wr, k4.2.2.2.1, wr1, h.wr],
    by rw [u5.sp, k4.2.2.2.2, sp1, h.sp], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.gpr, k4.1 r (by simp [hr.1, hr.2.1, hr.2.2.1]), g1 r (by simp [hr.1, hr.2.2.2.1, hr.2.2.2.2]),
      h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · rw [u5.gpr]
    have := (s1.gpr .a6).isLt; have := (s1.gpr .a7).isLt; have := h.cy
    rw [← a5] at this
    omega
  · have hv := h.val
    have hcw : pw s5.mem b 0 j = pw s.mem b 0 j :=
      colsV_congr fun i hi => by rw [hm5, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a6, a7, a5] at e4v
    show pw s5.mem b 0 j + (2 ^ 64) ^ j * dw s5.mem b (P + 8 * 0 + 8 * j) + (2 ^ 64) ^ (j + 1) * (s5.gpr .a5).toNat =
      colsV (fun i => lw s0.mem b i + hw s0.mem b i) j + (2 ^ 64) ^ j * (lw s0.mem b j + hw s0.mem b j) +
        (s0.gpr .a5).toNat
    rw [hcw, show P + 8 * 0 + 8 * j = P + 8 * j by omega, hm5, dw_write_self, u5.gpr,
      show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s4.gpr .t0).toNat + E * 2 ^ 64 * (s4.gpr .a5).toNat =
        E * (lw s0.mem b j + hw s0.mem b j) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, e4v, Nat.mul_add]
    omega

theorem fold_word {b : Addr} {s0 s : State} {j i : Nat} (h : FoldInv b s0 j s) (hj : j ≤ i) (hi : i ≤ 17) :
    dw s.mem b (P + 8 * i) = dw s0.mem b (P + 8 * i) := by
  have hP := P_eq
  exact dw_frame h.frame fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)

/-- Word `j < 8` of the fold. -/
theorem foldStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 8) {s : State}
    (h : FoldInv b s0 j s) : WP isa (.block (foldStep j)) s (FoldInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold foldStep
  rw [List.append_assoc, List.append_assoc, List.singleton_append]
  refine WP.block_append (WP.mono (hiWord_ok hcs (j := j) (by omega)) fun s1 ⟨a7, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine ld_ok (ctx_of hcs (g1 _ (by decide)) wr1) (by omega) (by omega) fun s2 u2 => ?_
  refine foldTail_ok hc (by omega) h (by rw [u2.mem, m1]) (by rw [u2.rd, rd1]) (by rw [u2.wr, wr1])
    (by rw [u2.sp, sp1]) (fun r hr => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other _ hr.2.1, g1 r (by simp [hr.1, hr.2.2])]
  · rw [u2.gpr, m1, show lw s0.mem b j = dw s0.mem b (P + 8 * j) from ite_eq_left hj, ← fold_word h (Nat.le_refl _) (by omega)]
    rfl
  · rw [u2.other _ (by decide), a7, fold_word h (by omega) (by omega), fold_word h (by omega) (by omega)]

/-- Word 8 of the fold. -/
theorem foldTop_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {s : State}
    (h : FoldInv b s0 8 s) : WP isa (.block foldTop) s (FoldInv b s0 9) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold foldTop
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.singleton_append]
  refine WP.block_append (WP.mono (hiWord_ok hcs (j := 8) (by omega)) fun s1 ⟨a7, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine ld_ok (ctx_of hcs (g1 _ (by decide)) wr1) (by omega) (by omega) fun s2 u2 => wp_andi (by decide) fun s3 u3 => ?_
  refine foldTail_ok hc (by omega) h (by rw [u3.mem, u2.mem, m1]) (by rw [u3.rd, u2.rd, rd1])
    (by rw [u3.wr, u2.wr, wr1]) (by rw [u3.sp, u2.sp, sp1]) (fun r hr => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2.1, u2.other _ hr.2.1, g1 r (by simp [hr.1, hr.2.2])]
  · rw [u3.gpr, and511, u2.gpr, m1, show lw s0.mem b 8 = dw s0.mem b (P + 8 * 8) % 2 ^ 9 from ite_eq_right (by omega),
      ← fold_word h (Nat.le_refl _) (by omega)]
    rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), a7, fold_word h (by omega) (by omega),
      fold_word h (by omega) (by omega)]

/-- The fold: `s`'s nine words and its carry. -/
theorem fold_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    WP isa (.block fold) s0 fun s => (∀ r, r ∉ clobF → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧
      s.sp = s0.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s0.mem s.mem ∧ (s.gpr .a5).toNat ≤ 1 ∧
      pw s.mem b 0 9 + 2 ^ 576 * (s.gpr .a5).toNat = colsV (fun i => lw s0.mem b i + hw s0.mem b i) 9 := by
  unfold fold
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  have steps : ∀ j ≤ 8, WP isa (.block ((List.range j).flatMap foldStep)) s1 (FoldInv b s1 j) := fun j hj => by
    induction j with
    | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by rw [u1.gpr]; decide, by simp [colsV]⟩
    | succ j ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact WP.block_append (WP.mono (ih (by omega)) fun s h => foldStep_ok hc1 (by omega) h)
  refine WP.block_append (WP.mono (steps 8 (Nat.le_refl _)) fun s h => ?_)
  refine WP.mono (foldTop_ok hc1 h) fun s' h' => ?_
  have a50 : (s1.gpr .a5).toNat = 0 := by rw [u1.gpr]; rfl
  have m1 : s1.mem = s0.mem := u1.mem
  refine ⟨fun r hr => by
      rw [h'.gpr r hr, u1.other r (fun e => hr (by rw [e]; decide))],
    by rw [h'.rd, u1.rd], by rw [h'.wr, u1.wr], by rw [h'.sp, u1.sp], by rw [← m1]; exact h'.frame, h'.cy, ?_⟩
  have hv := h'.val
  rw [a50, Nat.add_zero, m1] at hv
  exact hv

/-! ## The second fold -/

/-- `(s₈ >> 9) | (c << 55)` into `a5`, `s₈` cut to its nine bits, then the
carries: the nine words become `s mod 2⁵²¹ + s >> 521`. -/
theorem fold2_ok {b : Addr} {s : State} (hc : Ctx b s) (hc5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block fold2) s fun s' => (∀ r, r ∉ [Reg.t0, .a5, .a6] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s.mem s'.mem ∧
      pw s'.mem b 0 9 + 2 ^ 576 * (s'.gpr .a5).toNat =
        pw s.mem b 0 8 + 2 ^ 512 * (dw s.mem b (P + 64) % 2 ^ 9) + (dw s.mem b (P + 64) / 2 ^ 9 +
          (s.gpr .a5).toNat * 2 ^ 55) := by
  have hP := P_eq
  have hal := hc.al
  unfold fold2
  rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 =>
    wp_or fun s4 u4 => wp_andi (by decide) fun s5 u5 => ?_
  have hc5' : Ctx b s5 := ctx_of hc (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine sd_ok hc5' (by omega) (by omega) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := ctx_of hc5' (by rw [u6.gpr]) u6.wr
  have x8 : (s.mem.readW (b + BitVec.ofNat 64 (P + 64)) 64).toNat = dw s.mem b (P + 64) := rfl
  have a5v : (s6.gpr .a5).toNat = dw s.mem b (P + 64) / 2 ^ 9 + (s.gpr .a5).toNat * 2 ^ 55 := by
    rw [u6.gpr, u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, u2.other _ (by decide),
      u1.gpr, u1.other _ (by decide), BitVec.or_comm, shr_or_shl _ _ (by decide : 9 + 55 = 64), x8,
      Nat.mod_eq_of_lt (by omega : (s.gpr .a5).toNat < 2 ^ 9)]
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (P + 64)) (s5.gpr .t0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have t05 : (s5.gpr .t0).toNat = dw s.mem b (P + 64) % 2 ^ 9 := by
    rw [u5.gpr, and511, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  refine WP.mono (carry_ok hc6 9 (Nat.le_refl _))
    fun s' h' => ⟨fun r hr => ?_, by rw [h'.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
      by rw [h'.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [h'.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp],
      ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h'.gpr r (by simp [hr.1, hr.2.1]), u6.gpr, u5.other _ hr.1, u4.other _ hr.2.1, u3.other _ hr.2.1,
      u2.other _ hr.2.2, u1.other _ hr.1]
  · have f := h'.frame
    rw [hm6] at f
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))).trans f
  · have hv := h'.val
    rw [a5v] at hv
    rw [hv]
    have hlow : pw s6.mem b 0 8 = pw s.mem b 0 8 :=
      colsV_congr fun i hi => by rw [hm6, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have htop : dw s6.mem b (P + 8 * 0 + 8 * 8) = dw s.mem b (P + 64) % 2 ^ 9 := by
      rw [hm6, show P + 8 * 0 + 8 * 8 = P + 64 by omega, dw_write_self, t05]
    show pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 0 + 8 * 8) + _ = _
    rw [hlow, htop]

/-! ## The correction -/

theorem pw_lt (m : Mem) (b : Addr) (n : Nat) : pw m b 0 n < (2 ^ 64) ^ n :=
  GenWide.colsV_lt _ (fun _ => dw_lt _ _ _) n

/-- After `j` words of the carry of `+ a5` from `s0`, not stored. -/
structure ProbeInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a5] → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  val : (s.gpr .a5).toNat = (pw s0.mem b 0 j + (s0.gpr .a5).toNat) / (2 ^ 64) ^ j

theorem probeStep_ok {b : Addr} {s0 : State} (hc : Ctx b s0) {j : Nat} (hj : j < 9) {s : State}
    (h : ProbeInv b s0 j s) : WP isa (.block (probeStep j)) s (ProbeInv b s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  unfold probeStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => wp_add fun s2 u2 => wp_sltu fun s3 u3 => WP.block_nil ?_
  have e := carry (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64) (s.gpr .a5)
  refine ⟨fun r hr => ?_, by rw [u3.mem, u2.mem, u1.mem, h.mem], by rw [u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u3.wr, u2.wr, u1.wr, h.wr], by rw [u3.sp, u2.sp, u1.sp, h.sp], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2, u2.other _ hr.1, u1.other _ hr.1, h.gpr r (by simp [hr.1, hr.2])]
  · rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide)]
    have hv := h.val
    have hw : (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64).toNat = dw s0.mem b (P + 8 * 0 + 8 * j) := by
      rw [h.mem, show P + 8 * 0 + 8 * j = P + 8 * j by omega]; rfl
    rw [hw] at e
    have hlt := (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5).isLt
    generalize (if s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5 < s.gpr .a5
      then (1 : BitVec 64) else 0) = c at *
    generalize (s.mem.readW (b + BitVec.ofNat 64 (P + 8 * j)) 64 + s.gpr .a5) = t0 at *
    show c.toNat = (pw s0.mem b 0 j + (2 ^ 64) ^ j * dw s0.mem b (P + 8 * 0 + 8 * j) + (s0.gpr .a5).toNat) /
      (2 ^ 64) ^ (j + 1)
    rw [show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ .., ← Nat.div_div_eq_div_mul,
      Nat.add_right_comm, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), ← hv]
    omega

theorem probe_ok {b : Addr} {s0 : State} (hc : Ctx b s0) :
    ∀ j ≤ 9, WP isa (.block ((List.range j).flatMap probeStep)) s0 (ProbeInv b s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (probe_ok hc j (by omega)) fun s h => probeStep_ok hc (by omega) h)

theorem pw_succ (m : Mem) (b : Addr) (n : Nat) :
    pw m b 0 (n + 1) = pw m b 0 n + (2 ^ 64) ^ n * dw m b (P + 8 * n) := by
  show pw m b 0 n + (2 ^ 64) ^ n * dw m b (P + 8 * 0 + 8 * n) = _
  rw [show P + 8 * 0 + 8 * n = P + 8 * n by omega]

/-- `r = (s₂ + q) mod 2⁵²¹`, `q` the bit 521 of `s₂ + 1`. -/
theorem canon_ok {b : Addr} {s : State} (hc : Ctx b s) (hs : pw s.mem b 0 9 < 2 ^ 521 + 2 ^ 56) :
    WP isa (.block canon) s fun s' => (∀ r, r ∉ [Reg.t0, .a5] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 P, 72⟩] s.mem s'.mem ∧
      pw s'.mem b 0 9 = (pw s.mem b 0 9 + (pw s.mem b 0 9 + 1) / 2 ^ 521) % 2 ^ 521 := by
  have hP := P_eq
  have hal := hc.al
  unfold canon
  show WP isa (.block (Instr.li .a5 1 :: ((List.range 8).flatMap probeStep ++
    (Instr.load .d .t0 .a3 (P + 64) :: Instr.add .t0 .t0 .a5 :: Instr.shift .srl .d .a5 .t0 9 ::
      ((List.range 9).flatMap carryStep ++ [Instr.load .d .t0 .a3 (P + 64), .logicImm .and .t0 .t0 0x1ff,
        .store .d .t0 .a3 (P + 64)]))))) s _
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  refine WP.block_append (WP.mono (probe_ok hc1 8 (by omega)) fun s2 h2 => ?_)
  have hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by decide)) h2.wr
  refine ld_ok hc2 (by omega) (by omega) fun s3 u3 => wp_add fun s4 u4 => wp_srl (by decide) fun s5 u5 => ?_
  have hc5 : Ctx b s5 := ctx_of hc2 (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide)])
    (by rw [u5.wr, u4.wr, u3.wr])
  refine WP.block_append (WP.mono (carry_ok hc5 9 (Nat.le_refl _)) fun s6 h6 => ?_)
  have hc6 : Ctx b s6 := ctx_of hc5 (h6.gpr _ (by decide)) h6.wr
  refine ld_ok hc6 (by omega) (by omega) fun s7 u7 => wp_andi (by decide) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := ctx_of hc6 (by rw [u8.other _ (by decide), u7.other _ (by decide)]) (by rw [u8.wr, u7.wr])
  refine sd_ok hc8 (by omega) (by omega) fun s9 u9 => WP.block_nil ?_
  -- Memory.
  have m1 : s1.mem = s.mem := u1.mem
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, h2.mem, m1]
  have m8 : s8.mem = s6.mem := by rw [u8.mem, u7.mem]
  have hm9 : s9.mem = s6.mem.writeW (b + BitVec.ofNat 64 (P + 64)) (s8.gpr .t0) := by rw [u9.mem, m8]
  -- The values.
  generalize hS : pw s.mem b 0 9 = S at hs ⊢
  have hS8 : pw s.mem b 0 9 = pw s.mem b 0 8 + (2 ^ 64) ^ 8 * dw s.mem b (P + 8 * 8) := pw_succ s.mem b 8
  rw [hS] at hS8
  have h8lt := pw_lt s.mem b 8
  have hw8 : dw s.mem b (P + 8 * 8) < 2 ^ 10 := by omega
  have c8 : (s2.gpr .a5).toNat = (pw s.mem b 0 8 + 1) / 2 ^ 512 := by
    rw [h2.val, m1, u1.gpr]; rfl
  have c8le : (s2.gpr .a5).toNat ≤ 1 := by rw [c8]; omega
  have hq : (s5.gpr .a5).toNat = (S + 1) / 2 ^ 521 := by
    rw [u5.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, u4.gpr, u3.gpr,
      u3.other _ (by decide : Reg.a5 ≠ Reg.t0), BitVec.toNat_add, h2.mem, m1, c8]
    show ((dw s.mem b (P + 8 * 8)) + (pw s.mem b 0 8 + 1) / 2 ^ 512) % 2 ^ 64 / 2 ^ 9 = _
    rw [Nat.mod_eq_of_lt (by omega), hS8, Nat.add_right_comm, show (2 : Nat) ^ 521 = 2 ^ 512 * 2 ^ 9 by decide,
      ← Nat.div_div_eq_div_mul, show (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 by decide,
      Nat.add_mul_div_left _ _ (by decide), Nat.add_comm]
  have v6 := h6.val
  rw [m5, hS, hq] at v6
  have h6lt := pw_lt s6.mem b 9
  have hq1 : (S + 1) / 2 ^ 521 ≤ 1 := by omega
  have c6 : (s6.gpr .a5).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (s6.gpr .a5).toNat with h | h
    · exact h
    · exfalso; have : (2 : Nat) ^ 576 = (2 ^ 64) ^ 9 := by decide
      omega
  rw [c6, Nat.mul_zero, Nat.add_zero] at v6
  have t08 : (s8.gpr .t0).toNat = dw s6.mem b (P + 64) % 2 ^ 9 := by
    rw [u8.gpr, and511, u7.gpr]; rfl
  have h68 : pw s6.mem b 0 9 = pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 8) := pw_succ s6.mem b 8
  have h6lt8 := pw_lt s6.mem b 8
  have hlow : pw s9.mem b 0 8 = pw s6.mem b 0 8 :=
    colsV_congr fun i hi => by rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
  have h98 : pw s9.mem b 0 9 = pw s9.mem b 0 8 + (2 ^ 64) ^ 8 * dw s9.mem b (P + 8 * 8) := pw_succ s9.mem b 8
  have d9 : dw s9.mem b (P + 8 * 8) = dw s6.mem b (P + 64) % 2 ^ 9 := by
    rw [hm9, show P + 8 * 8 = P + 64 from rfl, dw_write_self, t08]
  rw [hlow, d9] at h98
  rw [show P + 8 * 8 = P + 64 from rfl] at h68
  refine ⟨fun r hr => ?_, by rw [u9.rd, u8.rd, u7.rd, h6.rd, u5.rd, u4.rd, u3.rd, h2.rd, u1.rd],
    by rw [u9.wr, u8.wr, u7.wr, h6.wr, u5.wr, u4.wr, u3.wr, h2.wr, u1.wr],
    by rw [u9.sp, u8.sp, u7.sp, h6.sp, u5.sp, u4.sp, u3.sp, h2.sp, u1.sp], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u9.gpr, u8.other _ hr.1, u7.other _ hr.1, h6.gpr r (by simp [hr.1, hr.2]), u5.other _ hr.2,
      u4.other _ hr.1, u3.other _ hr.1, h2.gpr r (by simp [hr.1, hr.2]), u1.other _ hr.2]
  · have f := h6.frame
    rw [m5] at f
    rw [hm9]
    exact f.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  · rw [h98]
    have : (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 := by decide
    rw [this] at h68 ⊢
    omega

/-! ## The rotation -/

/-- `x | (y << 18)` for `x < 2^18`. -/
theorem or_shl18 (x y : BitVec 64) (hx : x.toNat < 2 ^ 18) :
    (x ||| (y <<< 18)).toNat = x.toNat + y.toNat % 2 ^ 46 * 2 ^ 18 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ 46 * 2 ^ 18 by decide, Nat.mul_mod_mul_right,
    Nat.mul_comm (y.toNat % 2 ^ 46), Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

/-- What the rotation needs of `[o]`. -/
structure OCtx (b O : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  o : s.gpr .t2 = O
  oal : O.toNat % 8 = 0
  ow : ∀ i < 9, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8
  onw : O.toNat + 72 ≤ 2 ^ 64
  odis : Region.Disjoint ⟨O, 72⟩ (own b)

/-- Word `i` of `r` rotated, for `i < 8`, from `r`'s words. -/
abbrev rw' (m : Mem) (b : Addr) (i : Nat) : Nat :=
  dw m b (P + 8 * i) / 2 ^ 55 + dw m b (P + 8 * (i + 1)) % 2 ^ 55 * 2 ^ 9

/-- After `j` words of the rotation from `s0`. -/
structure RotInv (b O : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.t0, .a6] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = rw' s0.mem b i

theorem own_of_frame {b O : Addr} {s0 : State} (hO : OCtx b O s0) {n : Nat} (hn : n ≤ 72) {m : Mem}
    (f : Frame [⟨O, n⟩] s0.mem m) {d : Nat} (hd : P ≤ d) (hd' : d + 8 ≤ P + 160) : dw m b d = dw s0.mem b d :=
  dw_frame f fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact GenWide.disj_mono (GenWide.disj_symm (GenWide.disj_sub hO.odis (own_sub hd hd'))) hn

theorem own_of_rot {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (hj : j ≤ 9) (h : RotInv b O s0 j s)
    {d : Nat} (hd : P ≤ d) (hd' : d + 8 ≤ P + 160) : dw s.mem b d = dw s0.mem b d :=
  own_of_frame hO (by omega) h.frame hd hd'

/-- `(r_j >> 55) | (r_{j+1} << 9)` into `t0`. -/
theorem rotWord_ok {b : Addr} {s : State} (hc : Ctx b s) {j : Nat} (hj : j < 8) :
    WP isa (.block (rotWord j)) s fun s' =>
      (s'.gpr .t0).toNat = rw' s.mem b j ∧ (∀ r, r ∉ [Reg.t0, .a6] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hP := P_eq
  unfold rotWord
  refine ld_ok hc (by omega) (by omega) fun s1 u1 =>
    ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_srl (by decide) fun s3 u3 => wp_sll (by decide) fun s4 u4 => wp_or fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u5.gpr, u4.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      u2.gpr, u1.mem, shr_or_shl _ _ (by decide : 55 + 9 = 64)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.other _ hr.1, u4.other _ hr.2, u3.other _ hr.1, u2.other _ hr.2, u1.other _ hr.1]

/-- `[o + d] := t0` for a word `d / 8 < 9` of `[o]`. -/
theorem rot_store {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (h : RotInv b O s0 j s)
    {s1 : State} {is : List Instr} {Q : State → Prop} (hj : j < 9)
    (g1 : ∀ r, r ∉ [Reg.t0, .a6] → s1.gpr r = s.gpr r) (wr1 : s1.wr = s.wr)
    (k : ∀ s', Mupd s1 s' (s1.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s1.gpr .t0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d .t0 .t2 (8 * j) :: is)) s1 Q :=
  wp_sd (by omega) (by rw [g1 _ (by decide), h.gpr _ (by decide), hO.o]) (al8 hO.oal (by omega))
    (by rw [wr1, h.wr]; exact hO.ow j hj) k

/-- The frame and the words after a store of word `j`. -/
theorem rot_next {b O : Addr} {s0 s : State} (hO : OCtx b O s0) {j : Nat} (hj : j < 9) (h : RotInv b O s0 j s)
    {s' : State} {v : BitVec 64} (hm : s'.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) v) :
    Frame [⟨O, 8 * (j + 1)⟩] s0.mem s'.mem ∧ (∀ i < j, dw s'.mem O (8 * i) = rw' s0.mem b i) ∧
      dw s'.mem O (8 * j) = v.toNat := by
  have hon := hO.onw
  refine ⟨?_, fun i hi => ?_, by rw [hm, dw_write_self]⟩
  · rw [hm]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 8 * (j + 1)⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 8 * (j + 1)⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i hi

/-- Word `j < 7` of the rotation. -/
theorem rotStep_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) {j : Nat} (hj : j < 7) {s : State}
    (h : RotInv b O s0 j s) : WP isa (.block (rotStep j)) s (RotInv b O s0 (j + 1)) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hO.ctx (h.gpr _ (by decide)) h.wr
  unfold rotStep
  refine WP.block_append (WP.mono (rotWord_ok hcs (j := j) (by omega)) fun s1 ⟨t0, g1, m1, rd1, wr1, sp1⟩ => ?_)
  refine rot_store hO h (by omega) g1 wr1 fun s2 u2 => WP.block_nil ?_
  have hv : (s1.gpr .t0).toNat = rw' s0.mem b j := by
    rw [t0]; show dw s.mem b _ / _ + dw s.mem b _ % _ * _ = _
    rw [own_of_rot hO (by omega) h (by omega) (by omega), own_of_rot hO (by omega) h (by omega) (by omega)]
  obtain ⟨f, v1, v2⟩ := rot_next hO (by omega) h (by rw [u2.mem, m1])
  refine ⟨fun r hr => by rw [u2.gpr, g1 r hr, h.gpr r hr], by rw [u2.rd, rd1, h.rd], by rw [u2.wr, wr1, h.wr],
    by rw [u2.sp, sp1, h.sp], f, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact v1 i hi
  · rw [v2, hv]

/-- The rotation's words 0…6, by induction. -/
theorem rotSteps_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) :
    ∀ j ≤ 7, WP isa (.block ((List.range j).flatMap rotStep)) s0 (RotInv b O s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (rotSteps_ok hO j (by omega)) fun s h => rotStep_ok hO (by omega) h)

/-- The rotation's value from its words. -/
theorem rot_val (r o : Nat → Nat) (hr : ∀ i, r i < 2 ^ 64) (h8 : r 8 < 2 ^ 9)
    (ho : ∀ i < 7, o i = r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9)
    (h7 : o 7 = r 7 / 2 ^ 55 + r 8 % 2 ^ 55 * 2 ^ 9 + r 0 % 2 ^ 46 * 2 ^ 18)
    (h8' : o 8 = r 0 / 2 ^ 46 % 2 ^ 9) :
    colsV o 9 = colsV r 9 / 2 ^ 55 + 2 ^ 466 * (colsV r 9 % 2 ^ 55) := by
  have hs := shr_cols r (s := 55) (by decide) 8
  rw [show (64 : Nat) - 55 = 9 from rfl] at hs
  have e7 : colsV o 7 = colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 := colsV_congr ho
  have hR : colsV r 9 = colsV r 8 + (2 ^ 64) ^ 8 * r 8 := rfl
  have hc8 : colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 8 =
      colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 +
        (2 ^ 64) ^ 7 * (r 7 / 2 ^ 55 + r 8 % 2 ^ 55 * 2 ^ 9) := rfl
  have hm : r 0 % 2 ^ 55 = r 0 % 2 ^ 46 + 2 ^ 46 * (r 0 / 2 ^ 46 % 2 ^ 9) := by
    rw [show (2 : Nat) ^ 55 = 2 ^ 46 * 2 ^ 9 by decide, Nat.mod_mul]
  have hm' := Nat.mod_lt (r 0) (show 0 < 2 ^ 55 by decide)
  have ho9 : colsV o 9 = colsV o 7 + (2 ^ 64) ^ 7 * o 7 + (2 ^ 64) ^ 8 * o 8 := rfl
  rw [Nat.mod_eq_of_lt (by omega : r 8 < 2 ^ 55)] at hs
  have h80 := hr 0
  rw [ho9, e7, h7, h8']
  rw [show (2 ^ 64) ^ 7 = (2 : Nat) ^ 448 by decide, show (2 ^ 64) ^ 8 = (2 : Nat) ^ 512 by decide] at *
  generalize colsV (fun i => r i / 2 ^ 55 + r (i + 1) % 2 ^ 55 * 2 ^ 9) 7 = C at *
  generalize colsV r 8 = R8 at *
  generalize colsV r 9 = R at *
  generalize r 0 % 2 ^ 55 = M55 at *
  generalize r 0 % 2 ^ 46 = M46 at *
  generalize r 0 / 2 ^ 46 % 2 ^ 9 = Q at *
  omega

/-- Words 7 and 8 of the rotation. -/
theorem rotTop_ok {b O : Addr} {s0 : State} (hO : OCtx b O s0) {s : State} (h : RotInv b O s0 7 s)
    (h8 : dw s0.mem b (P + 64) < 2 ^ 9) :
    WP isa (.block rotTop) s fun s' => (∀ r, r ∉ [Reg.t0, .a6] → s'.gpr r = s0.gpr r) ∧ s'.rd = s0.rd ∧
      s'.wr = s0.wr ∧ s'.sp = s0.sp ∧ Frame [⟨O, 72⟩] s0.mem s'.mem ∧
      GenWide.ov s'.mem O 9 = pw s0.mem b 0 9 / 2 ^ 55 + 2 ^ 466 * (pw s0.mem b 0 9 % 2 ^ 55) := by
  have hP := P_eq
  have hcs : Ctx b s := ctx_of hO.ctx (h.gpr _ (by decide)) h.wr
  have hon := hO.onw
  unfold rotTop
  refine WP.block_append (WP.mono (rotWord_ok hcs (j := 7) (by omega)) fun s1 ⟨t0, g1, m1, rd1, wr1, sp1⟩ => ?_)
  have hc1 : Ctx b s1 := ctx_of hcs (g1 _ (by decide)) wr1
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => wp_sll (by decide) fun s3 u3 => wp_or fun s4 u4 => ?_
  have I7 : RotInv b O s0 7 s4 := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u4.other _ hr.1, u3.other _ hr.2, u2.other _ hr.2, g1 r (by simp [hr.1, hr.2]), h.gpr r (by simp [hr.1, hr.2])],
    by rw [u4.rd, u3.rd, u2.rd, rd1, h.rd], by rw [u4.wr, u3.wr, u2.wr, wr1, h.wr],
    by rw [u4.sp, u3.sp, u2.sp, sp1, h.sp], by rw [u4.mem, u3.mem, u2.mem, m1]; exact h.frame,
    by rw [u4.mem, u3.mem, u2.mem, m1]; exact h.val⟩
  refine rot_store (j := 7) hO I7 (by omega) (fun _ _ => rfl) rfl fun s5 u5 => ?_
  obtain ⟨f5, v5, w5⟩ := rot_next hO (by omega) I7 u5.mem
  have hc5 : Ctx b s5 := ctx_of hc1 (by rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide)]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr])
  refine ld_ok hc5 (by omega) (by omega) fun s6 u6 => wp_srl (by decide) fun s7 u7 => wp_andi (by decide) fun s8 u8 => ?_
  refine wp_sd (by omega) (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr,
      I7.gpr _ (by decide), hO.o]) (al8 hO.oal (by omega))
    (by rw [u8.wr, u7.wr, u6.wr, u5.wr, I7.wr]; exact hO.ow 8 (by omega)) fun s9 u9 => WP.block_nil ?_
  -- The words of `r`.
  have r0 : dw s.mem b P = dw s0.mem b (P + 8 * 0) := own_of_rot hO (by omega) h (by omega) (by omega)
  have hm8 : s8.mem = s5.mem := by rw [u8.mem, u7.mem, u6.mem]
  have hm9 : s9.mem = s5.mem.writeW (O + BitVec.ofNat 64 64) (s8.gpr .t0) := by rw [u9.mem, hm8]
  have hr7 : rw' s.mem b 7 = rw' s0.mem b 7 := by
    show dw s.mem b _ / _ + dw s.mem b _ % _ * _ = _
    rw [own_of_rot hO (by omega) h (by omega) (by omega), own_of_rot hO (by omega) h (by omega) (by omega)]
  have h7lt : rw' s0.mem b 7 < 2 ^ 18 := by
    have := dw_lt s0.mem b (P + 8 * 7)
    show dw s0.mem b (P + 8 * 7) / 2 ^ 55 + dw s0.mem b (P + 8 * (7 + 1)) % 2 ^ 55 * 2 ^ 9 < _
    rw [show P + 8 * (7 + 1) = P + 64 from rfl]
    omega
  have v7 : (s4.gpr .t0).toNat = rw' s0.mem b 7 + dw s0.mem b (P + 8 * 0) % 2 ^ 46 * 2 ^ 18 := by
    rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u3.gpr, u2.gpr, or_shl18 _ _ (by rw [t0, hr7]; exact h7lt),
      t0, hr7, m1]
    show rw' s0.mem b 7 + dw s.mem b P % 2 ^ 46 * 2 ^ 18 = _
    rw [r0]
  have v8 : (s8.gpr .t0).toNat = dw s0.mem b (P + 8 * 0) / 2 ^ 46 % 2 ^ 9 := by
    rw [u8.gpr, and511, u7.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, u6.gpr]
    exact congrArg (· / 2 ^ 46 % 2 ^ 9) (own_of_frame hO (by omega) f5 (by omega) (by omega))
  refine ⟨fun r hr => by rw [u9.gpr, u8.other _ (fun e => hr (by rw [e]; decide)),
      u7.other _ (fun e => hr (by rw [e]; decide)), u6.other _ (fun e => hr (by rw [e]; decide)), u5.gpr,
      I7.gpr r hr],
    by rw [u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, I7.rd], by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, I7.wr],
    by rw [u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, I7.sp], ?_, ?_⟩
  · rw [hm9]
    refine (f5.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 72⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 72⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · have hp : pw s0.mem b 0 9 = colsV (fun i => dw s0.mem b (P + 8 * i)) 9 :=
      colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
    rw [hp]
    refine rot_val (fun i => dw s0.mem b (P + 8 * i)) (fun i => dw s9.mem O (8 * i)) (fun _ => dw_lt _ _ _) h8
      (fun i hi => ?_) ?_ ?_
    · show dw s9.mem O (8 * i) = _
      rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega), v5 i hi]
    · show dw s9.mem O (8 * 7) = _
      rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega), w5, v7]
    · show dw s9.mem O (8 * 8) = _
      rw [hm9, dw_write_self, v8]

/-! ## The arithmetic modulo `p` -/

theorem mers_mod (u : Nat) : (u % 2 ^ 521 + u / 2 ^ 521) % (2 ^ 521 - 1) = u % (2 ^ 521 - 1) := by
  omega

/-- Rotating `r < p` right by 55 of its 521 bits divides it by `R = 2⁵⁷⁶` modulo `p`. -/
theorem rot_mod {r : Nat} (hr : r < 2 ^ 521 - 1) :
    r / 2 ^ 55 + 2 ^ 466 * (r % 2 ^ 55) < 2 ^ 521 - 1 ∧
      (r / 2 ^ 55 + 2 ^ 466 * (r % 2 ^ 55)) * 2 ^ 576 % (2 ^ 521 - 1) = r := by
  omega

/-- The correction: `(S + q) mod 2⁵²¹`, `q` the bit 521 of `S + 1`, is `S mod p`. -/
theorem canon_val {S : Nat} (hS : S < 2 ^ 521 + 2 ^ 56) :
    (S + (S + 1) / 2 ^ 521) % 2 ^ 521 < 2 ^ 521 - 1 ∧
      (S + (S + 1) / 2 ^ 521) % 2 ^ 521 = S % (2 ^ 521 - 1) := by
  by_cases h : 2 ^ 521 ≤ S + 1
  · have hq : (S + 1) / 2 ^ 521 = 1 := by omega
    rw [hq]; omega
  · have hq : (S + 1) / 2 ^ 521 = 0 := by omega
    rw [hq]; omega

theorem fold1_arith {H G X C w8 w17 : Nat} (hs : 2 ^ 9 * H + w8 % 2 ^ 9 = G + 2 ^ 576 * w17)
    (hX : X = C + 2 ^ 512 * (G + 2 ^ 576 * w17)) (hc : C < 2 ^ 512) :
    C + 2 ^ 512 * (w8 % 2 ^ 9) + H = X % 2 ^ 521 + X / 2 ^ 521 := by
  have := Nat.mod_lt w8 (show 0 < 2 ^ 9 by decide)
  omega

/-- The first fold's value: `T mod 2⁵²¹ + T >> 521`, for `T < 2¹⁰⁹⁷`. -/
theorem fold1_val (W : Nat → Nat) (hW : ∀ i, W i < 2 ^ 64) (hX : colsV W 18 < 2 ^ 1097) :
    colsV (fun i => (if i < 8 then W i else W i % 2 ^ 9) + (W (8 + i) / 2 ^ 9 + W (9 + i) % 2 ^ 9 * 2 ^ 55)) 9 =
      colsV W 18 % 2 ^ 521 + colsV W 18 / 2 ^ 521 := by
  rw [colsV_add']
  have hl : colsV (fun i => if i < 8 then W i else W i % 2 ^ 9) 9 = colsV W 8 + (2 ^ 64) ^ 8 * (W 8 % 2 ^ 9) := by
    show colsV (fun i => if i < 8 then W i else W i % 2 ^ 9) 8 + _ = _
    rw [colsV_congr (g := W) fun i hi => ite_eq_left hi]; rfl
  have hs := shr_cols (fun i => W (8 + i)) (s := 9) (by decide) 9
  rw [show (64 : Nat) - 9 = 55 from rfl] at hs
  have hh : colsV (fun i => W (8 + i) / 2 ^ 9 + W (8 + (i + 1)) % 2 ^ 9 * 2 ^ 55) 9 =
      colsV (fun i => W (8 + i) / 2 ^ 9 + W (9 + i) % 2 ^ 9 * 2 ^ 55) 9 :=
    colsV_congr fun i _ => by rw [show 8 + (i + 1) = 9 + i by omega]
  rw [hh] at hs
  have hsp := colsV_split W 8 10
  have h10 : colsV (fun j => W (8 + j)) 10 = colsV (fun j => W (8 + j)) 9 + (2 ^ 64) ^ 9 * W (8 + 9) := rfl
  have h17 : colsV W 18 = colsV W 17 + (2 ^ 64) ^ 17 * W 17 := rfl
  have hc8 := GenWide.colsV_lt W hW 8
  have e8 : ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 := by rw [← Nat.pow_mul]
  have e9 : ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 := by rw [← Nat.pow_mul]
  have e17 : ((2 : Nat) ^ 64) ^ 17 = 2 ^ 1088 := by rw [← Nat.pow_mul]
  rw [e8] at hl hsp hc8
  rw [e9] at hs h10
  rw [e17] at h17
  rw [hl]
  have hw17 : W 17 < 2 ^ 9 := by
    rcases Nat.lt_or_ge (W 17) (2 ^ 9) with h | h
    · exact h
    · exfalso
      have : 2 ^ 1088 * 2 ^ 9 ≤ 2 ^ 1088 * W 17 := Nat.mul_le_mul_left _ h
      omega
  rw [show 8 + 9 = 17 from rfl] at h10 hs
  rw [Nat.mod_eq_of_lt hw17] at hs
  rw [show 8 + 0 = 8 from rfl] at hs
  have hX' : colsV W 18 = colsV W 8 + 2 ^ 512 * (colsV (fun j => W (8 + j)) 9 + 2 ^ 576 * W 17) := by
    rw [← h10]; exact hsp
  exact fold1_arith hs hX' hc8

theorem fold2_arith {L8 w8 c c' R S : Nat} (hS : S = L8 + 2 ^ 512 * w8 + 2 ^ 576 * c) (hL : L8 < 2 ^ 512)
    (hSlt : S < 2 ^ 521 + 2 ^ 576) (hR : R < 2 ^ 576)
    (v5 : R + 2 ^ 576 * c' = L8 + 2 ^ 512 * (w8 % 2 ^ 9) + (w8 / 2 ^ 9 + c * 2 ^ 55)) :
    R = S % 2 ^ 521 + S / 2 ^ 521 ∧ R < 2 ^ 521 + 2 ^ 56 := by
  have h1 : S % 2 ^ 521 = L8 + 2 ^ 512 * (w8 % 2 ^ 9) := by omega
  have h2 : S / 2 ^ 521 = w8 / 2 ^ 9 + c * 2 ^ 55 := by omega
  have h3 : S / 2 ^ 521 ≤ 2 ^ 55 := by omega
  have h4 : c' = 0 := by omega
  subst h4
  omega

/-! ## The multiplication -/

open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW xv ov) in
theorem notin {r : Reg} (hr : r ∉ clobW) {L : List Reg} (hL : ∀ x ∈ L, x ∈ clobW := by decide) : r ∉ L :=
  fun h => hr (hL r h)

open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk ownR clobW xv ov) in
/-- `mulCore`: `[o] R ≡ [a] [b]` modulo `p`, `[o] < p`. -/
theorem mulCore_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) (hB : xv s.mem B 9 < 2 ^ 521 - 1) :
    WP isa (.block mulCore) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧
      ov s'.mem O 9 < 2 ^ 521 - 1 ∧ ov s'.mem O 9 * 2 ^ 576 % (2 ^ 521 - 1) = xv s.mem A 9 * xv s.mem B 9 % (2 ^ 521 - 1) := by
  have hP := P_eq
  have hT : T 9 = 1472 := rfl
  have hb := hC.nowrap
  have hal := hC.ctx.al
  unfold mulCore zeroT
  simp only [List.append_assoc, List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (u1.other _ (by decide)) u1.wr
  -- `T = 0`.
  refine WP.block_append (WP.mono (GenWide.zero_ok (k := 9) hc1 (by omega) (by omega) (by rw [u1.gpr]; rfl) 9 (by omega))
    fun s2 h2 => ?_)
  have hc2 : Ctx b s2 := ctx_of hc1 (by rw [h2.gpr]) h2.wr
  have g2 : ∀ r, r ≠ .a7 → s2.gpr r = s.gpr r := fun r hr => by rw [h2.gpr, u1.other _ hr]
  have m02 : ∀ {X : Addr} {d : Nat}, Region.Disjoint ⟨X + BitVec.ofNat 64 d, 8⟩ (own b) →
      dw s2.mem X d = dw s.mem X d := fun hd => by
    rw [dw_frame h2.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact GenWide.disj_sub hd (own_sub (Nat.le_refl _) (by omega)), u1.mem]
  -- The product.
  have hPC : PCtx b A B s2 :=
    ⟨hc2, hb, by rw [g2 _ (by decide), hC.a], by rw [g2 _ (by decide), hC.b'], hC.aal, hC.bal,
      by rw [h2.rd, h2.wr, u1.rd, u1.wr]; exact hC.ain, by rw [h2.rd, h2.wr, u1.rd, u1.wr]; exact hC.bin,
      hC.adis, hC.bdis⟩
  refine WP.block_append (WP.mono (rows_ok hPC (fun j hj => by
    exact h2.val j hj) 9 (Nat.le_refl _)) fun s3 h3 => ?_)
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  have hA2 : colsV (fun j => dw s2.mem A (8 * j)) 9 = xv s.mem A 9 := colsV_congr fun j hj => m02 (hC.adis j hj)
  have hB2 : colsV (fun j => dw s2.mem B (8 * j)) 9 = xv s.mem B 9 := colsV_congr fun j hj => m02 (hC.bdis j hj)
  have v3 := h3.val
  rw [hA2, hB2] at v3
  have hXlt : xv s.mem A 9 * xv s.mem B 9 < 2 ^ 1097 := by
    have hA : xv s.mem A 9 < ((2 : Nat) ^ 64) ^ 9 := GenWide.colsV_lt (fun j => dw s.mem A (8 * j)) (fun _ => dw_lt _ _ _) 9
    rw [show ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 by rw [← Nat.pow_mul]] at hA
    calc xv s.mem A 9 * xv s.mem B 9 ≤ (2 ^ 576 - 1) * (2 ^ 521 - 1) :=
          Nat.mul_le_mul (Nat.le_sub_one_of_lt hA) (Nat.le_of_lt hB)
      _ < 2 ^ 1097 := by decide
  generalize hX : xv s.mem A 9 * xv s.mem B 9 = X at v3 hXlt
  -- The first fold.
  refine WP.block_append (WP.mono (fold_ok hc3) fun s4 ⟨g4, rd4, wr4, sp4, f4, c4, v4⟩ => ?_)
  have hc4 : Ctx b s4 := ctx_of hc3 (g4 _ (by decide)) wr4
  have hW : pw s3.mem b 0 18 = colsV (fun i => dw s3.mem b (P + 8 * i)) 18 :=
    colsV_congr fun i _ => by rw [show P + 8 * 0 + 8 * i = P + 8 * i by omega]
  rw [hW] at v3
  have e4 := fold1_val (fun i => dw s3.mem b (P + 8 * i)) (fun _ => dw_lt _ _ _) (by rw [v3]; exact hXlt)
  rw [v3] at e4
  rw [show colsV (fun i => lw s3.mem b i + hw s3.mem b i) 9 = colsV (fun i => (if i < 8 then dw s3.mem b (P + 8 * i)
      else dw s3.mem b (P + 8 * i) % 2 ^ 9) + (dw s3.mem b (P + 8 * (8 + i)) / 2 ^ 9 +
        dw s3.mem b (P + 8 * (9 + i)) % 2 ^ 9 * 2 ^ 55)) 9 from rfl, e4] at v4
  -- The second fold.
  refine WP.block_append (WP.mono (fold2_ok hc4 c4) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_)
  have hc5 : Ctx b s5 := ctx_of hc4 (g5 _ (by decide)) wr5
  have h48 : pw s4.mem b 0 9 = pw s4.mem b 0 8 + 2 ^ 512 * dw s4.mem b (P + 64) := by
    rw [pw_succ, show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]]
  have l48 := pw_lt s4.mem b 8
  rw [show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]] at l48
  have l59 := pw_lt s5.mem b 9
  rw [show ((2 : Nat) ^ 64) ^ 9 = 2 ^ 576 by rw [← Nat.pow_mul]] at l59
  generalize hS : X % 2 ^ 521 + X / 2 ^ 521 = S at v4
  have hSlt : S < 2 ^ 521 + 2 ^ 576 := by omega
  have hS2 : pw s5.mem b 0 9 = S % 2 ^ 521 + S / 2 ^ 521 ∧ pw s5.mem b 0 9 < 2 ^ 521 + 2 ^ 56 :=
    fold2_arith (by rw [← v4, h48]) l48 hSlt l59 v5
  -- The correction.
  refine WP.block_append (WP.mono (canon_ok hc5 hS2.2) fun s6 ⟨g6, rd6, wr6, sp6, f6, v6⟩ => ?_)
  have hc6 : Ctx b s6 := ctx_of hc5 (g6 _ (by decide)) wr6
  obtain ⟨rlt, req⟩ := canon_val hS2.2
  rw [← v6] at rlt req
  -- The rotation.
  have hO : OCtx b O s6 :=
    ⟨hc6, hb, by rw [g6 _ (by decide), g5 _ (by decide), g4 _ (by decide), h3.gpr _ (by decide), g2 _ (by decide), hC.o],
      hC.oal, by rw [wr6, wr5, wr4, h3.wr, h2.wr, u1.wr]; exact hC.ow, hC.onw, hC.odis⟩
  have h68 : dw s6.mem b (P + 64) < 2 ^ 9 := by
    have e : pw s6.mem b 0 9 = pw s6.mem b 0 8 + (2 ^ 64) ^ 8 * dw s6.mem b (P + 8 * 8) := pw_succ s6.mem b 8
    rw [show ((2 : Nat) ^ 64) ^ 8 = 2 ^ 512 by rw [← Nat.pow_mul]] at e
    rw [show P + 8 * 8 = P + 64 from rfl] at e
    omega
  refine WP.block_append (WP.mono (rotSteps_ok hO 7 (Nat.le_refl _)) fun s7 h7 => ?_)
  refine WP.mono (rotTop_ok hO h7 h68) fun s8 ⟨g8, rd8, wr8, sp8, f8, v8⟩ => ?_
  obtain ⟨olt, oeq⟩ := rot_mod rlt
  rw [← v8] at olt oeq
  have hO6 : ∀ x ∈ [Region.mk (b + BitVec.ofNat 64 P) 72], ∃ r' ∈ [ownR 9 b, ⟨O, 8 * 9⟩], Region.Sub x r' :=
    fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
  refine ⟨fun r hr => ?_, by rw [rd8, rd6, rd5, rd4, h3.rd, h2.rd, u1.rd], by rw [wr8, wr6, wr5, wr4, h3.wr, h2.wr, u1.wr],
    by rw [sp8, sp6, sp5, sp4, h3.sp, h2.sp, u1.sp], ?_, olt, ?_⟩
  · rw [g8 r (notin hr), g6 r (notin hr), g5 r (notin hr), g4 r (notin hr), h3.gpr r (notin hr), g2 r (fun e => hr (by rw [e]; decide))]
  · have F1 : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s2.mem := by
      rw [← u1.mem]
      exact h2.frame.sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
    have F2 : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s2.mem s3.mem := h3.frame.sub fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
    have F8 : Frame [ownR 9 b, ⟨O, 8 * 9⟩] s6.mem s8.mem := f8.sub fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    exact ((((F1.trans F2).trans (f4.sub hO6)).trans (f5.sub hO6)).trans (f6.sub hO6)).trans F8
  · rw [oeq, req, hS2.1, mers_mod, ← hS, mers_mod]

open VG.Proof.Weierstrass.RISCV64.GenWide (CoreSpec fn_rv) in
theorem mulCore_spec :
    CoreSpec 9 mulCore (fun _ B => B < 2 ^ 521 - 1)
      (fun A B r => r < 2 ^ 521 - 1 ∧ r * 2 ^ (64 * 9) % (2 ^ 521 - 1) = A * B % (2 ^ 521 - 1)) :=
  fun hC hB => WP.mono (mulCore_ok hC hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

open VG.Impl.Weierstrass.Mont (p521p) in
open VG.Proof.Weierstrass.RISCV64 (mulRV) in
open VG.Proof.Weierstrass.RISCV64.GenWide (fn_rv) in
/-- `vg_p521_mul_mod_p` by its Mersenne form meets the contract by register. -/
theorem mul_rv (s : State) (hs : (mulRV p521p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (S := p521p) (by decide) (by decide) @mulCore_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

end VG.Proof.Weierstrass.RISCV64.P521Mersenne
