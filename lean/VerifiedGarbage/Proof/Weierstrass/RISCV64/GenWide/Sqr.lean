module

-- separate module: its proofs build in parallel with the field's code literal, which its importer's
-- constant time evaluates
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Montgomery's square modulo a wide modulus on RISC-V

`sqrCore k m` (`Impl/Weierstrass/RISCV64/GenWide.lean`) squares the operand
`a` at `t4`, for operands and a result apart from the whole own working
space (`sqrCore_ok`):

* the product `P = a²` at `SQ` (`sqr_ok`): the rows of the products `aᵢ aⱼ`,
  `i < j`, each a row of multiply-accumulate steps in place (`irow_ok`,
  `sqrRow_ok`, `rows_ok`), sum to `∑ⱼ aⱼ 2^(64 j) (a mod 2^(64 j))`
  (`rows_sum`), and `P` doubled plus the squares `aᵢ²` (`dword_ok`,
  `diag_ok`, `diags_ok`) is `a²` (`sq_sum`);
* Montgomery's reduction of `P` in place (`sred_ok`, `srounds_ok`): after `i`
  rounds, `P`'s words from `i` and the carry `a2` are `V` with
  `2^(64 i) V = a² + Q m` for some `Q < 2^(64 i)`;
* the top words and the carry into `T` (`copyT_ok`), and GenWide's final
  subtraction (`csub_ok`), as `mulCore_ok`'s.

`mulSqFn` takes it when the operands are the same pointer (`mulSqFast_spec`),
GenWide's entry and copies the rest (`fnWith_ok`), and meets the contract by
register (`mulSq_rv`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## A row in place -/

/-- After `j` steps of a row in place at `u` from `s0`. -/
structure IRowInv (b X : Addr) (xo u : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 u, 8 * j⟩] s0.mem s.mem
  val : colsV (fun i => dw s.mem b (u + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem b (u + 8 * i) + dw s0.mem X (xo + 8 * i) * (s0.gpr .a4).toNat) j +
      (s0.gpr .a5).toNat

theorem IRowInv.zero {b X : Addr} {xo u : Nat} (s0 : State) : IRowInv b X xo u s0 0 s0 :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [colsV]⟩

/-- What a row needs of its operands. -/
structure IRowOk (b X : Addr) (xb : Reg) (xo u n : Nat) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  hx : s0.gpr xb = X
  hxb : xb ∉ clobS
  hxo : ∀ i < n, xo + 8 * i < 2048
  xal : ∀ i < n, (X + BitVec.ofNat 64 (xo + 8 * i)).toNat % 8 = 0
  xin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (xo + 8 * i)) 8
  xdis : ∀ i < n, ∀ j ≤ n,
    Region.Disjoint ⟨X + BitVec.ofNat 64 (xo + 8 * i), 8⟩ ⟨b + BitVec.ofNat 64 u, 8 * j⟩
  top : u + 8 * n ≤ 2048
  t8 : u % 8 = 0

set_option linter.unusedSimpArgs false in
/-- Step `j` of a row. -/
theorem irowStep_ok {b X : Addr} {xb : Reg} {xo u n : Nat} {s0 : State} (hR : IRowOk b X xb xo u n s0)
    {j : Nat} (hj : j < n) {s : State} (h : IRowInv b X xo u s0 j s) :
    WP isa (.block (macStep xb (xo + 8 * j) (u + 8 * j) (u + 8 * j))) s
      (IRowInv b X xo u s0 (j + 1)) := by
  have hc : Ctx b s := ctx_of hR.ctx (h.gpr _ (by decide)) h.wr
  have hT := hR.top
  have ht8 := hR.t8
  have hxo := hR.hxo j hj
  have hb := hR.nowrap
  unfold macStep
  -- The word `x`.
  refine wp_ld (by omega) (by rw [h.gpr _ hR.hxb, hR.hx]) (hR.xal j hj)
    (by rw [h.rd, h.wr]; exact hR.xin j hj) fun s1 u1 => ?_
  refine ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 => ?_
  show WP isa (.block ([.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
    .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3] ++
    [Instr.store .d .t0 .a3 (u + 8 * j)])) s2 _
  refine WP.block_append (WP.mono mac_ok fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hc (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  -- Facts.
  have m3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have g3 : ∀ r, r ∉ clobS → s3.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1]
  have a6 : s2.gpr .a6 = s.mem.readW (X + BitVec.ofNat 64 (xo + 8 * j)) 64 := by
    rw [u2.other _ (by decide), u1.gpr]
  have a7 : s2.gpr .a7 = s.mem.readW (b + BitVec.ofNat 64 (u + 8 * j)) 64 := by
    rw [u2.gpr, u1.mem]
  have a4 : s2.gpr .a4 = s.gpr .a4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (u + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, m3]
  -- The words read are those of `s0`.
  have hX0 : dw s.mem X (xo + 8 * j) = dw s0.mem X (xo + 8 * j) :=
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
        dw s0.mem X (xo + 8 * j) * (s0.gpr .a4).toNat + dw s0.mem b (u + 8 * j) +
          (s.gpr .a5).toNat := by
      rw [e3, a6, a7, a4, a5, ← hX0, ← hT0, h.gpr _ (by decide)]; rfl
    show colsV (fun i => dw s4.mem b (u + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (u + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      colsV (fun i => dw s0.mem b (u + 8 * i) + dw s0.mem X (xo + 8 * i) * (s0.gpr .a4).toNat) j +
        (2 ^ 64) ^ j * (dw s0.mem b (u + 8 * j) + dw s0.mem X (xo + 8 * j) * (s0.gpr .a4).toNat) +
        (s0.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun i => dw s.mem b (u + 8 * i)) j = C at *
    have key : E * (s3.gpr .t0).toNat + E * 2 ^ 64 * (s3.gpr .a5).toNat =
        E * (s.gpr .a5).toNat + E * (dw s0.mem b (u + 8 * j) +
          dw s0.mem X (xo + 8 * j) * (s0.gpr .a4).toNat) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e3']; congr 1; omega
    omega

/-- The row. -/
theorem irow_ok {b X : Addr} {xb : Reg} {xo u n : Nat} {s0 : State}
    (hR : IRowOk b X xb xo u n s0) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap fun i =>
      macStep xb (xo + 8 * i) (u + 8 * i) (u + 8 * i))) s0 (IRowInv b X xo u s0 j)
  | 0, _ => WP.block_nil (IRowInv.zero s0)
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (irow_ok hR j (by omega)) fun s h => irowStep_ok hR (j := j) (by omega) h)

/-! ## The square's numbers -/

theorem colsV_split (f : Nat → Nat) (p : Nat) :
    ∀ n, colsV f (p + n) = colsV f p + (2 ^ 64) ^ p * colsV (fun j => f (p + j)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    rw [← Nat.add_assoc, colsV_succ, colsV_split f p n, colsV_succ, Nat.mul_add, Nat.pow_add, Nat.mul_assoc]
    omega

/-- A sum of `n` terms. -/
def sumN (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumN g n + g n

/-- Row `i` of the square's products: `aᵢ 2^(64 (2 i + 1)) a[i + 1 …]`. -/
def rowTerm (a : Nat → Nat) (k i : Nat) : Nat :=
  a i * (2 ^ 64) ^ (2 * i + 1) * colsV (fun j => a (i + 1 + j)) (k - 1 - i)

theorem sumN_add (g h : Nat → Nat) : ∀ n, sumN (fun i => g i + h i) n = sumN g n + sumN h n
  | 0 => rfl
  | n + 1 => by simp only [sumN]; rw [sumN_add g h n]; omega

theorem sumN_congr {g h : Nat → Nat} : ∀ {n}, (∀ i < n, g i = h i) → sumN g n = sumN h n
  | 0, _ => rfl
  | n + 1, e => by simp only [sumN]; rw [sumN_congr fun i hi => e i (by omega), e n (by omega)]

theorem sumN_cols (a : Nat → Nat) (c : Nat) : ∀ n, sumN (fun i => a i * (2 ^ 64) ^ i * c) n = colsV a n * c
  | 0 => by simp [sumN, colsV]
  | n + 1 => by simp only [sumN]; rw [sumN_cols a c n, colsV_succ]; grind

theorem rows_sum (a : Nat → Nat) :
    ∀ k, sumN (rowTerm a k) k = sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k
  | 0 => rfl
  | k + 1 => by
    have h : ∀ i < k, rowTerm a (k + 1) i = rowTerm a k i + a i * (2 ^ 64) ^ i * (colsV a 0 + a k * (2 ^ 64) ^ k) :=
      fun i hi => by
        unfold rowTerm
        rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, colsV_succ, show i + 1 + (k - 1 - i) = k by omega]
        have e : ((2 : Nat) ^ 64) ^ (2 * i + 1) * (2 ^ 64) ^ (k - 1 - i) = (2 ^ 64) ^ i * (2 ^ 64) ^ k := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
        simp only [colsV, Nat.zero_add]
        generalize colsV (fun j => a (i + 1 + j)) (k - 1 - i) = C
        generalize ((2 : Nat) ^ 64) ^ (2 * i + 1) = X at e
        generalize ((2 : Nat) ^ 64) ^ (k - 1 - i) = Y at e
        generalize ((2 : Nat) ^ 64) ^ i = U at e
        generalize ((2 : Nat) ^ 64) ^ k = V at e
        calc a i * X * (C + Y * a k) = a i * X * C + a i * (X * Y) * a k := by grind
          _ = _ := by rw [e]; grind
    have hk : rowTerm a (k + 1) k = 0 := by simp [rowTerm, colsV]
    show sumN (rowTerm a (k + 1)) k + rowTerm a (k + 1) k = sumN _ k + _
    rw [hk, Nat.add_zero, sumN_congr h, sumN_add, rows_sum a k, sumN_cols]
    simp only [colsV, Nat.zero_add]
    grind

/-- The square as its rows, doubled, and its squares. -/
theorem sq_sum (a : Nat → Nat) :
    ∀ k, colsV a k * colsV a k =
      sumN (fun i => a i * a i * (2 ^ 64) ^ (2 * i)) k + 2 * sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k
  | 0 => by simp [colsV, sumN]
  | k + 1 => by
    simp only [sumN]
    have ih := sq_sum a k
    rw [colsV_succ, show 2 * k = k + k by omega, Nat.pow_add]
    generalize sumN (fun i => a i * a i * (2 ^ 64) ^ (2 * i)) k = D at ih ⊢
    generalize sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k = X at ih ⊢
    generalize colsV a k = A at ih ⊢
    generalize ((2 : Nat) ^ 64) ^ k = E
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, ih]
    grind

/-! ## The square's product -/

theorem sq_facts (k : Nat) (h₁ : 7 ≤ k) (h : k ≤ 30) :
    SQ k % 8 = 0 ∧ SQ k + 8 * (2 * k) ≤ 2048 ∧ N k + 8 * k ≤ SQ k ∧ T k + 64 * k = 2048 ∧ T k + 8 * (k + 2) ≤ N k := by
  unfold SQ SO SB SA N T; omega

/-- The square's product's words. -/
abbrev PR (k : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (SQ k), 8 * (2 * k)⟩

structure PZeroInv (k : Nat) (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (SQ k), 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem b (SQ k + 8 * i) = 0

theorem pzero_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 7 ≤ k) (hk' : k ≤ 30)
    (h7 : s0.gpr .a7 = 0) :
    ∀ j ≤ 2 * k, WP isa (.block ((List.range j).map fun j => .store .d .a7 .a3 (SQ k + 8 * j))) s0
      (PZeroInv k b s0 j)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨t8, ttop, -, -, -⟩ := sq_facts k hk hk'
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (pzero_ok hc hk hk' h7 j (by omega)) fun s h => ?_)
    have hcs : Ctx b s := ctx_of hc (by rw [h.gpr]) h.wr
    refine sd_ok hcs (by omega) (by omega) fun s1 u1 => WP.block_nil ?_
    have hm1 : s1.mem = s.mem.writeW (b + BitVec.ofNat 64 (SQ k + 8 * j)) (0 : BitVec 64) := by rw [u1.mem, h.gpr, h7]
    refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], ?_,
      fun i hi => ?_⟩
    · rw [hm1]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by have := hc.al; omega)
    · rw [hm1]
      by_cases hij : i = j
      · subst hij; rw [dw_write_self]; rfl
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i (by omega)

/-- `P = 0`. -/
theorem zeroP_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 7 ≤ k) (hk' : k ≤ 30) :
    WP isa (.block (zeroP k)) s0 fun s =>
      (∀ r, r ≠ .a7 → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧ s.sp = s0.sp ∧
      Frame [PR k b] s0.mem s.mem ∧ ∀ i < 2 * k, dw s.mem b (SQ k + 8 * i) = 0 := by
  unfold zeroP
  refine wp_li (by decide) fun s1 u1 => WP.mono (pzero_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) hk hk'
    (by rw [u1.gpr]; rfl) (2 * k) (Nat.le_refl _)) fun s h => ?_
  refine ⟨fun r hr => by rw [h.gpr, u1.other r hr], by rw [h.rd, u1.rd], by rw [h.wr, u1.wr],
    by rw [h.sp, u1.sp], by rw [← u1.mem]; exact h.frame, h.val⟩

/-- What the square needs of the working space and of `a`. -/
structure SqOk (k : Nat) (b A : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  aal : A.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem SqOk.of {k : Nat} {b A : Addr} {s s' : State} (h : SqOk k b A s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (h4 : s'.gpr .t4 = s.gpr .t4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SqOk k b A s' :=
  ⟨ctx_of h.ctx h3 hwr, h.nowrap, h4.trans h.a, h.aal, by rw [hrd, hwr]; exact h.ain, h.adis, h.k7, h.k30⟩

/-- A part of the own working space within it. -/
theorem ownA_sub {k : Nat} (b : Addr) {d n : Nat} (hd : T k ≤ d) (hn : d + n ≤ T k + 64 * k) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (ownA k b) :=
  Offset.sub b hd hn

/-- Row `i` of the square's products: `P[2 i + 1 … i + k] += aᵢ a[i + 1 …]`, for
`P[i + k]` zero. -/
theorem sqrRow_ok {k : Nat} {b A : Addr} {s : State} (h : SqOk k b A s) {i : Nat} (hi : i + 1 < k)
    (hz : dw s.mem b (SQ k + 8 * (2 * i + 1) + 8 * (k - 1 - i)) = 0) :
    WP isa (.block (sqrRow k i)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * (2 * i + 1)), 8 * (k - 1 - i + 1)⟩] s.mem s'.mem ∧
      colsV (fun j => dw s'.mem b (SQ k + 8 * (2 * i + 1) + 8 * j)) (k - 1 - i + 1) =
        colsV (fun j => dw s.mem b (SQ k + 8 * (2 * i + 1) + 8 * j)) (k - 1 - i + 1) +
          dw s.mem A (8 * i) * colsV (fun j => dw s.mem A (8 * (i + 1) + 8 * j)) (k - 1 - i) := by
  have k7 := h.k7
  have k30 := h.k30
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
  have hb := h.nowrap
  have hc := h.ctx
  unfold sqrRow
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (by omega) (by rw [h.a]) (al8 h.aal (by omega)) (h.ain _ (by omega)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ctx_of hc (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr])
  have hR : IRowOk b A .t4 (8 * (i + 1)) (SQ k + 8 * (2 * i + 1)) (k - 1 - i) s2 :=
    { ctx := hc2
      nowrap := hb
      hx := by rw [u2.other _ (by decide), u1.other _ (by decide), h.a]
      hxb := by decide
      hxo := fun j hj => by omega
      xal := fun j hj => al8 h.aal (by omega)
      xin := fun j hj => by
        rw [u2.rd, u2.wr, u1.rd, u1.wr, show 8 * (i + 1) + 8 * j = 8 * (i + 1 + j) by omega]
        exact h.ain _ (by omega)
      xdis := fun j hj j' hj' => by
        rw [show 8 * (i + 1) + 8 * j = 8 * (i + 1 + j) by omega]
        exact disj_sub (h.adis _ (by omega)) (ownA_sub b (by omega) (by omega))
      top := by omega
      t8 := by omega }
  refine WP.block_append (WP.mono (irow_ok hR (k - 1 - i) (Nat.le_refl _)) fun s3 h3 => ?_)
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hm4 : s4.mem = s3.mem.writeW (b + BitVec.ofNat 64 (SQ k + 8 * (i + k))) (s3.gpr .a5) := u4.mem
  have eik : SQ k + 8 * (i + k) = SQ k + 8 * (2 * i + 1) + 8 * (k - 1 - i) := by omega
  refine ⟨fun r hr => ?_, by rw [u4.rd, h3.rd, u2.rd, u1.rd], by rw [u4.wr, h3.wr, u2.wr, u1.wr],
    by rw [u4.sp, h3.sp, u2.sp, u1.sp], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.gpr, h3.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      u2.other r hr.2.2.2.2.1, u1.other r hr.1]
  · rw [hm4, ← m2]
    refine (h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h3.val
    rw [colsV_add', colsV_mul, m2, u2.gpr, u2.other _ (by decide), u1.gpr] at hv
    have hlow : colsV (fun j => dw s4.mem b (SQ k + 8 * (2 * i + 1) + 8 * j)) (k - 1 - i) =
        colsV (fun j => dw s3.mem b (SQ k + 8 * (2 * i + 1) + 8 * j)) (k - 1 - i) :=
      colsV_congr fun j hj => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have htop : dw s4.mem b (SQ k + 8 * (2 * i + 1) + 8 * (k - 1 - i)) = (s3.gpr .a5).toNat := by
      rw [hm4, eik, dw_write_self]
    rw [colsV_succ, colsV_succ, hlow, htop, hz]
    simp only [Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat, Nat.zero_mod] at hv ⊢
    rw [hv, Nat.mul_comm (colsV (fun i_1 => dw s.mem A (8 * (i + 1) + 8 * i_1)) (k - 1 - i))]
    rfl

theorem colsV_split3 (f : Nat → Nat) (p n c : Nat) :
    colsV f (p + n + c) = colsV f p + (2 ^ 64) ^ p * colsV (fun j => f (p + j)) n +
      (2 ^ 64) ^ (p + n) * colsV (fun j => f (p + n + j)) c := by
  rw [colsV_split f (p + n) c, colsV_split f p n]

theorem colsV_zero : ∀ n, colsV (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [colsV_succ, colsV_zero n]; rfl

/-- The `n` words of `P` from word `j`. -/
abbrev pv (k : Nat) (m : Mem) (b : Addr) (j n : Nat) : Nat := colsV (fun i => dw m b (SQ k + 8 * (j + i))) n

/-- After `r` rows of the square's products, from `s0`. -/
structure RowsInv (k : Nat) (b A : Addr) (s0 : State) (r : Nat) (s : State) : Prop where
  gpr : ∀ x, x ∉ .a4 :: .a7 :: clobS → s.gpr x = s0.gpr x
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR k b] s0.mem s.mem
  val : pv k s.mem b 0 (2 * k) = sumN (rowTerm (fun j => dw s0.mem A (8 * j)) k) r
  zero : ∀ j, r + k ≤ j → j < 2 * k → dw s.mem b (SQ k + 8 * j) = 0

/-- `a`'s words through a frame of the own working space. -/
theorem dwA_frame {k : Nat} {b A : Addr} {m m' : Mem} (hf : Frame [PR k b] m m') (hk : 7 ≤ k) (hk' : k ≤ 30)
    (hdis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)) {i : Nat}
    (hi : i < k) : dw m' A (8 * i) = dw m A (8 * i) := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  exact dw_frame hf fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hdis i hi) (ownA_sub b (by omega) (by omega))

/-- The rows. -/
theorem rows_ok {k : Nat} {b A : Addr} {s0 : State} (h : SqOk k b A s0)
    (hz : ∀ j < 2 * k, dw s0.mem b (SQ k + 8 * j) = 0) :
    ∀ r ≤ k - 1, WP isa (.block ((List.range r).flatMap (sqrRow k))) s0 (RowsInv k b A s0 r)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl,
      by rw [pv, colsV_congr (g := fun _ => 0) fun i hi => hz _ (by omega), colsV_zero]; rfl,
      fun j _ hj => hz j hj⟩
  | r + 1, hr => by
    have k7 := h.k7
    have k30 := h.k30
    obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (rows_ok h hz r (by omega)) fun s hs => ?_)
    have hS : SqOk k b A s := h.of (hs.gpr _ (by decide)) (hs.gpr _ (by decide)) hs.rd hs.wr
    have hz' : dw s.mem b (SQ k + 8 * (2 * r + 1) + 8 * (k - 1 - r)) = 0 := by
      rw [show SQ k + 8 * (2 * r + 1) + 8 * (k - 1 - r) = SQ k + 8 * (r + k) by omega]
      exact hs.zero _ (Nat.le_refl _) (by omega)
    refine WP.mono (sqrRow_ok hS (i := r) (by omega) hz')
      fun s' ⟨g', rd', wr', sp', f', v'⟩ => ?_
    have hA : ∀ i < k, dw s.mem A (8 * i) = dw s0.mem A (8 * i) :=
      fun i hi => dwA_frame hs.frame k7 k30 h.adis hi
    -- Words outside the row's.
    have out : ∀ j, (j < 2 * r + 1 ∨ r + k + 1 ≤ j) → j < 2 * k →
        dw s'.mem b (SQ k + 8 * j) = dw s.mem b (SQ k + 8 * j) := fun j hj hj' =>
      dw_frame f' fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact Offset.disjoint b (by omega) (by omega) (by omega)
    refine ⟨fun x hx => ?_, by rw [rd', hs.rd], by rw [wr', hs.wr], by rw [sp', hs.sp], ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hx
      rw [g' x (by simp only [List.mem_cons, not_or]; exact ⟨hx.1, hx.2.2⟩), hs.gpr x (by
        simp only [List.mem_cons, not_or]; exact hx)]
    · exact hs.frame.trans (f'.sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega) (by omega)⟩)
    · have hv := hs.val
      have e' := colsV_split3 (fun i => dw s'.mem b (SQ k + 8 * (0 + i))) (2 * r + 1) (k - 1 - r + 1) (k - 1 - r)
      have e0 := colsV_split3 (fun i => dw s.mem b (SQ k + 8 * (0 + i))) (2 * r + 1) (k - 1 - r + 1) (k - 1 - r)
      rw [show 2 * r + 1 + (k - 1 - r + 1) + (k - 1 - r) = 2 * k by omega] at e' e0
      have L : colsV (fun i => dw s'.mem b (SQ k + 8 * (0 + i))) (2 * r + 1) =
          colsV (fun i => dw s.mem b (SQ k + 8 * (0 + i))) (2 * r + 1) :=
        colsV_congr fun i hi => out _ (.inl (by omega)) (by omega)
      have R : colsV (fun j => dw s'.mem b (SQ k + 8 * (0 + (2 * r + 1 + (k - 1 - r + 1) + j)))) (k - 1 - r) =
          colsV (fun j => dw s.mem b (SQ k + 8 * (0 + (2 * r + 1 + (k - 1 - r + 1) + j)))) (k - 1 - r) :=
        colsV_congr fun i hi => out _ (.inr (by omega)) (by omega)
      have M' : colsV (fun j => dw s'.mem b (SQ k + 8 * (0 + (2 * r + 1 + j)))) (k - 1 - r + 1) =
          colsV (fun j => dw s'.mem b (SQ k + 8 * (2 * r + 1) + 8 * j)) (k - 1 - r + 1) :=
        colsV_congr fun j _ => by rw [show SQ k + 8 * (0 + (2 * r + 1 + j)) = SQ k + 8 * (2 * r + 1) + 8 * j by omega]
      have M0 : colsV (fun j => dw s.mem b (SQ k + 8 * (0 + (2 * r + 1 + j)))) (k - 1 - r + 1) =
          colsV (fun j => dw s.mem b (SQ k + 8 * (2 * r + 1) + 8 * j)) (k - 1 - r + 1) :=
        colsV_congr fun j _ => by rw [show SQ k + 8 * (0 + (2 * r + 1 + j)) = SQ k + 8 * (2 * r + 1) + 8 * j by omega]
      have hP : colsV (fun j => dw s.mem A (8 * (r + 1) + 8 * j)) (k - 1 - r) =
          colsV (fun j => dw s0.mem A (8 * (r + 1 + j))) (k - 1 - r) :=
        colsV_congr fun j hj => by rw [show 8 * (r + 1) + 8 * j = 8 * (r + 1 + j) by omega, hA _ (by omega)]
      have ha : dw s.mem A (8 * r) = dw s0.mem A (8 * r) := hA _ (by omega)
      rw [pv, e0] at hv
      show pv k s'.mem b 0 (2 * k) = sumN (rowTerm (fun j => dw s0.mem A (8 * j)) k) r +
        rowTerm (fun j => dw s0.mem A (8 * j)) k r
      rw [pv, e', L, R, M', v', ← M0, hP, ha, ← hv, rowTerm]
      generalize colsV (fun i => dw s.mem b (SQ k + 8 * (0 + i))) (2 * r + 1) = X
      generalize colsV (fun j => dw s.mem b (SQ k + 8 * (0 + (2 * r + 1 + j)))) (k - 1 - r + 1) = Mi
      generalize colsV (fun j => dw s.mem b (SQ k + 8 * (0 + (2 * r + 1 + (k - 1 - r + 1) + j)))) (k - 1 - r) = Rt
      generalize colsV (fun j => dw s0.mem A (8 * (r + 1 + j))) (k - 1 - r) = Cn
      grind
    · intro j hj hj'
      rw [out _ (.inr (by omega)) hj']; exact hs.zero j (by omega) hj'

/-! ## The doubling and the squares -/

theorem dbl_nat {W B T1 bi : Nat} (hW : W < 2 ^ 64) (hB : B = W / 2 ^ 63) (hbi : bi ≤ 1)
    (hT : T1 = (W * 2 % 2 ^ 64 + bi) % 2 ^ 64) : T1 + 2 ^ 64 * B = 2 * W + bi ∧ B ≤ 1 := by
  omega

/-- Word `j` of `P` doubled with the bit `bi`, plus `x` and the carry `a5`. -/
theorem dword_ok {k : Nat} {b : Addr} {s : State} (hc : Ctx b s) (hk : 7 ≤ k) (hk' : k ≤ 30) {j : Nat}
    (hj : j < 2 * k) {x bi bo : Reg} (hx7 : x ≠ .a7) (hxo : x ≠ bo)
    (hi7 : bi ≠ .a7) (hio : bi ≠ bo) (ho7 : bo ≠ .a7) (ho6 : bo ≠ .a6) (ho5 : bo ≠ .a5) (ho3 : bo ≠ .a3)
    (hbi : (s.gpr bi).toNat ≤ 1) (hc5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block (dword k j x bi bo)) s fun s' =>
      dw s'.mem b (SQ k + 8 * j) + 2 ^ 64 * (s'.gpr .a5).toNat + 2 ^ 64 * (s'.gpr bo).toNat =
        2 * dw s.mem b (SQ k + 8 * j) + (s.gpr bi).toNat + (s.gpr x).toNat + (s.gpr .a5).toNat ∧
      (s'.gpr .a5).toNat ≤ 1 ∧ (s'.gpr bo).toNat ≤ 1 ∧
      (∀ r, r ∉ [.a7, .a6, .a5, bo] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * j), 8⟩] s.mem s'.mem := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  unfold dword
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 => ?_
  refine wp_add fun s4 u4 => wp_add fun s5 u5 => wp_sltu fun s6 u6 => wp_add fun s7 u7 => wp_sltu fun s8 u8 =>
    wp_add fun s9 u9 => ?_
  have hc9 : Ctx b s9 := ctx_of hc (by
      rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.other _ (Ne.symm ho3), u1.other _ (by decide)])
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine sd_ok hc9 (by omega) (by omega) fun s10 u10 => WP.block_nil ?_
  -- What each step read.
  have w1 : (s1.gpr .a7).toNat = dw s.mem b (SQ k + 8 * j) := by rw [u1.gpr]; rfl
  have a7_2 : s2.gpr .a7 = s1.gpr .a7 := u2.other _ (Ne.symm ho7)
  have bi3 : s3.gpr bi = s.gpr bi := by rw [u3.other _ hi7, u2.other _ hio, u1.other _ hi7]
  have x4 : s4.gpr x = s.gpr x := by rw [u4.other _ hx7, u3.other _ hx7, u2.other _ hxo, u1.other _ hx7]
  have x5 : s5.gpr x = s.gpr x := by rw [u5.other _ hx7, x4]
  have a5_6 : s6.gpr .a5 = s.gpr .a5 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (Ne.symm ho5), u1.other _ (by decide)]
  have bo9 : s9.gpr bo = s2.gpr bo := by
    rw [u9.other _ ho5, u8.other _ ho5, u7.other _ ho7, u6.other _ ho6, u5.other _ ho7, u4.other _ ho7,
      u3.other _ ho7]
  -- The numbers.
  have hB : (s9.gpr bo).toNat = dw s.mem b (SQ k + 8 * j) / 2 ^ 63 := by
    rw [bo9, u2.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, w1]
  have hT1 : (s4.gpr .a7).toNat = (dw s.mem b (SQ k + 8 * j) * 2 % 2 ^ 64 + (s.gpr bi).toNat) % 2 ^ 64 := by
    rw [u4.gpr, BitVec.toNat_add, u3.gpr, bi3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, a7_2, w1, Nat.pow_one]
  have c1e : s6.gpr .a6 = if s4.gpr .a7 + s4.gpr x < s4.gpr x then 1 else 0 := by
    rw [u6.gpr, u5.gpr, u5.other _ hx7]
  have s6a7 : s6.gpr .a7 = s4.gpr .a7 + s4.gpr x := by rw [u6.other _ (by decide), u5.gpr]
  have c2e : s8.gpr .a5 = if s6.gpr .a7 + s6.gpr .a5 < s6.gpr .a5 then 1 else 0 := by
    rw [u8.gpr, u7.gpr, u7.other .a5 (by decide)]
  have a6_8 : s8.gpr .a6 = s6.gpr .a6 := by rw [u8.other _ (by decide), u7.other _ (by decide)]
  have t3 : s9.gpr .a7 = s6.gpr .a7 + s6.gpr .a5 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]
  have m9 : s9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm : s10.mem = s.mem.writeW (b + BitVec.ofNat 64 (SQ k + 8 * j)) (s9.gpr .a7) := by rw [u10.mem, m9]
  have e1 := carry (s4.gpr .a7) (s4.gpr x)
  have e2 := carry (s6.gpr .a7) (s6.gpr .a5)
  have l1 := carry_le (s4.gpr .a7 + s4.gpr x < s4.gpr x)
  have l2 := carry_le (s6.gpr .a7 + s6.gpr .a5 < s6.gpr .a5)
  rw [← c1e] at e1 l1
  rw [← c2e] at e2 l2
  rw [s6a7] at e2
  have h5 : (s9.gpr .a5).toNat = (s8.gpr .a5).toNat + (s6.gpr .a6).toNat := by
    rw [u9.gpr, BitVec.toNat_add, a6_8, Nat.mod_eq_of_lt (by omega)]
  have hw := dw_lt s.mem b (SQ k + 8 * j)
  have hx := (s.gpr x).isLt
  obtain ⟨d1, d2⟩ := dbl_nat (B := (s9.gpr bo).toNat) hw hB hbi hT1
  have g10 : s10.gpr = s9.gpr := u10.gpr
  rw [x4] at e1
  rw [a5_6, x4] at e2
  have cc := (s4.gpr .a7 + s.gpr x).isLt
  refine ⟨?_, ?_, by rw [g10]; omega, fun r hr => ?_, by rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr],
    by rw [u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp], ?_⟩
  · rw [g10, hm, dw_write_self, t3, h5, s6a7, a5_6, x4]
    omega
  · rw [g10, h5]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u10.gpr, u9.other r hr.2.2.1, u8.other r hr.2.2.1, u7.other r hr.1, u6.other r hr.2.1, u5.other r hr.1,
      u4.other r hr.1, u3.other r hr.1, u2.other r hr.2.2.2, u1.other r hr.1]
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))

/-- Words `2 i` and `2 i + 1` of `P` doubled, with the bit `a2` and the carry
`a5`, plus `aᵢ²`. -/
theorem diag_ok {k : Nat} {b A : Addr} {s : State} (h : SqOk k b A s) {i : Nat} (hi : i < k)
    (h2 : (s.gpr .a2).toNat ≤ 1) (h5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block (diag k i)) s fun s' =>
      dw s'.mem b (SQ k + 8 * (2 * i)) + 2 ^ 64 * dw s'.mem b (SQ k + 8 * (2 * i + 1)) +
          2 ^ 64 * 2 ^ 64 * ((s'.gpr .a2).toNat + (s'.gpr .a5).toNat) =
        2 * (dw s.mem b (SQ k + 8 * (2 * i)) + 2 ^ 64 * dw s.mem b (SQ k + 8 * (2 * i + 1))) +
          ((s.gpr .a2).toNat + (s.gpr .a5).toNat) + dw s.mem A (8 * i) * dw s.mem A (8 * i) ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ (s'.gpr .a5).toNat ≤ 1 ∧
      (∀ r, r ∉ [.t0, .a1, .a2, .a4, .a5, .a6, .a7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * (2 * i)), 16⟩] s.mem s'.mem := by
  have k7 := h.k7
  have k30 := h.k30
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
  have hc := h.ctx
  unfold diag
  refine wp_ld (by omega) (by rw [h.a]) (al8 h.aal (by omega)) (h.ain _ (by omega)) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ctx_of hc (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [u3.wr, u2.wr, u1.wr])
  have a2_3 : s3.gpr .a2 = s.gpr .a2 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have a5_3 : s3.gpr .a5 = s.gpr .a5 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine WP.block_append (WP.mono (dword_ok hc3 k7 k30 (j := 2 * i) (x := .t0) (bi := .a2) (bo := .a4) (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a2_3]; exact h2) (by rw [a5_3]; exact h5)) fun s4 ⟨e4, c4, b4, g4, rd4, wr4, sp4, f4⟩ => ?_)
  have hc4 : Ctx b s4 := ctx_of hc3 (g4 _ (by decide)) wr4
  refine WP.mono (dword_ok hc4 k7 k30 (j := 2 * i + 1) (x := .a1) (bi := .a4) (bo := .a2) (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    b4 c4) fun s5 ⟨e5, c5, b5, g5, rd5, wr5, sp5, f5⟩ => ?_
  -- The words of the square of `aᵢ`.
  have hp := mul_words (s1.gpr .a6) (s1.gpr .a6)
  have hai : (s1.gpr .a6).toNat = dw s.mem A (8 * i) := by rw [u1.gpr]; rfl
  have lo : s3.gpr .t0 = s1.gpr .a6 * s1.gpr .a6 := by rw [u3.other _ (by decide), u2.gpr]
  have hi' : s4.gpr .a1 = BitVec.ofNat 64 ((s1.gpr .a6).toNat * (s1.gpr .a6).toNat / 2 ^ 64) := by
    rw [g4 _ (by decide), u3.gpr, u2.other _ (by decide)]
  have w1 : dw s4.mem b (SQ k + 8 * (2 * i + 1)) = dw s.mem b (SQ k + 8 * (2 * i + 1)) := by
    rw [dw_frame f4 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m3]
  have w0 : dw s5.mem b (SQ k + 8 * (2 * i)) = dw s4.mem b (SQ k + 8 * (2 * i)) :=
    dw_frame f5 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)
  rw [lo, a2_3, a5_3, m3] at e4
  rw [hi', w1] at e5
  rw [hai] at hp
  refine ⟨?_, b5, c5, fun r hr => ?_, by rw [rd5, rd4, u3.rd, u2.rd, u1.rd], by rw [wr5, wr4, u3.wr, u2.wr, u1.wr],
    by rw [sp5, sp4, u3.sp, u2.sp, u1.sp], ?_⟩
  · rw [w0]
    rw [hai] at e5
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g5 r (by simp [hr.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      g4 r (by simp [hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      u3.other r hr.2.1, u2.other r hr.1, u1.other r hr.2.2.2.2.2.1]
  · rw [← m3]
    exact (f4.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩).trans
      (f5.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega) (by omega)⟩)

/-- After `i` steps of the doubling and the squares, from `sR`. -/
structure DiagInv (k : Nat) (b A : Addr) (sR : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.t0, .a1, .a2, .a4, .a5, .a6, .a7] → s.gpr r = sR.gpr r
  rd : s.rd = sR.rd
  wr : s.wr = sR.wr
  sp : s.sp = sR.sp
  frame : Frame [PR k b] sR.mem s.mem
  rest : ∀ j, 2 * i ≤ j → j < 2 * k → dw s.mem b (SQ k + 8 * j) = dw sR.mem b (SQ k + 8 * j)
  c2 : (s.gpr .a2).toNat ≤ 1
  c5 : (s.gpr .a5).toNat ≤ 1
  val : pv k s.mem b 0 (2 * i) + (2 ^ 64) ^ (2 * i) * ((s.gpr .a2).toNat + (s.gpr .a5).toNat) =
    2 * pv k sR.mem b 0 (2 * i) + sumN (fun j => dw sR.mem A (8 * j) * dw sR.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) i

theorem diags_ok {k : Nat} {b A : Addr} {sR : State} (h : SqOk k b A sR) (h2 : sR.gpr .a2 = 0)
    (h5 : sR.gpr .a5 = 0) :
    ∀ i ≤ k, WP isa (.block ((List.range i).flatMap (diag k))) sR (DiagInv k b A sR i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl,
      by rw [h2]; decide, by rw [h5]; decide, by simp [pv, colsV, sumN, h2, h5]⟩
  | i + 1, hi => by
    have k7 := h.k7
    have k30 := h.k30
    obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (diags_ok h h2 h5 i (by omega)) fun s hs => ?_)
    have hS : SqOk k b A s := h.of (hs.gpr _ (by decide)) (hs.gpr _ (by decide)) hs.rd hs.wr
    refine WP.mono (diag_ok hS (i := i) (by omega) hs.c2 hs.c5) fun s' ⟨e, c2', c5', g', rd', wr', sp', f'⟩ => ?_
    have out : ∀ j, (j < 2 * i ∨ 2 * i + 2 ≤ j) → j < 2 * k →
        dw s'.mem b (SQ k + 8 * j) = dw s.mem b (SQ k + 8 * j) := fun j hj hj' =>
      dw_frame f' fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact Offset.disjoint b (by omega) (by omega) (by omega)
    have hA : dw s.mem A (8 * i) = dw sR.mem A (8 * i) := dwA_frame hs.frame k7 k30 h.adis (by omega)
    refine ⟨fun r hr => by rw [g' r hr, hs.gpr r hr], by rw [rd', hs.rd], by rw [wr', hs.wr], by rw [sp', hs.sp],
      hs.frame.trans (f'.sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega) (by omega)⟩),
      fun j hj hj' => by rw [out j (.inr (by omega)) hj', hs.rest j (by omega) hj'], c2', c5', ?_⟩
    have hv := hs.val
    have p0 := hs.rest (2 * i) (Nat.le_refl _) (by omega)
    have p1 := hs.rest (2 * i + 1) (by omega) (by omega)
    have low : pv k s'.mem b 0 (2 * i) = pv k s.mem b 0 (2 * i) :=
      colsV_congr fun j hj => by rw [Nat.zero_add, out j (.inl hj) (by omega)]
    show pv k s'.mem b 0 (2 * i + 1 + 1) + (2 ^ 64) ^ (2 * i + 1 + 1) * _ =
      2 * pv k sR.mem b 0 (2 * i + 1 + 1) + (sumN _ i + _)
    simp only [pv, colsV_succ, Nat.zero_add] at low hv ⊢
    rw [low]
    rw [hA, p0, p1] at e
    generalize colsV (fun i => dw s.mem b (SQ k + 8 * i)) (2 * i) = X at hv ⊢
    generalize colsV (fun i => dw sR.mem b (SQ k + 8 * i)) (2 * i) = Y at hv ⊢
    generalize sumN (fun j => dw sR.mem A (8 * j) * dw sR.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) i = Z at hv ⊢
    generalize dw s'.mem b (SQ k + 8 * (2 * i)) = r0 at e ⊢
    generalize dw s'.mem b (SQ k + 8 * (2 * i + 1)) = r1 at e ⊢
    generalize dw sR.mem b (SQ k + 8 * (2 * i)) = w0 at e ⊢
    generalize dw sR.mem b (SQ k + 8 * (2 * i + 1)) = w1 at e ⊢
    generalize (s'.gpr .a2).toNat + (s'.gpr .a5).toNat = c' at e ⊢
    generalize (s.gpr .a2).toNat + (s.gpr .a5).toNat = c at e hv
    generalize dw sR.mem A (8 * i) = ai at e ⊢
    have E1 : ((2 : Nat) ^ 64) ^ (2 * i + 1 + 1) = (2 ^ 64) ^ (2 * i) * (2 ^ 64 * 2 ^ 64) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    have E0 : ((2 : Nat) ^ 64) ^ (2 * i + 1) = (2 ^ 64) ^ (2 * i) * 2 ^ 64 := Nat.pow_succ ..
    rw [E1, E0]
    generalize ((2 : Nat) ^ 64) ^ (2 * i) = P at hv ⊢
    generalize (2 : Nat) ^ 64 = E at e ⊢
    calc X + P * r0 + P * E * r1 + P * (E * E) * c' = X + P * (r0 + E * r1 + E * E * c') := by grind
      _ = X + P * (2 * (w0 + E * w1) + c + ai * ai) := by rw [e]
      _ = (X + P * c) + 2 * (P * w0 + P * E * w1) + ai * ai * P := by grind
      _ = _ := by rw [hv]; grind

/-- `P = a²`. -/
theorem sqr_ok {k : Nat} {b A : Addr} {s : State} (h : SqOk k b A s) :
    WP isa (.block (sqr k)) s fun s' =>
      (∀ r, r ∉ [.t0, .a1, .t3, .a2, .a4, .a5, .a6, .a7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [PR k b] s.mem s'.mem ∧ pv k s'.mem b 0 (2 * k) = xv s.mem A k * xv s.mem A k := by
  have k7 := h.k7
  have k30 := h.k30
  unfold sqr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (zeroP_ok h.ctx k7 k30) fun s1 ⟨g1, rd1, wr1, sp1, f1, z1⟩ => ?_)
  have h1 : SqOk k b A s1 := h.of (g1 _ (by decide)) (g1 _ (by decide)) rd1 wr1
  refine WP.block_append (WP.mono (rows_ok h1 z1 (k - 1) (Nat.le_refl _)) fun s2 h2 => ?_)
  refine wp_li (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => ?_
  have h4 : SqOk k b A s4 := h1.of (by rw [u4.other _ (by decide), u3.other _ (by decide), h2.gpr _ (by decide)])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), h2.gpr _ (by decide)]) (by rw [u4.rd, u3.rd, h2.rd])
    (by rw [u4.wr, u3.wr, h2.wr])
  refine WP.mono (diags_ok h4 (by rw [u4.other _ (by decide), u3.gpr]; rfl) (by rw [u4.gpr]; rfl) k (Nat.le_refl _))
    fun s5 h5 => ?_
  have m4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  have fr : Frame [PR k b] s.mem s4.mem := by rw [m4]; exact f1.trans h2.frame
  have hA : ∀ i < k, dw s4.mem A (8 * i) = dw s.mem A (8 * i) := fun i hi => dwA_frame fr k7 k30 h.adis hi
  have hA1 : ∀ i < k, dw s1.mem A (8 * i) = dw s.mem A (8 * i) := fun i hi => dwA_frame f1 k7 k30 h.adis hi
  refine ⟨fun r hr => ?_, by rw [h5.rd, u4.rd, u3.rd, h2.rd, rd1], by rw [h5.wr, u4.wr, u3.wr, h2.wr, wr1],
    by rw [h5.sp, u4.sp, u3.sp, h2.sp, sp1], fr.trans h5.frame, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h5.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2]), u4.other r hr.2.2.2.2.2.1, u3.other r hr.2.2.2.1,
      h2.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      g1 r hr.2.2.2.2.2.2.2]
  · have hv := h5.val
    have hr := h2.val
    rw [← m4] at hr
    rw [hr] at hv
    -- The rows and the squares as `a²`.
    have hlast : sumN (rowTerm (fun j => dw s1.mem A (8 * j)) k) (k - 1) =
        sumN (rowTerm (fun j => dw s1.mem A (8 * j)) k) k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, sumN]
      simp [rowTerm, colsV]
    rw [hlast, rows_sum] at hv
    have ha1 : ∀ j < k, dw s1.mem A (8 * j) = dw s.mem A (8 * j) := fun j hj => hA1 _ (by omega)
    have ha4 : ∀ j < k, dw s4.mem A (8 * j) = dw s.mem A (8 * j) := fun j hj => hA _ (by omega)
    rw [sumN_congr (g := fun j => dw s1.mem A (8 * j) * (2 ^ 64) ^ j * colsV (fun j => dw s1.mem A (8 * j)) j)
        (h := fun j => dw s.mem A (8 * j) * (2 ^ 64) ^ j * colsV (fun j => dw s.mem A (8 * j)) j)
        fun j hj => by rw [ha1 j hj, colsV_congr fun i hi => ha1 i (by omega)],
      sumN_congr (g := fun j => dw s4.mem A (8 * j) * dw s4.mem A (8 * j) * (2 ^ 64) ^ (2 * j))
        (h := fun j => dw s.mem A (8 * j) * dw s.mem A (8 * j) * (2 ^ 64) ^ (2 * j))
        fun j hj => by rw [ha4 j hj]] at hv
    have hsq := sq_sum (fun j => dw s.mem A (8 * j)) k
    have hlt := colsV_lt (fun j => dw s.mem A (8 * j)) (fun _ => dw_lt _ _ _) k
    have hlt2 : xv s.mem A k * xv s.mem A k < (2 ^ 64) ^ (2 * k) := by
      rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_two]
      exact Nat.mul_lt_mul_of_lt_of_lt hlt hlt
    simp only [xv] at hlt2 ⊢
    generalize sumN (fun j => dw s.mem A (8 * j) * (2 ^ 64) ^ j * colsV (fun j => dw s.mem A (8 * j)) j) k = X at hv hsq
    generalize sumN (fun j => dw s.mem A (8 * j) * dw s.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) k = D at hv hsq
    generalize colsV (fun j => dw s.mem A (8 * j)) k * colsV (fun j => dw s.mem A (8 * j)) k = S at hsq hlt2 ⊢
    have hpos : 0 < ((2 : Nat) ^ 64) ^ (2 * k) := Nat.pow_pos (by decide)
    generalize ((2 : Nat) ^ 64) ^ (2 * k) = E at hv hlt2 hpos
    generalize (s5.gpr .a2).toNat + (s5.gpr .a5).toNat = c at hv
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · omega
    · have : E ≤ E * c := Nat.le_mul_of_pos_right _ hc
      omega

/-! ## The reduction -/

/-- A round of the reduction in place: `P[i …] += q m` for `q = Pᵢ m'`, with
the carry `a2` into word `i + k`, its carry out in `a2`. -/
theorem sred_ok {k : Nat} {b : Addr} {m' : Nat} {s : State} (h : RedOk k b m' s) {i : Nat} (hi : i < k)
    (ha2 : (s.gpr .a2).toNat ≤ 1) :
    WP isa (.block (sred k i)) s fun s' =>
      (∀ r, r ∉ .a4 :: .a2 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * (i + 1)), 8 * k⟩] s.mem s'.mem ∧ (s'.gpr .a2).toNat ≤ 1 ∧
      2 ^ 64 * (colsV (fun j => dw s'.mem b (SQ k + 8 * (i + 1) + 8 * j)) k + (2 ^ 64) ^ k * (s'.gpr .a2).toNat) =
        dw s.mem b (SQ k + 8 * i) + 2 ^ 64 * colsV (fun j => dw s.mem b (SQ k + 8 * (i + 1) + 8 * j)) k +
          (2 ^ 64) ^ k * (s.gpr .a2).toNat + dw s.mem b (SQ k + 8 * i) * m' % 2 ^ 64 * nv k s.mem b := by
  have k7 := h.k7
  have k30 := h.k30
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  have hb := h.nowrap
  have hc := h.ctx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold sred
  simp only [Nat.add_sub_cancel]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_mul fun s2 u2 => ?_
  refine ld_ok (ctx_of hc (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr]))
    (by omega) (by omega) fun s3 u3 => wp_mulhu fun s4 u4 => wp_li (by decide) fun s5 u5 =>
      wp_sltu fun s6 u6 => wp_add fun s7 u7 => ?_
  show WP isa (.block (((List.range j).flatMap fun i' =>
      macStep .a3 (N (j + 1) + 8 + 8 * i') (SQ (j + 1) + 8 * (i + 1) + 8 * i') (SQ (j + 1) + 8 * (i + 1) + 8 * i')) ++
    [.load .d .a7 .a3 (SQ (j + 1) + 8 * (i + (j + 1))), .add .t0 .a7 .a5, .sltu .t3 .t0 .a5, .add .t0 .t0 .a2,
      .sltu .a2 .t0 .a2, .add .a2 .a2 .t3, .store .d .t0 .a3 (SQ (j + 1) + 8 * (i + (j + 1)))])) s7 _
  -- What the quotient block leaves.
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have g7 : ∀ r, r ∉ .a4 :: clobS → s7.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other r hr.2.2.2.2.1, u6.other r hr.2.2.2.1, u5.other r hr.2.2.2.1, u4.other r hr.2.2.2.2.1,
      u3.other r hr.2.2.2.2.2.1, u2.other r hr.1, u1.other r hr.2.2.2.2.2.2]
  have hc7 : Ctx b s7 := ctx_of hc (g7 _ (by decide)) (by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  have hT0 : (s1.gpr .a7).toNat = dw s.mem b (SQ (j + 1) + 8 * i) := by rw [u1.gpr]; rfl
  have hq : (s7.gpr .a4).toNat = dw s.mem b (SQ (j + 1) + 8 * i) * m' % 2 ^ 64 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
  have hn0 : (s3.gpr .a6).toNat = dw s.mem b (N (j + 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, show N (j + 1) = N (j + 1) + 8 * 0 by rfl]; rfl
  have hC0 : 2 ^ 64 * (s7.gpr .a5).toNat = dw s.mem b (SQ (j + 1) + 8 * i) +
      dw s.mem b (SQ (j + 1) + 8 * i) * m' % 2 ^ 64 * dw s.mem b (N (j + 1)) := by
    have hp := mul_words (s4.gpr .a4) (s3.gpr .a6)
    have e4a : s4.gpr .a4 = s3.gpr .a4 := u4.other _ (by decide)
    have e3a : (s3.gpr .a4).toNat = dw s.mem b (SQ (j + 1) + 8 * i) * m' % 2 ^ 64 := by
      rw [u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
    have e4 : s4.gpr .a5 = BitVec.ofNat 64 ((s3.gpr .a4).toNat * (s3.gpr .a6).toNat / 2 ^ 64) := by
      rw [u4.gpr]
    have e6 : (s6.gpr .t3).toNat = if dw s.mem b (SQ (j + 1) + 8 * i) = 0 then 0 else 1 := by
      rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide), u2.other _ (by decide), sltu0_toNat, hT0]
    rw [e4a, e3a, hn0] at hp
    rw [BitVec.toNat_mul, e3a, hn0] at hp
    obtain ⟨c1, c2⟩ := c0_nat (dw_lt _ _ _) (dw_lt _ _ _) h.inv hp e6
    rw [u7.gpr, BitVec.toNat_add, u6.other _ (by decide), u5.other _ (by decide), e4, e3a, hn0,
      Nat.mod_eq_of_lt c2]
    exact c1
  -- The row.
  have hR : IRowOk b b .a3 (N (j + 1) + 8) (SQ (j + 1) + 8 * (i + 1)) j s7 :=
    { ctx := hc7
      nowrap := hb
      hx := hc7.a3
      hxb := by decide
      hxo := fun i' hi' => by omega
      xal := fun i' _ => al8 hc7.al (by omega)
      xin := fun i' hi' => hc7.inR (by omega)
      xdis := fun i' hi' j' hj' => Offset.disjoint b (.inl (by omega)) (by omega) (by omega)
      top := by omega
      t8 := by omega }
  refine WP.block_append (WP.mono (irow_ok hR j (Nat.le_refl _)) fun s8 h8 => ?_)
  have hc8 : Ctx b s8 := ctx_of hc7 (h8.gpr _ (by decide)) h8.wr
  refine ld_ok hc8 (by omega) (by omega) fun s9 u9 => wp_add fun s10 u10 => wp_sltu fun s11 u11 =>
    wp_add fun s12 u12 => wp_sltu fun s13 u13 => wp_add fun s14 u14 => ?_
  have hc14 : Ctx b s14 := ctx_of hc8 (by rw [u14.other _ (by decide), u13.other _ (by decide),
    u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide)])
    (by rw [u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr])
  refine sd_ok hc14 (by omega) (by omega) fun s15 u15 => WP.block_nil ?_
  have m14 : s14.mem = s8.mem := by rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem]
  have m15 : s15.mem = s8.mem.writeW (b + BitVec.ofNat 64 (SQ (j + 1) + 8 * (i + (j + 1)))) (s14.gpr .t0) := by
    rw [u15.mem, m14]
  have g15 : s15.gpr = s14.gpr := u15.gpr
  have a2_7 : s7.gpr .a2 = s.gpr .a2 := g7 _ (by decide)
  have a2_11 : s11.gpr .a2 = s.gpr .a2 := by
    rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), h8.gpr _ (by decide), a2_7]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g15, u14.other r hr.2.1, u13.other r hr.2.1, u12.other r hr.2.2.1, u11.other r hr.2.2.2.2.1,
      u10.other r hr.2.2.1, u9.other r hr.2.2.2.2.2.2.2, h8.gpr r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      g7 r (by simp [hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]
  · rw [u15.rd, u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, h8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u15.wr, u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, h8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u15.sp, u14.sp, u13.sp, u12.sp, u11.sp, u10.sp, u9.sp, h8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  · rw [m15, ← m7]
    refine (h8.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  -- The tail's sums.
  all_goals
    have e10 := carry (s9.gpr .a7) (s9.gpr .a5)
    have l10 := carry_le (s9.gpr .a7 + s9.gpr .a5 < s9.gpr .a5)
    have t0_11 : s11.gpr .t0 = s9.gpr .a7 + s9.gpr .a5 := by rw [u11.other _ (by decide), u10.gpr]
    have t3_11 : s11.gpr .t3 = if s9.gpr .a7 + s9.gpr .a5 < s9.gpr .a5 then 1 else 0 := by
      rw [u11.gpr, u10.gpr, u10.other _ (by decide)]
    have e12 := carry (s11.gpr .t0) (s11.gpr .a2)
    have l12 := carry_le (s11.gpr .t0 + s11.gpr .a2 < s11.gpr .a2)
    have a2_13 : s13.gpr .a2 = if s11.gpr .t0 + s11.gpr .a2 < s11.gpr .a2 then 1 else 0 := by
      rw [u13.gpr, u12.gpr, u12.other .a2 (by decide)]
    have t3_13 : s13.gpr .t3 = s11.gpr .t3 := by rw [u13.other _ (by decide), u12.other _ (by decide)]
    have t0_14 : s14.gpr .t0 = s11.gpr .t0 + s11.gpr .a2 := by
      rw [u14.other _ (by decide), u13.other _ (by decide), u12.gpr]
    have a2_14 : (s14.gpr .a2).toNat = (s13.gpr .a2).toNat + (s11.gpr .t3).toNat := by
      rw [u14.gpr, BitVec.toNat_add, t3_13, Nat.mod_eq_of_lt (by
        rw [a2_13, t3_11]; have := carry_le (s11.gpr .t0 + s11.gpr .a2 < s11.gpr .a2)
        have := carry_le (s9.gpr .a7 + s9.gpr .a5 < s9.gpr .a5); omega)]
    rw [← t3_11] at e10 l10
    rw [← a2_13] at e12 l12
    rw [t0_11] at e12
    rw [a2_11] at e12
  · rw [g15, a2_14]
    have := (s9.gpr .a7 + s9.gpr .a5).isLt
    have := (s.gpr .a2).isLt
    have := (s9.gpr .a7 + s9.gpr .a5 + s.gpr .a2).isLt
    omega
  · -- The value.
    have hv := h8.val
    rw [colsV_add', colsV_mul, m7, hq] at hv
    have fr : ∀ d, SQ (j + 1) + 8 * (i + (j + 1)) ≤ d → d + 8 ≤ 2048 → dw s8.mem b d = dw s.mem b d :=
      fun d hd hd' => by
        rw [dw_frame h8.frame fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m7]
    have hw9 : (s9.gpr .a7).toNat = dw s.mem b (SQ (j + 1) + 8 * (i + (j + 1))) := by
      rw [u9.gpr, ← fr _ (Nat.le_refl _) (by omega)]; rfl
    have a5_9 : s9.gpr .a5 = s8.gpr .a5 := u9.other _ (by decide)
    have hlow : colsV (fun x => dw s15.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * x)) j =
        colsV (fun x => dw s8.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * x)) j :=
      colsV_congr fun x hx => by rw [m15, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have htop : dw s15.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * j) = (s14.gpr .t0).toNat := by
      rw [m15, show SQ (j + 1) + 8 * (i + 1) + 8 * j = SQ (j + 1) + 8 * (i + (j + 1)) by omega, dw_write_self]
    have htop0 : dw s.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * j) = dw s.mem b (SQ (j + 1) + 8 * (i + (j + 1))) := by
      rw [show SQ (j + 1) + 8 * (i + 1) + 8 * j = SQ (j + 1) + 8 * (i + (j + 1)) by omega]
    have hN : nv (j + 1) s.mem b = dw s.mem b (N (j + 1)) +
        2 ^ 64 * colsV (fun x => dw s.mem b (N (j + 1) + 8 + 8 * x)) j := by
      rw [nv, colsV_shift]
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [colsV_congr (g := fun x => dw s.mem b (N (j + 1) + 8 + 8 * x)) fun x _ => by
        rw [show N (j + 1) + 8 * (x + 1) = N (j + 1) + 8 + 8 * x by omega]]
    rw [g15, a2_14, colsV_succ, colsV_succ, hlow, htop, t0_14, t0_11, a2_11, hN, htop0]
    rw [hw9] at e10
    have a5n : (s9.gpr .a5).toNat = (s8.gpr .a5).toNat := by rw [a5_9]
    rw [a5n] at e10
    generalize (s9.gpr .a7 + s9.gpr .a5 + s.gpr .a2).toNat = t12 at e12 ⊢
    generalize (s9.gpr .a7 + s9.gpr .a5).toNat = t10 at e10 e12
    generalize (s11.gpr .t3).toNat = t3 at e10 ⊢
    generalize (s13.gpr .a2).toNat = c13 at e12 ⊢
    generalize colsV (fun x => dw s8.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * x)) j = R8 at hv ⊢
    generalize colsV (fun x => dw s.mem b (SQ (j + 1) + 8 * (i + 1) + 8 * x)) j = Pl at hv ⊢
    generalize colsV (fun x => dw s.mem b (N (j + 1) + 8 + 8 * x)) j = Nr at hv ⊢
    generalize dw s.mem b (SQ (j + 1) + 8 * i) * m' % 2 ^ 64 = q at hv hC0 ⊢
    generalize (s8.gpr .a5).toNat = a58 at hv e10
    generalize (s7.gpr .a5).toNat = a57 at hv hC0
    generalize dw s.mem b (SQ (j + 1) + 8 * (i + (j + 1))) = PK at e10 ⊢
    generalize dw s.mem b (SQ (j + 1) + 8 * i) = P0 at hC0 ⊢
    generalize dw s.mem b (N (j + 1)) = N0 at hC0 ⊢
    generalize (s.gpr .a2).toNat = a2 at e12 ⊢
    have p1 : ((2 : Nat) ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 := Nat.pow_succ ..
    rw [p1]
    generalize ((2 : Nat) ^ 64) ^ j = X at hv ⊢
    generalize (2 : Nat) ^ 64 = E at hv hC0 e10 e12 ⊢
    calc E * (R8 + X * t12 + X * E * (c13 + t3))
        = E * R8 + E * X * (t12 + E * c13) + E * X * E * t3 := by grind
      _ = E * R8 + E * X * (t10 + a2) + E * X * E * t3 := by rw [e12]
      _ = E * R8 + E * X * (t10 + E * t3) + E * X * a2 := by grind
      _ = E * R8 + E * X * (PK + a58) + E * X * a2 := by rw [e10]
      _ = E * (R8 + X * a58) + E * X * PK + E * X * a2 := by grind
      _ = E * (Pl + Nr * q + a57) + E * X * PK + E * X * a2 := by rw [hv]
      _ = E * a57 + E * Pl + E * Nr * q + E * X * PK + E * X * a2 := by grind
      _ = (P0 + q * N0) + E * Pl + E * Nr * q + E * X * PK + E * X * a2 := by rw [hC0]
      _ = _ := by grind

/-- After `i` rounds of the reduction from `s0`, of `V` (the product) modulo `M`. -/
structure SRedInv (k : Nat) (b : Addr) (M V : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ .a4 :: .a2 :: clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [PR k b] s0.mem s.mem
  c2 : (s.gpr .a2).toNat ≤ 1
  val : ∃ Q, Q < (2 ^ 64) ^ i ∧
    (2 ^ 64) ^ i * (pv k s.mem b i (2 * k - i) + (2 ^ 64) ^ k * (s.gpr .a2).toNat) = V + Q * M

theorem nv_PR {k : Nat} {b : Addr} {m m' : Mem} (hf : Frame [PR k b] m m') (hk : 7 ≤ k) (hk' : k ≤ 30) :
    nv k m' b = nv k m b := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  exact colsV_congr fun i hi => dw_frame hf fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)

/-- The rounds of the reduction. -/
theorem srounds_ok {k : Nat} {b : Addr} {m' M V : Nat} {s0 : State} (h : RedOk k b m' s0)
    (hM : nv k s0.mem b = M) (hV : pv k s0.mem b 0 (2 * k) = V) (h2 : s0.gpr .a2 = 0) :
    ∀ i ≤ k, WP isa (.block ((List.range i).flatMap (sred k))) s0 (SRedInv k b M V s0 i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by rw [h2]; decide,
      ⟨0, by decide, by
        simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero, h2, Nat.zero_mul, Nat.add_zero]
        exact hV⟩⟩
  | i + 1, hi => by
    have k7 := h.k7
    have k30 := h.k30
    obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (srounds_ok h hM hV h2 i (by omega)) fun s hs => ?_)
    have hN : nv k s.mem b = M := by rw [nv_PR hs.frame k7 k30, hM]
    have hinv : dw s.mem b (N k) * m' % 2 ^ 64 = 2 ^ 64 - 1 := by
      rw [dw_frame hs.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)]
      exact h.inv
    have hR : RedOk k b m' s :=
      ⟨ctx_of h.ctx (hs.gpr _ (by decide)) hs.wr, h.nowrap, by rw [hs.gpr _ (by decide), h.t6], h.m'lt,
        hinv, k7, k30⟩
    refine WP.mono (sred_ok hR (i := i) (by omega) hs.c2) fun s' ⟨g', rd', wr', sp', f', c2', e'⟩ => ?_
    refine ⟨fun r hr => by rw [g' r hr, hs.gpr r hr], by rw [rd', hs.rd], by rw [wr', hs.wr], by rw [sp', hs.sp],
      hs.frame.trans (f'.sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega) (by omega)⟩), c2', ?_⟩
    obtain ⟨Q, hQ, hv⟩ := hs.val
    refine ⟨Q + (2 ^ 64) ^ i * (dw s.mem b (SQ k + 8 * i) * m' % 2 ^ 64), ?_, ?_⟩
    · have : dw s.mem b (SQ k + 8 * i) * m' % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
      have : (2 ^ 64) ^ i * (dw s.mem b (SQ k + 8 * i) * m' % 2 ^ 64 + 1) ≤ (2 ^ 64) ^ i * 2 ^ 64 :=
        Nat.mul_le_mul_left _ (by omega)
      rw [show ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 from Nat.pow_succ ..]
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    · -- The words above the round's.
      have up : colsV (fun x => dw s'.mem b (SQ k + 8 * (i + 1 + (k + x)))) (k - i - 1) =
          colsV (fun x => dw s.mem b (SQ k + 8 * (i + (k + 1 + x)))) (k - i - 1) :=
        colsV_congr fun x hx => by
          rw [show i + 1 + (k + x) = i + (k + 1 + x) by omega]
          exact dw_frame f' fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
      have mid' : colsV (fun x => dw s'.mem b (SQ k + 8 * (i + 1) + 8 * x)) k =
          colsV (fun x => dw s'.mem b (SQ k + 8 * (i + 1 + x))) k :=
        colsV_congr fun x _ => by rw [show SQ k + 8 * (i + 1) + 8 * x = SQ k + 8 * (i + 1 + x) by omega]
      have mid : colsV (fun x => dw s.mem b (SQ k + 8 * (i + 1) + 8 * x)) k =
          colsV (fun x => dw s.mem b (SQ k + 8 * (i + (x + 1)))) k :=
        colsV_congr fun x _ => by rw [show SQ k + 8 * (i + 1) + 8 * x = SQ k + 8 * (i + (x + 1)) by omega]
      rw [mid', mid, hN] at e'
      rw [pv, show 2 * k - (i + 1) = k + (k - i - 1) by omega, colsV_split, up]
      rw [pv, show 2 * k - i = (k + 1) + (k - i - 1) by omega, colsV_split, colsV_shift] at hv
      simp only [Nat.add_zero] at hv
      generalize colsV (fun x => dw s'.mem b (SQ k + 8 * (i + 1 + x))) k = R' at e' ⊢
      generalize colsV (fun x => dw s.mem b (SQ k + 8 * (i + (k + 1 + x)))) (k - i - 1) = Up at hv ⊢
      generalize colsV (fun x => dw s.mem b (SQ k + 8 * (i + (x + 1)))) k = R at e' hv
      generalize dw s.mem b (SQ k + 8 * i) * m' % 2 ^ 64 = q at e' ⊢
      generalize dw s.mem b (SQ k + 8 * i) = P0 at e' hv
      generalize (s'.gpr .a2).toNat = c' at e' ⊢
      generalize (s.gpr .a2).toNat = c at e' hv
      rw [show ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 from Nat.pow_succ ..,
        show ((2 : Nat) ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from Nat.pow_succ ..] at *
      generalize ((2 : Nat) ^ 64) ^ i = Ei at hv ⊢
      generalize ((2 : Nat) ^ 64) ^ k = Ek at hv e' ⊢
      generalize (2 : Nat) ^ 64 = E at hv e' ⊢
      calc Ei * E * (R' + Ek * Up + Ek * c') = Ei * (E * (R' + Ek * c')) + Ei * E * Ek * Up := by grind
        _ = Ei * (P0 + E * R + Ek * c + q * M) + Ei * E * Ek * Up := by rw [e']
        _ = Ei * (P0 + E * R + Ek * E * Up + Ek * c) + Ei * q * M := by grind
        _ = V + Q * M + Ei * q * M := by rw [hv]
        _ = _ := by grind

/-! ## The result into `T` -/

/-- After `j` words of the copy from `s0`. -/
structure CopyInv (k : Nat) (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .a7 → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * j⟩] s0.mem s.mem
  val : ∀ x < j, dw s.mem b (T k + 8 * x) = dw s0.mem b (SQ k + 8 * k + 8 * x)

theorem copy_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 7 ≤ k) (hk' : k ≤ 30) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun x =>
      [.load .d .a7 .a3 (SQ k + 8 * k + 8 * x), .store .d .a7 .a3 (T k + 8 * x)])) s0 (CopyInv k b s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
    obtain ⟨t8, -⟩ := T_facts k (by omega) hk'
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (copy_ok hc hk hk' j (by omega)) fun s h => ?_)
    have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
    refine ld_ok hcs (by omega) (by omega) fun s1 u1 => ?_
    refine sd_ok (ctx_of hcs (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 => WP.block_nil ?_
    have hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * j)) (s1.gpr .a7) := by rw [u2.mem, u1.mem]
    have hw : (s1.gpr .a7).toNat = dw s0.mem b (SQ k + 8 * k + 8 * j) := by
      rw [u1.gpr]
      show dw s.mem b _ = _
      exact dw_frame h.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
    refine ⟨fun r hr => by rw [u2.gpr, u1.other r hr, h.gpr r hr], by rw [u2.rd, u1.rd, h.rd],
      by rw [u2.wr, u1.wr, h.wr], by rw [u2.sp, u1.sp, h.sp], ?_, fun x hx => ?_⟩
    · rw [hm2]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by omega)
    · rw [hm2]
      by_cases hxj : x = j
      · subst hxj; rw [dw_write_self, hw]
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val x (by omega)

/-- `T` = the top `k` words of `P` and the carry `a2`. -/
theorem copyT_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 7 ≤ k) (hk' : k ≤ 30) :
    WP isa (.block (copyT k)) s0 fun s =>
      (∀ r, r ≠ .a7 → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧ s.sp = s0.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s.mem ∧
      tv k s.mem b (k + 1) = pv k s0.mem b k k + (2 ^ 64) ^ k * (s0.gpr .a2).toNat := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  obtain ⟨t8, -⟩ := T_facts k (by omega) hk'
  unfold copyT
  refine WP.block_append (WP.mono (copy_ok hc hk hk' k (Nat.le_refl _)) fun s h => ?_)
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  refine sd_ok hcs (by omega) (by omega) fun s1 u1 => WP.block_nil ?_
  have hm1 : s1.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * k)) (s.gpr .a2) := u1.mem
  refine ⟨fun r hr => by rw [u1.gpr, h.gpr r hr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp],
    ?_, ?_⟩
  · rw [hm1]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · rw [tv, colsV_succ, hm1, dw_write_self, h.gpr _ (by decide),
      colsV_congr (g := fun x => dw s0.mem b (SQ k + 8 * (k + x))) fun x hx => by
        rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), h.val x hx,
          show SQ k + 8 * k + 8 * x = SQ k + 8 * (k + x) by omega]]

/-! ## The square's operation -/

/-- `[t2] = [t4]² R⁻¹ mod m`, for operands and a result apart from the whole
own working space. -/
theorem sqrCore_ok {k m : Nat} {b A O : Addr} {s : State} (hC : CoreOk k b A A O s)
    (hAo : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b))
    (hOo : Region.Disjoint ⟨O, 8 * k⟩ (ownA k b))
    (hm : m < 2 ^ (64 * k)) (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1)
    (hB : xv s.mem A k < m) :
    WP isa (.block (sqrCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownA k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k < m ∧ ov s'.mem O k * 2 ^ (64 * k) % m = xv s.mem A k * xv s.mem A k % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  have hb := hC.nowrap
  unfold sqrCore
  simp only [List.append_assoc, List.singleton_append]
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  have hS1 : SqOk k b A s1 := ⟨hc1, hb, by rw [g1 _ (by decide), hC.a], hC.aal,
    by rw [rd1, wr1]; exact hC.ain, hAo, k7, k30⟩
  refine WP.block_append (WP.mono (sqr_ok hS1) fun s2 ⟨g2, rd2, wr2, sp2, f2, v2⟩ => ?_)
  refine wp_li64 (by decide) _ fun s3 e3 k3 => wp_li (by decide) fun s4 u4 => ?_
  have m4 : s4.mem = s2.mem := by rw [u4.mem, k3.2.1]
  have g4 : ∀ r, r ∉ [.a2, .t6, .a7] → s4.gpr r = s2.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.other r hr.1, k3.1 r (by simp [hr.2.1, hr.2.2])]
  have hc4 : Ctx b s4 := ctx_of hc1 (by rw [g4 _ (by decide), g2 _ (by decide)])
    (by rw [u4.wr, k3.2.2.2.1, wr2])
  have hN4 : ∀ i < k, dw s4.mem b (N k + 8 * i) = dw s1.mem b (N k + 8 * i) := fun i hi => by
    rw [m4]; exact dw_frame f2 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)
  have hR : RedOk k b (negInv m) s4 :=
    { ctx := hc4
      nowrap := hb
      t6 := by rw [u4.other _ (by decide), e3]
      m'lt := Nat.mod_lt _ (by decide)
      inv := by
        rw [show N k = N k + 8 * 0 by rfl, hN4 0 (by omega), w1 0 (by omega)]
        unfold negInv at hinv ⊢; exact hinv
      k7 := k7
      k30 := k30 }
  have hM : nv k s4.mem b = m := by rw [← nv1]; exact colsV_congr fun i hi => hN4 i hi
  have hA2 : xv s1.mem A k = xv s.mem A k :=
    colsV_congr fun i hi => dw_frame f1 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disj_sub (hAo i hi) (ownA_sub b (by omega) (by omega))
  refine WP.block_append (WP.mono (srounds_ok hR hM (by rw [m4, v2, hA2]) (by rw [u4.gpr]; rfl) k (Nat.le_refl _))
    fun s5 h5 => ?_)
  have hc5 : Ctx b s5 := ctx_of hc4 (h5.gpr _ (by decide)) h5.wr
  refine WP.block_append (WP.mono (copyT_ok hc5 k7 k30) fun s6 ⟨g6, rd6, wr6, sp6, f6, v6⟩ => ?_)
  have hc6 : Ctx b s6 := ctx_of hc5 (g6 _ (by decide)) wr6
  -- The value before the final subtraction.
  obtain ⟨Q, hQ, hv⟩ := h5.val
  rw [show 2 * k - k = k by omega, ← v6] at hv
  have hRk : ((2 : Nat) ^ 64) ^ k = 2 ^ (64 * k) := (Nat.pow_mul ..).symm
  rw [hRk] at hv hQ
  have hAlt : xv s.mem A k < 2 ^ (64 * k) := by
    rw [← hRk]; exact colsV_lt _ (fun _ => dw_lt _ _ _) k
  obtain ⟨hV2, hVm⟩ := mont_nat (V := tv k s6.mem b (k + 1)) (by rw [Nat.mul_comm]; exact hv) hAlt hB hQ
  have hNv6 : nv k s6.mem b = m := by
    rw [← hM]
    refine colsV_congr fun i hi => ?_
    rw [dw_frame f6 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)]
    exact dw_frame h5.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega)
  have gO : s6.gpr .t2 = O := by
    rw [g6 _ (by decide), h5.gpr _ (by decide), g4 _ (by decide), g2 _ (by decide), g1 _ (by decide), hC.o]
  have hCs : CsubOk k b O s6 :=
    { ctx := hc6
      nowrap := hb
      t2 := gO
      oal := hC.oal
      onw := hC.onw
      ow := by rw [wr6, h5.wr, u4.wr, k3.2.2.2.1, wr2, wr1]; exact hC.ow
      tdis := fun i hi => disj_symm (disj_sub hOo (ownA_sub b (by omega) (by omega)))
      ndis := fun i hi => disj_symm (disj_sub hOo (ownA_sub b (by omega) (by omega)))
      k7 := k7
      k30 := k30 }
  refine WP.mono (csub_ok hCs (by rw [hNv6]; exact hV2)) fun s7 ⟨g7, rd7, wr7, sp7, f7, v7⟩ => ?_
  rw [hNv6] at v7
  refine ⟨fun r hr => ?_, by rw [rd7, rd6, h5.rd, u4.rd, k3.2.2.1, rd2, rd1],
    by rw [wr7, wr6, h5.wr, u4.wr, k3.2.2.2.1, wr2, wr1],
    by rw [sp7, sp6, h5.sp, u4.sp, k3.2.2.2.2, sp2, sp1], ?_, by rw [v7]; exact Nat.mod_lt _ (by omega),
    by rw [v7]; exact hVm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g6 r hr.2.2.2.2.2.2.2.2,
      h5.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g4 r (by simp [hr.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g2 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]),
      g1 r (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · have sub : ∀ {d n : Nat}, T k ≤ d → d + n ≤ T k + 64 * k →
        ∀ r ∈ [(⟨b + BitVec.ofNat 64 d, n⟩ : Region)], ∃ r' ∈ [ownA k b, ⟨O, 8 * k⟩], Region.Sub r r' :=
      fun hd hn r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., ownA_sub b hd hn⟩
    have sub7 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region), ⟨O, 8 * k⟩],
        ∃ r' ∈ [ownA k b, ⟨O, 8 * k⟩], Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., ownA_sub b (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun x h => h⟩
    have f24 : Frame [ownA k b, ⟨O, 8 * k⟩] s.mem s4.mem := by
      rw [m4]
      exact (f1.sub (sub (by omega) (by omega))).trans (f2.sub (sub (by omega) (by omega)))
    exact ((f24.trans (h5.frame.sub (sub (by omega) (by omega)))).trans (f6.sub (sub (Nat.le_refl _) (by omega)))).trans
      (f7.sub sub7)

/-- The fast path of `mulSqFn`: the square when the operands are the same
pointer, else the product. -/
theorem mulSqFast_spec {k m : Nat} (hm : m < 2 ^ (64 * k))
    (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1) :
    FastSpec k (.ite (.eq .t4 .t5) (.block (sqrCore k m)) (.block (mulCore k m))) (fun _ B => B < m)
      (fun A B r => r < m ∧ r * 2 ^ (64 * k) % m = A * B % m) := by
  intro b A B O s hC hA hB hO hp
  refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun he => ?_) (fun _ => CoreSpec.fast (@mulCore_spec k m hm hinv) hC hA hB hO hp)
  have hAB : A = B := by rw [← hC.a, ← hC.b']; exact beq_iff_eq.mp he
  subst hAB
  exact WP.mono (sqrCore_ok hC hA hO hm hinv hp) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

end VG.Proof.Weierstrass.RISCV64.GenWide

/-! ## The contract by register -/

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X448.RISCV64.R64 (dw colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV rvOwn rvOwnEnd)

/-- `fnWith k fast core` meets a contract by register, from `fnWith_ok`. -/
theorem fnWith_rv {S : Modulus} (hk : 7 ≤ S.k) (hk' : S.k ≤ 30) {fast : Prog isa} {core : List Instr}
    {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop} (hfast : FastSpec S.k fast pre res)
    (hcore : CoreSpec S.k core pre res) {s : State} (hs : rvPre S s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fnWith S.k fast core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) S.k) ∧
      Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k) := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, rvOwn_gt (show 6 < S.k by omega)] at fo fa fb
  simp only [arg, numAt_xv] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ :=
    fnWith_ok hk hk' hfast hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame (by omega) hk' fo f⟩

theorem mulSq_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulSqFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnWith_rv hS.k7 hS.k30 (@mulSqFast_spec S.k S.m hS.lt hS.inv)
    (@mulCore_spec S.k S.m hS.lt hS.inv) hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩


theorem mulSqA_rv {S : Modulus} (hS : WideOk S) (s : State)
    (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV S)).pre s) :
    ∃ t s', Exec isa (mulSqFnA S.k S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv hS.k7 hS.k30
    (@mulSqFast_spec S.k S.m hS.lt hS.inv) hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, v1, v2, k⟩

end VG.Proof.Weierstrass.RISCV64.GenWide
