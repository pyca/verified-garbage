module

public import VerifiedGarbage.Impl.X25519.AArch64.Hybrid
public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Prod2
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mul
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# X25519 on AArch64: adding up the limbs of `DA` and `CB`

Untrusted: everything here is checked by Lean. `Hybrid.recombine` adds limb
`k` of `DA + CB` (or of `DA + 4p - CB`) into five words at bit `limbOff k`
(`place_ok`); with every limb below 2²⁹ no word overflows, so the words are the
limbs' exact value, which the 38-fold reduces modulo `p` (`recombine_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Hybrid
open VG.Impl.X25519.AArch64.Neon (limbOff)
open VG.Proof.Ed25519.AArch64 (read_x Scr word load_sc Keep F fold_ok store4_ok fe_st4 st4_outside clob Outside)
open VG.Proof.Ed25519.Word64 (val4)
open VG.Proof.X25519 (toFe toFe_congr fold256)

theorem place2_ok {s : State} {a b : Reg} {sh : Nat} (h0 : 0 < sh) (h64 : sh < 64)
    (ha14 : a ≠ .x14) (ha15 : a ≠ .x15) (hb14 : b ≠ .x14) (hb15 : b ≠ .x15) (hab : b ≠ a)
    (hno : (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + (s.gpr .x12).toNat * 2 ^ sh < 2 ^ 128) :
    WP isa (.block [.lsl .x .x14 .x12 sh, .lsr .x .x15 .x12 (64 - sh), .adds .x a a .x14, .adcs .x b b .x15]) s
      fun t => (t.gpr a).toNat + 2 ^ 64 * (t.gpr b).toNat =
          (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + (s.gpr .x12).toNat * 2 ^ sh ∧
        (∀ r, r ≠ a → r ≠ b → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨s.write .x .x14 (s.gpr .x12 <<< sh), by simp [exec, read_x, Size.bits, h64], ?_⟩
  refine WP.block_cons_iff.mpr ⟨(s.write .x .x14 (s.gpr .x12 <<< sh)).write .x .x15 (s.gpr .x12 >>> (64 - sh)),
    by simp [exec, read_x, Size.bits, show 64 - sh < 64 by omega, RegUpd.gpr_write_of_ne], ?_⟩
  generalize hS : (s.write .x .x14 (s.gpr .x12 <<< sh)).write .x .x15 (s.gpr .x12 >>> (64 - sh)) = s₂
  have g14 : s₂.gpr .x14 = s.gpr .x12 <<< sh := by rw [← hS]; simp [RegUpd.gpr_write]
  have g15 : s₂.gpr .x15 = s.gpr .x12 >>> (64 - sh) := by rw [← hS]; simp [RegUpd.gpr_write]
  have gr : ∀ r, r ≠ .x14 → r ≠ .x15 → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [← hS]; simp [RegUpd.gpr_write, h1, h2]
  have m2 : s₂.mem = s.mem := by rw [← hS]; rfl
  have r2 : s₂.rd = s.rd := by rw [← hS]; rfl
  have w2 : s₂.wr = s.wr := by rw [← hS]; rfl
  have sp2 : s₂.sp = s.sp := by rw [← hS]; rfl
  have ga := gr a ha14 ha15
  have gb := gr b hb14 hb15
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ?_⟩⟩
  simp only [read_x, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, ↓reduceIte, hab, BitVec.setWidth_eq,
    RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry,
    Size.bits, g14, g15, ga, gb, m2, r2, w2, sp2, and_true, ha15.symm, hab.symm]
  refine ⟨?_, fun r h1 h2 h3 h4 => ?_⟩
  · have hlo : (s.gpr .x12 <<< sh).toNat = (s.gpr .x12).toNat * 2 ^ sh % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hhi : (s.gpr .x12 >>> (64 - sh)).toNat = (s.gpr .x12).toNat / 2 ^ (64 - sh) := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hsplit : (s.gpr .x12).toNat * 2 ^ sh = (s.gpr .x12).toNat * 2 ^ sh % 2 ^ 64 +
        2 ^ 64 * ((s.gpr .x12).toNat / 2 ^ (64 - sh)) := by
      have h2 : (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega
      have e2 : (s.gpr .x12).toNat * 2 ^ sh / 2 ^ 64 = (s.gpr .x12).toNat / 2 ^ (64 - sh) := by
        rw [h2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos sh)]
      have := Nat.mod_add_div ((s.gpr .x12).toNat * 2 ^ sh) (2 ^ 64)
      rw [e2] at this
      omega
    have e0 := VG.Proof.Ed25519.Word64.addCarry_value (s.gpr a) (s.gpr .x12 <<< sh) false
    have e1 := VG.Proof.Ed25519.Word64.addCarry_value (s.gpr b) (s.gpr .x12 >>> (64 - sh))
      (VG.Proof.Ed25519.Word64.carryOut (s.gpr a) (s.gpr .x12 <<< sh) false)
    dsimp only [VG.Proof.Ed25519.Word64.addCarry, VG.Proof.Ed25519.Word64.carryOut] at e0 e1
    simp only [hlo, hhi, Bool.toNat_false, Nat.add_zero] at e0 e1 ⊢
    generalize s.gpr a + s.gpr Reg.x12 <<< sh + BitVec.ofNat 64 0 = A' at e0 e1 ⊢
    generalize decide (2 ^ 64 ≤ (s.gpr a).toNat + (s.gpr Reg.x12).toNat * 2 ^ sh % 2 ^ 64) = c at e0 e1 ⊢
    generalize s.gpr b + s.gpr Reg.x12 >>> (64 - sh) + BitVec.ofNat 64 c.toNat = B' at e0 e1 ⊢
    omega
  · simp only [h1, h2, ↓reduceIte]; exact gr r h3 h4
theorem place1_ok {s : State} {a b : Reg} (hz : s.gpr .x10 = 0) (hab : b ≠ a) (ha10 : a ≠ .x10)
    (hno : (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + (s.gpr .x12).toNat < 2 ^ 128) :
    WP isa (.block [.adds .x a a .x12, .adcs .x b b .x10]) s
      fun t => (t.gpr a).toNat + 2 ^ 64 * (t.gpr b).toNat =
          (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + (s.gpr .x12).toNat ∧
        (∀ r, r ≠ a → r ≠ b → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ?_⟩⟩
  simp only [read_x, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, ↓reduceIte, hab, BitVec.setWidth_eq,
    RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry,
    Size.bits, and_true, hab.symm, ha10.symm, hz]
  refine ⟨?_, fun r h1 h2 => by simp only [h1, h2, ↓reduceIte]⟩
  have e0 := VG.Proof.Ed25519.Word64.addCarry_value (s.gpr a) (s.gpr .x12) false
  have e1 := VG.Proof.Ed25519.Word64.addCarry_value (s.gpr b) 0
    (VG.Proof.Ed25519.Word64.carryOut (s.gpr a) (s.gpr .x12) false)
  dsimp only [VG.Proof.Ed25519.Word64.addCarry, VG.Proof.Ed25519.Word64.carryOut] at e0 e1
  simp only [Bool.toNat_false, Nat.add_zero] at e0 e1 ⊢
  generalize s.gpr a + s.gpr .x12 + BitVec.ofNat 64 0 = A' at e0 e1 ⊢
  generalize s.gpr b + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ (s.gpr a).toNat + (s.gpr .x12).toNat)).toNat = B'
    at e0 e1 ⊢
  have : (0 : BitVec 64).toNat = 0 := rfl
  omega

/-- The accumulator `x4`–`x7`, `x20`, as a number. -/
def accVal (s : State) : Nat :=
  (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat + 2 ^ 192 * (s.gpr .x7).toNat +
    2 ^ 256 * (s.gpr .x20).toNat

/-- The registers `place` may write. -/
def placeRegs : List Reg := [.x4, .x5, .x6, .x7, .x20, .x14, .x15]

theorem place_ok {s : State} {k : Nat} (hk : k < 10) (hz : s.gpr .x10 = 0)
    (hb : accVal s + (s.gpr .x12).toNat * 2 ^ VG.Impl.X25519.AArch64.Neon.limbOff k <
      2 ^ (64 * (VG.Impl.X25519.AArch64.Neon.limbOff k / 64 + 2))) :
    WP isa (.block (place k)) s fun t =>
      accVal t = accVal s + (s.gpr .x12).toNat * 2 ^ VG.Impl.X25519.AArch64.Neon.limbOff k ∧
      (∀ r, r ∉ placeRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  have v4 := (s.gpr .x4).isLt; have v5 := (s.gpr .x5).isLt; have v6 := (s.gpr .x6).isLt
  have v7 := (s.gpr .x7).isLt; have v20 := (s.gpr .x20).isLt
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [place, VG.Impl.X25519.AArch64.Neon.limbOff, accReg, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, ↓reduceIte, Nat.reduceEqDiff]
      at hb ⊢
    simp only [accVal] at hb ⊢
    first
      | refine WP.mono (place1_ok hz (by decide) (by decide) (by omega)) fun t ⟨tv, tr, tm, trd, tw, tsp⟩ => ?_
      | refine WP.mono (place2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by omega)) fun t ⟨tv, tr, tm, trd, tw, tsp⟩ => ?_
    refine ⟨?_, fun r hr => ?_, tm, trd, tw, tsp⟩
    · (first | have e4 := congrArg BitVec.toNat (tr .x4 (by decide) (by decide) (by decide) (by decide)) | have e4 := congrArg BitVec.toNat (tr .x4 (by decide) (by decide)) | skip)
      (first | have e5 := congrArg BitVec.toNat (tr .x5 (by decide) (by decide) (by decide) (by decide)) | have e5 := congrArg BitVec.toNat (tr .x5 (by decide) (by decide)) | skip)
      (first | have e6 := congrArg BitVec.toNat (tr .x6 (by decide) (by decide) (by decide) (by decide)) | have e6 := congrArg BitVec.toNat (tr .x6 (by decide) (by decide)) | skip)
      (first | have e7 := congrArg BitVec.toNat (tr .x7 (by decide) (by decide) (by decide) (by decide)) | have e7 := congrArg BitVec.toNat (tr .x7 (by decide) (by decide)) | skip)
      (first | have e20 := congrArg BitVec.toNat (tr .x20 (by decide) (by decide) (by decide) (by decide)) | have e20 := congrArg BitVec.toNat (tr .x20 (by decide) (by decide)) | skip)
      omega
    · simp only [placeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      first
        | exact tr r hr.1 hr.2.1
        | exact tr r hr.2.1 hr.2.2.1
        | exact tr r hr.2.2.1 hr.2.2.2.1
        | exact tr r hr.2.2.2.1 hr.2.2.2.2.1
        | exact tr r hr.1 hr.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
        | exact tr r hr.2.1 hr.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
        | exact tr r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
        | exact tr r hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2


theorem sum_ok {s : State} {base : Addr} (hs : Scr s base false) {k : Nat} (hk : k < 10) (sub : Bool)
    (hbias : sub = true → s.gpr (biasReg k) = BitVec.ofNat 64 (bias k))
    (h0 : (word s.mem base (LBUF + 16 * k)).toNat < 2 ^ 28)
    (h1 : (word s.mem base (LBUF + 16 * k + 8)).toNat < bias k) :
    WP isa (.block ([ld .x12 (LBUF + 16 * k), ld .x13 (LBUF + 16 * k + 8)] ++
      (if sub then [.add .x .x12 .x12 (biasReg k), .sub .x .x12 .x12 .x13] else [.add .x .x12 .x12 .x13]))) s
      fun t => (t.gpr .x12).toNat = (if sub then (word s.mem base (LBUF + 16 * k)).toNat + bias k -
          (word s.mem base (LBUF + 16 * k + 8)).toNat
        else (word s.mem base (LBUF + 16 * k)).toNat + (word s.mem base (LBUF + 16 * k + 8)).toNat) ∧
        (∀ r, r ≠ .x12 → r ≠ .x13 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp := by
  have a0 : (LBUF + 16 * k) % 8 = 0 := by simp only [LBUF]; omega
  have a1 : (LBUF + 16 * k + 8) % 8 = 0 := by simp only [LBUF]; omega
  have b0 : LBUF + 16 * k + 8 ≤ 4096 := by simp only [LBUF]; omega
  have b1 : LBUF + 16 * k + 8 + 8 ≤ 4096 := by simp only [LBUF]; omega
  have hbk : bias k < 2 ^ 28 := by simp only [bias]; split <;> (try split) <;> omega
  rw [List.cons_append, List.cons_append]
  refine WP.block_cons_iff.mpr ⟨_, load_sc hs a0 b0 .x12, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, load_sc (hs.write (by decide) _) a1 b1 .x13, ?_⟩
  simp only [RegUpd.mem_write]
  generalize hS : (s.write .x .x12 (word s.mem base (LBUF + 16 * k))).write .x .x13
    (word s.mem base (LBUF + 16 * k + 8)) = s₂
  have g12 : s₂.gpr .x12 = word s.mem base (LBUF + 16 * k) := by rw [← hS]; simp [RegUpd.gpr_write]
  have g13 : s₂.gpr .x13 = word s.mem base (LBUF + 16 * k + 8) := by rw [← hS]; simp [RegUpd.gpr_write]
  have gr : ∀ r, r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [← hS]; simp [RegUpd.gpr_write, h1, h2]
  have m2 : s₂.mem = s.mem := by rw [← hS]; rfl
  have r2 : s₂.rd = s.rd := by rw [← hS]; rfl
  have w2 : s₂.wr = s.wr := by rw [← hS]; rfl
  have sp2 : s₂.sp = s.sp := by rw [← hS]; rfl
  cases sub with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ?_⟩
    simp only [read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.sp_write, g12, g13, m2, r2, w2, sp2, and_true, BitVec.toNat_add]
    refine ⟨Nat.mod_eq_of_lt (by omega), fun r h1 h2 => ?_⟩
    rw [RegUpd.gpr_write_of_ne _ _ _ h1, gr r h1 h2]
  | true =>
    have hb := hbias rfl
    have hbr : biasReg k ≠ .x12 ∧ biasReg k ≠ .x13 := by
      simp only [biasReg]; split <;> (try split) <;> exact ⟨by decide, by decide⟩
    simp only [↓reduceIte]
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ?_⟩⟩
    simp only [read_x, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x13 ≠ Reg.x12),
      BitVec.setWidth_eq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, g12, g13,
      gr _ hbr.1 hbr.2, hb, m2, r2, w2, sp2, and_true, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    refine ⟨by omega, fun r h1 h2 => ?_⟩
    rw [RegUpd.gpr_write_of_ne _ _ _ h1, RegUpd.gpr_write_of_ne _ _ _ h1, gr r h1 h2]


/-- Limb `k` of `DA + CB`, or of `DA + 4p - CB`, from the limbs at `LBUF`. -/
def limbSumVal (m : Mem) (base : Addr) (sub : Bool) (k : Nat) : Nat :=
  if sub then (word m base (LBUF + 16 * k)).toNat + bias k - (word m base (LBUF + 16 * k + 8)).toNat
  else (word m base (LBUF + 16 * k)).toNat + (word m base (LBUF + 16 * k + 8)).toNat

theorem bound_step {A s X : Nat} (hA : A < 2 ^ 5 * X) (hs : s < 2 ^ 29) : A + s * X < 2 ^ 30 * X := by
  have h1 : s * X ≤ (2 ^ 29 - 1) * X := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ 29 - 1) * X + 2 ^ 5 * X ≤ 2 ^ 30 * X := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by decide)
  omega

theorem off_fits : ∀ k < 10, limbOff k + 30 ≤ 64 * (limbOff k / 64 + 2) := by decide
theorem off_grow : ∀ k < 10, limbOff k + 30 ≤ start (k + 1) + 5 := by decide
theorem bias_lt : ∀ k < 10, limbB k < bias k ∧ bias k < 2 ^ 28 := by decide +kernel

/-- The registers the limb loop writes. -/
def loopRegs : List Reg := [.x4, .x5, .x6, .x7, .x20, .x12, .x13, .x14, .x15]

theorem limbs_ok {s : State} {base : Addr} (hs : Scr s base false) (sub : Bool)
    (hz : s.gpr .x10 = 0) (hbias : sub = true → ∀ k < 10, s.gpr (biasReg k) = BitVec.ofNat 64 (bias k))
    (hL : ∀ k < 10, (word s.mem base (LBUF + 16 * k)).toNat < 2 ^ 27 ∧
      (word s.mem base (LBUF + 16 * k + 8)).toNat ≤ limbB k) (ha : accVal s = 0) :
    WP isa (.block ((List.range 10).flatMap (limbSum sub))) s fun t =>
      accVal t = valN (limbSumVal s.mem base sub) 10 ∧ accVal t < 2 ^ (start 10 + 5) ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10)
    (fun n (t : State) => accVal t = valN (limbSumVal s.mem base sub) n ∧ accVal t < 2 ^ (start n + 5) ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp)
    (fun n t hn ⟨ta, tb, tg, tm, tr, tw, tsp⟩ => ?_) 10 (by decide) s
    ⟨by rw [ha]; rfl, by rw [ha]; exact Nat.two_pow_pos _, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩)
    fun t ⟨ta, tb, rest⟩ => ⟨ta, tb, rest⟩
  have ht : Scr t base false := ⟨by rw [tg _ (by decide)]; exact hs.x0, tw ▸ hs.wr, hs.nowrap⟩
  obtain ⟨l0, l1⟩ := hL n hn
  have bl := bias_lt n hn
  rw [limbSum, WP.block_append_iff]
  refine WP.mono (sum_ok ht hn sub (fun h => by
      rw [tg _ (by simp only [loopRegs, biasReg]; split <;> (try split) <;> decide)]; exact hbias h n hn)
    (by rw [tm]; omega) (by rw [tm]; omega)) fun u ⟨u12, ug, um, ur, uw, usp⟩ => ?_
  have hsv : (u.gpr .x12).toNat = limbSumVal s.mem base sub n := by rw [u12, tm]; rfl
  have hs29 : limbSumVal s.mem base sub n < 2 ^ 29 := by
    simp only [limbSumVal]; split <;> omega
  have hacc : accVal u = accVal t := by
    simp only [accVal, ug .x4 (by decide) (by decide), ug .x5 (by decide) (by decide), ug .x6 (by decide) (by decide),
      ug .x7 (by decide) (by decide), ug .x20 (by decide) (by decide)]
  have hX : 2 ^ (start n + 5) = 2 ^ 5 * 2 ^ limbOff n := by rw [start_eq n hn, Nat.pow_add, Nat.mul_comm]
  have hbnd := bound_step (A := accVal u) (s := limbSumVal s.mem base sub n) (X := 2 ^ limbOff n)
    (by rw [hacc, ← hX]; exact tb) hs29
  have h30 : 2 ^ 30 * 2 ^ limbOff n ≤ 2 ^ (64 * (limbOff n / 64 + 2)) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by have := off_fits n hn; omega)
  refine WP.mono (place_ok hn (by rw [ug _ (by decide) (by decide)]; exact hz.symm ▸ (tg _ (by decide)))
    (by rw [hsv]; omega)) fun v ⟨va, vg, vm, vr, vw, vsp⟩ => ?_
  refine ⟨?_, ?_, fun r hr => ?_, vm.trans (um.trans tm), vr.trans (ur.trans tr), vw.trans (uw.trans tw),
    vsp.trans (usp.trans tsp)⟩
  · rw [va, hsv, hacc, ta]; rfl
  · rw [va, hsv]
    have : 2 ^ 30 * 2 ^ limbOff n ≤ 2 ^ (start (n + 1) + 5) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by have := off_grow n hn; omega)
    omega
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vg r (by simp only [placeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩),
      ug r hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1, tg r (by simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)]

theorem recPrefix_ok (s : State) (sub : Bool) :
    WP isa (.block (([.movz .w .x10 0 0, .movz .w .x11 38 0, .movz .w .x4 0 0, .movz .w .x5 0 0, .movz .w .x6 0 0,
      .movz .w .x7 0 0, .movz .w .x20 0 0] : List Instr) ++
      (if sub then
        ([.movz .w .x9 0xffb4 0, .movk .w .x9 0x0fff 1, .movz .w .x16 0xfffc 0, .movk .w .x16 0x0fff 1,
          .movz .w .x17 0xfffc 0, .movk .w .x17 0x07ff 1] : List Instr)
       else []))) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x11 = 38 ∧ accVal t = 0 ∧
      (sub = true → ∀ k < 10, t.gpr (biasReg k) = BitVec.ofNat 64 (bias k)) ∧
      (∀ r, r ∉ [Reg.x10, .x11, .x4, .x5, .x6, .x7, .x20, .x9, .x16, .x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  cases sub <;>
  · apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some,
      runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, show 16 * 1 < Size.w.bits from by decide,
      Option.some.injEq, exists_eq_left', RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      RegUpd.sp_write]
    refine ⟨by simp [RegUpd.gpr_write], by simp [RegUpd.gpr_write]; rfl, by simp [accVal, RegUpd.gpr_write],
      fun h k hk => ?_, fun r hr => ?_, by first | rfl | trivial, by first | rfl | trivial,
      by first | rfl | trivial, by first | rfl | trivial⟩
    · first
        | exact absurd h (by decide)
        | (have : k = 0 ∨ (k ≠ 0 ∧ k % 2 = 0) ∨ k % 2 = 1 := by omega
           rcases this with rfl | ⟨h0, he⟩ | ho
           · simp [biasReg, bias, RegUpd.gpr_write, State.read]; decide
           · simp [biasReg, bias, RegUpd.gpr_write, State.read, h0, he]; decide
           · simp [biasReg, bias, RegUpd.gpr_write, State.read, show k ≠ 0 by omega, ho]; decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]


theorem recombine_ok {s : State} {base : Addr} (hs : Scr s base false) (sub : Bool) {o : Nat}
    (ho : o % 8 = 0) (ho1 : 64 ≤ o) (ho2 : o + 32 ≤ 768)
    (hL : ∀ k < 10, (word s.mem base (LBUF + 16 * k)).toNat < 2 ^ 27 ∧
      (word s.mem base (LBUF + 16 * k + 8)).toNat ≤ limbB k) :
    WP isa (.block (recombine sub o)) s fun t =>
      Keep base s t ∧ Outside base o 32 s.mem t.mem ∧
      F t.mem base o = toFe (VG.Proof.X25519.AArch64.Hybrid.val (limbSumVal s.mem base sub)) := by
  rw [recombine, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (recPrefix_ok s sub) fun t ⟨tz, t38, ta, tb, tg, tm, tr, tw, tsp⟩ => ?_
  have ht : Scr t base false := ⟨by rw [tg _ (by decide)]; exact hs.x0, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (limbs_ok ht sub tz tb (by rw [tm]; exact hL) ta) fun u ⟨ua, ub, ug, um, ur, uw, usp⟩ => ?_
  have hu : Scr u base false := ⟨by rw [ug _ (by decide), tg _ (by decide)]; exact hs.x0, uw ▸ tw ▸ hs.wr, hs.nowrap⟩
  have uz : u.gpr .x10 = 0 := by rw [ug _ (by decide)]; exact tz
  have u38 : u.gpr .x11 = 38 := by rw [ug _ (by decide)]; exact t38
  have u20 : (u.gpr .x20).toNat < 2 ^ 52 := by
    have h : accVal u < 2 ^ (start 10 + 5) := ub
    rw [show start 10 + 5 = 261 from rfl] at h
    unfold accVal at h
    omega
  refine WP.mono (fold_ok u uz u38 u20) fun v ⟨ve, vk⟩ => ?_
  have hv : Scr v base false := ⟨by rw [vk.gpr _ (by decide)]; exact hu.x0, vk.wr ▸ hu.wr, hu.nowrap⟩
  refine WP.mono (store4_ok hv ⟨ho, show o + 32 ≤ 4096 by omega⟩) fun w hw => ?_
  subst hw
  refine ⟨⟨fun r hr => ?_, by simp only; rw [vk.rd, ur, tr], by simp only; rw [vk.wr, uw, tw],
    by simp only; rw [vk.sp, usp, tsp], ?_⟩, ?_, ?_⟩
  · have sub : ∀ L : List Reg, (∀ x ∈ L, x ∈ clob) → r ∉ L := fun L hL h => hr (hL r h)
    simp only
    rw [vk.gpr r (sub _ (by decide)), ug r (sub _ (by decide)), tg r (sub _ (by decide))]
  · simp only
    rw [vk.mem, um, tm]
    exact (st4_outside _ _ (by omega) _ _ _ _).mono (by omega) (by omega)
  · simp only
    rw [vk.mem, um, tm]
    exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    rw [fe_st4 _ _ (by omega), ve]
    apply toFe_congr
    rw [← fold256]
    have : accVal u = val4 (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) (u.gpr .x7) + 2 ^ 256 * (u.gpr .x20).toNat := by
      simp only [accVal, val4]
    rw [← this, ua, tm, VG.Proof.X25519.AArch64.Hybrid.val_eq_valN]

theorem val_bias : val bias = 4 * VG.Spec.X25519.P := by decide

/-- The limbs' sum is `DA + CB`. -/
theorem val_limbSum_add (m : Mem) (base : Addr) :
    val (limbSumVal m base false) =
      val (fun k => (word m base (LBUF + 16 * k)).toNat) + val (fun k => (word m base (LBUF + 16 * k + 8)).toNat) := by
  simp only [val, S10, limbSumVal, Bool.false_eq_true, ↓reduceIte, Nat.add_mul]; omega

/-- The limbs' sum is `DA + 4p - CB`, if each limb of `CB` is at most its limb of `4p`. -/
theorem val_limbSum_sub (m : Mem) (base : Addr) (h : ∀ k < 10, (word m base (LBUF + 16 * k + 8)).toNat ≤ bias k) :
    val (limbSumVal m base true) + val (fun k => (word m base (LBUF + 16 * k + 8)).toNat) =
      val (fun k => (word m base (LBUF + 16 * k)).toNat) + 4 * VG.Spec.X25519.P := by
  have add : ∀ f g : Nat → Nat, val f + val g = S10 fun k => (f k + g k) * 2 ^ limbOff k := fun f g => by
    simp only [val, S10, Nat.add_mul]; omega
  rw [← val_bias, add, add]
  refine S10_congr fun k hk => congrArg (· * 2 ^ limbOff k) ?_
  have := h k hk
  simp only [limbSumVal, ↓reduceIte]
  omega

end VG.Proof.X25519.AArch64.Hybrid
