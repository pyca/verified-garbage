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

Untrusted: everything here is checked by Lean. `Hybrid.recombine` puts limb
`k` of `DA + CB` (or of `DA + 4p - CB`) at bit `limbOff k` of one of two
accumulators, by the parity of `k` (`put_ok`): with every limb below 2²⁹, limbs
of the same parity do not overlap, so no word carries. The accumulators' sum
(`combine_ok`) is the limbs' exact value, which the 38-fold reduces modulo `p`
(`recombine_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Hybrid
open VG.Impl.X25519.AArch64.Neon (limbOff)
open VG.Proof.Ed25519.AArch64 (read_x Scr word load_sc Keep Keeps movReg_ok F fold_ok store4_ok fe_st4 st4_outside clob
  Outside)
open VG.Proof.Ed25519.Word64 (val4)
open VG.Proof.X25519 (toFe toFe_congr fold256)

theorem lsl_ok (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    WP isa (.block [.lsl .x d n sh]) s fun t =>
      (t.gpr d).toNat = (s.gpr n).toNat * 2 ^ sh % 2 ^ 64 ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨s.write .x d (s.gpr n <<< sh), by simp [exec, read_x, Size.bits, h],
    WP.block_nil_iff.mpr ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem lsr_ok (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    WP isa (.block [.lsr .x d n sh]) s fun t =>
      (t.gpr d).toNat = (s.gpr n).toNat / 2 ^ sh ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨s.write .x d (s.gpr n >>> sh), by simp [exec, read_x, Size.bits, h],
    WP.block_nil_iff.mpr ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem addReg_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t =>
      (t.gpr d).toNat = ((s.gpr n).toNat + (s.gpr m).toNat) % 2 ^ 64 ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, read_x, read_x, BitVec.toNat_add]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem adcs_ok (s : State) (d n m : Reg) :
    WP isa (.block [.adcs .x d n m]) s fun t =>
      (t.gpr d).toNat + 2 ^ 64 * t.c.toNat = (s.gpr n).toNat + (s.gpr m).toNat + s.c.toNat ∧
        Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · simp only [read_x, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, ↓reduceIte, BitVec.setWidth_eq]
    exact VG.Proof.Ed25519.Word64.addCarry_value (s.gpr n) (s.gpr m) s.c
  · simp only [RegUpd.gpr_addWithCarry, show r ≠ d by simpa using hr, ↓reduceIte]

theorem adds_ok (s : State) (d n m : Reg) :
    WP isa (.block [.adds .x d n m]) s fun t =>
      (t.gpr d).toNat + 2 ^ 64 * t.c.toNat = (s.gpr n).toNat + (s.gpr m).toNat ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · simp only [read_x, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, ↓reduceIte, BitVec.setWidth_eq]
    exact VG.Proof.Ed25519.Word64.addCarry_value (s.gpr n) (s.gpr m) false
  · simp only [RegUpd.gpr_addWithCarry, show r ≠ d by simpa using hr, ↓reduceIte]

/-- `lsl x14, x12, #sh; add a, a, x14`. -/
theorem putAdd_ok (s : State) (a : Reg) {sh : Nat} (h : sh < 64) (ha14 : a ≠ .x14) :
    WP isa (.block [.lsl .x .x14 .x12 sh, .add .x a a .x14]) s fun t =>
      (t.gpr a).toNat = ((s.gpr a).toNat + (s.gpr .x12).toNat * 2 ^ sh % 2 ^ 64) % 2 ^ 64 ∧
        Keeps [.x14, a] s t := by
  rw [show ([.lsl .x .x14 .x12 sh, .add .x a a .x14] : List Instr) =
    [.lsl .x .x14 .x12 sh] ++ [.add .x a a .x14] from rfl, WP.block_append_iff]
  refine WP.mono (lsl_ok s .x14 .x12 h) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (addReg_ok s₁ a a .x14) fun t ⟨e2, k2⟩ => ⟨?_, (k1.mono (by simp)).trans (k2.mono (by simp))⟩
  rw [e2, e1, k1.gpr a (by simpa using ha14)]

/-- `lsl x14, x12, #sh; add a, a, x14; lsr b, x12, #sh'`. -/
theorem putSpan_ok (s : State) (a b : Reg) {sh sh' : Nat} (h : sh < 64) (h' : sh' < 64)
    (ha14 : a ≠ .x14) (ha12 : a ≠ .x12) (hab : a ≠ b) :
    WP isa (.block [.lsl .x .x14 .x12 sh, .add .x a a .x14, .lsr .x b .x12 sh']) s fun t =>
      (t.gpr a).toNat = ((s.gpr a).toNat + (s.gpr .x12).toNat * 2 ^ sh % 2 ^ 64) % 2 ^ 64 ∧
      (t.gpr b).toNat = (s.gpr .x12).toNat / 2 ^ sh' ∧ Keeps [.x14, a, b] s t := by
  rw [show ([.lsl .x .x14 .x12 sh, .add .x a a .x14, .lsr .x b .x12 sh'] : List Instr) =
    [.lsl .x .x14 .x12 sh, .add .x a a .x14] ++ [.lsr .x b .x12 sh'] from rfl, WP.block_append_iff]
  refine WP.mono (putAdd_ok s a h ha14) fun s₁ ⟨e1, k1⟩ => ?_
  have h12 : s₁.gpr .x12 = s.gpr .x12 := k1.gpr _ (by simpa using ha12.symm)
  refine WP.mono (lsr_ok s₁ b .x12 h') fun t ⟨e2, k2⟩ =>
    ⟨?_, by rw [e2, h12], (k1.mono (by simp)).trans (k2.mono (by simp))⟩
  rw [k2.gpr a (by simpa using hab), e1]

/-- The value of the words `rs`, least significant first. -/
def wl (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * wl s rs

theorem wl_congr {s t : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, t.gpr r = s.gpr r) → wl t rs = wl s rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [wl, h r List.mem_cons_self, wl_congr fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The words of the even limbs' accumulator that the first `n` limbs write. -/
def wA (n : Nat) : List Reg :=
  [[], [.x4], [.x4], [.x4, .x5], [.x4, .x5], [.x4, .x5, .x6], [.x4, .x5, .x6], [.x4, .x5, .x6],
    [.x4, .x5, .x6], [.x4, .x5, .x6, .x7]].getD n [.x4, .x5, .x6, .x7]
/-- The words of the odd limbs' accumulator that the first `n` limbs write. -/
def wB (n : Nat) : List Reg :=
  [[], [], [.x2], [.x2], [.x2, .x3], [.x2, .x3], [.x2, .x3, .x8], [.x2, .x3, .x8], [.x2, .x3, .x8, .x21],
    [.x2, .x3, .x8, .x21]].getD n [.x2, .x3, .x8, .x21, .x15]
/-- A bound on the even limbs' accumulator after the first `n` limbs: the end of its last limb. -/
def endA (n : Nat) : Nat := [0, 29, 29, 80, 80, 131, 131, 182, 182, 233].getD n 233
/-- The end of the odd limbs' accumulator's last limb after the first `n < 10` limbs. -/
def endB (n : Nat) : Nat := [0, 0, 55, 55, 106, 106, 157, 157, 208, 208].getD n 0
/-- A bound on the odd limbs' accumulator after the first `n` limbs (`2²⁵⁹` after all ten). -/
def bndB (n : Nat) : Nat := if n = 10 then 2 ^ 256 * 8 else 2 ^ endB n

/-- The registers `put` may write. -/
def putRegs : List Reg := [.x4, .x5, .x6, .x7, .x2, .x3, .x8, .x21, .x15, .x14]

theorem put_ok {s : State} {k : Nat} (hk : k < 10) (hv : (s.gpr .x12).toNat < 2 ^ 29)
    (hA : wl s (wA k) < 2 ^ endA k) (hB : wl s (wB k) < bndB k) :
    WP isa (.block (put k)) s fun t =>
      wl t (wA (k + 1)) + wl t (wB (k + 1)) =
        wl s (wA k) + wl s (wB k) + (s.gpr .x12).toNat * 2 ^ VG.Impl.X25519.AArch64.Neon.limbOff k ∧
      wl t (wA (k + 1)) < 2 ^ endA (k + 1) ∧ wl t (wB (k + 1)) < bndB (k + 1) ∧ Keeps putRegs s t := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  have v4 := (s.gpr .x4).isLt; have v5 := (s.gpr .x5).isLt; have v6 := (s.gpr .x6).isLt
  have v8 := (s.gpr .x8).isLt; have v21 := (s.gpr .x21).isLt
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [put, wA, wB, endA, endB, bndB, VG.Impl.X25519.AArch64.Neon.limbOff, List.getD_cons_succ,
      List.getD_cons_zero, List.getD_nil, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, wl, Nat.mul_zero,
      Nat.add_zero, Nat.reducePow, Nat.reduceMul] at hA hB ⊢
    first
      | refine WP.mono (movReg_ok s _ .x12) fun t ⟨e, kt⟩ => ?_
        replace e := congrArg BitVec.toNat e
      | refine WP.mono (lsl_ok s _ .x12 (by decide)) fun t ⟨e, kt⟩ => ?_
      | refine WP.mono (putAdd_ok s _ (by decide) (by decide)) fun t ⟨e, kt⟩ => ?_
      | refine WP.mono (putSpan_ok s _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
          fun t ⟨e, e', kt⟩ => ?_
    refine ⟨?_, ?_, ?_, kt.mono (by decide)⟩ <;>
    · (try simp (disch := decide) only [kt.gpr, e])
      (try simp only [e'])
      omega


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

theorem bias_lt : ∀ k < 10, limbB k < bias k ∧ bias k < 2 ^ 28 := by decide +kernel

/-- The registers the limb loop writes. -/
def loopRegs : List Reg := [.x4, .x5, .x6, .x7, .x2, .x3, .x8, .x21, .x15, .x14, .x12, .x13]

theorem acc_ne : ∀ n < 11, ∀ r ∈ wA n ++ wB n, r ≠ .x12 ∧ r ≠ .x13 := by decide

theorem limbs_ok {s : State} {base : Addr} (hs : Scr s base false) (sub : Bool)
    (hbias : sub = true → ∀ k < 10, s.gpr (biasReg k) = BitVec.ofNat 64 (bias k))
    (hL : ∀ k < 10, (word s.mem base (LBUF + 16 * k)).toNat < 2 ^ 27 ∧
      (word s.mem base (LBUF + 16 * k + 8)).toNat ≤ limbB k) :
    WP isa (.block ((List.range 10).flatMap (limbSum sub))) s fun t =>
      wl t (wA 10) + wl t (wB 10) = valN (limbSumVal s.mem base sub) 10 ∧
      wl t (wA 10) < 2 ^ endA 10 ∧ wl t (wB 10) < bndB 10 ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10)
    (fun n (t : State) => wl t (wA n) + wl t (wB n) = valN (limbSumVal s.mem base sub) n ∧
      wl t (wA n) < 2 ^ endA n ∧ wl t (wB n) < bndB n ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp)
    (fun n t hn ⟨ta, tA, tB, tg, tm, tr, tw, tsp⟩ => ?_) 10 (by decide) s
    ⟨rfl, Nat.one_pos, Nat.one_pos, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩)
    fun t h => h
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
  have hne := acc_ne n (by omega)
  have huA : wl u (wA n) = wl t (wA n) :=
    wl_congr fun r hr => ug r (hne r (List.mem_append_left _ hr)).1 (hne r (List.mem_append_left _ hr)).2
  have huB : wl u (wB n) = wl t (wB n) :=
    wl_congr fun r hr => ug r (hne r (List.mem_append_right _ hr)).1 (hne r (List.mem_append_right _ hr)).2
  refine WP.mono (put_ok hn (by rw [hsv]; exact hs29) (by rw [huA]; exact tA) (by rw [huB]; exact tB))
    fun v ⟨va, vA, vB, vk⟩ => ?_
  refine ⟨?_, vA, vB, fun r hr => ?_, vk.mem.trans (um.trans tm), vk.rd.trans (ur.trans tr),
    vk.wr.trans (uw.trans tw), vk.sp.trans (usp.trans tsp)⟩
  · rw [va, hsv, huA, huB, ta]; rfl
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vk.gpr r (by simp only [putRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
        ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
          hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1⟩),
      ug r hr.2.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2,
      tg r (by simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)]

/-- The accumulator `x4`–`x7`, `x20`, as a number. -/
def accVal (s : State) : Nat :=
  (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat + 2 ^ 192 * (s.gpr .x7).toNat +
    2 ^ 256 * (s.gpr .x20).toNat

theorem combine_ok (s : State) (hz : s.gpr .x10 = 0) (h15 : (s.gpr .x15).toNat < 2 ^ 63) :
    WP isa (.block combine) s fun t =>
      accVal t = wl s [.x4, .x5, .x6, .x7] + wl s [.x2, .x3, .x8, .x21, .x15] ∧
        Keeps [.x4, .x5, .x6, .x7, .x20] s t := by
  rw [show combine = ([.adds .x .x4 .x4 .x2] : List Instr) ++ (([.adcs .x .x5 .x5 .x3] : List Instr) ++
    (([.adcs .x .x6 .x6 .x8] : List Instr) ++ (([.adcs .x .x7 .x7 .x21] : List Instr) ++
    ([.adcs .x .x20 .x15 .x10] : List Instr)))) from rfl, WP.block_append_iff]
  refine WP.mono (adds_ok s .x4 .x4 .x2) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok s₁ .x5 .x5 .x3) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok s₂ .x6 .x6 .x8) fun s₃ ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok s₃ .x7 .x7 .x21) fun s₄ ⟨e4, k4⟩ => ?_
  refine WP.mono (adcs_ok s₄ .x20 .x15 .x10) fun t ⟨e5, k5⟩ => ⟨?_,
    (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      ((k4.mono (by decide)).trans (k5.mono (by decide)))⟩
  simp only [k1.gpr _ (show Reg.x5 ∉ [Reg.x4] by decide), k1.gpr _ (show Reg.x3 ∉ [Reg.x4] by decide),
    k1.gpr _ (show Reg.x6 ∉ [Reg.x4] by decide), k1.gpr _ (show Reg.x8 ∉ [Reg.x4] by decide),
    k1.gpr _ (show Reg.x7 ∉ [Reg.x4] by decide), k1.gpr _ (show Reg.x21 ∉ [Reg.x4] by decide),
    k1.gpr _ (show Reg.x15 ∉ [Reg.x4] by decide), k1.gpr _ (show Reg.x10 ∉ [Reg.x4] by decide),
    k2.gpr _ (show Reg.x6 ∉ [Reg.x5] by decide), k2.gpr _ (show Reg.x8 ∉ [Reg.x5] by decide),
    k2.gpr _ (show Reg.x7 ∉ [Reg.x5] by decide), k2.gpr _ (show Reg.x21 ∉ [Reg.x5] by decide),
    k2.gpr _ (show Reg.x15 ∉ [Reg.x5] by decide), k2.gpr _ (show Reg.x10 ∉ [Reg.x5] by decide),
    k3.gpr _ (show Reg.x7 ∉ [Reg.x6] by decide), k3.gpr _ (show Reg.x21 ∉ [Reg.x6] by decide),
    k3.gpr _ (show Reg.x15 ∉ [Reg.x6] by decide), k3.gpr _ (show Reg.x10 ∉ [Reg.x6] by decide),
    k4.gpr _ (show Reg.x15 ∉ [Reg.x7] by decide), k4.gpr _ (show Reg.x10 ∉ [Reg.x7] by decide), hz]
    at e2 e3 e4 e5
  simp only [accVal, wl, Nat.mul_zero, Nat.add_zero,
    k5.gpr _ (show Reg.x4 ∉ [Reg.x20] by decide), k5.gpr _ (show Reg.x5 ∉ [Reg.x20] by decide),
    k5.gpr _ (show Reg.x6 ∉ [Reg.x20] by decide), k5.gpr _ (show Reg.x7 ∉ [Reg.x20] by decide),
    k4.gpr _ (show Reg.x4 ∉ [Reg.x7] by decide), k4.gpr _ (show Reg.x5 ∉ [Reg.x7] by decide),
    k4.gpr _ (show Reg.x6 ∉ [Reg.x7] by decide), k3.gpr _ (show Reg.x4 ∉ [Reg.x6] by decide),
    k3.gpr _ (show Reg.x5 ∉ [Reg.x6] by decide), k2.gpr _ (show Reg.x4 ∉ [Reg.x5] by decide)]
  have c4 := Bool.toNat_le s₄.c
  have : (0 : BitVec 64).toNat = 0 := rfl
  omega

theorem recPrefix_ok (s : State) (sub : Bool) :
    WP isa (.block (([.movz .w .x10 0 0, .movz .w .x11 38 0] : List Instr) ++
      (if sub then
        ([.movz .w .x9 0xffb4 0, .movk .w .x9 0x0fff 1, .movz .w .x16 0xfffc 0, .movk .w .x16 0x0fff 1,
          .movz .w .x17 0xfffc 0, .movk .w .x17 0x07ff 1] : List Instr)
       else []))) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x11 = 38 ∧
      (sub = true → ∀ k < 10, t.gpr (biasReg k) = BitVec.ofNat 64 (bias k)) ∧
      (∀ r, r ∉ [Reg.x10, .x11, .x9, .x16, .x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  cases sub <;>
  · apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some,
      runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, show 16 * 1 < Size.w.bits from by decide,
      Option.some.injEq, exists_eq_left', RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      RegUpd.sp_write]
    refine ⟨by simp [RegUpd.gpr_write], by simp [RegUpd.gpr_write]; rfl,
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
      simp [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]


theorem recombine_ok {s : State} {base : Addr} (hs : Scr s base false) (sub : Bool) {o : Nat}
    (ho : o % 8 = 0) (ho1 : 64 ≤ o) (ho2 : o + 32 ≤ 768)
    (hL : ∀ k < 10, (word s.mem base (LBUF + 16 * k)).toNat < 2 ^ 27 ∧
      (word s.mem base (LBUF + 16 * k + 8)).toNat ≤ limbB k) :
    WP isa (.block (recombine sub o)) s fun t =>
      Keep base s t ∧ Outside base o 32 s.mem t.mem ∧
      F t.mem base o = toFe (VG.Proof.X25519.AArch64.Hybrid.val (limbSumVal s.mem base sub)) := by
  rw [recombine, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (recPrefix_ok s sub) fun t ⟨tz, t38, tb, tg, tm, tr, tw, tsp⟩ => ?_
  have ht : Scr t base false := ⟨by rw [tg _ (by decide)]; exact hs.x0, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (limbs_ok ht sub tb (by rw [tm]; exact hL)) fun u ⟨ua, uA, uB, ug, um, ur, uw, usp⟩ => ?_
  have uz : u.gpr .x10 = 0 := by rw [ug _ (by decide)]; exact tz
  have u38 : u.gpr .x11 = 38 := by rw [ug _ (by decide)]; exact t38
  have uB' : wl u [.x2, .x3, .x8, .x21, .x15] < 2 ^ 256 * 8 := uB
  have u15 : (u.gpr .x15).toNat < 2 ^ 63 := by
    simp only [wl, Nat.mul_zero, Nat.add_zero] at uB'
    omega
  refine WP.mono (combine_ok u uz u15) fun c ⟨ce, ck⟩ => ?_
  have hc : Scr c base false :=
    ⟨by rw [ck.gpr _ (by decide), ug _ (by decide), tg _ (by decide)]; exact hs.x0, ck.wr ▸ uw ▸ tw ▸ hs.wr, hs.nowrap⟩
  have cz : c.gpr .x10 = 0 := (ck.gpr _ (by decide)).trans uz
  have c38 : c.gpr .x11 = 38 := (ck.gpr _ (by decide)).trans u38
  have c20 : (c.gpr .x20).toNat < 2 ^ 52 := by
    have hA : wl u [.x4, .x5, .x6, .x7] < 2 ^ 233 := uA
    unfold accVal at ce
    omega
  refine WP.mono (fold_ok c cz c38 c20) fun v ⟨ve, vk⟩ => ?_
  have hv : Scr v base false := ⟨by rw [vk.gpr _ (by decide)]; exact hc.x0, vk.wr ▸ hc.wr, hc.nowrap⟩
  refine WP.mono (store4_ok hv ⟨ho, show o + 32 ≤ 4096 by omega⟩) fun w hw => ?_
  subst hw
  refine ⟨⟨fun r hr => ?_, by simp only; rw [vk.rd, ck.rd, ur, tr], by simp only; rw [vk.wr, ck.wr, uw, tw],
    by simp only; rw [vk.sp, ck.sp, usp, tsp], ?_⟩, ?_, ?_⟩
  · have sub : ∀ L : List Reg, (∀ x ∈ L, x ∈ clob) → r ∉ L := fun L hL h => hr (hL r h)
    simp only
    rw [vk.gpr r (sub _ (by decide)), ck.gpr r (sub _ (by decide)), ug r (sub _ (by decide)),
      tg r (sub _ (by decide))]
  · simp only
    rw [vk.mem, ck.mem, um, tm]
    exact (st4_outside _ _ (by omega) _ _ _ _).mono (by omega) (by omega)
  · simp only
    rw [vk.mem, ck.mem, um, tm]
    exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    rw [fe_st4 _ _ (by omega), ve]
    apply toFe_congr
    rw [← fold256]
    have : accVal c = val4 (c.gpr .x4) (c.gpr .x5) (c.gpr .x6) (c.gpr .x7) + 2 ^ 256 * (c.gpr .x20).toNat := by
      simp only [accVal, val4]
    rw [← this, ce, VG.Proof.X25519.AArch64.Hybrid.val_eq_valN, ← tm]
    exact congrArg (· % _) ua

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
