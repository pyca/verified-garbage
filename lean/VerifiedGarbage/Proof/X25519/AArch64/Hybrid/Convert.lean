module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Exec
public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Radix
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# X25519 on AArch64: splitting field elements into radix-2²⁵·⁵ limbs

Untrusted: everything here is checked by Lean. `Neon.words` puts word `k` of
two field elements in the 64-bit lanes of `v19 + k`; `Neon.limb` takes limb `i`
of both from them.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Neon
open VG.Proof.Ed25519.AArch64 (Scr off word Outside ofs)
open VG.Proof.Curve448.AArch64.Neon (setMem lane_ushr lane_shl trn1_0 trn1_1 trn2_0 trn2_1)

theorem V_ne : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := by decide

/-- Read vector registers through the writes after them (distinctness from the context). -/
macro "vred" : tactic =>
  `(tactic| simp (disch := assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne, RegUpd.mem_setV,
    VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_v])

/-- Word `k` of the elements at `a 0` and `a 1` of `m`, in lanes 0 and 1 of `v_{19+k}`. -/
def WordsIn (s : State) (m : Mem) (base : Addr) (a : Nat → Nat) : Prop :=
  ∀ k < 4, ∀ e < 2, vdword (s.v (V (19 + k))) e = word m base (a e + 8 * k)

/-- The registers `words` writes. -/
def wordsRegs : List VReg := [V 19, V 20, V 21, V 22, V 27, V 28]

theorem flags_setV (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).flags = s.flags := rfl

theorem scratch_setV {s : State} {base : Addr} (hs : Scratch s base) (r : VReg) (x : BitVec 128) :
    Scratch (s.setV r x) base := scratch_of hs rfl rfl

theorem words_eq (a₁ a₂ : Nat) : words a₁ a₂ 19 27 =
    [ldq 27 a₁, ldq 28 a₂, vo (.perm .trn1 .d2 (V 19) (V 27) (V 28)), vo (.perm .trn2 .d2 (V 20) (V 27) (V 28)),
      ldq 27 (a₁ + 16), ldq 28 (a₂ + 16), vo (.perm .trn1 .d2 (V 21) (V 27) (V 28)),
      vo (.perm .trn2 .d2 (V 22) (V 27) (V 28))] := rfl

theorem words_ok {s : State} {base : Addr} (hs : Scratch s base) {a₁ a₂ : Nat}
    (h₁ : a₁ % 16 = 0) (h₁' : a₁ + 32 ≤ 4096) (h₂ : a₂ % 16 = 0) (h₂' : a₂ + 32 ≤ 4096) :
    WP isa (.block (words a₁ a₂ 19 27)) s fun t =>
      WordsIn t s.mem base (fun e => if e = 0 then a₁ else a₂) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags ∧
      (∀ r : VReg, r ∉ wordsRegs → t.v r = s.v r) := by
  rw [words_eq]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 27 h₁ (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scratch_setV hs _ _) 28 h₂ (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scratch_setV (scratch_setV (scratch_setV (scratch_setV hs _ _) _ _) _ _) _ _)
    27 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scratch_setV (scratch_setV (scratch_setV (scratch_setV
    (scratch_setV hs _ _) _ _) _ _) _ _) _ _) 28 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
    true_and]
  refine ⟨fun k hk e he => ?_, fun r hr => ?_⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
    simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne, Nat.reduceAdd,
      trn1_0, trn1_1, trn2_0, trn2_1, vdword_ld, ↓reduceIte, Nat.reduceEqDiff] <;>
    exact congrArg (word _ base) (by omega)
  · simp only [wordsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
    simp only [RegUpd.v_setV_of_ne _ _ r1, RegUpd.v_setV_of_ne _ _ r2, RegUpd.v_setV_of_ne _ _ r3,
      RegUpd.v_setV_of_ne _ _ r4, RegUpd.v_setV_of_ne _ _ r5, RegUpd.v_setV_of_ne _ _ r6]


/-- The value of the four words at `o`. -/
abbrev feAt (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.Ed25519.AArch64.fe m base o

theorem lane_and' (x m : BitVec 128) {k : Nat} (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ k - 1) {e : Nat} (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ k := by
  rw [VG.Proof.Curve448.AArch64.Neon.vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

theorem lane_addN (x y : BitVec 128) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun _ a b => a + b) x y) e).toNat = ((vdword x e).toNat + (vdword y e).toNat) % 2 ^ 64 := by
  rw [VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add]

/-- The limbs a limb's code computes from the four words of an element. -/
theorem limbOf_words (w0 w1 w2 w3 : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) :
    let x := w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3
    limbOf x 0 = w0 % 2 ^ 26 ∧ limbOf x 1 = w0 / 2 ^ 26 % 2 ^ 25 ∧
    limbOf x 2 = (w0 / 2 ^ 51 + w1 * 2 ^ 13 % 2 ^ 64) % 2 ^ 64 % 2 ^ 26 ∧
    limbOf x 3 = w1 / 2 ^ 13 % 2 ^ 25 ∧ limbOf x 4 = w1 / 2 ^ 38 ∧ limbOf x 5 = w2 % 2 ^ 25 ∧
    limbOf x 6 = w2 / 2 ^ 25 % 2 ^ 26 ∧
    limbOf x 7 = (w2 / 2 ^ 51 + w3 * 2 ^ 13 % 2 ^ 64) % 2 ^ 64 % 2 ^ 25 ∧
    limbOf x 8 = w3 / 2 ^ 12 % 2 ^ 26 ∧ limbOf x 9 = w3 / 2 ^ 38 := by
  intro x
  simp only [x, limbOf, limbOff, wdIn, width, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMod,
    ↓reduceIte, Nat.reduceEqDiff]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩


/-- The limbs of the element at `o`, from its words. -/
theorem limbOf_fe (m : Mem) (base : Addr) (o : Nat) :
    let w := fun k => (word m base (o + 8 * k)).toNat
    limbOf (feAt m base o) 0 = w 0 % 2 ^ 26 ∧ limbOf (feAt m base o) 1 = w 0 / 2 ^ 26 % 2 ^ 25 ∧
    limbOf (feAt m base o) 2 = (w 0 / 2 ^ 51 + w 1 * 2 ^ 13 % 2 ^ 64) % 2 ^ 64 % 2 ^ 26 ∧
    limbOf (feAt m base o) 3 = w 1 / 2 ^ 13 % 2 ^ 25 ∧ limbOf (feAt m base o) 4 = w 1 / 2 ^ 38 ∧
    limbOf (feAt m base o) 5 = w 2 % 2 ^ 25 ∧ limbOf (feAt m base o) 6 = w 2 / 2 ^ 25 % 2 ^ 26 ∧
    limbOf (feAt m base o) 7 = (w 2 / 2 ^ 51 + w 3 * 2 ^ 13 % 2 ^ 64) % 2 ^ 64 % 2 ^ 25 ∧
    limbOf (feAt m base o) 8 = w 3 / 2 ^ 12 % 2 ^ 26 ∧ limbOf (feAt m base o) 9 = w 3 / 2 ^ 38 := by
  intro w
  have := limbOf_words (w 0) (w 1) (w 2) (w 3) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  simp only [w, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at this ⊢
  exact this


/-- The limb masks: `2²⁶ - 1` and `2²⁵ - 1` in the 64-bit lanes of `v24` and `v25`. -/
def Masks (s : State) : Prop :=
  (∀ e < 2, (vdword (s.v (V 24)) e).toNat = 2 ^ 26 - 1) ∧ ∀ e < 2, (vdword (s.v (V 25)) e).toNat = 2 ^ 25 - 1

theorem limb_ok {s : State} {m : Mem} {base : Addr} {a : Nat → Nat} (hw : WordsIn s m base a) (hm : Masks s)
    {i : Nat} (hi : i < 10) :
    WP isa (.block (limb 19 24 25 28 29 i)) s fun t =>
      (∀ e < 2, (vdword (t.v (V 28)) e).toNat = limbOf (feAt m base (a e)) i) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags ∧
      ∀ r, r ≠ V 28 → r ≠ V 29 → t.v r = s.v r := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [limb, limbOff, width, maskOf, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMod,
      Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceLeDiff, or_self,
      or_true, true_or]
    repeat refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_nil_iff.mpr ?_
    simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
      true_and]
    refine ⟨fun e he => ?_, fun r h1 h2 => ?_⟩
    · simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
      have h0 := hw 0 (by decide) e he
      have h1 := hw 1 (by decide) e he
      have h2 := hw 2 (by decide) e he
      have h3 := hw 3 (by decide) e he
      have L := limbOf_fe m base (a e)
      simp only [Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3 L
      obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9⟩ := L
      simp only [lane_and' _ _ hm.1 he, lane_and' _ _ hm.2 he, lane_addN _ _ he, lane_ushr _ _ _ he,
        lane_shl _ _ _ he, h0, h1, h2, h3, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9]
    · simp (disch := assumption) only [RegUpd.v_setV_of_ne]


/-- Word `c` of row `i` of the first operands: limb `i` of element `c mod 2`, doubled in the upper
half for odd `i`. -/
def rowWord (F : Nat → Nat → Nat) (i c : Nat) : Nat := (if 2 ≤ c ∧ i % 2 = 1 then 2 else 1) * F (c % 2) i

/-- The rows of the first operands at `FBUF`. -/
def FRows (m : Mem) (base : Addr) (F : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ i < n, ∀ c < 4, nw m base (FBUF + 16 * i + 4 * c) = rowWord F i c

theorem uzp1_word (lo hi : BitVec 128) (c : Nat) (hc : c < 4) :
    (vword (VPermOp.eval .uzp1 .s4 lo hi) c).toNat =
      (vdword (if c < 2 then lo else hi) (c % 2)).toNat % 2 ^ 32 := by
  rw [VG.Proof.Curve448.AArch64.Neon.uzp_words lo hi c hc]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Row `i` of the first operands, from their words. -/
theorem rowF_ok {s : State} {m : Mem} {base : Addr} {a : Nat → Nat} (hs : Scratch s base)
    (hw : WordsIn s m base a) (hm : Masks s) {i : Nat} (hi : i < 10) :
    WP isa (.block (limb 19 24 25 28 29 i ++
        (if i % 2 = 1 then [vo (.shift .shl .d2 (V 29) (V 28) 1), vo (.perm .uzp1 .s4 (V 30) (V 28) (V 29))]
         else [vo (.perm .uzp1 .s4 (V 30) (V 28) (V 28))]) ++ [stq 30 (FBUF + 16 * i)])) s fun t =>
      (∀ c < 4, nw t.mem base (FBUF + 16 * i + 4 * c) = rowWord (fun e => limbOf (feAt m base (a e))) i c) ∧
      Outside base (FBUF + 16 * i) 16 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.flags = s.flags ∧ ∀ r, r ≠ V 28 → r ≠ V 29 → r ≠ V 30 → t.v r = s.v r := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (limb_ok hw hm hi) fun t ⟨tl, tm, tg, tr, tw, tsp, tf, tv⟩ => ?_
  have ht : Scratch t base := scratch_of hs tg tw
  have hF : ∀ e < 2, limbOf (feAt m base (a e)) i < 2 ^ 26 := fun e _ => limbOf_lt26 _ _
  have hd : (FBUF + 16 * i) % 16 = 0 := by simp only [FBUF]; omega
  have hd' : FBUF + 16 * i + 16 ≤ 4096 := by simp only [FBUF]; omega
  rw [WP.block_append_iff]
  have ok : ∀ (x : BitVec 128), (∀ e < 2, (vdword x e).toNat = (if i % 2 = 1 then 2 else 1) * limbOf (feAt m base (a e)) i) →
      ∀ c < 4, (vword (VPermOp.eval .uzp1 .s4 (t.v (V 28)) x) c).toNat = rowWord (fun e => limbOf (feAt m base (a e))) i c := by
    intro x hx c hc
    rw [uzp1_word _ _ c hc, rowWord]
    have hc2 : c % 2 < 2 := Nat.mod_lt _ (by decide)
    have := hF (c % 2) hc2
    split
    · rw [tl _ hc2]
      simp only [show ¬(2 ≤ c ∧ i % 2 = 1) by omega, ↓reduceIte, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [hx _ hc2]
      split <;> split <;> (first | omega | (rw [Nat.mod_eq_of_lt (by omega)]))
  split
  · rename_i hodd
    refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_nil_iff.mpr ?_
    refine WP.block_cons_iff.mpr ⟨_, exec_stq (scratch_setV (scratch_setV ht _ _) _ _) 30 hd hd', ?_⟩
    refine WP.block_nil_iff.mpr ?_
    simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_gpr,
      VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr,
      VG.Proof.Curve448.AArch64.Neon.setMem_sp, VG.Proof.Curve448.AArch64.Neon.setMem_v, flags_setMem,
      RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV]
    simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
    refine ⟨fun c hc => ?_, by rw [tm]; exact st_outside _ _ _ hd', tg, tr, tw, tsp, tf, fun r h1 h2 h3 => ?_⟩
    · rw [nw_st _ _ _ _ hc]
      refine ok _ (fun e he => ?_) c hc
      rw [lane_shl _ _ _ he, tl e he]
      simp only [hodd, ↓reduceIte]
      have := hF e he
      omega
    · simp (disch := assumption) only [RegUpd.v_setV_of_ne]; exact tv r h1 h2
  · rename_i hodd
    refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
    refine WP.block_nil_iff.mpr ?_
    refine WP.block_cons_iff.mpr ⟨_, exec_stq (scratch_setV ht _ _) 30 hd hd', ?_⟩
    refine WP.block_nil_iff.mpr ?_
    simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_gpr,
      VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr,
      VG.Proof.Curve448.AArch64.Neon.setMem_sp, VG.Proof.Curve448.AArch64.Neon.setMem_v, flags_setMem,
      RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV]
    simp only [RegUpd.v_setV_self]
    refine ⟨fun c hc => ?_, by rw [tm]; exact st_outside _ _ _ hd', tg, tr, tw, tsp, tf, fun r h1 h2 h3 => ?_⟩
    · rw [nw_st _ _ _ _ hc]
      refine ok _ (fun e he => ?_) c hc
      rw [tl e he]
      simp only [hodd, ↓reduceIte, Nat.one_mul]
    · simp (disch := assumption) only [RegUpd.v_setV_of_ne]; exact tv r h1 h2


/-- The constants of `prod2` at `CONST`. -/
def Consts (m : Mem) (base : Addr) : Prop :=
  (∀ e < 2, (word m base (M26 + 8 * e)).toNat = 2 ^ 26 - 1) ∧
  (∀ e < 2, (word m base (M25 + 8 * e)).toNat = 2 ^ 25 - 1) ∧ ∀ c < 4, nw m base (C19 + 4 * c) = 19

/-- A field element's place: aligned, below `FBUF`. -/
def Below (o : Nat) : Prop := o % 16 = 0 ∧ o + 32 ≤ FBUF

theorem masks_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base) :
    WP isa (.block [ldq 24 M26, ldq 25 M25]) s fun t =>
      Masks t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags ∧
      ∀ r, r ≠ V 24 → r ≠ V 25 → t.v r = s.v r := by
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 24 (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scratch_setV hs _ _) 25 (by decide) (by decide), ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
    true_and]
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, fun r h1 h2 => ?_⟩
  · simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
    rw [vdword_ld _ _ _ he]; exact hc.1 e he
  · simp only [RegUpd.v_setV_self]
    rw [vdword_ld _ _ _ he]; exact hc.2.1 e he
  · simp (disch := assumption) only [RegUpd.v_setV_of_ne]

/-- `convertF`: the rows of `[f₁]` and `[f₂]` at `FBUF`. -/
theorem convertF_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base)
    {f₁ f₂ : Nat} (h₁ : Below f₁) (h₂ : Below f₂) :
    WP isa (.block (convertF f₁ f₂)) s fun t =>
      FRows t.mem base (fun e => limbOf (feAt s.mem base (if e = 0 then f₁ else f₂))) 10 ∧
      Outside base FBUF 160 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.flags = s.flags := by
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  simp only [FBUF] at b1 b2
  rw [convertF, List.append_assoc, WP.block_append_iff]
  refine WP.mono (masks_ok hs hc) fun t ⟨tmk, tm, tg, tr, tw, tsp, tf, tv⟩ => ?_
  have ht : Scratch t base := scratch_of hs tg tw
  rw [WP.block_append_iff]
  refine WP.mono (words_ok ht a1 (by omega) a2 (by omega)) fun u ⟨uw, um, ug, ur, uw', usp, uf, uv⟩ => ?_
  have hu : Scratch u base := scratch_of ht ug uw'
  have umk : Masks u := ⟨fun e he => by rw [uv _ (by decide)]; exact tmk.1 e he,
    fun e he => by rw [uv _ (by decide)]; exact tmk.2 e he⟩
  rw [tm] at uw
  let F := fun e => limbOf (feAt s.mem base (if e = 0 then f₁ else f₂))
  let inv := fun n (x : State) =>
    WordsIn x s.mem base (fun e => if e = 0 then f₁ else f₂) ∧ Masks x ∧ FRows x.mem base F n ∧
    Outside base FBUF 160 s.mem x.mem ∧ x.gpr = s.gpr ∧ x.rd = s.rd ∧ x.wr = s.wr ∧ x.sp = s.sp ∧
    x.flags = s.flags
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10) inv (fun n x hn ⟨xw, xm, xr, xo, xg, xr', xw', xsp, xf⟩ => ?_) 10
    (by decide) u ⟨uw, umk, fun _ h => absurd h (by omega), by rw [um, tm]; exact Outside.refl _ _ _ _,
      ug.trans (tg), ur.trans tr, uw'.trans tw, usp.trans tsp, uf.trans tf⟩)
    fun x ⟨_, _, xr, xo, xg, xr', xw', xsp, xf⟩ => ⟨xr, xo, xg, xr', xw', xsp, xf⟩
  have hx : Scratch x base := scratch_of hs xg xw'
  refine WP.mono (rowF_ok hx xw xm hn) fun y ⟨yr, yo, yg, yr', yw, ysp, yf, yv⟩ =>
    ⟨fun k hk e he => by rw [yv _ (V_ne _ (by omega) _ (by decide) (by omega)) (V_ne _ (by omega) _ (by decide) (by omega))
      (V_ne _ (by omega) _ (by decide) (by omega))]; exact xw k hk e he,
     ⟨fun e he => by rw [yv _ (by decide) (by decide) (by decide)]; exact xm.1 e he,
      fun e he => by rw [yv _ (by decide) (by decide) (by decide)]; exact xm.2 e he⟩,
     fun i hi c hc => ?_, xo.trans (yo.mono (by simp only [FBUF]; omega) (by simp only [FBUF]; omega)),
     yg.trans xg, yr'.trans xr', yw.trans xw', ysp.trans xsp, yf.trans xf⟩
  rcases (show i < n ∨ i = n by omega) with h | rfl
  · rw [Outside.nw yo (by simp only [FBUF]; omega) (by simp only [FBUF]; omega)]; exact xr i h c hc
  · exact yr c hc


/-- The second operands: limb `j` of element `c mod 2` in word `c` of `v_j`, and 19 times it in `v_{9+j}`. -/
def GRegs (s : State) (G : Nat → Nat → Nat) (n : Nat) : Prop :=
  (∀ j < 10, ∀ c < 4, (vword (s.v (V j)) c).toNat = G (c % 2) j) ∧
  ∀ j < n, ∀ c < 4, (vword (s.v (V (10 + j))) c).toNat = 19 * G (c % 2) (j + 1)

/-- The constant 19 in each 32-bit lane of `v26`. -/
def C19In (s : State) : Prop := ∀ c < 4, (vword (s.v (V 26)) c).toNat = 19

theorem rowG_ok {s : State} {m : Mem} {base : Addr} {a : Nat → Nat}
    (hw : WordsIn s m base a) (hm : Masks s) {j : Nat} (hj : j < 10) :
    WP isa (.block (limb 19 24 25 28 29 j ++ [vo (.perm .uzp1 .s4 (V j) (V 28) (V 28))])) s fun t =>
      (∀ c < 4, (vword (t.v (V j)) c).toNat = limbOf (feAt m base (a (c % 2))) j) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags ∧
      ∀ r, r ≠ V 28 → r ≠ V 29 → r ≠ V j → t.v r = s.v r := by
  rw [WP.block_append_iff]
  refine WP.mono (limb_ok hw hm hj) fun t ⟨tl, tm, tg, tr, tw, tsp, tf, tv⟩ => ?_
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV]
  refine ⟨fun c hc => ?_, tm, tg, tr, tw, tsp, tf, fun r h1 h2 h3 => ?_⟩
  · simp only [RegUpd.v_setV_self]
    rw [uzp1_word _ _ c hc]
    have hc2 : c % 2 < 2 := Nat.mod_lt _ (by decide)
    have := limbOf_lt26 (feAt m base (a (c % 2))) j
    split <;> rw [tl _ hc2] <;> exact Nat.mod_eq_of_lt (by omega)
  · rw [RegUpd.v_setV_of_ne _ _ h3]; exact tv r h1 h2

theorem mulG_ok {s : State} {G : Nat → Nat → Nat} (hG : ∀ e j, G e j < 2 ^ 26) {n : Nat} (hn : n < 9)
    (hg : GRegs s G n) (h19 : C19In s) :
    WP isa (.block [vo (.mul (V (10 + n)) (V (n + 1)) (V 26))]) s fun t =>
      GRegs t G (n + 1) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.flags = s.flags ∧ ∀ r, r ≠ V (10 + n) → t.v r = s.v r := by
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV, flags_setV,
    true_and]
  have n10 : ∀ j < 10, V j ≠ V (10 + n) := fun j hj => V_ne _ (by omega) _ (by omega) (by omega)
  refine ⟨⟨fun j hj c hc => ?_, fun j hj c hc => ?_⟩, fun r h => RegUpd.v_setV_of_ne _ _ h⟩
  · rw [RegUpd.v_setV_of_ne _ _ (n10 j hj)]; exact hg.1 j hj c hc
  · rcases (show j < n ∨ j = n by omega) with h | rfl
    · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact hg.2 j h c hc
    · rw [RegUpd.v_setV_self, vword_map2 _ _ _ hc, BitVec.toNat_mul, hg.1 (j + 1) (by omega) c hc, h19 c hc]
      have := hG (c % 2) (j + 1)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]


theorem convertG_eq (g₁ g₂ : Nat) : convertG g₁ g₂ =
    [ldq 24 M26, ldq 25 M25] ++ [ldq 26 C19] ++ words g₁ g₂ 19 27 ++
    (List.range 10).flatMap (fun j => limb 19 24 25 28 29 j ++ [vo (.perm .uzp1 .s4 (V j) (V 28) (V 28))]) ++
    (List.range 9).flatMap (fun j => [vo (.mul (V (10 + j)) (V (j + 1)) (V 26))]) := rfl

/-- `convertG`: the limbs of `[g₁]` and `[g₂]`, and their 19 multiples, in `v0`–`v18`. -/
theorem convertG_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base)
    {g₁ g₂ : Nat} (h₁ : Below g₁) (h₂ : Below g₂) :
    WP isa (.block (convertG g₁ g₂)) s fun t =>
      GRegs t (fun e => limbOf (feAt s.mem base (if e = 0 then g₁ else g₂))) 9 ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.flags = s.flags := by
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  simp only [FBUF] at b1 b2
  rw [convertG_eq, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (masks_ok hs hc) fun t ⟨tmk, tm, tg, tr, tw, tsp, tf, tv⟩ => ?_
  have ht : Scratch t base := scratch_of hs tg tw
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ht 26 (by decide) (by decide), ?_⟩
  refine WP.block_nil_iff.mpr ?_
  have h19 : C19In (t.setV (V 26) (t.mem.read (off base C19) 16)) := fun c hc' => by
    rw [RegUpd.v_setV_self, vword_ld _ _ _ hc', tm]; exact hc.2.2 c hc'
  have tmk' : Masks (t.setV (V 26) (t.mem.read (off base C19) 16)) :=
    ⟨fun e he => by rw [RegUpd.v_setV_of_ne _ _ (by decide)]; exact tmk.1 e he,
     fun e he => by rw [RegUpd.v_setV_of_ne _ _ (by decide)]; exact tmk.2 e he⟩
  have t'm : (t.setV (V 26) (t.mem.read (off base C19) 16)).mem = s.mem := tm
  have t'g : (t.setV (V 26) (t.mem.read (off base C19) 16)).gpr = s.gpr := tg
  have t'r : (t.setV (V 26) (t.mem.read (off base C19) 16)).rd = s.rd := tr
  have t'w : (t.setV (V 26) (t.mem.read (off base C19) 16)).wr = s.wr := tw
  have t'sp : (t.setV (V 26) (t.mem.read (off base C19) 16)).sp = s.sp := tsp
  have t'f : (t.setV (V 26) (t.mem.read (off base C19) 16)).flags = s.flags := tf
  generalize t.setV (V 26) (t.mem.read (off base C19) 16) = t' at h19 tmk' t'm t'g t'r t'w t'sp t'f
  have ht' : Scratch t' base := scratch_of hs t'g t'w
  rw [WP.block_append_iff]
  refine WP.mono (words_ok ht' a1 (by omega) a2 (by omega)) fun u ⟨uw, um, ug, ur, uw', usp, uf, uv⟩ => ?_
  rw [t'm] at uw
  have umk : Masks u := ⟨fun e he => by rw [uv _ (by decide)]; exact tmk'.1 e he,
    fun e he => by rw [uv _ (by decide)]; exact tmk'.2 e he⟩
  have u19 : C19In u := fun c hc' => by rw [uv _ (by decide)]; exact h19 c hc'
  let G := fun e => limbOf (feAt s.mem base (if e = 0 then g₁ else g₂))
  let inv := fun n (x : State) =>
    WordsIn x s.mem base (fun e => if e = 0 then g₁ else g₂) ∧ Masks x ∧ C19In x ∧
    (∀ j < n, ∀ c < 4, (vword (x.v (V j)) c).toNat = G (c % 2) j) ∧
    x.mem = s.mem ∧ x.gpr = s.gpr ∧ x.rd = s.rd ∧ x.wr = s.wr ∧ x.sp = s.sp ∧ x.flags = s.flags
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 10) inv
    (fun n x hn ⟨xw, xm, x19, xg, xmm, xgg, xr, xww, xsp, xf⟩ => ?_) 10 (by decide) u
    ⟨uw, umk, u19, fun _ h => absurd h (by omega), um.trans t'm, ug.trans t'g, ur.trans t'r, uw'.trans t'w,
      usp.trans t'sp, uf.trans t'f⟩) fun x ⟨_, _, x19, xg, xmm, xgg, xr, xww, xsp, xf⟩ => ?_
  · refine WP.mono (rowG_ok xw xm hn) fun y ⟨yl, ym, yg, yr, yw, ysp, yf, yv⟩ =>
      ⟨fun k hk e he => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, fun c hc' => ?_, fun j hj c hc' => ?_,
        ym.trans xmm, yg.trans xgg, yr.trans xr, yw.trans xww, ysp.trans xsp, yf.trans xf⟩
    · rw [yv _ (V_ne _ (by omega) _ (by decide) (by omega)) (V_ne _ (by omega) _ (by decide) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega))]
      exact xw k hk e he
    · rw [yv _ (by decide) (by decide) (V_ne _ (by decide) _ (by omega) (by omega))]; exact xm.1 e he
    · rw [yv _ (by decide) (by decide) (V_ne _ (by decide) _ (by omega) (by omega))]; exact xm.2 e he
    · rw [yv _ (by decide) (by decide) (V_ne _ (by decide) _ (by omega) (by omega))]; exact x19 c hc'
    · rcases (show j < n ∨ j = n by omega) with h | rfl
      · rw [yv _ (V_ne _ (by omega) _ (by decide) (by omega)) (V_ne _ (by omega) _ (by decide) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega))]
        exact xg j h c hc'
      · exact yl c hc'
  · have hx : GRegs x G 0 := ⟨xg, fun _ h => absurd h (by omega)⟩
    let inv2 := fun n (y : State) =>
      GRegs y G n ∧ C19In y ∧ y.mem = s.mem ∧ y.gpr = s.gpr ∧ y.rd = s.rd ∧ y.wr = s.wr ∧ y.sp = s.sp ∧
      y.flags = s.flags
    refine WP.mono (wp_range_flatMap (M := isa) (N := 9) inv2
      (fun n y hn ⟨yg, y19, ymm, ygg, yr, yww, ysp, yf⟩ => ?_) 9 (by decide) x
      ⟨hx, x19, xmm, xgg, xr, xww, xsp, xf⟩) fun y ⟨yg, _, ymm, ygg, yr, yww, ysp, yf⟩ =>
        ⟨yg, ymm, ygg, yr, yww, ysp, yf⟩
    refine WP.mono (mulG_ok (fun e j => limbOf_lt26 _ _) hn yg y19) fun z ⟨zg, zm, zgg, zr, zw, zsp, zf, zv⟩ =>
      ⟨zg, fun c hc' => ?_, zm.trans ymm, zgg.trans ygg, zr.trans yr, zw.trans yww, zsp.trans ysp, zf.trans yf⟩
    rw [zv _ (V_ne _ (by decide) _ (by omega) (by omega))]; exact y19 c hc' 

end VG.Proof.X25519.AArch64.Hybrid
