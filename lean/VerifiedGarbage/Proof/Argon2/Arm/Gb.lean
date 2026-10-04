import VerifiedGarbage.Proof.Argon2.Arm.Mix
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on ARMv7: GB on the permuted block

`wp_gb`: GB on the words at `[r3, #a]`, …, `[r3, #d]` stores the words of
`Proof.Argon2.mix` (`gbMem`), with the registers of `gbRegs` written. The
permuted block in `scratch[1024, 2048)` as a vector of words (`working`), and
`gbAt_ok`: one GB updates it as `Proof.Argon2.mixWords`, and writes nothing
else.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Sha512.Arm (lo hi ld st)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr')
open VG.Impl.Argon2.Arm (gb gbAt wOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A Reg64 Wrote wp_st mem_rd rd64_write64_self
  rd64_write64_ne frame_write64)
open VG.Proof.Blake2.ArmB (wp_ld64 wp_xor64 wp_rotr wp_rotr' pair_swap)

/-- The registers GB writes. -/
def gbRegs : List Reg := [.r0, .r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The memory after GB on the words at `V + a`, …, `V + d`. -/
def gbMem (m : Mem) (V : BitVec 32) (a b c d : Nat) : Mem :=
  let r := Proof.Argon2.mix (rd64 m V a) (rd64 m V b) (rd64 m V c) (rd64 m V d)
  write64 (write64 (write64 (write64 m V a r.1) V b r.2.1) V c r.2.2.1) V d r.2.2.2

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_gb {a b c d : Nat} {V : BitVec 32} {N : Nat} (hN : N ≤ 4092)
    (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) (hc : c + 8 ≤ N) (hd : d + 8 ≤ N)
    (hRV : Reg64 s.wr V N) (h3 : s.gpr .r3 = V)
    (K : ∀ s', Wrote gbRegs s s' (gbMem s.mem V a b c d) → WP isa (.block rest) s' Q) :
    WP isa (.block (gb a b c d ++ rest)) s Q := by
  unfold gb
  simp only [List.append_assoc]
  have iV : ∀ o, o + 8 ≤ N → InRegions (s.rd ++ s.wr) (A V o) 4 ∧
      InRegions (s.rd ++ s.wr) (A V (o + 4)) 4 := fun o ho => ⟨mem_rd (hRV o ho).1, mem_rd (hRV o ho).2⟩
  -- Load the four words.
  refine wp_ld64 (by decide) (by decide) (by omega) h3 rfl (iV a ha).1 (iV a ha).2
    fun s₁ o₁ pa => ?_
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3]) o₁.mem
    (by rw [o₁.rd, o₁.wr]; exact (iV b hb).1) (by rw [o₁.rd, o₁.wr]; exact (iV b hb).2)
    fun s₂ o₂ pb => ?_
  have O₂ := o₁.trans o₂
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), h3]) O₂.mem
    (by rw [O₂.rd, O₂.wr]; exact (iV c hc).1) (by rw [O₂.rd, O₂.wr]; exact (iV c hc).2)
    fun s₃ o₃ pc => ?_
  have O₃ := O₂.trans o₃
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), h3]) O₃.mem
    (by rw [O₃.rd, O₃.wr]; exact (iV d hd).1) (by rw [O₃.rd, O₃.wr]; exact (iV d hd).2)
    fun s₄ o₄ pd => ?_
  have O₄ := O₃.trans o₄
  -- a := addMul(a, b)
  refine addMul_ok (by decide) (pa.of_only ((o₂.trans o₃).trans o₄) (by decide) (by decide))
    (pb.of_only (o₃.trans o₄) (by decide) (by decide)) fun s₅ o₅ pa₁ => ?_
  -- d := (d ⊕ a) >>> 32
  refine wp_xor64 (by decide) (by decide) (pd.of_only o₅ (by decide) (by decide)) pa₁
    fun s₆ o₆ p₆ => ?_
  have pd₁ := pair_swap p₆
  -- c := addMul(c, d)
  refine addMul_ok (by decide) (pc.of_only ((o₄.trans o₅).trans o₆) (by decide) (by decide)) pd₁
    fun s₇ o₇ pc₁ => ?_
  -- b := (b ⊕ c) >>> 24
  refine wp_xor64 (by decide) (by decide)
    (pb.of_only ((((o₃.trans o₄).trans o₅).trans o₆).trans o₇) (by decide) (by decide)) pc₁
    fun s₈ o₈ p₈ => ?_
  refine wp_rotr (n := 24) (by decide) (by decide) (by decide) (by decide) (by decide) p₈
    fun s₉ o₉ pb₁ => ?_
  -- a := addMul(a, b)
  refine addMul_ok (by decide) (pa₁.of_only ((((o₆.trans o₇).trans o₈).trans o₉)) (by decide) (by decide))
    pb₁ fun s₁₀ o₁₀ pa₂ => ?_
  -- d := (d ⊕ a) >>> 16
  refine wp_xor64 (by decide) (by decide)
    (pd₁.of_only ((((o₇.trans o₈).trans o₉).trans o₁₀)) (by decide) (by decide)) pa₂
    fun s₁₁ o₁₁ p₁₁ => ?_
  refine wp_rotr (n := 16) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₁
    fun s₁₂ o₁₂ pd₂ => ?_
  -- c := addMul(c, d)
  refine addMul_ok (by decide)
    (pc₁.of_only (((((o₈.trans o₉).trans o₁₀).trans o₁₁).trans o₁₂)) (by decide) (by decide)) pd₂
    fun s₁₃ o₁₃ pc₂ => ?_
  -- b := (b ⊕ c) >>> 63
  refine wp_xor64 (by decide) (by decide)
    (pb₁.of_only ((((o₁₀.trans o₁₁).trans o₁₂).trans o₁₃)) (by decide) (by decide)) pc₂
    fun s₁₄ o₁₄ p₁₄ => ?_
  refine wp_rotr' (n := 63) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₄
    fun s₁₅ o₁₅ pb₂ => ?_
  have O₁₅ := ((((((((((O₄.trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀).trans
    o₁₁).trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅
  have pa₂' := pa₂.of_only ((((o₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅) (by decide) (by decide)
  have pc₂' := pc₂.of_only (o₁₄.trans o₁₅) (by decide) (by decide)
  have pd₂' := pd₂.of_only ((o₁₃.trans o₁₄).trans o₁₅) (by decide) (by decide)
  -- Store them.
  have w : Reg64 s₁₅.wr V N := by rw [O₁₅.wr]; exact hRV
  have r3 : s₁₅.gpr .r3 = V := by rw [O₁₅.gpr _ (by decide), h3]
  refine wp_st (by omega) r3 pa₂' (w a ha).1 (w a ha).2 fun s₁₆ u₁₆ => ?_
  refine wp_st (by omega) (by rw [u₁₆.gpr, r3]) (by rw [Pair, u₁₆.gpr]; exact pb₂)
    (by rw [u₁₆.wr]; exact (w b hb).1) (by rw [u₁₆.wr]; exact (w b hb).2) fun s₁₇ u₁₇ => ?_
  refine wp_st (by omega) (by rw [u₁₇.gpr, u₁₆.gpr, r3]) (by rw [Pair, u₁₇.gpr, u₁₆.gpr]; exact pc₂')
    (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).1) (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).2)
    fun s₁₈ u₁₈ => ?_
  refine wp_st (by omega) (by rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, r3])
    (by rw [Pair, u₁₈.gpr, u₁₇.gpr, u₁₆.gpr]; exact pd₂')
    (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr]; exact (w d hd).1)
    (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr]; exact (w d hd).2) fun s₁₉ u₁₉ => K s₁₉ ⟨fun r hr => ?_, ?_,
      by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, O₁₅.rd], by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, O₁₅.wr],
      by rw [u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, O₁₅.sp]⟩
  · rw [u₁₉.gpr, u₁₈.gpr, u₁₇.gpr, u₁₆.gpr]
    exact (O₁₅.mono (by decide)).gpr r hr
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, O₁₅.mem]
    rfl

end

/-! ## The permuted block -/

/-- The permuted block, at `B + 1024`. -/
def working (m : Mem) (B : BitVec 32) : Block := Vector.ofFn fun i => rd64 m B (wOff i.val)

theorem working_get (m : Mem) (B : BitVec 32) (i : Fin 128) :
    (working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The permuted block's region. -/
abbrev permR (B : BitVec 32) : Region := ⟨State.addr B + BitVec.ofNat 64 1024, 1024⟩

theorem wOff_lt (i : Fin 128) : wOff i.val + 8 ≤ 2048 := by have := i.isLt; simp only [wOff]; omega

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : Word) :
    working (write64 m B (wOff i.val) v) B = (working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true]
    exact rd64_write64_self m v (by have := wOff_lt i; omega)
  · simp only [h, ite_false]
    exact rd64_write64_ne m v (by have := wOff_lt i; omega) (by simp only [wOff]; omega)
      (by simp only [wOff]; omega)

/-- A write to a word of the permuted block stays in its region. -/
theorem frame_write (m m' : Mem) (hf : Frame [permR B] m m') (i : Fin 128) (v : Word) :
    Frame [permR B] m (write64 m' B (wOff i.val) v) := by
  have c : ∀ e, e + 4 ≤ 1024 → (permR B).Contains (A B (1024 + e)) 4 := fun e he => by
    rw [VG.Proof.Sha512.Arm.A_eq (by omega), ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ he (by omega)
  have m₁ := List.mem_singleton_self (permR B)
  have := i.isLt
  simp only [write64]
  exact (hf.writeW m₁ _ (c (8 * i.val) (by omega))).writeW m₁ _
    (by rw [show wOff i.val + 4 = 1024 + (8 * i.val + 4) by simp only [wOff]; omega]
        exact c _ (by omega))

end

/-! ## GB -/

/-- `s'` is `s` but for the registers GB writes and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ gbRegs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : Keep s s₁) (k₂ : Keep s₁ s₂) : Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp⟩

theorem Keep.r3 {s s' : State} (k : Keep s s') : s'.gpr .r3 = s.gpr .r3 := k.gpr _ (by decide)

/-- What a step of GB leaves: the registers but GB's, and the memory at `B`
with the permuted block `v` in place of the old one, `Frame [permR B]`. -/
structure Step (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  keep : Keep s t
  working : working t.mem B = v
  frame : Frame [permR B] s.mem t.mem

theorem Step.trans {B : BitVec 32} {s t u : State} {v w : Block} (h : Step B s v t) (h' : Step B t w u) :
    Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

theorem gbAt_ok {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32) {s : State} (h3 : s.gpr .r3 = B)
    (hA : Reg64 s.wr B 2048) (a b c d : Fin 128) :
    WP isa (gbAt a.val b.val c.val d.val) s
      (Step B s (Proof.Argon2.mixWords (working s.mem B) a b c d)) := by
  unfold gbAt
  rw [← List.append_nil (gb _ _ _ _)]
  refine wp_gb (N := 2048) (by decide) (wOff_lt a) (wOff_lt b) (wOff_lt c) (wOff_lt d) hA h3
    fun t w => WP.block_nil ⟨⟨w.gpr, w.rd, w.wr, w.sp⟩, ?_, ?_⟩
  · rw [w.mem, gbMem]
    simp only [working_write hfit, ← working_get]
    rfl
  · rw [w.mem, gbMem]
    exact frame_write hfit _ _ (frame_write hfit _ _ (frame_write hfit _ _ (frame_write hfit _ _
      (Frame.refl _ _) _ _) _ _) _ _) _ _

end VG.Proof.Argon2.Arm
