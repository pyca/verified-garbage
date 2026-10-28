module

public import VerifiedGarbage.Proof.Argon2.Arm.Gb
import VerifiedGarbage.Proof.Argon2.Arm.Rounds
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.Arm.Rounds
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Argon2.Permutation
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.Arm.Gb

/-!
# Argon2 on ARMv7: the loops over the rows and the columns

A pass (`Impl.Argon2.Arm.pass`) runs P on row (column) 0 at `r3`, moving
`r3` on to the next row (column) each time, eight times, counting down in the
word at `r3 + 2088`, which moves with `r3`. `iter_ok`: an iteration from
`Inv n` (`8 - n` rows or columns done) reaches `Inv (n - 1)`, with the flags
saying whether `n - 1` is zero; `pass_ok`: a pass permutes every row
(column) of the block at `B` and writes nothing outside the block and the
counts; `rounds_ok`: the rows, then the columns.

Constant time (`pass_ct`): the taint analysis proves that each piece's
addresses depend only on `r3`, which both runs agree on, and the loop's
branches agree since the count is the same in both runs (`RelCT.loop`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (pass next ctrOff permuteAt wOff)
open VG.Proof.Sha512.Arm (A A_eq Reg64 rd64 mem_rd)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str wp_mov wp_add wp_sub wp_cmp op2_imm)

/-- The words in which the passes keep their counts. -/
abbrev ctrR (B : BitVec 32) : Region := ⟨State.addr B + BitVec.ofNat 64 2088, 2008⟩

/-- `scratch` at `B`: within the address space, and writable. -/
structure Scr (B : BitVec 32) (wr : List Region) : Prop where
  fit : B.toNat + 4096 ≤ 2 ^ 32
  wr : ∀ o, o + 4 ≤ 4096 → InRegions wr (A B o) 4

theorem Scr.reg64 {B : BitVec 32} {wr : List Region} (h : Scr B wr) : Reg64 wr B 2048 :=
  fun o ho => ⟨h.wr o (by omega), h.wr (o + 4) (by omega)⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

/-- A word of `scratch` outside the regions a pass writes is unchanged. -/
theorem outside_pass {m m' : Mem} (hf : Frame [permR B, ctrR B] m m') {d : Nat} (hd : d + 4 ≤ 1024 ∨
    (2048 ≤ d ∧ d + 4 ≤ 2088)) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [A_eq (by omega)]
  exact ⟨Offset.disjoint _ (by omega) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega)⟩

/-- A word of `scratch` beyond the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [permR B] m m') {d : Nat} (hd : 2048 ≤ d)
    (hd' : d + 4 ≤ 4096) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  rw [A_eq (by omega)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The permuted block is unchanged by writes to the counts. -/
theorem working_ctr {m m' : Mem} (hf : Frame [ctrR B] m m') : working m' B = working m B := by
  apply Vector.ext
  intro j hj
  have rd (o : Nat) (ho : o + 4 ≤ 2048) : m'.readW (A B o) 32 = m.readW (A B o) 32 := by
    refine hf.readW (r := ⟨A B o, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [A_eq (by omega)]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  simp only [working, Vector.getElem_ofFn, rd64, wOff]
  rw [rd _ (by omega), rd _ (by omega)]

/-- The count at `B + o` is written within the counts. -/
theorem ctr_contains {o : Nat} (ho : 2088 ≤ o) (ho' : o + 4 ≤ 4096) : (ctrR B).Contains (A B o) 4 := by
  rw [A_eq (by omega)]
  exact Offset.contains _ ho (by omega) (by omega)

end

/-! ## A pass -/

/-- What a pass needs of the row or column `index i` it permutes in iteration
`i`: they are injective, and `sh * i` words on from those of iteration 0. -/
structure PassOk (index : Fin 8 → Fin 16 → Fin 128) (sh : Nat) : Prop where
  inj : ∀ i, Function.Injective (index i)
  idx : ∀ i k, (index i k).val = (index 0 k).val + sh * i.val
  le : sh ≤ 16
  enc : encodable (BitVec.ofNat 32 (8 * sh)) = true
  enc8 : encodable (BitVec.ofNat 32 (8 * (8 * sh))) = true

theorem rows_ok : PassOk rowIndex 16 :=
  ⟨Proof.Argon2.rowIndex_injective, fun i k => by simp only [rowIndex]; omega, by decide, by decide,
    by decide⟩

theorem cols_ok : PassOk colIndex 2 :=
  ⟨Proof.Argon2.colIndex_injective, fun i k => by simp only [colIndex]; omega, by decide, by decide,
    by decide⟩

theorem foldl_take_succ {α : Type} (f : α → Fin 8 → α) (x : α) {j : Nat} (hj : j < 8) :
    ((List.finRange 8).take (j + 1)).foldl f x = f (((List.finRange 8).take j).foldl f x) ⟨j, hj⟩ := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hj)]
  simp

theorem off_le {sh j : Nat} (hsh : sh ≤ 16) (hj : j ≤ 8) : sh * j ≤ 128 :=
  Nat.le_trans (Nat.mul_le_mul hsh hj) (by decide)

section
variable (index : Fin 8 → Fin 16 → Fin 128) (sh : Nat) (s₀ : State)

/-- After `8 - n` iterations of a pass from `s₀`, with `n` left. -/
structure Inv (n : Nat) (s : State) : Prop where
  le : n ≤ 8
  r3 : s.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - n)))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ctr : s.mem.readW (A (s₀.gpr .r3) (8 * (sh * (8 - n)) + ctrOff)) 32 = BitVec.ofNat 32 n
  working : working s.mem (s₀.gpr .r3) = ((List.finRange 8).take (8 - n)).foldl
    (fun b i => Spec.Argon2.permuteAt (index i) b) (working s₀.mem (s₀.gpr .r3))
  frame : Frame [permR (s₀.gpr .r3), ctrR (s₀.gpr .r3)] s₀.mem s.mem

end

/-- What a pass leaves: `r3` and the regions as they were, the block at `B`
permuted to `v`, and nothing written outside it and the counts. -/
structure Passed (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  r3 : t.gpr .r3 = s.gpr .r3
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  working : working t.mem B = v
  frame : Frame [permR B, ctrR B] s.mem t.mem

theorem Passed.trans {B : BitVec 32} {s t u : State} {v w : Block} (h : Passed B s v t)
    (h' : Passed B t w u) : Passed B s w u :=
  ⟨h'.r3.trans h.r3, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.working,
    h.frame.trans h'.frame⟩

theorem count_sub : ∀ n < 9, 1 ≤ n → BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by decide

theorem count_ne : ∀ n < 9, 1 ≤ n →
    (!(BitVec.ofNat 32 (n - 1) - 0 == 0)) = decide (n - 1 ≠ 0) := by decide

theorem finish_r3 (sh : Nat) (x : BitVec 32) :
    x + BitVec.ofNat 32 (8 * (sh * (8 - 0))) - BitVec.ofNat 32 (8 * (8 * sh)) = x := by
  rw [Nat.sub_zero, Nat.mul_comm sh 8, BitVec.add_sub_cancel]

section
variable {index : Fin 8 → Fin 16 → Fin 128} {sh : Nat} (hP : PassOk index sh) {s₀ : State}
  (hs : Scr (s₀.gpr .r3) s₀.wr)
include hP hs

/-- One iteration of a pass, from `n ≥ 1` rows or columns left. -/
theorem iter_ok {n : Nat} (hn : 1 ≤ n) {s : State} (h : Inv index sh s₀ n s) :
    WP isa (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) s fun t =>
      Inv index sh s₀ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)) := by
  have fit := hs.fit
  have hle := h.le
  have hsh := hP.le
  have hi : 8 - n < 8 := by omega
  have o₀ := off_le hsh (Nat.sub_le 8 n)
  have o₁ := off_le hsh (Nat.sub_le 8 (n - 1))
  have e₁ : 8 * (sh * (8 - n)) + 8 * sh = 8 * (sh * (8 - (n - 1))) := by
    rw [show 8 - (n - 1) = 8 - n + 1 by omega, Nat.mul_succ, Nat.mul_add]
  apply WP.seq
  refine (permuteAt_ok fit (index ⟨8 - n, hi⟩) (index 0) (sh * (8 - n)) (hP.idx _) (hP.inj _)
    ⟨h.r3, by rw [h.wr]; exact hs.reg64⟩).mono fun t st => ?_
  have k := st.keep
  have r3t : t.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - n))) := k.r3.trans h.r3
  unfold next
  refine wp_ldr (a := A (s₀.gpr .r3) (8 * (sh * (8 - n)) + ctrOff)) (by decide)
    (by rw [r3t]; exact A_shift _ _ _)
    (mem_rd (by rw [k.wr, h.wr]; exact hs.wr _ (by simp only [ctrOff]; omega))) fun t₁ u₁ => ?_
  refine wp_sub (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_add (op2_imm hP.enc) fun t₃ u₃ => ?_
  have r3₃ : t₃.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - (n - 1)))) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3t, BitVec.add_assoc,
      ← BitVec.ofNat_add, e₁]
  refine wp_str (a := A (s₀.gpr .r3) (8 * (sh * (8 - (n - 1))) + ctrOff)) (by decide)
    (by rw [r3₃]; exact A_shift _ _ _)
    (by rw [u₃.wr, u₂.wr, u₁.wr, k.wr, h.wr]; exact hs.wr _ (by simp only [ctrOff]; omega))
    fun t₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t₅ u₅ hz => WP.block_nil ?_
  have v₁ : t₁.gpr .r0 = BitVec.ofNat 32 n := by
    rw [u₁.gpr, outside_perm fit st.frame (by simp only [ctrOff]; omega) (by simp only [ctrOff]; omega),
      h.ctr]
  have v₃ : t₃.gpr .r0 = BitVec.ofNat 32 (n - 1) := by
    rw [u₃.other _ (by decide), u₂.gpr, v₁, count_sub n (by omega) hn]
  have m₅ : t₅.mem = t.mem.writeW (A (s₀.gpr .r3) (8 * (sh * (8 - (n - 1))) + ctrOff))
      (BitVec.ofNat 32 (n - 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  have cf : Frame [ctrR (s₀.gpr .r3)] t.mem t₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (ctr_contains fit (by simp only [ctrOff]; omega) (by simp only [ctrOff]; omega))
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, u₄.gpr, r3₃]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, k.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, k.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, k.sp, h.sp]
  · rw [m₅, Mem.readW_writeW_self32]
  · rw [working_ctr fit cf, st.working, h.working, show 8 - (n - 1) = 8 - n + 1 by omega,
      foldl_take_succ _ _ hi]
  · rw [m₅]
    exact (h.frame.trans (st.frame.mono (by simp))).writeW (by simp) _
      (ctr_contains fit (by simp only [ctrOff]; omega) (by simp only [ctrOff]; omega))
  · show some (!t₅.z) = _
    rw [hz, u₄.gpr, v₃, count_ne n (by omega) hn]

omit hP in
/-- The start of a pass: eight rows or columns left. -/
theorem start_ok :
    WP isa (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) s₀ (Inv index sh s₀ 8) := by
  have fit := hs.fit
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_
  refine wp_str (by decide) (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact hs.wr _ (by decide))
    fun t₂ u₂ => WP.block_nil ?_
  have m₂ : t₂.mem = s₀.mem.writeW (A (s₀.gpr .r3) ctrOff) (BitVec.ofNat 32 8) := by
    rw [u₂.mem, u₁.mem, u₁.gpr]; rfl
  have z : 8 * (sh * (8 - 8)) = 0 := by simp
  have cf : Frame [ctrR (s₀.gpr .r3)] s₀.mem t₂.mem := by
    rw [m₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ctr_contains fit (by decide) (by decide))
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.other _ (by decide), z]; exact (BitVec.add_zero _).symm
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]
  · rw [m₂, z, Nat.zero_add, Mem.readW_writeW_self32]
  · rw [working_ctr fit cf]; rfl
  · rw [m₂]
    exact (Frame.refl _ _).writeW (by simp) _ (ctr_contains fit (by decide) (by decide))

/-- The loop of a pass, from the start. -/
theorem loop_ok {s : State} (h : Inv index sh s₀ 8 s) :
    WP isa (.loop (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) .ne) s (Inv index sh s₀ 0) := by
  have step (n : Nat) (u : State) (hu : Inv index sh s₀ n u ∧ 1 ≤ n) :
      WP isa (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) u fun t =>
        (isa.eval .ne t = some false ∧ Inv index sh s₀ 0 t) ∨
        (isa.eval .ne t = some true ∧ ∃ m < n, Inv index sh s₀ m t ∧ 1 ≤ m) := by
    refine (iter_ok hP hs hu.2 hu.1).mono fun t ⟨ht, he⟩ => ?_
    by_cases hz : n - 1 = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false] at he
      exact .inl ⟨he, hz ▸ ht⟩
    · simp only [hz, ne_eq, not_false_eq_true, decide_true] at he
      exact .inr ⟨he, n - 1, by omega, ht, by omega⟩
  exact VG.WP.loop (M := isa) (fun (n : Nat) (u : State) => Inv index sh s₀ n u ∧ 1 ≤ n) step 8 s
    ⟨h, by decide⟩

/-- A pass permutes every row (column), and writes nothing outside the block
and the counts. -/
theorem pass_ok :
    WP isa (pass (index 0) (8 * sh)) s₀ (Passed (s₀.gpr .r3) s₀
      ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (index i) b)
        (working s₀.mem (s₀.gpr .r3)))) := by
  unfold pass
  refine WP.seq ((start_ok hs).mono fun s₁ h₁ => WP.seq ((loop_ok hP hs h₁).mono fun s₂ h₂ => ?_))
  refine wp_sub (op2_imm hP.enc8) fun t u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u.gpr, h₂.r3, finish_r3 sh _]
  · rw [u.rd, h₂.rd]
  · rw [u.wr, h₂.wr]
  · rw [u.sp, h₂.sp]
  · rw [u.mem, h₂.working, Nat.sub_zero, List.take_of_length_le (by simp)]
  · rw [u.mem]; exact h₂.frame

end

/-- The rows, then the columns. -/
theorem rounds_ok {s : State} (hs : Scr (s.gpr .r3) s.wr) :
    WP isa Impl.Argon2.Arm.rounds s (Passed (s.gpr .r3) s
      ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (colIndex i) b)
        ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (rowIndex i) b)
          (working s.mem (s.gpr .r3))))) := by
  show WP isa (.seq (pass (rowIndex 0) (8 * 16)) (pass (colIndex 0) (8 * 2))) s _
  refine WP.seq ((pass_ok rows_ok hs).mono fun t ht => ?_)
  have hs' : Scr (t.gpr .r3) t.wr := by rw [ht.r3, ht.wr]; exact hs
  refine (pass_ok cols_ok hs').mono fun u hu => ?_
  rw [ht.r3, ht.working] at hu
  exact ht.trans hu

/-! ## Constant time -/

/-- Two runs on the same `scratch`. -/
def PassRel (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ Scr (s₁.gpr .r3) s₁.wr ∧ Scr (s₂.gpr .r3) s₂.wr

section
variable {index : Fin 8 → Fin 16 → Fin 128} {sh : Nat} (hP : PassOk index sh)
include hP

/-- Two runs of a pass leak the same, given that the taint analysis proves
that the addresses of the loop's body and of the end of the pass depend only
on `r3`. -/
theorem pass_ct
    (hbody : ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r3])
      (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) hc).isSome = true)
    (hfin : ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r3])
      (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) hc).isSome = true) :
    RelCT isa PassRel (pass (index 0) (8 * sh)) PassRel := by
  obtain ⟨_, hbody⟩ := hbody
  obtain ⟨_, hfin⟩ := hfin
  unfold pass
  let I (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ σ₁ σ₂, PassRel σ₁ σ₂ ∧ Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂
  have agree {n : Nat} {σ₁ σ₂ : State} (hp : PassRel σ₁ σ₂) (s₁ s₂ : State)
      (h : Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂) :
      VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs [.r3]) s₁ s₂ :=
    VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r3, h.2.r3, hp.1]
  -- The start.
  have hstart : RelCT isa PassRel (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) (I 8) := by
    have ct : RelCT isa PassRel (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) fun _ _ => True :=
      RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r3]) (fun s₁ s₂ h => VG.Arm.Taint.agree_ofRegs
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide)
    refine (ct.wpDep (F := fun σ => Inv index sh σ 8)
      fun s₁ s₂ h => ⟨start_ok h.2.1, start_ok h.2.2⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, i₁, i₂⟩
    exact ⟨σ₁, σ₂, hp, i₁, i₂⟩
  -- The loop.
  have hloop : RelCT isa (I 8) (.loop (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) .ne)
      (I 0) := by
    refine (RelCT.loop (fun n s₁ s₂ => I n s₁ s₂ ∧ 1 ≤ n) (fun n => ?_) 8).mono
      (fun s₁ s₂ h => ⟨h, by decide⟩) (fun _ _ h => h)
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨σ₁, σ₂, hp, i₁, i₂⟩, hn⟩ e₁ e₂
    have ct := (RelCT.taint (A := taint)
      (P := fun s₁ s₂ => Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂) (VG.Arm.Taint.ofRegs [.r3])
      (agree hp) hbody).wp
      (F₁ := fun t => Inv index sh σ₁ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)))
      (F₂ := fun t => Inv index sh σ₂ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)))
      (fun _ _ h => ⟨iter_ok hP hp.2.1 hn h.1, iter_ok hP hp.2.2 hn h.2⟩)
    obtain ⟨ht, -, ⟨j₁, c₁⟩, ⟨j₂, c₂⟩⟩ := ct _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂
    refine ⟨ht, by rw [c₁, c₂], fun hf => ?_, fun htr => ?_⟩
    · rw [c₁] at hf
      have hz : n - 1 = 0 := by simpa using hf
      exact ⟨σ₁, σ₂, hp, hz ▸ j₁, hz ▸ j₂⟩
    · rw [c₁] at htr
      have hz : n - 1 ≠ 0 := by simpa using htr
      exact ⟨n - 1, by omega, ⟨σ₁, σ₂, hp, j₁, j₂⟩, by omega⟩
  -- The end.
  have hend : RelCT isa (I 0)
      (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) PassRel := by
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, hp, i₁, i₂⟩ e₁ e₂
    have fin_ok {σ s : State} (i : Inv index sh σ 0 s) :
        WP isa (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) s
          fun t => t.gpr .r3 = σ.gpr .r3 ∧ t.wr = σ.wr :=
      wp_sub (op2_imm hP.enc8) fun t u => WP.block_nil
        ⟨by rw [u.gpr, i.r3, finish_r3 sh _], by rw [u.wr, i.wr]⟩
    have ct := (RelCT.taint (A := taint)
      (P := fun s₁ s₂ => Inv index sh σ₁ 0 s₁ ∧ Inv index sh σ₂ 0 s₂) (VG.Arm.Taint.ofRegs [.r3])
      (agree hp) hfin).wp (fun _ _ h => ⟨fin_ok h.1, fin_ok h.2⟩)
    obtain ⟨ht, -, ⟨a₁, w₁⟩, ⟨a₂, w₂⟩⟩ := ct _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂
    refine ⟨ht, by rw [a₁, a₂, hp.1], ?_, ?_⟩
    · rw [a₁, w₁]; exact hp.2.1
    · rw [a₂, w₂]; exact hp.2.2
  exact hstart.seq (hloop.seq hend)

end

/-- The rows, then the columns. -/
theorem rounds_ct : RelCT isa PassRel Impl.Argon2.Arm.rounds PassRel := by
  show RelCT isa PassRel (.seq (pass (rowIndex 0) (8 * 16)) (pass (colIndex 0) (8 * 2))) PassRel
  exact (pass_ct rows_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    (pass_ct cols_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)

end VG.Proof.Argon2.Arm
