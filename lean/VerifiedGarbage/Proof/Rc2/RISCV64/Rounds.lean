module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Mix
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.RISCV64.Lookup

/-!
# RC2 on RISC-V: the steps of the rounds

`mix_run`, `reverseMix_run` and `mash_run`: each step maps the four words
in `a3`–`a6` (`Holds`) to the specification's step of them.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem getD_set (v : Spec.Rc2.State) (x : BitVec 16) {i j : Nat} (hj : j < 4) :
    (v.set! i x).getD j 0 = if i = j then x else v.getD j 0 := by
  rw [Proof.Rc2.getD_eq_getElem _ _ hj, Proof.Rc2.getD_eq_getElem _ _ hj]
  simp [Vector.getElem_set!]

theorem wordReg_0 : wordReg 0 = .a3 := rfl
theorem wordReg_1 : wordReg 1 = .a4 := rfl
theorem wordReg_2 : wordReg 2 = .a5 := rfl
theorem wordReg_3 : wordReg 3 = .a6 := rfl
theorem wordReg_4 : wordReg 4 = .a3 := rfl
theorem wordReg_5 : wordReg 5 = .a4 := rfl
theorem wordReg_6 : wordReg 6 = .a5 := rfl

/-- `Holds` after changing word `i`. -/
theorem Holds.set {v : Spec.Rc2.State} {u t : State} (H : Holds v u) {i : Nat} {x : BitVec 16}
    (hx : t.gpr (wordReg i) = x.setWidth 64) (hk : ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i')) :
    Holds (v.set! i x) t := by
  intro i' hi'
  rw [getD_set _ _ hi']
  by_cases h : i = i'
  · subst h; rw [ite_eq_left rfl]; exact hx
  · rw [ite_eq_right h, hk i' hi' (Ne.symm h)]; exact H i' hi'

/-- The words before `i`: their registers' values. -/
theorem Holds.nb {v : Spec.Rc2.State} {u : State} (H : Holds v u) (i d : Nat) :
    u.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := by
  have := H ((i + d) % 4) (Nat.mod_lt _ (by decide))
  rw [← this]; congr 1; simp [wordReg]

theorem mix_val (X K A B C : BitVec 16) (k : BitVec 64) (hk : k.setWidth 16 = K) :
    ((X.setWidth 64 + k + (A.setWidth 64 &&& B.setWidth 64) +
      (C.setWidth 64 ^^^ (A.setWidth 64 &&& C.setWidth 64))) <<< 48) >>> 48 =
      (X + K + (A &&& B) + (~~~A &&& C)).setWidth 64 := by
  rw [mask16]
  congr 1
  simp only [lo16_add, lo16_and, lo16_xor, lo16_ext, hk, andNot_xor]

theorem rmix_val (X K A B C : BitVec 16) (k : BitVec 64) (hk : k.setWidth 16 = K) :
    ((X.setWidth 64 - k - (A.setWidth 64 &&& B.setWidth 64) -
      (C.setWidth 64 ^^^ (A.setWidth 64 &&& C.setWidth 64))) <<< 48) >>> 48 =
      (X - K - (A &&& B) - (~~~A &&& C)).setWidth 64 := by
  rw [mask16]
  congr 1
  simp only [lo16_sub, lo16_and, lo16_xor, lo16_ext, hk, andNot_xor]

/-- The first three instructions of a mix's inputs. -/
def andInputs (i : Nat) : List Instr :=
  [.logic .and .t0 (wordReg (i + 3)) (wordReg (i + 2)), .logic .and .t1 (wordReg (i + 3)) (wordReg (i + 1)),
   .logic .xor .t1 (wordReg (i + 1)) .t1]

theorem andInputs_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (andInputs i)) u fun t =>
      t.gpr .t0 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .t1 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem ∧ Keep [.t0, .t1] u t := by
  refine WP.mono (WP.keep [.t0, .t1] (c := .block (andInputs i)) (Q := fun t =>
      t.gpr .t0 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .t1 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold andInputs; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3, wordReg_4, wordReg_5, wordReg_6])

/-- The sum and rotation of a mix, on word `i` of `a3`–`a6`. -/
theorem addRot_run (u : State) {i s : Nat} (hi : i < 4) (hs : 1 ≤ s ∧ s < 16) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) + u.gpr .t2 + u.gpr .t0 + u.gpr .t1) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (addInputs (wordReg i) ++ rotateSum (wordReg i) s)) u fun t =>
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.a7, wordReg i] u t := by
  refine WP.mono (WP.keep [.a7, wordReg i] (c := .block (addInputs (wordReg i) ++ rotateSum (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, addInputs, rotateSum, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  have h48 : (48 : Nat) < 64 := by decide
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold addInputs rotateSum
    rrun [show 48 + s < 64 by omega, show 64 - s < 64 by omega]
    rw [mask16] at hy
    have h16 := congrArg (BitVec.setWidth 16) hy
    rw [lo16_ext, lo16_ext] at h16
    rw [rotSum16 _ hs.1 hs.2, h16]

theorem wordReg_ne : ∀ i' < 4, ∀ i < 4, i' ≠ i → wordReg i' ≠ wordReg i := by decide
theorem wordReg_other : ∀ i < 4, wordReg i ∉ [Reg.a7, .a2, .a1, .t3, .t0, .t1, .t2] := by decide
theorem rotation_bounds : ∀ i < 4, 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by decide

/-- A step that changes only word `i` and the code's temporaries. -/
theorem keep_others {u t : State} {i : Nat} (hi : i < 4) (k : Keep [.a7, .t0, .t1, .t2, wordReg i] u t) :
    ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i') := fun i' hi' hne => by
  refine k.gpr ?_
  have h1 := wordReg_other i' hi'
  have h2 := wordReg_ne i' hi' i hi hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨h1.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

theorem mix_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u) {j i : Nat}
    (hj : j < 64) (hi : i < 4) :
    WP isa (.block (mix j i)) u fun t =>
      Holds (Spec.Rc2.mix (Spec.Rc2.scheduleAt u.mem T) j i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t0, .t1, .t2, wordReg i] u t := by
  have e : mix j i = andInputs i ++ (loadKey j ++ (addInputs (wordReg i) ++
      rotateSum (wordReg i) (Spec.Rc2.rotation i))) := by
    simp only [mix, mixInputs, andInputs, List.append_assoc, List.cons_append, List.nil_append]
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  rw [e, WP.block_append_iff]
  refine WP.mono (andInputs_run u hi) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_run t₁ (E.keep k₁ (by decide)) hj) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have x2 : t₂.gpr (wordReg i) = u.gpr (wordReg i) := by
    rw [k₂.gpr (by simp; exact Ne.symm o.2.2.2.2.2.2 |> fun h => by simpa using o.2.2.2.2.2.2),
      k₁.gpr (by simp; exact ⟨o.2.2.2.2.1, o.2.2.2.2.2.1⟩)]
  have r10 : t₂.gpr .t0 = t₁.gpr .t0 := k₂.gpr (by decide)
  have r11 : t₂.gpr .t1 = t₁.gpr .t1 := k₂.gpr (by decide)
  have hs := rotation_bounds i hi
  refine WP.mono (addRot_run t₂ hi hs (y := v.getD i 0 + (Spec.Rc2.scheduleAt u.mem T).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) + (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0))
    (by rw [x2, r10, r11, a₁, b₁, H i hi, H.nb i 3, H.nb i 2, H.nb i 1]
        exact mix_val _ _ _ _ _ _ (by rw [a₂, m₁])))
    fun t₃ ⟨a₃, m₃, k₃⟩ => ⟨?_, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  exact H.set (by rw [a₃]) (keep_others hi (((k₁.trans k₂).trans k₃).mono (by simp)))

theorem rot_run (u : State) {i s : Nat} (hi : i < 4) (hs : 1 ≤ s ∧ s < 16) {y : BitVec 16}
    (hy : u.gpr (wordReg i) = y.setWidth 64) :
    WP isa (.block (rotate16 (wordReg i) s)) u fun t =>
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.a7, wordReg i] u t := by
  refine WP.mono (WP.keep [.a7, wordReg i] (c := .block (rotate16 (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, rotate16, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold rotate16
    rrun [hy, show 48 + s < 64 by omega, show 16 - s < 64 by omega]
    exact rot16 y hs.1 hs.2

theorem sub_run (u : State) {i : Nat} (hi : i < 4) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) - u.gpr .t2 - u.gpr .t0 - u.gpr .t1) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (subInputs (wordReg i))) u fun t =>
      t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (subInputs (wordReg i)))
    (Q := fun t => t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, subInputs, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold subInputs mask
    rrun
    exact hy

theorem reverseMix_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    {j i : Nat} (hj : j < 64) (hi : i < 4) :
    WP isa (.block (reverseMix j i)) u fun t =>
      Holds (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt u.mem T) j i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t0, .t1, .t2, wordReg i] u t := by
  have hs := rotation_bounds i hi
  have e : reverseMix j i = rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ (andInputs i ++ (loadKey j ++
      subInputs (wordReg i))) := by
    simp only [reverseMix, mixInputs, andInputs, List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  refine WP.mono (rot_run u hi (s := 16 - Spec.Rc2.rotation i) (by omega) (H i hi)) fun t₀ ⟨a₀, m₀, k₀⟩ => ?_
  have H₀ : ∀ d, d = 1 ∨ d = 2 ∨ d = 3 →
      t₀.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := fun d hd => by
    rw [← H.nb i d]
    refine k₀.gpr ?_
    have := wordReg_ne ((i + d) % 4) (Nat.mod_lt _ (by decide)) i hi (by omega)
    have h1 := wordReg_other ((i + d) % 4) (Nat.mod_lt _ (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
    rw [show wordReg (i + d) = wordReg ((i + d) % 4) by simp [wordReg]]
    exact ⟨h1.1, this⟩
  rw [WP.block_append_iff]
  refine WP.mono (andInputs_run t₀ hi) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  have n3 : Reg.a2 ∉ [Reg.a7, wordReg i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, Ne.symm o.2.1⟩
  refine WP.mono (loadKey_run t₁ ((E.keep k₀ n3).keep k₁ (by decide)) hj) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have x2 : t₂.gpr (wordReg i) = t₀.gpr (wordReg i) := by
    rw [k₂.gpr (by simpa using o.2.2.2.2.2.2), k₁.gpr (by simp; exact ⟨o.2.2.2.2.1, o.2.2.2.2.2.1⟩)]
  have r10 : t₂.gpr .t0 = t₁.gpr .t0 := k₂.gpr (by decide)
  have r11 : t₂.gpr .t1 = t₁.gpr .t1 := k₂.gpr (by decide)
  refine WP.mono (sub_run t₂ hi (y := (v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
    (Spec.Rc2.scheduleAt u.mem T).getD j 0 - (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0))
    (by rw [x2, r10, r11, a₁, b₁, a₀, H₀ 3 (by omega), H₀ 2 (by omega),
          H₀ 1 (by omega), rotateLeft_reverse _ _ hs.1 hs.2]
        exact rmix_val _ _ _ _ _ _ (by rw [a₂, m₁, m₀])))
    fun t₃ ⟨a₃, m₃, k₃⟩ => ⟨?_, by rw [m₃, m₂, m₁, m₀],
      (((k₀.trans k₁).trans k₂).trans k₃).mono (by simp)⟩
  exact H.set (by rw [a₃]) (keep_others hi ((((k₀.trans k₁).trans k₂).trans k₃).mono (by simp)))

/-! ## Mashing -/

theorem idx_val (w : BitVec 16) :
    ((w.setWidth 64) <<< 58) >>> 57 = BitVec.ofNat 64 (2 * (w &&& 63#16).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h63 : (w &&& 63#16).toNat = w.toNat % 64 := by
    rw [BitVec.toNat_and, show (63#16).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := w.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h63,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show w.toNat < 2 ^ 64 by omega)]
  omega

/-- A mash of word `i`, in the direction `d`. -/
def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem keep_others' {u t : State} {i : Nat} (hi : i < 4)
    (k : Keep [.a7, .t3, .t0, .t1, .t2, wordReg i] u t) :
    ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i') := fun i' hi' hne => by
  refine k.gpr ?_
  have h1 := wordReg_other i' hi'
  have h2 := wordReg_ne i' hi' i hi hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨h1.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

theorem mashIndex_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (mashIndex i)) u fun t =>
      t.gpr .t0 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem ∧ Keep [.t0] u t := by
  refine WP.mono (WP.keep [.t0] (c := .block (mashIndex i)) (Q := fun t =>
      t.gpr .t0 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold mashIndex; rrun [wordReg_3, wordReg_4, wordReg_5, wordReg_6])

theorem adjust_run (u : State) (sub : Bool) {i : Nat} (hi : i < 4) :
    WP isa (.block (adjust sub (wordReg i))) u fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .t1 else u.gpr (wordReg i) + u.gpr .t1)
        <<< 48) >>> 48) ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (adjust sub (wordReg i))) (Q := fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .t1 else u.gpr (wordReg i) + u.gpr .t1)
        <<< 48) >>> 48) ∧ t.mem = u.mem) ?_
    (by cases sub <;> simp [writesOnly, Code.allInstrs_eq, instrs, adjust, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> cases sub <;>
    (unfold adjust mask; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3])

theorem mash_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    WP isa (mash d i) u fun t =>
      Holds (mashSpec d (Spec.Rc2.scheduleAt u.mem T) i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t3, .t0, .t1, .t2, wordReg i] u t := by
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  unfold mash
  apply WP.seq
  refine WP.mono (mashIndex_run u hi) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
  let w := v.getD ((i + 3) % 4) 0
  have hidx : (w &&& 63#16).toNat < 64 := by
    rw [BitVec.toNat_and, show (63#16).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  have hr : ∀ k < 16, InRegions (t₁.rd ++ t₁.wr) (T + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [k₁.2.1, k₁.2.2]; exact E.rd (8 * k) 8 (by omega)
  have h3 : t₁.gpr .a2 = T := by rw [k₁.gpr (by decide)]; exact E.a2
  have hq : t₁.gpr .t0 = BitVec.ofNat 64 (2 * (w &&& 63#16).toNat) := by rw [a₁, H.nb i 3]; exact idx_val w
  apply WP.seq
  refine WP.mono (keyLookup_run t₁ h3 E.al hidx hq hr) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  refine WP.mono (adjust_run t₂ (d == .decrypt) hi) fun t₃ ⟨a₃, m₃, k₃⟩ =>
    ⟨?_, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  have x2 : t₂.gpr (wordReg i) = (v.getD i 0).setWidth 64 := by
    rw [k₂.gpr (by simp [o]), k₁.gpr (by simp [o])]
    exact H i hi
  have K : (Spec.Rc2.scheduleAt t₁.mem T) = Spec.Rc2.scheduleAt u.mem T := by rw [m₁]
  have hk := keep_others' hi (((k₁.trans k₂).trans k₃).mono (by simp))
  rw [K] at a₂
  cases d
  · show Holds (Spec.Rc2.mash _ i v) t₃
    refine H.set ?_ hk
    rw [a₃, x2, a₂, mask16]
    simp only [show (Spec.Rc2.Direction.encrypt == .decrypt) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [lo16_add, lo16_ext, lo16_ext]; rfl
  · show Holds (Spec.Rc2.reverseMash _ i v) t₃
    refine H.set ?_ hk
    rw [a₃, x2, a₂, mask16]
    simp only [show (Spec.Rc2.Direction.decrypt == .decrypt) = true from rfl, ↓reduceIte]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [lo16_sub, lo16_ext, lo16_ext]; rfl

end VG.Proof.Rc2.RISCV64
