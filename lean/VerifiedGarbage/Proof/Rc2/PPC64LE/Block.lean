module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
public import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
meta import VerifiedGarbage.Impl.Rc2.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Spec.Rc2

/-! ### `Rc2.PPC64LE.Rounds`, which only this module used -/

section

/-! ### `Rc2.PPC64LE.Mix`, which this module and modules that import it used -/

section

/-!
# RC2 on PPC64LE: mixing and mashing

`mix_run`, `reverseMix_run` and `mash_run`: each step of the rounds maps
the four words in `r6`–`r9` (`Holds`) to the specification's step of them.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The four words are in `r6`–`r9`, zero-extended. -/
def Holds (v : Spec.Rc2.State) (s : State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

/-- What the rounds need: the schedule at `r3`, `T`, readable a doubleword at
a time. -/
structure KeyEnv (T : Addr) (s : State) : Prop where
  r3 : s.gpr .r3 = T
  rd : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 o) n

theorem KeyEnv.keep {T : Addr} {s t : State} (E : KeyEnv T s) {rs : List Reg} (h : Keep rs s t)
    (h3 : Reg.r3 ∉ rs) : KeyEnv T t :=
  ⟨by rw [h.gpr h3]; exact E.r3, fun o n hn => by rw [h.2.1, h.2.2]; exact E.rd o n hn⟩

/-! ## Words in 64-bit registers -/

/-- Bytes `k` and `k + 1` of a word, as a little-endian 16-bit word. -/
theorem word16_bytes (x : BitVec 32) (k : Nat) :
    (x >>> (8 * k)).setWidth 16 =
      (x.extractLsb' (8 * k) 8).zeroExtend 16 ||| (x.extractLsb' (8 * (k + 1)) 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, Nat.add_comm]
  · simp only [h8, decide_false, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and,
      decide_true, show i - 8 < 8 by omega_using [hi], show i - 8 < 16 by omega_using [hi]]
    rw [show 8 * k + i = 8 * (k + 1) + (i - 8) by omega_using [h8]]

theorem key_word (m : Mem) (T : Addr) {o k j : Nat} (hk : k ≤ 2) (hj : j < 64) (ho : o + k = 2 * j) :
    ((m.readW (T + BitVec.ofNat 64 o) 32) >>> (8 * k)).setWidth 16 = (Spec.Rc2.scheduleAt m T).getD j 0 := by
  rw [word16_bytes, ← Mem.readW_byte m _ (by omega_using [hk]), ← Mem.readW_byte m _ (by omega_using [hk]), Offset.add_add,
    Offset.add_add, Spec.Rc2.scheduleAt, Proof.Rc2.getD_ofFn _ _ hj]
  simp only
  rw [show o + k = 2 * j from ho, show o + (k + 1) = 2 * j + 1 by omega_using [ho]]

theorem lo16_add (x y : BitVec 64) : (x + y).setWidth 16 = x.setWidth 16 + y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.add_mod]

theorem lo16_sub (x y : BitVec 64) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  omega_using []

theorem lo16_ext (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq x)

theorem lo16_and (x y : BitVec 64) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo16_xor (x y : BitVec 64) : (x ^^^ y).setWidth 16 = x.setWidth 16 ^^^ y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem andNot_xor (a c : BitVec 16) : c ^^^ (a &&& c) = ~~~a &&& c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem mask16 (x : BitVec 64) : (x <<< 48) >>> 48 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp [h, hi]; intro _; omega_using [h]
  · simp [h]; intro _; omega

theorem rot16 (y : BitVec 16) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    (((y.setWidth 64 >>> (16 - s)) ||| (y.setWidth 64 <<< s)) <<< 48) >>> 48 = (y.rotateLeft s).setWidth 64 := by
  rw [mask16]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt h2]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and, show i < 64 by omega]
  by_cases h : i < s
  · rw [ite_eq_left h]
    simp [h, show 16 - s + i < 64 by omega, show 16 - s + i < 16 by omega]
  · rw [ite_eq_right h]
    simp [h, show 16 - s + i < 64 by omega, show i - s < 64 by omega, show i - s < 16 by omega,
      BitVec.getLsbD_of_ge y (16 - s + i) (by omega)]

/-! ## The steps, for any registers -/

theorem loadKey_run (u : State) {T : Addr} (E : KeyEnv T u) {j : Nat} (hj : j < 64) :
    WP isa (.block (loadKey j)) u fun t =>
      (t.gpr .r12).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem ∧
        Keep [.r12] u t := by
  refine WP.mono (WP.keep (c := .block (loadKey j)) [.r12] (Q := fun t =>
      (t.gpr .r12).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem) ?_
    (by unfold loadKey; split <;> rfl) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold loadKey
  split
  · rrun [E.r3, E.rd (2 * j) 4 (by omega_arith), show 2 * j < 32768 by omega_using [hj]]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    have := key_word u.mem T (o := 2 * j) (k := 0) (j := j) (by decide) hj (by omega_using [])
    rwa [Nat.mul_zero, BitVec.ushiftRight_zero] at this
  · have : j = 63 := by omega_arith
    subst this
    rrun [E.r3, E.rd 124 4 (by decide)]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), lo32_ext]
    exact key_word u.mem T (o := 124) (k := 2) (j := 63) (by decide) (by decide) (by decide)

end VG.Proof.Rc2.PPC64LE

end

end

/-!
# RC2 on PPC64LE: the steps of the rounds

`mix_run`, `reverseMix_run` and `mash_run`: each step maps the four words
in `r6`–`r9` (`Holds`) to the specification's step of them.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem getD_set (v : Spec.Rc2.State) (x : BitVec 16) {i j : Nat} (hj : j < 4) :
    (v.set! i x).getD j 0 = if i = j then x else v.getD j 0 := by
  rw [Proof.Rc2.getD_eq_getElem _ _ hj, Proof.Rc2.getD_eq_getElem _ _ hj]
  simp [Vector.getElem_set!]

theorem wordReg_0 : wordReg 0 = .r6 := rfl
theorem wordReg_1 : wordReg 1 = .r7 := rfl
theorem wordReg_2 : wordReg 2 = .r8 := rfl
theorem wordReg_3 : wordReg 3 = .r9 := rfl
theorem wordReg_4 : wordReg 4 = .r6 := rfl
theorem wordReg_5 : wordReg 5 = .r7 := rfl
theorem wordReg_6 : wordReg 6 = .r8 := rfl

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
  [.logic .and .r10 (wordReg (i + 3)) (wordReg (i + 2)), .logic .and .r11 (wordReg (i + 3)) (wordReg (i + 1)),
   .logic .xor .r11 (wordReg (i + 1)) .r11]

theorem andInputs_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (andInputs i)) u fun t =>
      t.gpr .r10 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .r11 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem ∧ Keep [.r10, .r11] u t := by
  refine WP.mono (WP.keep [.r10, .r11] (c := .block (andInputs i)) (Q := fun t =>
      t.gpr .r10 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .r11 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold andInputs; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3, wordReg_4, wordReg_5, wordReg_6])

/-- The sum and rotation of a mix, on word `i` of `r6`–`r9`. -/
theorem addRot_run (u : State) {i s : Nat} (hi : i < 4) (hs : 1 ≤ s ∧ s < 16) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) + u.gpr .r12 + u.gpr .r10 + u.gpr .r11) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (addInputs (wordReg i) ++ rotate16 (wordReg i) s)) u fun t =>
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.r0, wordReg i] u t := by
  refine WP.mono (WP.keep [.r0, wordReg i] (c := .block (addInputs (wordReg i) ++ rotate16 (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, addInputs, rotate16, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  have h48 : (48 : Nat) < 64 := by decide
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold addInputs rotate16 mask
    rrun [show s < 64 by omega_using [hs], show 16 - s < 64 by omega_using []]
    rw [hy]
    exact rot16 y hs.1 hs.2

theorem wordReg_ne : ∀ i' < 4, ∀ i < 4, i' ≠ i → wordReg i' ≠ wordReg i := by decide
theorem wordReg_other : ∀ i < 4, wordReg i ∉ [Reg.r0, .r3, .r4, .r5, .r10, .r11, .r12] := by decide
theorem rotation_bounds : ∀ i < 4, 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by decide

/-- A step that changes only word `i` and the code's temporaries. -/
theorem keep_others {u t : State} {i : Nat} (hi : i < 4) (k : Keep [.r0, .r10, .r11, .r12, wordReg i] u t) :
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
        Keep [.r0, .r10, .r11, .r12, wordReg i] u t := by
  have e : mix j i = andInputs i ++ (loadKey j ++ (addInputs (wordReg i) ++
      rotate16 (wordReg i) (Spec.Rc2.rotation i))) := by
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
  have r10 : t₂.gpr .r10 = t₁.gpr .r10 := k₂.gpr (by decide)
  have r11 : t₂.gpr .r11 = t₁.gpr .r11 := k₂.gpr (by decide)
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
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.r0, wordReg i] u t := by
  refine WP.mono (WP.keep [.r0, wordReg i] (c := .block (rotate16 (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, rotate16, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold rotate16 mask
    rrun [hy, show s < 64 by omega_using [hs], show 16 - s < 64 by omega_using []]
    exact rot16 y hs.1 hs.2

theorem sub_run (u : State) {i : Nat} (hi : i < 4) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) - u.gpr .r12 - u.gpr .r10 - u.gpr .r11) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (subInputs (wordReg i))) u fun t =>
      t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (subInputs (wordReg i)))
    (Q := fun t => t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, subInputs, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold subInputs mask
    rrun
    exact hy

theorem reverseMix_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    {j i : Nat} (hj : j < 64) (hi : i < 4) :
    WP isa (.block (reverseMix j i)) u fun t =>
      Holds (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt u.mem T) j i v) t ∧ t.mem = u.mem ∧
        Keep [.r0, .r10, .r11, .r12, wordReg i] u t := by
  have hs := rotation_bounds i hi
  have e : reverseMix j i = rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ (andInputs i ++ (loadKey j ++
      subInputs (wordReg i))) := by
    simp only [reverseMix, mixInputs, andInputs, List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  refine WP.mono (rot_run u hi (s := 16 - Spec.Rc2.rotation i) (by omega_using [hs]) (H i hi)) fun t₀ ⟨a₀, m₀, k₀⟩ => ?_
  have H₀ : ∀ d, d = 1 ∨ d = 2 ∨ d = 3 →
      t₀.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := fun d hd => by
    rw [← H.nb i d]
    refine k₀.gpr ?_
    have := wordReg_ne ((i + d) % 4) (Nat.mod_lt _ (by decide)) i hi (by omega_using [hd])
    have h1 := wordReg_other ((i + d) % 4) (Nat.mod_lt _ (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
    rw [show wordReg (i + d) = wordReg ((i + d) % 4) by simp [wordReg]]
    exact ⟨h1.1, this⟩
  rw [WP.block_append_iff]
  refine WP.mono (andInputs_run t₀ hi) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  have n3 : Reg.r3 ∉ [Reg.r0, wordReg i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, Ne.symm o.2.1⟩
  refine WP.mono (loadKey_run t₁ ((E.keep k₀ n3).keep k₁ (by decide)) hj) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have x2 : t₂.gpr (wordReg i) = t₀.gpr (wordReg i) := by
    rw [k₂.gpr (by simpa using o.2.2.2.2.2.2), k₁.gpr (by simp; exact ⟨o.2.2.2.2.1, o.2.2.2.2.2.1⟩)]
  have r10 : t₂.gpr .r10 = t₁.gpr .r10 := k₂.gpr (by decide)
  have r11 : t₂.gpr .r11 = t₁.gpr .r11 := k₂.gpr (by decide)
  refine WP.mono (sub_run t₂ hi (y := (v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
    (Spec.Rc2.scheduleAt u.mem T).getD j 0 - (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0))
    (by rw [x2, r10, r11, a₁, b₁, a₀, H₀ 3 (by omega_using []), H₀ 2 (by omega_using []),
          H₀ 1 (by omega_using []), rotateLeft_reverse _ _ hs.1 hs.2]
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
  rw [Nat.mod_eq_of_lt (show w.toNat < 2 ^ 64 by omega_using [])]
  omega_using []

/-- A mash of word `i`, in the direction `d`. -/
def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem keep_others' {u t : State} {i : Nat} (hi : i < 4)
    (k : Keep [.r0, .r5, .r10, .r11, .r12, wordReg i] u t) :
    ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i') := fun i' hi' hne => by
  refine k.gpr ?_
  have h1 := wordReg_other i' hi'
  have h2 := wordReg_ne i' hi' i hi hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨h1.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

theorem mashIndex_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (mashIndex i)) u fun t =>
      t.gpr .r10 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem ∧ Keep [.r10] u t := by
  refine WP.mono (WP.keep [.r10] (c := .block (mashIndex i)) (Q := fun t =>
      t.gpr .r10 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold mashIndex; rrun [wordReg_3, wordReg_4, wordReg_5, wordReg_6])

theorem adjust_run (u : State) (sub : Bool) {i : Nat} (hi : i < 4) :
    WP isa (.block (adjust sub (wordReg i))) u fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .r11 else u.gpr (wordReg i) + u.gpr .r11)
        <<< 48) >>> 48) ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (adjust sub (wordReg i))) (Q := fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .r11 else u.gpr (wordReg i) + u.gpr .r11)
        <<< 48) >>> 48) ∧ t.mem = u.mem) ?_
    (by cases sub <;> simp [writesOnly, Code.allInstrs_eq, instrs, adjust, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> cases sub <;>
    (unfold adjust mask; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3])

theorem mash_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    WP isa (mash d i) u fun t =>
      Holds (mashSpec d (Spec.Rc2.scheduleAt u.mem T) i v) t ∧ t.mem = u.mem ∧
        Keep [.r0, .r5, .r10, .r11, .r12, wordReg i] u t := by
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  unfold mash
  apply WP.seq
  refine WP.mono (mashIndex_run u hi) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
  let w := v.getD ((i + 3) % 4) 0
  have hidx : (w &&& 63#16).toNat < 64 := by
    rw [BitVec.toNat_and, show (63#16).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega_using []
  have hr : ∀ o n, o + n ≤ 128 → InRegions (t₁.rd ++ t₁.wr) (T + BitVec.ofNat 64 o) n := fun o n h => by
    rw [k₁.2.1, k₁.2.2]; exact E.rd o n h
  have h3 : t₁.gpr .r3 = T := by rw [k₁.gpr (by decide)]; exact E.r3
  have hq : t₁.gpr .r10 = BitVec.ofNat 64 (2 * (w &&& 63#16).toNat) := by rw [a₁, H.nb i 3]; exact idx_val w
  apply WP.seq
  refine WP.mono (keyLookup_run t₁ h3 hidx hq hr) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
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

end VG.Proof.Rc2.PPC64LE

end

end

/-! ### `Rc2.PPC64LE.BlockIO`, which only this module used -/

section

/-! # RC2 on PPC64LE: loading and storing the block -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem lane (x : BitVec 64) {i : Nat} (hi : i < 4) :
    (x <<< (48 - 16 * i)) >>> 48 = ((x >>> (16 * i)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp only [h, hj, decide_true, Bool.true_and, show 48 + j < 64 by omega_using [h], show ¬48 + j < 48 - 16 * i by omega_using [],
      decide_false, Bool.not_false]
    rw [show 48 + j - (48 - 16 * i) = 16 * i + j by omega_using [hi]]
  · simp only [h, show ¬48 + j < 64 by omega_using [h], decide_false, Bool.false_and, Bool.and_false]

theorem lane3 (x : BitVec 64) : x >>> 48 = ((x >>> (16 * 3)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp [h, hj]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge x (48 + j) (by omega_using [h])]
    simp

theorem blockLoad_run (u : State) (hr : InRegions (u.rd ++ u.wr) (u.gpr .r4) 8) :
    WP isa (.block blockLoad) u fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem ∧
        Keep [.r6, .r7, .r8, .r9, .r11] u t := by
  refine WP.mono (WP.keep [.r6, .r7, .r8, .r9, .r11] (c := .block blockLoad) (Q := fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold blockLoad
  rrun [hr]
  intro i hi
  rw [decode_read64 _ _ _ hi]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact lane _ (i := 0) (by decide)
  · exact lane _ (i := 1) (by decide)
  · exact lane _ (i := 2) (by decide)
  · exact lane3 _

theorem pack_or (v : Spec.Rc2.State) :
    (v.getD 1 0).setWidth 64 <<< 16 ||| (v.getD 0 0).setWidth 64 ||| (v.getD 2 0).setWidth 64 <<< 32 |||
      (v.getD 3 0).setWidth 64 <<< 48 = pack v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h₁ : j < 16
  · simp (disch := omega_arith) [h₁, hj, show j < 32 by omega_using [h₁], show j < 48 by omega_using [h₁]]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega_using [h₂], show j - 16 < 64 by omega_using [hj], show j - 16 < 16 by omega_using [h₂],
        BitVec.getLsbD_of_ge]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 32 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show j - 32 < 16 by omega_using [h₃], BitVec.getLsbD_of_ge]
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 48 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show ¬j - 32 < 16 by omega_using [h₃], show j - 32 - 16 = j - 48 by omega_using [],
          BitVec.getLsbD_of_ge]

theorem blockStore_run (u : State) {v : Spec.Rc2.State} (H : Holds v u) (hw : InRegions u.wr (u.gpr .r4) 8) :
    WP isa (.block blockStore) u fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v) ∧ Keep [.r11, .r12] u t := by
  refine WP.mono (WP.keep [.r11, .r12] (c := .block blockStore) (Q := fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v)) ?_
    (by rfl) rfl) fun t ⟨a, c⟩ => ⟨a, c⟩
  have h0 := H 0 (by decide)
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  rw [wordReg_0] at h0
  rw [wordReg_1] at h1
  rw [wordReg_2] at h2
  rw [wordReg_3] at h3
  unfold blockStore
  rrun [hw, h0, h1, h2, h3]
  exact congrArg _ (pack_or v)

end VG.Proof.Rc2.PPC64LE

end

end

/-! ### `Rc2.PPC64LE.Cipher`, which this module and modules that import it used -/

section

/-! # RC2 on PPC64LE: composition of the sixteen rounds -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- `c` maps the words to `g` of them, on memory `m` with the schedule at `T`. -/
def RunsTo (T : Addr) (m : Mem) (c : Prog isa) (g : Spec.Rc2.State → Spec.Rc2.State) : Prop :=
  ∀ u, KeyEnv T u → u.mem = m → ∀ v, Holds v u →
    WP isa c u fun t => Holds (g v) t ∧ t.mem = m ∧ Keep roundRegs u t

theorem roundRegs_append : ∀ r ∈ roundRegs ++ roundRegs, r ∈ roundRegs := fun r h => by
  rcases List.mem_append.1 h with h | h <;> exact h

theorem RunsTo.of_eq {T : Addr} {m : Mem} {c : Prog isa} {g g' : Spec.Rc2.State → Spec.Rc2.State}
    (h : RunsTo T m c g) (e : ∀ v, g v = g' v) : RunsTo T m c g' := fun u E hm v H =>
  WP.mono (h u E hm v H) fun _ ⟨a, b, c⟩ => ⟨e v ▸ a, b, c⟩

theorem RunsTo.nil {T : Addr} {m : Mem} : RunsTo T m (.block []) id := fun _ _ hm _ H =>
  WP.block_nil ⟨H, hm, Keep.refl _ _⟩

theorem RunsTo.seq {T : Addr} {m : Mem} {c₁ c₂ : Prog isa} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m c₁ g₁) (h₂ : RunsTo T m c₂ g₂) : RunsTo T m (.seq c₁ c₂) (fun v => g₂ (g₁ v)) :=
  fun u E hm v H => WP.seq <| WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.append {T : Addr} {m : Mem} {l₁ l₂ : List Instr} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m (.block l₁) g₁) (h₂ : RunsTo T m (.block l₂) g₂) :
    RunsTo T m (.block (l₁ ++ l₂)) (fun v => g₂ (g₁ v)) := fun u E hm v H => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.foldr {T : Addr} {m : Mem} (f : Nat → Prog isa) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (f i) (g i)) :
    RunsTo T m (l.foldr (fun i rest => .seq (f i) rest) (.block [])) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    exact (RunsTo.seq (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem RunsTo.flatMap {T : Addr} {m : Mem} (f : Nat → List Instr) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (.block (f i)) (g i)) :
    RunsTo T m (.block (l.flatMap f)) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    rw [List.flatMap_cons]
    exact (RunsTo.append (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem mix_regs : ∀ i < 4, ∀ r ∈ [Reg.r0, .r10, .r11, .r12, wordReg i], r ∈ roundRegs := by decide
theorem mash_regs : ∀ i < 4, ∀ r ∈ [Reg.r0, .r5, .r10, .r11, .r12, wordReg i], r ∈ roundRegs := by decide

theorem mix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (mix j i)) (Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (mix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem reverseMix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (reverseMix j i)) (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (reverseMix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem mash_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    RunsTo T m (mash d i) (mashSpec d (Spec.Rc2.scheduleAt m T) i) := fun u E hm _ H =>
  WP.mono (mash_run u E H d hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mash_regs i hi)⟩

def mixRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mixRound k j v
  | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then mashRoundSpec d k (mixRoundSpec d k j v) else mixRoundSpec d k j v

theorem mixRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (.block (mixRound d j)) (mixRoundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  cases d with
  | encrypt =>
    refine (RunsTo.flatMap (fun i => mix (4 * j + i) i)
      (fun i => Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) (4 * j + i) i) (List.range 4) fun i hi => ?_).of_eq fun _ => rfl
    have := List.mem_range.1 hi
    exact mix_runsTo (by omega_using [hj, this]) this
  | decrypt =>
    refine (RunsTo.flatMap (fun i => reverseMix (4 * (15 - j) + i) i)
      (fun i => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) (4 * (15 - j) + i) i) [3, 2, 1, 0]
      fun i hi => ?_).of_eq fun _ => rfl
    have : i < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
    exact reverseMix_runsTo (by omega_using [this]) this

theorem order_lt (d : Spec.Rc2.Direction) : ∀ i ∈ order d, i < 4 := by cases d <;> decide

theorem mashRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (mashRound d) (mashRoundSpec d (Spec.Rc2.scheduleAt m T)) :=
  (RunsTo.foldr _ _ _ fun i hi => mash_runsTo d (order_lt d i hi)).of_eq fun _ => by cases d <;> rfl

theorem round_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (round d j) (roundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  unfold round
  by_cases h : j = 4 ∨ j = 10
  · rw [ite_eq_left h]
    exact (RunsTo.seq (mixRound_runsTo d hj) (mashRound_runsTo d)).of_eq fun v => by
      simp only [roundSpec, ite_eq_left h]
  · rw [ite_eq_right h]
    exact (RunsTo.seq (mixRound_runsTo d hj) RunsTo.nil).of_eq fun v => by
      simp only [roundSpec, ite_eq_right h, id]

theorem rounds_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (rounds d) (fun v => (List.range 16).foldl (fun v j => roundSpec d (Spec.Rc2.scheduleAt m T) j v) v) :=
  RunsTo.foldr _ _ _ fun _ hj => round_runsTo d (List.mem_range.1 hj)

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

end VG.Proof.Rc2.PPC64LE

end

end

/-! # Verified RC2 block encryption and decryption on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .r3, 128⟩] ∧ s.wr = [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 256⟩]
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .r4) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .r3)) (Spec.Rc2.blockAt s.mem (s.gpr .r4))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr⟩ := hs
  unfold blockCode
  apply WP.seq
  refine WP.mono (blockLoad_run s (by rw [hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (s.gpr .r3) t₁ := ⟨k₁.gpr (by decide), fun o n hn => by
    rw [k₁.2.1, k₁.2.2, hrd]; exact ⟨_, by simp, Offset.contains_base _ hn (by omega_using [hn])⟩⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .r4 = s.gpr .r4 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (blockStore_run t₂ H₂ (by rw [p4, k₂.2.2, k₁.2.2, hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .r4) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁]

/-- The registers the block functions write. -/
def blockRegs : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : (blockCode d).noCalls = true) (hl : (instrs (blockCode d)).all (fun i => !i.writesLr) = true)
    (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) hn hl, hp⟩

end VG.Proof.Rc2.PPC64LE
