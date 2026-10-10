import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The schedule in memory

Byte `b` of S_{j+1}[x] in `scheduleAt` is the byte at `1024 j + 256 b + x`
(`sEntry_byte`), and Pᵢ₊₁ the little-endian word at `4096 + 4 i`
(`pEntry_read`).
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- Byte `b` of four bytes combined little-endian. -/
theorem byte_of_le4 (a0 a1 a2 a3 : Byte) {b : Nat} (hb : b < 4) :
    (a0.zeroExtend 32 ||| a1.zeroExtend 32 <<< 8 ||| a2.zeroExtend 32 <<< 16 |||
        a3.zeroExtend 32 <<< 24).extractLsb' (8 * b) 8 = [a0, a1, a2, a3].getD b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [hi, BitVec.getLsbD_of_ge, decide_eq_true, decide_eq_false]

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) {i : Nat} (h : i < n) (d : α) :
    (Vector.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Vector.getD, Array.getD, h]

theorem sEntry_byte (m : Mem) (p : Addr) {j b : Nat} (hj : j < 4) (hb : b < 4) (x : Byte) :
    (sEntry (scheduleAt m p) j x).extractLsb' (8 * b) 8 =
      m (p + BitVec.ofNat 64 (1024 * j + 256 * b + x.toNat)) := by
  have hx := x.isLt
  rw [sEntry, scheduleAt, getD_ofFn _ (by omega)]
  simp only [show ¬ 18 + 256 * j + x.toNat < 18 by omega, ite_false,
    show (18 + 256 * j + x.toNat - 18) / 256 = j by omega,
    show (18 + 256 * j + x.toNat - 18) % 256 = x.toNat by omega]
  rw [byte_of_le4 _ _ _ _ hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ] <;> congr 3 <;> omega

/-- Two words with the same bytes are the same. -/
theorem word_ext {x y : BitVec 32} (h : ∀ b < 4, x.extractLsb' (8 * b) 8 = y.extractLsb' (8 * b) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and,
    show 8 * (i / 8) + i % 8 = i by omega] at this
  exact this

theorem pEntry_read (m : Mem) (p : Addr) {i : Nat} (hi : i < 18) :
    pEntry (scheduleAt m p) i = m.readW (p + BitVec.ofNat 64 (4096 + 4 * i)) 32 := by
  rw [pEntry, scheduleAt, getD_ofFn _ (by omega)]
  simp only [hi, ite_true]
  refine word_ext fun b hb => ?_
  rw [byte_of_le4 _ _ _ _ hb, ← Mem.readW_byte _ _ hb, Offset.add_add]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 4168, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    scheduleAt m' p = scheduleAt m p := by
  apply Vector.ext; intro i hi
  simp only [scheduleAt, Vector.getElem_ofFn]
  split
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

theorem scheduleAt_eq_of_frame {rs : List Region} {m m' : Mem} (p : Addr) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 4168⟩ : Region).Disjoint r) : scheduleAt m' p = scheduleAt m p :=
  scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 4168⟩) hd (show 4168 ≤ 2 ^ 64 by decide) hi

/-! ## Writing one entry -/

/-- The offset in the schedule of byte `b` of entry `i` (Pᵢ₊₁ for `i < 18`,
then the S-boxes' entries). -/
def entryOff (i b : Nat) : Nat :=
  if i < 18 then 4096 + 4 * i + b else 1024 * ((i - 18) / 256) + 256 * b + (i - 18) % 256

theorem entryOff_lt {i b : Nat} (hi : i < 1042) (hb : b < 4) : entryOff i b < 4168 := by
  unfold entryOff; split <;> omega

theorem entryOff_inj {i i' b b' : Nat} (hi : i < 1042) (hi' : i' < 1042) (hb : b < 4) (hb' : b' < 4)
    (h : entryOff i b = entryOff i' b') : i = i' ∧ b = b' := by
  unfold entryOff at h; split at h <;> split at h <;> omega

/-- Entry `i` of a schedule from its four bytes. -/
theorem scheduleAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 1042) :
    (scheduleAt m p)[i] =
      (m (p + BitVec.ofNat 64 (entryOff i 0))).zeroExtend 32 |||
        (m (p + BitVec.ofNat 64 (entryOff i 1))).zeroExtend 32 <<< 8 |||
        (m (p + BitVec.ofNat 64 (entryOff i 2))).zeroExtend 32 <<< 16 |||
        (m (p + BitVec.ofNat 64 (entryOff i 3))).zeroExtend 32 <<< 24 := by
  simp only [scheduleAt, Vector.getElem_ofFn, entryOff]
  split
  · simp only [Nat.add_zero]
  · simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one]

/-- Memory that holds the bytes of `w` at entry `i`, and agrees elsewhere in
the schedule, holds the schedule with entry `i` replaced. -/
theorem scheduleAt_set {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 1042) (w : Word)
    (hw : ∀ b < 4, m' (p + BitVec.ofNat 64 (entryOff i b)) = w.extractLsb' (8 * b) 8)
    (ho : ∀ i' < 1042, i' ≠ i → ∀ b < 4,
      m' (p + BitVec.ofNat 64 (entryOff i' b)) = m (p + BitVec.ofNat 64 (entryOff i' b))) :
    scheduleAt m' p = (scheduleAt m p).set i w := by
  apply Vector.ext; intro i' hi'
  rw [Vector.getElem_set]
  split
  · rename_i h; subst h
    rw [scheduleAt_get _ _ hi', hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    refine word_ext fun b hb => ?_
    rw [byte_of_le4 _ _ _ _ hb]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rename_i h
    rw [scheduleAt_get _ _ hi', scheduleAt_get _ _ hi', ho i' hi' (Ne.symm h) 0 (by decide),
      ho i' hi' (Ne.symm h) 1 (by decide), ho i' hi' (Ne.symm h) 2 (by decide),
      ho i' hi' (Ne.symm h) 3 (by decide)]

theorem ofNat_add_ne (p : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) (h : d ≠ e) :
    p + BitVec.ofNat 64 d ≠ p + BitVec.ofNat 64 e := fun h' => h (by
  have := congrArg (fun x => (x - p).toNat) h'
  simp only [Mem.sub_ofNat_toNat p hd, Mem.sub_ofNat_toNat p he] at this
  exact this)

theorem write1_self (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem write1_ne {m : Mem} {a x : Addr} (v : BitVec 8) (h : x ≠ a) : m.write a 1 v x = m x :=
  Mem.write_apply fun h' => h (by
    have : (x - a).toNat = 0 := by omega
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [this]; rfl)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; simp)

/-- The offsets of other entries are outside P-array entry `i`. -/
theorem entryOff_outside_P {i i' b : Nat} (hi : i < 18) (hi' : i' < 1042) (hne : i' ≠ i) (hb : b < 4) :
    entryOff i' b + 1 ≤ 4096 + 4 * i ∨ 4096 + 4 * i + 4 ≤ entryOff i' b := by
  unfold entryOff; split <;> omega

/-- Writing P-array entry `i`. -/
theorem scheduleAt_writeW_P (m : Mem) (p : Addr) {i : Nat} (hi : i < 18) (w : Word) :
    scheduleAt (m.writeW (p + BitVec.ofNat 64 (4096 + 4 * i)) w) p = (scheduleAt m p).set i w := by
  refine scheduleAt_set (by omega) w (fun b hb => ?_) (fun i' hi' hne b hb => ?_)
  · rw [show entryOff i b = 4096 + 4 * i + b by simp [entryOff, hi], ← Offset.add_add p (4096 + 4 * i) b,
      Mem.readW_byte (m.writeW (p + BitVec.ofNat 64 (4096 + 4 * i)) w) _ hb, Mem.readW_writeW_self32]
  · have hs := Offset.sep p (d := entryOff i' b) (n := 1) (e := 4096 + 4 * i) (k := 4)
      (entryOff_outside_P hi hi' hne hb) (by have := entryOff_lt hi' hb; omega) (by omega)
    exact Mem.write_apply (hs _ (by rw [BitVec.sub_self]; decide))

/-- Writing entry `i` a byte at a time. -/
theorem scheduleAt_write_bytes (m : Mem) (p : Addr) {i : Nat} (hi : i < 1042) (w : Word) :
    scheduleAt ((((m.write (p + BitVec.ofNat 64 (entryOff i 0)) 1 (w.extractLsb' 0 8)).write
        (p + BitVec.ofNat 64 (entryOff i 1)) 1 (w.extractLsb' 8 8)).write
        (p + BitVec.ofNat 64 (entryOff i 2)) 1 (w.extractLsb' 16 8)).write
        (p + BitVec.ofNat 64 (entryOff i 3)) 1 (w.extractLsb' 24 8)) p = (scheduleAt m p).set i w := by
  have lt : ∀ b < 4, entryOff i b < 2 ^ 64 := fun b hb => by have := entryOff_lt hi hb; omega
  have ne : ∀ b < 4, ∀ b' < 4, b ≠ b' →
      p + BitVec.ofNat 64 (entryOff i b) ≠ p + BitVec.ofNat 64 (entryOff i b') := fun b hb b' hb' h =>
    ofNat_add_ne p (lt b hb) (lt b' hb') fun h' => h (entryOff_inj hi hi hb hb' h').2
  refine scheduleAt_set hi w (fun b hb => ?_) (fun i' hi' hne b hb => ?_)
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · rw [write1_ne _ (ne 0 (by decide) 3 (by decide) (by decide)),
        write1_ne _ (ne 0 (by decide) 2 (by decide) (by decide)),
        write1_ne _ (ne 0 (by decide) 1 (by decide) (by decide)), write1_self]
    · rw [write1_ne _ (ne 1 (by decide) 3 (by decide) (by decide)),
        write1_ne _ (ne 1 (by decide) 2 (by decide) (by decide)), write1_self]
    · rw [write1_ne _ (ne 2 (by decide) 3 (by decide) (by decide)), write1_self]
    · rw [write1_self]
  · have o : ∀ c < 4, p + BitVec.ofNat 64 (entryOff i' b) ≠ p + BitVec.ofNat 64 (entryOff i c) :=
      fun c hc => ofNat_add_ne p (by have := entryOff_lt hi' hb; omega) (lt c hc)
        fun h' => hne (entryOff_inj hi' hi hb hc h').1
    rw [write1_ne _ (o 3 (by decide)), write1_ne _ (o 2 (by decide)), write1_ne _ (o 1 (by decide)),
      write1_ne _ (o 0 (by decide))]

end VG.Proof.Blowfish
