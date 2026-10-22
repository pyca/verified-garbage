module

public import VerifiedGarbage.Proof.MillerRabin.Keeps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Candidate data retained across rounds, independently of the next witness. -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Spec.Rsa.Mont

structure PreparedCore (m : Mem) (ws : Addr) : Prop where
  large : 3 ≤ numAt m ws (wOf m ws) 0
  odd : numAt m ws (wOf m ws) 0 % 2 = 1
  inverse : ((m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 0)) 64).toNat *
    (wordAt m ws minvWord).toNat + 1) % 2 ^ 64 = 0
  one : numAt m ws (wOf m ws) 9 = 2 ^ (64 * wOf m ws) % numAt m ws (wOf m ws) 0
  minus : numAt m ws (wOf m ws) 10 =
    numAt m ws (wOf m ws) 0 - 2 ^ (64 * wOf m ws) % numAt m ws (wOf m ws) 0
  exponent : numAt m ws (wOf m ws) 27 = Spec.MillerRabin.exponent (numAt m ws (wOf m ws) 0)
  tail : m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 27 + 8 * wOf m ws)) 64 =
    BitVec.twoPow 64 ((Spec.Rsa.splitTwos (numAt m ws (wOf m ws) 0 - 1)).1 % 64)

theorem prepared_core {m : Mem} {ws : Addr}
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact m ws) : PreparedCore m ws :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.2.1, P.2.2.2.2.2.1, P.2.2.2.2.2.2.1, P.2.2.2.2.2.2.2⟩

theorem PreparedCore.prepared {m : Mem} {ws : Addr} (P : PreparedCore m ws)
    (witness : numAt m ws (wOf m ws) 5 < numAt m ws (wOf m ws) 0) :
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact m ws :=
  ⟨P.large, P.odd, P.inverse, witness, P.one, P.minus, P.exponent, P.tail⟩

theorem PreparedCore.congr {m m' : Mem} {ws : Addr} (P : PreparedCore m ws)
    (width : wOf m' ws = wOf m ws)
    (numbers : ∀ j, j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27 →
      numAt m' ws (wOf m ws) j = numAt m ws (wOf m ws) j)
    (low : m'.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 0)) 64 =
      m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 0)) 64)
    (inverse : wordAt m' ws minvWord = wordAt m ws minvWord)
    (tail : m'.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 27 + 8 * wOf m ws)) 64 =
      m.readW (ws + BitVec.ofNat 64 (arrAt (wOf m ws) 27 + 8 * wOf m ws)) 64) : PreparedCore m' ws := by
  constructor
  · rw [width, numbers 0 (.inl rfl)]; exact P.large
  · rw [width, numbers 0 (.inl rfl)]; exact P.odd
  · rw [width, low, inverse]; exact P.inverse
  · rw [width, numbers 0 (.inl rfl), numbers 9 (.inr (.inl rfl))]; exact P.one
  · rw [width, numbers 0 (.inl rfl), numbers 10 (.inr (.inr (.inl rfl)))]; exact P.minus
  · rw [width, numbers 0 (.inl rfl), numbers 27 (.inr (.inr (.inr rfl)))]; exact P.exponent
  · rw [width, numbers 0 (.inl rfl), tail]; exact P.tail

theorem keeps_read {L : Spec.MillerRabin.Workspace} {B : Addr} {len w d size : Nat} {m m' : Mem}
    (h : Spec.MillerRabin.Keeps L B len w m m') (fit : d + size ≤ 8 * len)
    (headers : ∀ k ∈ [L.flag, L.value, L.words, L.windows, L.digit], d + size ≤ 8 * k ∨ 8 * k + 8 ≤ d)
    (arrays : ∀ j ∈ [2, 3, 5, 6, L.base], d + size ≤ arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ d)
    (table : d + size ≤ arrAt w L.table ∨ arrAt w (L.table + 16) ≤ d) :
    m'.read (B + BitVec.ofNat 64 d) size = m.read (B + BitVec.ofNat 64 d) size := by
  apply Mem.read_congr
  intro i hi
  rw [Offset.add_add]
  apply h (d + i) (by omega)
  · intro k hk; have := headers k hk; omega
  · intro j hj; have := arrays j hj; omega
  · omega

private theorem static_array_fit {len w j : Nat} (fit : arrAt w 28 ≤ 8 * len)
    (selected : j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27) : arrAt w j + 8 * w ≤ 8 * len := by
  have index : j + 1 ≤ 28 := by omega
  calc
    arrAt w j + 8 * w ≤ arrAt w j + 8 * (w + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 8 (by omega)) _
    _ = hdrBytes + (j + 1) * (8 * (w + 2)) := by
      simp only [arrAt, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    _ ≤ arrAt w 28 := Nat.add_le_add_left (Nat.mul_le_mul_right _ index) _
    _ ≤ 8 * len := fit

theorem kept_number {B : Addr} {len w j : Nat} {m m' : Mem}
    (h : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B len w m m')
    (fit : arrAt w 28 ≤ 8 * len) (selected : j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    numAt m' B w j = numAt m B w j := by
  unfold numAt
  apply congrArg BitVec.toNat
  apply keeps_read (d := arrAt w j) (size := 8 * w) h
  · exact static_array_fit fit selected
  · intro k hk
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      right <;> simp only [arrAt, hdrBytes] <;> omega
  · intro k hk
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases selected with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp only [arrAt, hdrBytes] <;> omega
  · rcases selected with rfl | rfl | rfl | rfl <;>
      simp only [Spec.MillerRabin.compact, arrAt, hdrBytes] <;> omega

end VG.Proof.MillerRabin
