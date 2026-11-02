module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeptArrays
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! The phase's immutable shared-round constants. Witness imports,
Montgomery conversions and the shared round itself preserve these data. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.MillerRabin.Arm (LayoutLite PreparedLite KeepsLite wJs)

structure RoundData (base : BitVec 32) (capacity w n : Nat) (m : Mem) : Prop where
  data : MontData base capacity w m
  minWords : 4 ≤ w
  maxWords : w ≤ 128
  fits : arrAt w 28 ≤ 8 * capacity
  large : 3 ≤ n
  odd : n % 2 = 1
  modulus : numAt m (VG.Arm.State.addr base) w 0 = n
  r2 : numAt m (VG.Arm.State.addr base) w 4 = 2 ^ (128 * w) % n
  one : numAt m (VG.Arm.State.addr base) w 9 = 2 ^ (64 * w) % n
  minus : numAt m (VG.Arm.State.addr base) w 10 = n - 2 ^ (64 * w) % n
  exponent : numAt m (VG.Arm.State.addr base) w 27 = Proof.MillerRabin.Round.exponent n
  power : m.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64 =
    BitVec.twoPow 64 ((Spec.Rsa.splitTwos (n - 1)).1 % 64)

theorem RoundData.layout {base : BitVec 32} {capacity w n : Nat} {m : Mem}
    (h : RoundData base capacity w n m) : LayoutLite m (VG.Arm.State.addr base) capacity := by
  refine ⟨h.data.layout, ?_⟩
  rw [h.data.width]
  exact ⟨h.minWords, h.maxWords, h.fits⟩

theorem RoundData.prepared {base : BitVec 32} {capacity w n : Nat} {m : Mem}
    (h : RoundData base capacity w n m) (witness : numAt m (VG.Arm.State.addr base) w 5 < n) :
    PreparedLite m (VG.Arm.State.addr base) := by
  unfold PreparedLite
  rw [h.data.width]
  dsimp only
  rw [h.modulus]
  exact ⟨h.large, h.odd, h.data.inverse, witness, h.one, h.minus, h.exponent, h.power⟩

theorem RoundData.after_reads {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m)
    (header : ∀ d, d + 8 ≤ 128 → m'.readW (off (VG.Arm.State.addr base) d) 64 =
      m.readW (off (VG.Arm.State.addr base) d) 64)
    (arrays : ∀ q ∈ [0, 4, 9, 10, 27], numAt m' (VG.Arm.State.addr base) w q =
      numAt m (VG.Arm.State.addr base) w q)
    (power : m'.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64 =
      m.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64) : RoundData base capacity w n m' :=
  ⟨(h.data.after_reads header (arrays 0 (by simp))).1, h.minWords, h.maxWords, h.fits, h.large, h.odd,
    (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    (arrays 9 (by simp)).trans h.one, (arrays 10 (by simp)).trans h.minus,
    (arrays 27 (by simp)).trans h.exponent, power.trans h.power⟩

theorem RoundData.after_operand {base : BitVec 32} {capacity w n o : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m) (oBound : o < 8) (o0 : o ≠ 0) (o4 : o ≠ 4)
    (keep : Keeps (VG.Arm.State.addr base) capacity w o m m') : RoundData base capacity w n m' := by
  have size : 256 ≤ 8 * capacity :=
    Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) h.fits
  have unwritten (q : Nat) (member : q ∈ [0, 4, 9, 10, 27]) : q < 28 ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
  refine h.after_reads (fun _ bound => keeps_header_readW keep size (by omega)) ?_ ?_
  · intro q member
    have p := unwritten q member
    have read := operand_keeps_extended keep h.fits p.1 p.2.1 p.2.2.1 p.2.2.2 (d := 0) (n := 8 * w) (by omega)
    simpa only [numAt, off, Nat.add_zero] using congrArg BitVec.toNat read
  · unfold Mem.readW
    rw [operand_keeps_extended keep h.fits (q := 27) (by decide) (by decide) (by decide) (by omega)
      (d := 8 * w) (n := 8) (by omega)]

theorem RoundData.after_round {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m)
    (keep : KeepsLite (VG.Arm.State.addr base) capacity w m m') : RoundData base capacity w n m' := by
  have size : 128 ≤ 8 * capacity := Nat.le_trans (by decide : 128 ≤ 256)
    (Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) h.fits)
  have unwritten : ∀ q ∈ [0, 4, 9, 10, 27], q < 28 ∧ q ∉ wJs := by decide
  refine h.after_reads (fun _ bound => round_keeps_header keep size bound) ?_ ?_
  · intro q member
    have p := unwritten q member
    have read := round_keeps_array keep h.fits p.1 p.2 (d := 0) (n := 8 * w) (by omega)
    simpa only [numAt, off, Nat.add_zero] using congrArg BitVec.toNat read
  · unfold Mem.readW
    rw [round_keeps_array keep h.fits (q := 27) (by decide) (by decide) (d := 8 * w) (n := 8) (by omega)]

private theorem array64 {w q : Nat} (words : w ≤ 128) (index : q ≤ 27) :
    arrAt w q + 8 * (w + 2) ≤ 2 ^ 64 := by
  have scale := Nat.mul_le_mul_right (8 * (w + 2)) index
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega

theorem RoundData.after_aux_word {base : BitVec 32} {capacity w n d : Nat} {m : Mem}
    (h : RoundData base capacity w n m) (lower : 128 ≤ d) (upper : d + 4 ≤ 256) (value : BitVec 32) :
    RoundData base capacity w n (m.writeW (off (VG.Arm.State.addr base) d) value) := by
  have outside := writeW32_outside m (VG.Arm.State.addr base) value (d := d) (by omega)
  refine h.after_reads (fun _ bound => outside.word (.inl (by omega)) (by omega)) ?_ ?_
  · intro q member
    have indexBound : ∀ q ∈ [0, 4, 9, 10, 27], q ≤ 27 := by decide
    have fit := array64 h.maxWords (indexBound q member)
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
      omega
    · exact Nat.le_trans (by omega) fit
  · have fit := array64 h.maxWords (q := 27) (by decide)
    exact outside.word (.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega)) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
