module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! The shared RSA arithmetic and Miller–Rabin preservation contracts also
protect constants in arrays above the eight Montgomery arithmetic arrays. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.MillerRabin.Arm (KeepsLite wJs)

theorem operand_keeps_extended {m m' : Mem} {base : Addr} {capacity w o q d n : Nat}
    (keep : Keeps base capacity w o m m') (fits : arrAt w 28 ≤ 8 * capacity) (bound : q < 28)
    (q2 : q ≠ 2) (q3 : q ≠ 3) (qo : q ≠ o) (bytes : d + n ≤ 8 * (w + 2)) :
    m'.read (off base (arrAt w q + d)) n = m.read (off base (arrAt w q + d)) n := by
  have arrayFit := Nat.le_trans (array_end_le bound) fits
  apply Mem.read_congr
  intro i hi
  change m' (base + BitVec.ofNat 64 (arrAt w q + d) + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  apply keep (arrAt w q + d + i) (by omega)
  intro a ha
  have different : q ≠ a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact q2
    · exact q3
    · exact qo
  have := array_sep (w := w) different
  omega

theorem round_keeps_read {m m' : Mem} {base : Addr} {capacity w d n : Nat}
    (keep : KeepsLite base capacity w m m') (fit : d + n ≤ 8 * capacity)
    (header : ∀ k ∈ [23, 26, 29, 30], d + n ≤ 8 * k ∨ 8 * k + 8 ≤ d)
    (arrays : ∀ j ∈ wJs, d + n ≤ arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ d) :
    m'.read (off base d) n = m.read (off base d) n := by
  apply Mem.read_congr
  intro i hi
  change m' (base + BitVec.ofNat 64 d + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  apply keep (d + i) (by omega)
  · intro k hk
    have := header k hk
    omega
  · intro j hj
    have := arrays j hj
    omega

theorem round_keeps_header {m m' : Mem} {base : Addr} {capacity w d bits : Nat}
    (keep : KeepsLite base capacity w m m') (size : 128 ≤ 8 * capacity) (fit : d + bits / 8 ≤ 128) :
    m'.readW (off base d) bits = m.readW (off base d) bits := by
  unfold Mem.readW
  rw [round_keeps_read keep (by omega) (by
    intro k hk
    have bound : ∀ k ∈ [23, 26, 29, 30], 16 ≤ k := by decide
    have := bound k hk
    left
    omega) (by
    intro j _
    left
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
    omega)]

theorem round_keeps_array {m m' : Mem} {base : Addr} {capacity w q d n : Nat}
    (keep : KeepsLite base capacity w m m') (fits : arrAt w 28 ≤ 8 * capacity) (bound : q < 28)
    (unwritten : q ∉ wJs) (bytes : d + n ≤ 8 * (w + 2)) :
    m'.read (off base (arrAt w q + d)) n = m.read (off base (arrAt w q + d)) n := by
  have arrayFit := Nat.le_trans (array_end_le bound) fits
  refine round_keeps_read keep (by omega) ?_ ?_
  · intro k hk
    have upper : ∀ k ∈ [23, 26, 29, 30], k ≤ 30 := by decide
    have := upper k hk
    right
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
    omega
  · intro j hj
    have different : q ≠ j := fun same => unwritten (same ▸ hj)
    have := array_sep (w := w) different
    omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
