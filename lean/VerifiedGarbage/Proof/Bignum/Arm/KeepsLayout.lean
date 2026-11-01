module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Reuse the shared preservation contract between RSA arithmetic operations -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)

theorem keeps_header_word {m m' : Mem} {base : Addr} {len w o d : Nat}
    (keep : Keeps base len w o m m') (size : 256 ≤ 8 * len) (hd : d + 8 ≤ 256) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro j hj
  change m' (base + BitVec.ofNat 64 d + BitVec.ofNat 64 j) = _
  rw [Offset.add_add]
  apply keep (d + j) (by omega)
  intro a _
  left
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega

theorem keeps_header_readW {m m' : Mem} {base : Addr} {len w o d bits : Nat}
    (keep : Keeps base len w o m m') (size : 256 ≤ 8 * len) (hd : d + bits / 8 ≤ 256) :
    m'.readW (off base d) bits = m.readW (off base d) bits := by
  apply Mem.readW_congr
  intro j hj
  change m' (base + BitVec.ofNat 64 d + BitVec.ofNat 64 j) = _
  rw [Offset.add_add]
  apply keep (d + j) (by omega)
  intro a _
  left
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega

theorem keeps_layout {m m' : Mem} {base : Addr} {len o : Nat}
    (layout : Layout m base len) (keep : Keeps base len (wOf m base) o m m') :
    wOf m' base = wOf m base ∧ Layout m' base len := by
  have size : 256 ≤ 8 * len := by
    have := layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have width : wOf m' base = wOf m base :=
    congrArg BitVec.toNat (keeps_header_word keep size (d := 48) (by decide))
  refine ⟨width, ?_⟩
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  change word m' base (8 * (8 + j)) = _
  rw [keeps_header_word keep size (by omega)]
  exact layout.2.2.2 j hj

theorem keeps_array_read {m m' : Mem} {base : Addr} {len w o q d n : Nat}
    (keep : Keeps base len w o m m') (fits : arrAt w 8 ≤ 8 * len)
    (hq : Operand q) (neq : q ≠ o) (hd : d + n ≤ 8 * (w + 2)) :
    m'.read (off base (arrAt w q + d)) n = m.read (off base (arrAt w q + d)) n := by
  have bound := Nat.le_trans (array_end_le hq.1) fits
  apply Mem.read_congr
  intro j hj
  change m' (base + BitVec.ofNat 64 (arrAt w q + d) + BitVec.ofNat 64 j) = _
  rw [Offset.add_add]
  apply keep (arrAt w q + d + j) (by omega)
  intro a ha
  have different : q ≠ a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hq.2.1
    · exact hq.2.2
    · exact neq
  have sep := array_sep (w := w) different
  omega

theorem keeps_array_word {m m' : Mem} {base : Addr} {len w o q d bits : Nat}
    (keep : Keeps base len w o m m') (fits : arrAt w 8 ≤ 8 * len)
    (hq : Operand q) (neq : q ≠ o) (hd : d + bits / 8 ≤ 8 * (w + 2)) :
    m'.readW (off base (arrAt w q + d)) bits = m.readW (off base (arrAt w q + d)) bits := by
  simp only [Mem.readW, keeps_array_read keep fits hq neq hd]

theorem keeps_array_num {m m' : Mem} {base : Addr} {len w o q : Nat}
    (keep : Keeps base len w o m m') (fits : arrAt w 8 ≤ 8 * len)
    (hq : Operand q) (neq : q ≠ o) : numAt m' base w q = numAt m base w q := by
  have h := keeps_array_read (d := 0) (n := 8 * w) keep fits hq neq (by omega)
  simpa only [numAt, off, Nat.add_zero] using congrArg BitVec.toNat h

end VG.Proof.Bignum.Arm
