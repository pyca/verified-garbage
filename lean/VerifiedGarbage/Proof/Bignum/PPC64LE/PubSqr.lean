module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.SqrCore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios

/-!
# The RSA public-key operation on PPC64LE: Montgomery squares

`sqrOp_ok`: `SqrCore.lean`'s `sqrN_ok`, with the bases; stated as
`montOp_ok` with `b = a`, for `a` other than array 3.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE

/-- `sqrOp o a`, in the working space at `B` with array 0 at `r10`, the arrays'
size in `r29`, `2 w` in `r11` and `-n⁻¹ mod 2³²` in `r12`. -/
theorem sqrOpN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (ha3 : a ≠ 3) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : val32 s.mem B (slot w a) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (sqrOp o a) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w a) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep montRegs s t := by
  unfold sqrOp
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r5) (by decide) (by decide) h10 h29 o) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r6) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) a) fun t₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 2) fun t₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := k12.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 3) fun t₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ t.mem = t₅.mem)
    (by prun [(k15.gpr .r11 (by decide)).trans h11, BitVec.add_zero]) (by decide)) fun t₆ ⟨⟨a4, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have hm : t₆.mem = s.mem := by rw [m6, m5, m4, m2, m1]
  have g : ∀ r ∈ [Reg.r10, .r11, .r12], t₆.gpr r = s.gpr r := fun r hr => k16.gpr r (by revert r hr; decide)
  have g5 : t₆.gpr .r5 = off B (slot w o) := by rw [k6.gpr .r5 (by decide), k5.gpr .r5 (by decide),
    k4.gpr .r5 (by decide), k2.gpr .r5 (by decide), a5]
  have g6 : t₆.gpr .r6 = off B (slot w a) := by rw [k6.gpr .r6 (by decide), k5.gpr .r6 (by decide),
    k4.gpr .r6 (by decide), a6]
  have g8 : t₆.gpr .r8 = off B (slot w 2) := by rw [k6.gpr .r8 (by decide), k5.gpr .r8 (by decide), a8]
  have g9 : t₆.gpr .r9 = off B (slot w 3) := by rw [k6.gpr .r9 (by decide), a9]
  rw [← hm] at hinv hA ⊢
  refine WP.mono (Sqr.sqrN_ok (hs.congr k16.wr) hn ho ha ho2 ho3 ha2 ha3 hw2 hw' hZ g5 g6 g8 g9
    ((g _ (by decide)).trans h10) ((g _ (by decide)).trans h11) a4 (by rw [g _ (by decide)]; exact h12)
    (by rw [g _ (by decide)]; exact hinv) hA) fun t ⟨h, k⟩ => ⟨h, (k16.trans k).mono⟩

/-- `sqrOpN_ok` for arrays below 8. -/
theorem sqrOp_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : val32 s.mem B (slot w a) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (sqrOp o a) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w a) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep montRegs s t :=
  sqrOpN_ok hs (by decide) ho ha ho2 ho3 ha2 ha3 hw2 hw' hZ h10 h29 h11 h12 hinv hA

end VG.Proof.Bignum.PPC64LE.Pub
