module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactHeaderStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactHeaderPointers
public import VerifiedGarbage.Spec.MillerRabin

/-! The native header satisfies the existing compact Miller–Rabin layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa.Mont (arrAt wOf)

theorem compact_header {s : State} {base : Addr} {bytes w wsLen : Nat}
    (h : Scr s base bytes) (lower : 4 ≤ w) (upper : w ≤ 128)
    (fit : arrAt w 28 ≤ bytes) (size : bytes = 8 * wsLen) :
    WP isa (.block (compactHeader w)) s fun t =>
      Scr t base bytes ∧ Outside base 0 256 s.mem t.mem ∧
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem base wsLen ∧
      wOf t.mem base = w ∧ Keeps [.eax, .edx] s t := by
  have head : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right 256 _) fit
  have fit8 : arrAt w 8 ≤ bytes := by
    have mul := Nat.mul_le_mul_right (8 * (w + 2)) (by decide : 8 ≤ 28)
    unfold arrAt Spec.Rsa.Mont.hdrBytes at fit ⊢
    omega
  unfold compactHeader
  refine WP.block_append (WP.mono (compact_header_start h head upper) ?_)
  rintro a ⟨ha, F, count, stride, zero, K⟩
  refine WP.mono (compact_header_pointers ha fit8 zero 8 (by decide)) ?_
  rintro t ⟨ht, F', pointers, _, K'⟩
  have width : wOf t.mem base = w := by
    change (word t.mem base 48).toNat = w
    rw [F'.word (by decide) (by decide)]
    exact count
  have stride' : (word t.mem base 224).toNat = 8 * (w + 2) := by
    rw [F'.word (by decide) (by decide)]
    exact stride
  have mont : Spec.Rsa.Mont.Layout t.mem base wsLen := by
    unfold Spec.Rsa.Mont.Layout
    rw [width]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [← size]; exact fit8
    · intro j hj
      change word t.mem base (8 * (8 + j)) = off base (arrAt w j)
      rw [show 8 * (8 + j) = 64 + 8 * j by omega]
      exact pointers j hj
  refine ⟨ht, F.trans (F'.mono (by omega) (by omega)), ?_, width, K.trans (K'.mono (by decide))⟩
  refine ⟨.inr rfl, mont, ?_, ?_, ?_, ?_⟩
  · rw [width]; exact lower
  · rw [width]; exact upper
  · change arrAt (wOf t.mem base) 28 ≤ 8 * wsLen
    rw [width, ← size]; exact fit
  · change word t.mem base 224 = BitVec.ofNat 64 (8 * (wOf t.mem base + 2))
    rw [width]
    apply BitVec.eq_of_toNat_eq
    rw [stride', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Dsa.X86.Generation
