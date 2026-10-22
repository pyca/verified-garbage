module

public import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry
public import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset

/-! # Workspace transfers reuse the existing verified byte-copy loop -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)
open VG.Proof.Mont.X86.Rt (PtrAt)

def ptr32 (base : Addr) (d : Nat) : BitVec 32 := BitVec.ofNat 32 (base.toNat + d)

theorem ptrAt_eq {s : State} {base : Addr} {r : Reg} {d : Nat} (h : PtrAt s base r d) :
    s.gpr r = ptr32 base d := by
  apply BitVec.eq_of_toNat_eq
  exact h

theorem ptr32_toNat {base : Addr} {d : Nat} (h : base.toNat + d < 2 ^ 32) :
    (ptr32 base d).toNat = base.toNat + d := by
  simp only [ptr32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ptr32_addr {base : Addr} {d : Nat} (h : base.toNat + d < 2 ^ 32) :
    byteAddr (ptr32 base d) = VG.Proof.Mont.off base d := by
  apply BitVec.eq_of_toNat_eq
  have b := base.isLt
  simp only [byteAddr, ptr32, VG.Proof.Mont.off, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

theorem arrays_apart (w : Nat) {a o : Nat} (h : a ≠ o) :
    arrAt w a + 8 * w ≤ arrAt w o ∨ arrAt w o + 8 * w ≤ arrAt w a := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := array_monotone w (show a + 1 ≤ o by omega)
    simp only [arrAt, Nat.add_mul, Nat.one_mul] at *
    omega
  · right
    have := array_monotone w (show o + 1 ≤ a by omega)
    simp only [arrAt, Nat.add_mul, Nat.one_mul] at *
    omega

theorem copy_ok {s : State} {base : Addr} {size w o a : Nat}
    (hs : Scr s base size) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ size) (ho : o < 28) (ha : a < 28) (hno : a ≠ o)
    (hwidth : s.mem.readW (VG.Proof.Mont.off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (copy o a) s fun t =>
      numAt t.mem base w o = numAt s.mem base w a ∧
      Frame [⟨VG.Proof.Mont.off base (arrAt w o), 8 * w⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .edx, .ecx] s t := by
  have nwa := hs.nowrap
  have fa : arrAt w a + 8 * w ≤ size := by
    have := array_monotone w (show a + 1 ≤ 28 by omega)
    simp only [arrAt, Nat.add_mul, Nat.one_mul] at this hf ⊢
    omega
  have fo : arrAt w o + 8 * w ≤ size := by
    have := array_monotone w (show o + 1 ≤ 28 by omega)
    simp only [arrAt, Nat.add_mul, Nat.one_mul] at this hf ⊢
    omega
  have h52 : 52 ≤ size := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  have wa := ptr32_toNat (base := base) (d := arrAt w a) (by omega)
  have wo := ptr32_toNat (base := base) (d := arrAt w o) (by omega)
  have aa := ptr32_addr (base := base) (d := arrAt w a) (by omega)
  have ao := ptr32_addr (base := base) (d := arrAt w o) (by omega)
  unfold copy
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc hs h52, hwidth]) hu hs.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc hs₁ h52, m₁, hwidth]) hu hs₁.edi_toNat fun s₂ K₂ m₂ p₂ => ?_
  have K₁₂ : Keeps [.esi, .edx, .ebx] s s₂ :=
    (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := hs.of_keeps K₁₂ (by decide)
  refine width_ok (by rw [readSrc_sc hs₂ h52, m₂, m₁, hwidth]) fun s₃ K₃ m₃ v₃ => ?_
  have K : Keeps [.eax, .ebx, .esi, .edx, .ecx] s s₃ :=
    (K₁₂.mono (by decide)).trans (K₃.mono (by decide))
  have hs₃ := hs.of_keeps K (by decide)
  have mem : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.block_nil (WP.mono (copyBuffers_ok (n := 8 * w) (by omega) (by omega)
    (by rw [wa]; omega) (by rw [wo]; omega)
    (by rw [aa]; exact hs₃.read fa) (by rw [ao]; exact hs₃.write fo)
    (by rw [aa, ao]; exact Offset.disjoint _ (arrays_apart w hno) (by omega) (by omega))
    (by rw [K₃.1 .esi (by decide), K₂.1 .esi (by decide)]; exact ptrAt_eq p₁)
    (by rw [K₃.1 .ebx (by decide)]; exact ptrAt_eq p₂) v₃) ?_)
  rintro t ⟨V, _, _, F, Kt⟩
  rw [aa, ao, mem] at V
  rw [ao, mem] at F
  exact ⟨congrArg BitVec.toNat V, F, K.trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
