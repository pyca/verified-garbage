module

public import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2

/-! # Table selection reuses the shared RSA selection loop -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem select_ok {s : State} {base : Addr} {size w o a : Nat} {k : Bool}
    (hs : Scr s base size) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ size) (ho : o < 28) (ha : a < 28) (hna : a ≠ o)
    (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) (mask : s.gpr .esi = cmask k) :
    WP isa (select o a) s fun t =>
      val32 t.mem base (arrAt w o) (2 * w) =
        (if k then val32 s.mem base (arrAt w a) (2 * w) else val32 s.mem base (arrAt w o) (2 * w)) ∧
      Outside base (arrAt w o) (8 * w) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ebp, .ecx, .edx, .esi] s t := by
  have fa := array_fits_bytes hf ha
  have fo := array_fits_bytes hf ho
  have h52 : 52 ≤ size := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  unfold select
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc hs h52, hwidth]) hu hs.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [readSrc_sc hs₁ h52, m₁, hwidth]) hu hs₁.edi_toNat fun s₂ K₂ m₂ p₂ => ?_
  have K₂' : Keeps [.ebp, .ebx, .edx] s s₂ :=
    (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := hs.of_keeps K₂' (by decide)
  refine width_ok (by rw [readSrc_sc hs₂ h52, m₂, m₁, hwidth]) fun s₃ K₃ m₃ v₃ => ?_
  refine wp_movS rfl fun s₄ U₄ _ => wp_movS rfl fun s₅ U₅ _ => wp_movS rfl fun s₆ U₆ _ => WP.block_nil ?_
  have K₆ : Keeps [.eax, .ebx, .ebp, .ecx, .edx, .esi, .edi] s s₆ :=
    (((((K₂'.mono (by decide)).trans (K₃.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide)))
  have mem₆ : s₆.mem = s.mem := by rw [U₆.mem, U₅.mem, U₄.mem, m₃, m₂, m₁]
  have saved : s₆.gpr .esi = s.gpr .edi := by
    rw [U₆.other .esi (by decide), U₅.gpr, U₄.other .edi (by decide), K₃.1 .edi (by decide),
      K₂'.1 .edi (by decide)]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok
    (W := base) (L := size) ⟨by rw [K₆.2.2]; exact hs.wr, hs.nowrap⟩ (x := arrAt w a) (d := arrAt w o)
    (N := 2 * w) k (by omega) (by omega) (by omega) (by have := arrays_apart w hna; omega)
    (by rw [PtrAt, U₆.other .ebp (by decide), U₅.other .ebp (by decide), U₄.other .ebp (by decide),
          K₃.1 .ebp (by decide), K₂.1 .ebp (by decide)]; exact p₁)
    (by rw [PtrAt, U₆.other .ebx (by decide), U₅.other .ebx (by decide), U₄.other .ebx (by decide),
          K₃.1 .ebx (by decide)]; exact p₂)
    (by rw [U₆.gpr, U₅.other .edx (by decide), U₄.other .edx (by decide), v₃, BitVec.toNat_ofNat]; omega)
    (by rw [U₆.other .ecx (by decide), U₅.other .ecx (by decide), U₄.gpr, K₃.1 .esi (by decide),
          K₂'.1 .esi (by decide), mask])) ?_)
  rintro u ⟨O, V, _, K⟩
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  rw [mem₆, show 4 * (2 * w) = 8 * w by omega] at O
  rw [mem₆] at V
  have allK : Keeps [.eax, .ebx, .ebp, .ecx, .edx, .esi, .edi] s t :=
    (K₆.trans (K.mono (by decide))).trans (U.keeps.mono (by decide))
  refine ⟨by rw [U.mem]; exact V, by rw [U.mem]; exact O, ?_⟩
  refine ⟨fun r hr => ?_, allK.2⟩
  by_cases he : r = .edi
  · subst r
    rw [U.gpr, K.1 .esi (by decide), saved]
  · exact allK.1 r (by cases r <;> simp_all)

end VG.Proof.MillerRabin.X86
