module

public import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Equality tests use RSA's existing word comparison and zero test -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem equal_tail_ok {s : State} {base : Addr} {size d : Nat}
    (hs : Scr s base size) (hd : d + 4 ≤ size) :
    WP isa (.block [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .alu .or .eax (.reg .ecx),
      .shift .shr .eax 31, .alu .xor .eax (.imm 1), .store (sc d) .eax]) s fun t =>
      w32 t.mem base d = (decide (s.gpr .ecx = 0)).toNat ∧
      Outside base d 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  refine wp_movS rfl fun s₁ U₁ _ => wp_subS rfl fun s₂ U₂ _ => wp_orS rfl fun s₃ U₃ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₄ U₄ =>
    wp_logicS (.inr rfl) rfl fun s₅ U₅ => ?_
  have K₅ : Keeps [.eax] s s₅ := (((U₁.keeps.trans U₂.keeps).trans U₃.keeps).trans U₄.keeps).trans U₅.keeps
  have mem : s₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have hs₅ := hs.of_keeps K₅ (by decide)
  have value : s₅.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ecx = 0)).toNat := by
    rw [U₅.gpr, ite_eq_right (by decide), U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr,
      U₂.other .ecx (by decide), U₁.other .ecx (by decide)]
    exact VG.Proof.Rsa.zero_test32 _
  refine wp_storeS (hs₅.ea (by omega)) (hs₅.write hd) fun t M => WP.block_nil ?_
  refine ⟨?_, ?_, K₅.trans (M.keeps _)⟩
  · rw [M.mem, w32_write_self, value, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by cases decide (s.gpr .ecx = 0) <;> decide)
  · rw [M.mem, mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

theorem equal_ok {s : State} {base : Addr} {size w a b d : Nat}
    (hs : Scr s base size) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ size) (ha : a < 28) (hb : b < 28) (hd : d + 4 ≤ size)
    (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (equal d a b) s fun t =>
      w32 t.mem base d =
        (decide (val32 s.mem base (arrAt w a) (2 * w) = val32 s.mem base (arrAt w b) (2 * w))).toNat ∧
      Outside base d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp, .ecx, .edx] s t := by
  have fa := array_fits_bytes hf ha
  have fb := array_fits_bytes hf hb
  have h52 : 52 ≤ size := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  unfold equal
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
  refine wp_movS rfl fun s₄ U₄ _ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .ebx, .ebp, .ecx, .edx] s s₄ :=
    (((K₂'.mono (by decide)).trans (K₃.mono (by decide))).trans (U₄.keeps.mono (by decide)))
  have hs₄ := hs.of_keeps K₄ (by decide)
  have mem₄ : s₄.mem = s.mem := by rw [U₄.mem, m₃, m₂, m₁]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.eqLoop_ok ⟨hs₄.wr, hs₄.nowrap⟩
    (x := arrAt w a) (y := arrAt w b) (N := 2 * w)
    (by omega) (by omega) (by omega)
    (by rw [PtrAt, U₄.other .ebp (by decide), K₃.1 .ebp (by decide), K₂.1 .ebp (by decide)]; exact p₁)
    (by rw [PtrAt, U₄.other .ebx (by decide), K₃.1 .ebx (by decide)]; exact p₂)
    U₄.gpr (by rw [U₄.other .edx (by decide), v₃, BitVec.toNat_ofNat]; omega)) ?_)
  rintro u ⟨mem, eq, K⟩
  have KK : Keeps [.eax, .ebx, .ebp, .ecx, .edx] s u := K₄.trans (K.mono (by decide))
  have hsU := hs.of_keeps KK (by decide)
  refine WP.mono (equal_tail_ok hsU hd) fun t ⟨V, O, Kt⟩ => ?_
  have allmem : u.mem = s.mem := mem.trans mem₄
  rw [mem₄] at eq
  rw [allmem] at O
  exact ⟨by rw [V, decide_eq_decide.mpr eq], O, KK.trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
