module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProtectedContext
import VerifiedGarbage.Proof.MillerRabin.X86.Geometry

/-! # Save and restore the 32-byte tail borrowed from array one -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem saveTail_ok {s : State} {base : Addr} {bytes w : Nat}
    (h : ProtectedContext s base bytes) (hf : arrAt w 28 ≤ bytes)
    (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa saveTail s
      (TransferResult s (ptr32 base (scratch w)) (ptr32 (byteAddr (s.gpr .esp)) savedTail) 32) := by
  have bound : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have h52 : 52 ≤ bytes := by simp only [scratch] at bound; omega
  unfold saveTail
  apply h.to_stack (by decide) (by decide) bound (by decide)
  simp only [List.append_assoc]
  refine scratchPointer_ok (by decide) (by rw [readSrc_sc h.ws h52, hwidth]) h.ws.edi_toNat
    fun s₁ K₁ m₁ p₁ => ?_
  refine stackPointer_ok fun s₂ K₂ m₂ p₂ => ?_
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  refine ⟨((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U.keeps.mono (by decide)),
    by rw [U.mem, m₂, m₁], ?_, ?_, U.gpr⟩
  · rw [U.other .esi (by decide), K₂.1 .esi (by decide)]
    exact ptrAt_eq p₁
  · rw [U.other .ebx (by decide), p₂, K₁.1 .esp (by decide)]
    exact ptr32_stack _ _

theorem restoreTail_ok {s : State} {base : Addr} {bytes w : Nat}
    (h : ProtectedContext s base bytes) (hf : arrAt w 28 ≤ bytes)
    (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa restoreTail s
      (TransferResult s (ptr32 (byteAddr (s.gpr .esp)) savedTail) (ptr32 base (scratch w)) 32) := by
  have bound : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have h52 : 52 ≤ bytes := by simp only [scratch] at bound; omega
  unfold restoreTail
  apply h.from_stack (by decide) (by decide) bound (by decide)
  simp only [List.append_assoc]
  refine scratchPointer_ok (by decide) (by rw [readSrc_sc h.ws h52, hwidth]) h.ws.edi_toNat
    fun s₁ K₁ m₁ p₁ => ?_
  refine stackPointer_ok fun s₂ K₂ m₂ p₂ => ?_
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  refine ⟨((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U.keeps.mono (by decide)),
    by rw [U.mem, m₂, m₁], ?_, ?_, U.gpr⟩
  · rw [U.other .esi (by decide), p₂, K₁.1 .esp (by decide)]
    exact ptr32_stack _ _
  · rw [U.other .ebx (by decide), K₂.1 .ebx (by decide)]
    exact ptrAt_eq p₁

end VG.Proof.MillerRabin.X86
