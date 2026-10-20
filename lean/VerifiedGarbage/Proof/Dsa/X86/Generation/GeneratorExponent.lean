module
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Bytes

/-! # Reload the generator exponent without rebuilding the modulus context -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem generatorExponent_ok {s : State} {base : Addr} {size n p len : Nat}
    (C : Context n p base size s) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (loadComponent len n (slot n 8)) s fun t => Context n p base size t ∧
      val32 t.mem base (slot n 8) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      (∀ i < 8, wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n) ∧
      Outside base (slot n 8) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have bound : slot n 8 + 8 * n ≤ size := by
    have := slot_bound (n := n) (i := 8) (by decide)
    have := C.size_le
    unfold stride at *
    omega
  refine WP.mono (loadComponent_ok C.scr bound fit h4 hlen hw4 read
    (apart.sub_right (Offset.sub_base _ bound))) fun t ⟨value, K, O⟩ => ?_
  refine ⟨C.outside_keep K (by decide) (by decide) O
    (.inl (by simp only [slot, stride]; omega)) (by simp only [slot, stride]; omega),
    by rw [← wordsVal_eq_val32]; exact value, ?_, O, K⟩
  intro i hi
  apply O.wordsVal
  · have mul := Nat.mul_le_mul_right (16 * n + 8) (show i + 1 ≤ 8 by omega)
    simp only [slot, stride]
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  · have := slot_bound (n := n) (i := i) (by omega)
    have := C.size_le
    have := C.scr.nowrap
    unfold stride at *
    omega
end VG.Proof.Dsa.X86.Generation
