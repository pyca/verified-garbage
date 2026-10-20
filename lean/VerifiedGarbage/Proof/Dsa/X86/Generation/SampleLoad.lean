module
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Bytes

/-! # Loading a witness preserves the prepared modulus and its constants -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem sampleLoad_ok {s : State} {base : Addr} {size n m len : Nat}
    (C : Context n m base size s) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (loadComponent len n (slot n 5)) s fun t => Context n m base size t ∧
      wordsVal t.mem base (slot n 5) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      Outside base (slot n 5) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have bound : slot n 5 + 8 * n ≤ size := by
    have := slot_bound (n := n) (i := 5) (by decide)
    have := C.size_le
    unfold stride at *
    omega
  refine WP.mono (loadComponent_ok C.scr bound fit h4 hlen hw4 read
    (apart.sub_right (Offset.sub_base _ bound))) fun t ⟨value, K, O⟩ => ?_
  refine ⟨C.outside_keep K (by decide) (by decide) O ?_ ?_, value, O, K⟩
  · simp only [slot, stride]; omega
  · simp only [slot]; omega
end VG.Proof.Dsa.X86.Generation
