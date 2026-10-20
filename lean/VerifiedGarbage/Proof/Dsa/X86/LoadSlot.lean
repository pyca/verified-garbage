module

import VerifiedGarbage.Proof.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Loading DSA operands preserves the runtime arithmetic context -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem loadSlot_ok {s : State} {base : Addr} {size len n m i : Nat}
    (h : Context n m base size s) (hi : i < 9) (hi0 : i ≠ 0)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨off base (slot n i), 8 * n⟩) :
    WP isa (loadComponent len n (slot n i)) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base (slot n i) (8 * n) s.mem t.mem := by
  have bound := slot_bound (n := n) hi
  simp only [stride] at bound
  have sep := slot_sep (n := n) hi0
  refine WP.mono (loadComponent_ok h.scr (by have := h.size_le; omega) hp h4 hlen hw4 hr hd)
    fun t ⟨V, K, O⟩ => ⟨?_, V, K, O⟩
  apply h.outside_keep K (by decide) (by decide) O
  · simp only [stride] at sep
    omega
  · have := slot_header n i
    omega

end VG.Proof.Dsa.X86
