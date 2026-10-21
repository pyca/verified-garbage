module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow

/-! # Alignment marker and top sentinel remain available across all three passes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

structure Context (base : Addr) (size n marker out k : Nat) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < n
  fit : out + 4 * (n + 1) ≤ size
  markerFit : marker + 8 ≤ size
  apart : marker + 8 ≤ out
  index : k < 64
  value : word s.mem base marker = BitVec.twoPow 64 k
  top : w32 s.mem base (out + 4 * n) = 0

theorem halfIf_context {s : State} {base : Addr} {size n marker out j k : Nat}
    (C : Context base size n marker out k s) (choice : 1 ≤ j ∧ j ≤ 3) :
    WP isa (halfIf n marker out j) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (halfIf_ok C.scratch C.positive C.fit C.markerFit C.top C.index choice C.value)
    fun t ⟨O, V, K⟩ => ?_
  refine ⟨⟨C.scratch.of_keeps K (by decide), C.positive, C.fit, C.markerFit, C.apart, C.index, ?_, ?_⟩, O, V, K⟩
  · rw [O.word (Or.inl C.apart) (by have := C.scratch.nowrap; have := C.markerFit; omega)]
    exact C.value
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by have := C.scratch.nowrap; have := C.fit; omega)]
    exact C.top

end VG.Proof.RsaKeyGen.X86.ExponentShift
