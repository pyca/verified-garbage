module

public import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

/-! # Constant-time public width scans through the saved field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ScanFieldPre (fp fl : Field) (p : ScanPublic) (s : State) : Prop :=
  Scr s p.base p.extent ∧ s.gpr .rdi = p.base ∧ pWorkspace ≤ p.extent ∧
  word s.mem p.base fp.offset = p.pointer ∧ word s.mem p.base fl.offset = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.base p.extent p.pointer p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

theorem scanField_ct (fp fl : Field) {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))]) hint).isSome = true) :
    RelCT isa (Two (ScanFieldPre fp fl))
      (.seq (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))]) Checks.significant)
      (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := ScanPre) [.rdi] (pins_of (fun p _ => p.base) (by
    intro p s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1)) hT ?_) significant_ct
  intro p s ⟨hs, hdi, hZ, hp, hl, hsrc, h1, h64⟩
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = p.pointer ∧ t.gpr .rcx = BitVec.ofNat 64 p.bytes.length ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨htp, htl, hmem⟩, hk⟩ => ⟨htp, htl, hsrc.congrK ?_ hk, h1, h64⟩
  · xrun [State.ea, Core.field, hdi, fieldAddress, hp, hl,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  · rw [hmem]
    exact InScr.refl _ _ _

end VG.Proof.Dsa.X86_64
