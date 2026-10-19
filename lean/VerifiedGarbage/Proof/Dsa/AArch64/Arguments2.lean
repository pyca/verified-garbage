module

public import VerifiedGarbage.Proof.Dsa.AArch64.Arguments
import VerifiedGarbage.Proof.Framework.Block

/-! # Input and output bindings for streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def Arguments2 (mem original : Mem) (B : Addr) (a output : Operand) : Prop :=
  word mem B (8 * arg) = pointerValue original B a.pointer ∧
  word mem B (8 * argLen) = word original B a.length.offset ∧
  word mem B (8 * result) = pointerValue original B output.pointer ∧
  word mem B (8 * resultLen) = word original B output.length.offset

/-- Bind the reduction input and result while preserving saved fields and
both structural and modulus words of the selected child. -/
theorem arguments2_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 256 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (a output : Operand) (ha : pointerFits a.pointer) (hout : pointerFits output.pointer) :
    WP isa (.block (Core.operand arg argLen a ++ Core.operand result resultLen output)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Arguments2 t.mem s.mem B a output ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B argumentRanges s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hn := hg.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hual, hfieldsu, hfu, hku⟩ => ?_
  have hchildu := call_ready child hfu (by decide) (by decide) ho (by omega)
  refine WP.mono (operand_context hgu hZ output hout (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨hgt, hto, htol, hfieldst, hft, hkt⟩ => ?_
  rw [pointerValue_congr hfieldsu] at hto
  rw [hfieldsu output.length] at htol
  refine ⟨hgt, call_ready hchildu hft (by decide) (by decide) ho (by omega), ?_,
    fun f => (hfieldst f).trans (hfieldsu f), ?_, (hku.trans hkt).mono (by decide)⟩
  · exact ⟨(call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hua,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hual, hto, htol⟩
  · exact (call_argument_frame hfu (by decide) (by decide)).trans
      (call_argument_frame hft (by decide) (by decide))

end VG.Proof.Dsa.AArch64
